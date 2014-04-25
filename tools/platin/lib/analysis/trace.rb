#
# PLATIN tool set
#
# trace analysis (similar to SWEET single path mode)
#
require 'core/utils'
require 'core/pml'

module PML

# Class to monitor traces and generate events
# should implement a 'run' method
class TraceMonitor
  attr_reader :observers
  def initialize
    @observers = []
  end
  def subscribe(obj)
    @observers.push(obj)
  end
  def publish(msg,*args)
    @observers.each do |obs|
      obs.send(msg,*args)
    end
  end
end

#
# Class to monitor machine trace and generate events
#
# Traces need to be of the form [programcounter, cycles]
# Generated events: block, function, ret, loop{enter,exit,cont}, eof
#
class MachineTraceMonitor < TraceMonitor
  def initialize(pml, options, trace)
    super()
    @pml, @options = pml, options
    @trace = trace
    @program_entry = @pml.machine_functions.by_label(options.trace_entry)
    if not @program_entry
      die("Trace Analysis: Could not find trace entry function '#{options.trace_entry}' in PML file. Make sure it is serialized by patmos-clang.")
    end
    @start = @program_entry.blocks.first.address
    # whether an instruction is a watch point
    @wp = {}
    # basic block watch points
    @wp_block_start = {}
    # call instruction watch points
    @wp_call_instr = {}
    # return instruction watch points
    @wp_return_instr = {}
    # empty (zero-size) blocks before the key'ed block
    @empty_blocks = {}
    # Playground: Learn about instruction costs
    # @wp_instr = {}
    build_watchpoints

    assert("missing sca graph data") { @pml.sca_graph }

    @nodes = {}
    @outedges = {}

    @pml.sca_graph.nodes.each { |node|
      @nodes[node.id] = node
      @rootnode = node if node.function.mapsto == "main"
    }
    assert("main/root missing") { @rootnode }
    @pml.sca_graph.edges.each { |edge|
      srcn = @nodes[edge.src]
      dstn = @nodes[edge.dst]
      f = srcn.function
      cs = nil
      # XXX should rather enumerate instructions in f
      catch (:found) do
        iis = f.blocks.each { |bb|
          bb.instructions.each { |i|
            if i.callid == edge.inst
              cs = i
              throw :found
            end
          }
        }
      end
      assert("callsite from SCA graph not found") { cs }
      (@outedges[[srcn,cs]] ||= []) << dstn
      #(preds[dstn] ||= []) << [cs,edge]
    }

  end
  def scawalk_
    nodes = [@rootnode]
    @callstack.each { |call|
      debug(@options, :trace) { "call on stack: #{call} -> #{call.callees}" }
      node = nodes.detect { |n| n.function == call.function }
      debug(@options, :trace) { "node narrowed to: #{node}" } if nodes.length > 1
      #needle = @outedges[node].find_all { |e| e.first == call }
      #assert("cs not found") { needle }
      #nodes = needle.map { |n| n[1] }
      nodes = @outedges[[node,call]]
      assert("no node(s) for #{node}::#{call}") { nodes }
      debug(@options, :trace) { "next node(s): #{nodes}" }
    }
    node = nodes.detect { |n| n.function == @current_function }
    debug(@options, :trace) { "final narrow: #{node}" } if nodes.length > 1
    assert("unexpected end to walk"){node}
    return node.size
  end

  def scawalk(callstring)
    @callstack.clear
    callstring.each { |addr,name|
      next unless cs = @wp_call_instr[addr]
      debug(@options, :trace) { "call to #{name} maps to #{cs}" }
      @callstack << cs
      @current_function = @pml.machine_functions.by_label(name)
    }
    assert("no current function") { @current_function }
    scawalk_
  end

  # run monitor
  def run
    @finished = false # set to true on (observed) program exit
    @executed_instructions = 0
    @callstack = []
    @loopstack = nil
    @current_function = nil
    @last_block = nil
    @spill_map = Hash.new [nil,nil,nil,nil,-1]

    # Playground: learn about instruction costs
    # @last_ins  = [nil,0] # XXX: playing
    # @inscost   = {}  # XXX: playing

    pending_return, pending_call = nil, nil
    @trace.each do |t|
      (callstring,cost) = t

      if callstring.detect { |_,name| name == "exit" }
        @finished = true
        break
      end
      next unless callstring[0..-2].detect { |_,name| name == "main" }
      t_cost = Integer(/delta=(\d+)/.match(cost)[1])
      sca_cost = scawalk(callstring)
      assert("cost not in SCA graph") { sca_cost || t_cost == 0 }
      sca_cost ||= 0
      assert("under estimated") { sca_cost >= t_cost }
      debug(@options, :trace) { "sres[#{@current_function}]: static=#{sca_cost}, trace=#{t_cost}" }
      #puts "scata:0x#{@current_function.address.to_s(16)},#{sca_cost},#{t_cost}"
      shash = callstring.join('::')
      over = sca_cost - t_cost
      @spill_map[shash] = [@current_function.address.to_s(16), callstring.join('::'), sca_cost, t_cost, over] if over > @spill_map[shash][-1]
    end
    if ! @finished
      die("Trace Analysis: did not observe return from program entry #{@program_entry}")
    end

    @spill_map.each_value { |v|
      puts "scmax:0x#{v[0]},#{v[1..-1].join(',')}"
    }


    # Playground: learn about instruction costs
    # @inscost.each do |op,cycs|
    #  puts "COST #{op} #{cycs}"
    # end

    publish(:eof)
  end

  private

  def handle_loopheader(b)
    if b.loopheader?
      if b.loopnest == @loopstack.length && @loopstack[-1].loopheader.name != b.name
        publish(:loopexit, @loopstack.pop, @cycles)
      end
      if b.loopnest == @loopstack.length
        publish(:loopcont, b.loop, @cycles)
      else
        @loopstack.push b.loop
        publish(:loopenter, b.loop, @cycles)
      end
    end
  end

  def handle_call(c, call_pc)
    assert("No call instruction before function entry #{call_pc} + 1 + #{c.delay_slots}} != #{@executed_instructions}") {
      call_pc + 1 + c.delay_slots == @executed_instructions
    }
    @lastblock = nil
    @callstack.push(c)
    #debug(@options, :trace) { "Call from #{@callstack.inspect}" }
  end

  def handle_return(r, ret_pc)
    exit_loops_downto(0)
    if @callstack.empty?
      publish(:ret, r, nil, @cycles)
    else
      publish(:ret, r, @callstack[-1], @cycles)
    end
    return nil if(r.function == @program_entry) # intended program exit
    assert("Callstack empty at return (inconsistent callstack)") { ! @callstack.empty? }
    c = @callstack.pop
    @last_block = c.block
    @loopstack = c.block.loops.reverse
    @current_function = c.function
    #debug(@options, :trace) { "Return to #{c}" }
    #debug(@options, :trace) { "callstack #{@callstack}" }
  end

  def exit_loops_downto(nest)
    while nest < @loopstack.length
      publish(:loopexit, @loopstack.pop, @cycles)
    end
  end

  def build_watchpoints
    # generate watchpoints for all relevant machine functions
    @pml.machine_functions.each do |fun|
      # address of function
      addr = fun.address
      abs_instr_index = 0
      call_return_instr = {}

      # for all basic blocks
      fun.blocks.each do |block|

        # blocks that consist of labels only (used in some benchmarks for flow facts)
        if block.empty?
          (@empty_blocks[block.address]||=[]).push(block)
          next
        end

        # generate basic block event at first instruction
        add_watch(@wp_block_start, block.address, block)
        block.instructions.each do |instruction|
          # Playground: Learn about instruction costs
          # @wp_instr[instruction.address] = instruction

          # trigger return-instruction event at return instruction
          # CAVEAT: delay slots and predicated returns
          if instruction.returns?
            add_watch(@wp_return_instr,instruction.address,instruction)
          end
          # trigger call-instruction event at call instructions
          # CAVEAT: delay slots and predicated calls
          if ! instruction.callees.empty?
            add_watch(@wp_call_instr,instruction.address,instruction)
          end
          abs_instr_index += 1
        end
      end
    end
  end
  def add_watch(dict, addr, data)
    if ! addr
      warn ("No address for #{data.inspect[0..60]}")
    elsif dict[addr]
      raise Exception.new("Duplicate watchpoint at address #{addr.inspect}: #{data} already set to #{dict[addr]}")
    else
      @wp[addr] = true
      dict[addr] = data
    end
  end
end

# Recorder which just dumps event to the given stream
class VerboseRecorder
  def initialize(out=$>)
    @out = out
  end
  def method_missing(event, *args)
    @out.puts("EVENT #{event.to_s.ljust(15)} #{args.join(" ")}")
  end
end

# Recorder Specifications
class RecorderSpecification
  SPEC_RE = %r{ \A
                ([gf])
                (?: / ([0-9]+))?
                :
                ([blic]+)
                (?: / ([0-9]+))?
                \Z }x
  SCOPES = { 'g' => :global, 'f' => :function }
  ENTITIES = { 'b' => :block_frequencies, 'i' => :infeasible_blocks, 'l' => :loop_header_bounds, 'c' => :call_targets }
  attr_reader :entity_types, :entity_context, :calllimit
  def initialize(entity_types, entity_context, calllimit)
    @entity_types, @entity_context, @calllimit = entity_types, entity_context, calllimit
  end

  def RecorderSpecification.help(out=$stderr)
    out.puts("== Trace Recorder Specification ==")
    out.puts("")
    out.puts("spec              := <spec-item>,...")
    out.puts("spec-item         := <scope-selection> ':' <entity-selection>")
    out.puts("scope-selection   :=   'g' (=analysis-entry-scope)")
    out.puts("                     | 'f'['/' <callstring-length>] (=function-scopes)")
    out.puts("entity-selection  := <entity-type>+ [ '/' <callstring-length> ]")
    out.puts("entity-type       :=   'b' (=block frequencies)")
    out.puts("                     | 'i' (=infeasible blocks)")
    out.puts("                     | 'l' (=loop bounds)")
    out.puts("                     | 'c' (=indirect call targets)")
    out.puts("callstring-length := <integer>")
    out.puts("")
    out.puts("Example: g:lc/1  ==> loop bounds and call targets in global scope using callstring length 1")
    out.puts("         g:b/0   ==> block frequencies in global scope (context insensitive)")
    out.puts("         f:b     ==> local block frequencies for every executed function (default callstring/virtual inlining)")
    out.puts("         f/2:b/1 ==> block frequencies for every executed function (distinguished by callstrings")
    out.puts("                     of length 2), virtually inlining directly called functions")
  end
  def RecorderSpecification.parse(str, default_callstring_length)
    recorders = []
    str.split(/\s*,\s*/).each { |recspec|
      if recspec =~ SPEC_RE
        scopestr,scopectx,etypes,ectx,elimit = $1,$2,$3,$4,$5
        entity_types = etypes.scan(/./).map { |etype|
          ENTITIES[etype] or die("RecorderSpecification '#{recspec}': Unknown entity type #{etype}")
        }
        entity_context = ectx ? ectx.to_i : default_callstring_length
        scope_context = scopectx ? scopectx.to_i : default_callstring_length
        entity_call_limit = nil
        if scopestr == 'f' # intraprocedural
          entity_call_limit = entity_context
        end
        spec = RecorderSpecification.new(entity_types, entity_context, entity_call_limit)
        scope = SCOPES[scopestr] or die("Bad scope type #{scopestr}")
        recorders.push([scope,scope_context,spec])
      else
        die("Bad recorder Specfication '#{recspec}': does not match #{SPEC_RE}")
      end
    }
    recorders
  end
end


# Recorder for a function (intra- or interprocedural)
class FunctionRecorder
  attr_reader :results, :rid, :report_block_frequencies
  def initialize(scheduler, rid, function, context, spec)
    @scheduler = scheduler
    @rid, @function, @context = rid, function, context
    @callstack, @calllimit = [], spec.calllimit
    @callstring_length = spec.entity_context
    @report_block_frequencies = spec.entity_types.include?(:block_frequencies)
    @record_block_frequencies = @report_block_frequencies || spec.entity_types.include?(:infeasible_blocks)
    @record_calltargets = spec.entity_types.include?(:call_targets)
    @record_loopheaders = spec.entity_types.include?(:loop_header_bounds)
    @results = FrequencyRecord.new("FunctionRecorder_#{rid}(#{function}, #{context || 'global'})")
  end
  def global?
    ! @context
  end
  def type
    global? ? 'global' : 'function'
  end
  def scope
    if @context
      ContextRef.new(@function, @context)
    else
      @function
    end
  end
  def active?
    return true unless @calllimit
    @callstack.length <= @calllimit
  end
  def start(function, cycles)
    # puts "#{self}: starting at #{cycles}"
    results.start(cycles)
    @callstack = []
    function.blocks.each { |bb| results.init_block(in_context(bb)) } if @record_block_frequencies
  end
  def function(callee,callsite,cycles)
    results.call(in_context(callsite),callee) if active? && @record_calltargets
    @callstack.push(callsite)
    callee.blocks.each { |bb| results.init_block(in_context(bb)) } if active? && @record_block_frequencies
  end
  def block(bb, cycles)
    return unless active?
    # puts "#{self}: visiting #{bb} active:#{active?} calllimit:#{@calllimit}"
    results.increment_block(in_context(bb)) if @record_block_frequencies
  end
  def loopenter(loop, cycles)
    return unless active?
    assert("loopenter: not a loop") { loop.kind_of?(Loop) }
    results.start_loop(in_context(loop)) if @record_loopheaders
  end
  def loopcont(loop, _)
    return unless active?
    assert("loopcont: not a loop") { loop.kind_of?(Loop) }
    results.increment_loop(in_context(loop)) if @record_loopheaders
  end
  def loopexit(loop, _)
    return unless active?
    assert("loopexit: not a loop") { loop.kind_of?(Loop) }
    results.stop_loop(in_context(loop)) if @record_loopheaders
  end
  def ret(rsite,csite,cycles)
    if @callstack.length == 0
      # puts "#{self}: stopping at #{rsite}->#{csite}"
      results.stop(cycles)
      @scheduler.deactivate(self)
    else
      @callstack.pop
    end
  end
  def eof ; end
  def method_missing(event, *args); end
  def to_s
    results.name
  end
  def dump(io=$stdout)
    header = "Observations for #{self}\n  function: #{@function}"
    header += "\n  context: #{@context}" if @context && ! @context.empty?
    results.dump(io, header)
  end
private
  def in_context(pp)
    ctx = Context.callstack_suffix(@callstack, @callstring_length)
    ContextRef.new(pp,ctx)
  end
end

# Utility class to record frequencies when analyzing traces
class FrequencyRecord
  attr_reader :name, :runs, :cycles, :blockfreqs, :calltargets, :loopbounds
  def initialize(name)
    @name = name
    @runs = 0
    @calltargets = {}
    @loopbounds = {}
    @blockfreqs = nil
  end
  def start(cycles)
    @cycles_start = cycles
    @runs += 1
    @current_record = {}
    @current_loops = {}
  end
  def init_block(pp)
    assert("pp has wrong type: #{pp.class}") { pp.kind_of?(ContextRef) }
    @current_record[pp] ||= 0 if @current_record
  end
  def increment_block(pp)
    @current_record[pp] += 1 if @current_record
  end
  def start_loop(hpp)
    return unless @current_loops
    @current_loops[hpp] = 1
  end
  def increment_loop(hpp)
    return unless @current_loops
    @current_loops[hpp] += 1
  end
  def stop_loop(hpp)
    merge_loop_bound(hpp, @current_loops[hpp])
  end
  def to_s
    "FrequencyRecord{ name = #{@name} }"
  end
  def call(callsite,callee)
    (@calltargets[callsite]||=Set.new).add(callee) if @current_record && callsite
  end
  def stop(cycles)
    die "Recorder: stop without start: #{@name}" unless @current_record
    @cycles = merge_ranges(cycles - @cycles_start, @cycles)
    unless @blockfreqs
      @blockfreqs = {}
      @current_record.each do |bref,count|
        @blockfreqs[bref] = count .. count
      end
    else
      @current_record.each do |bref,count|
        if ! @blockfreqs.include?(bref)
          @blockfreqs[bref] = 0 .. count
        else
          @blockfreqs[bref] = merge_ranges(count, @blockfreqs[bref])
        end
      end
      @blockfreqs.each do |bref,count|
        @blockfreqs[bref] = merge_ranges(count, 0..0) unless @current_record.include?(bref)
      end
    end
    @current_record, @current_loops = nil, nil
  end
  def dump(io=$>, header=nil)
    (io.puts "No records";return) unless @blockfreqs
    io.puts "---"
    io.puts header if header
    io.puts "  cycles: #{cycles}"
    @blockfreqs.keys.sort.each do |bref|
      io.puts "  #{bref.class.to_s.ljust(15)} \\in #{@blockfreqs[bref]}"
    end
    @calltargets.each do |site,recv|
      io.puts "  #{site} calls #{recv.to_a.join(", ")}"
    end
    @loopbounds.each do |loop,bound|
      io.puts "  Loop #{loop} in #{bound}"
    end
  end
private
  def merge_loop_bound(key,bound)
    unless @loopbounds[key]
      @loopbounds[key] = bound..bound
    else
      @loopbounds[key] = merge_ranges(bound, @loopbounds[key])
    end
  end
end


# Records progress node trace
class ProgressTraceRecorder
  attr_reader :trace, :internal_preds
  def initialize(pml, entry, is_machine_code, options)
    @pml, @options = pml, options
    @trace, @entry, @rg_level = [], entry, is_machine_code ? :dst : :src
    @internal_preds, @pred_list = [], []
    @rg_callstack = []
  end
  # set current relation graph
  # if there is no relation graph, skip function
  def function(callee,callsite,cycles)
    @rg = @pml.relation_graphs.by_name(callee.name, @rg_level)
    #debug(@options,:trace) { "Call to rg for #{@rg_level}-#{callee}: #{@rg.nodes.first}" } if rg
    @rg_callstack.push(@node)
    @node = nil
  end
  # follow relation graph, emit progress nodes
  def block(bb, _)
    return unless @rg
    if ! @node
      first_node = @rg.nodes.first
      assert("at_entry == at entry RG node") {
        first_node.type == :entry
      }
      assert("at_entry == at first block") {
        bb == first_node.get_block(@rg_level)
      }
      @node = first_node
      # debug(@options, :trace) { "Visiting first node: #{@node} (#{bb})" }
      return
    end
    # find matching successor progress node
    succs = @node.successors_matching(bb, @rg_level)
    assert("progress trace: no (unique) successor (but #{succs.length}) at #{@node}, "+
           "following #{@node.get_block(@rg_level)}->#{bb} (level #{@rg_level})") {
      succs.length == 1
    }
    succ = succs.first
    if succ.type == :progress
      trace.push(succ)
      internal_preds.push(@pred_list)
      @pred_list = []
    else
      @pred_list.push(succ)
    end
    @node = succ
    # debug(@options,:trace) { "Visiting node: #{@node} (#{bb})" }
  end
  # set current relation graph
  def ret(rsite,csite,cycles)
    return if csite.nil?
    @rg = @pml.relation_graphs.by_name(csite.function.name, @rg_level)
    @node = @rg_callstack.pop
    #debug(@options, :trace) { "Return to rg for #{@rg_level}-#{csite.function}: #{@rg.nodes.first}" } if @rg
  end
  def eof ; end
  def method_missing(event, *args); end
end


end # module pml
