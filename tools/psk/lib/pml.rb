#
# PSK tool set
# pml.rb
#
# PML data format classes
#
# Provide smart accessors, caching, etc.
#
module PML

  RE_HEX=/[0-9A-Fa-f]/

  def assert(msg)
    unless yield
      pnt = Thread.current.backtrace[1]
      $stderr.puts ("#{$0}: Assertion failed in #{pnt}: #{msg}")
      puts "    "+Thread.current.backtrace[1..-1].join("\n    ")
      exit 1
    end
  end

  # TODO: refactor label stuff
  def parse_mbb_label(label)
    label =~ /\A\.LBB(\d+)_(\d+)$/
    [$1.to_i, $2.to_i] if $1
  end

  def dquote(str)
    '"' + str + '"'
  end

  def merge_ranges(r1,r2=nil)
    assert("first argument is nil") { r1 }
    r1=Range.new(r1,r1) unless r1.kind_of?(Range)
    return r1 unless r2
    [r1.min,r2.min].min .. [r1.max,r2.max].max
  end

  def reachable_set(entry)
    reachable = Set.new
    todo = [entry]
    while !todo.empty?
      item = todo.pop
      next if reachable.include?(item)
      reachable.add(item)
      successors = yield item
      successors.each do |succ|
        todo.push(succ)
      end
    end
    reachable
  end

  # Proxy for YAML data
  class Proxy
    # The PML data corresponding to the object
    attr_reader :data
  end

  # Proxy for read-only lists
  class ListProxy
    attr_reader :list
    def to_s
      list.to_s
    end
    def method_missing(name,*args,&block)
      list.send(name,*args,&block)
    end
  end

  # class providing convenient accessors and additional program information derived
  # from PML files
  class PMLDoc < Proxy
    attr_reader :bitcode_functions,:machine_functions,:flowfacts

    def initialize(data_or_io)
      stream = if data_or_io.kind_of?(Array)
                 data_or_io
               elsif data_or_io.kind_of?(IO)
                 stream = YAML::load_stream(data_or_io)
                 stream = stream.documents if stream.respond_to?(:documents) # ruby 1.8 compat
                 stream
               elsif
                 [data_or_io]
               end
      if stream.length == 1
        @data = stream[0]
      else
        @data = PMLDoc.merge_stream(stream)
      end
      @bitcode_functions = FunctionList.new(@data['bitcode-functions'])
      @machine_functions = FunctionList.new(@data['machine-functions'])
      @data['flowfacts'] ||= []
      @flowfacts = FlowFactList.from_pml(self, @data['flowfacts'])
    end
    def add_timing(timing_entry)
      @data['timing'] ||= []
      @data['timing'].push(timing_entry.data)      
    end
    def to_s
      "PMLDoc{bitcode-functions: |#{bitcode_functions.length}|, machine-functions: |#{machine_functions.length}"+
        ", flowfacts: |#{flowfacts.length}|}"
    end
    def dump_to_file(filename)
      if filename.nil?
        dump($>)
      else
        File.open(filename, "w") do |fh|
          dump(fh)
        end
      end
    end
    def dump(io)
      io.write(YAML::dump(data))
    end

    def PMLDoc.from_file(filename)
      File.open(filename) { |fh| PMLDoc.new(fh) }
    end

    def PMLDoc.merge_stream(stream)
      merged_doc = {}
      stream.each do |doc|
        doc.each do |k,v|
          if(v.kind_of? Array)
            (merged_doc[k]||=[]).concat(v)
          elsif(! merged_doc[k])
            merged_doc[k] = doc[k]
          elsif(merged_doc[k] != doc[k])
            raise Exception.new("psk-merge: mismatch in non-list attribute #{k}: #{merged_doc[k]} and #{doc[k]}")
          end
        end
      end
      merged_doc
    end
  end
  
  class Reference < Proxy
    attr_reader :qname
    def Reference.from_pml(functions, data)
      assert("PML Reference: no function attribute") { data['function'] }
      function = functions.by_name(data['function'])
      if block = data['block']
        block = function.blocks.by_name(block)
        if index = data['instruction']
          ins = block.instructions[index]
          return InstructionRef.new(ins,data)
        else
          return BlockRef.new(block,data)
        end
      elsif loop = data['loop']
        loop = function.blocks.by_name(loop)
        return LoopRef.new(loop, data)
      else
        return FunctionRef.new(function,data)
      end
    end
  end

  # Qualified name for functions
  class FunctionRef < Reference
    attr_reader :function, :qname
    def initialize(function, data=nil)
      @function = function
      @qname = function.qname
      @data = data || { 'function' => function.name }
    end
  end

  # Qualified name for blocks
  class BlockRef < Reference
    attr_reader :block, :qname
    def initialize(block, data = nil)
      @block = block
      @qname = block.qname
      @data = data || { 'function' => block.function.name, 'block' => block.name }
    end
  end

  # Qualified name for loops
  class LoopRef < Reference
    attr_reader :loopblock, :qname
    def initialize(block, data = nil)
      @loopblock = block
      @qname = block.qname
      @data = data || { 'function' => loopblock.function.name, 'loop' => loopblock.name }
    end
  end

  # Qualified name for instructions
  class InstructionRef < Reference
    attr_reader :instruction, :qname
    def initialize(instruction, data = nil)
      @instruction = instruction
      @qname = instruction.qname
      @data = data || { 'function' => instruction.function.name,
        'block' => instruction.block.name, 'instruction' => instruction.name }
    end
    def block
      instruction.block
    end
  end

  # Lists of functions, blocks and instructions
  class ProgramPointList < ListProxy
    attr_reader :list
    def initialize(list)
      @list = list
      build_lookup
    end
    def by_name(key)
      lookup(@named,key,"name")
    end
    private
    def lookup(dict,key,name)
      v = dict[key]
      raise Exception.new("#{self.class}#by_#{name}: No object with key '#{key}' in #{dict.inspect}") unless v
      v
    end
    def add_lookup(dict,key,val,name,opts={})
      return if ! key && opts[:ignore_if_missing]
      raise Exception.new("#{self.class}#by_#{name}: Duplicate object with key #{key}: #{val} and #{dict[key]}") if dict[key]
      dict[key] = val
    end
    def build_lookup
      @named = {}
      @list.each do |v|
        add_lookup(@named,v.name,v,"name")
      end
    end
  end

  # List of functions in the program
  class FunctionList < ProgramPointList
    def initialize(data)
      super(data.map { |f| Function.new(f) })
      @data = data
    end

    # return [rs, unresolved]
    # rs .. list of (known functions) reachable from name
    # unresolved .. set of callsites that could not be resolved
    def reachable_from(name)
      unresolved = Set.new
      rs = reachable_set(by_name(name)) { |f|
        callees = []
        f.each_callsite { |cs|
          cs['callees'].each { |n|
            if(! @named[n])
              unresolved.add(cs)
            else
              callees.push(by_name(n))
            end
          }
        }
        callees
      }
      [rs, unresolved]
    end

    def [](name)
      by_name(name)
    end
    def by_address(addr)
      lookup(@address, addr, "address")
    end
    def by_label(label)
      lookup(@labelled, label, "label")
    end
    def build_lookup
      super()
      @address = {}
      @labelled = {}
      @list.each do |v|
        add_lookup(@labelled,v.label,v,"label",:ignore_if_missing => true)
        add_lookup(@address,v.address,v,"address",:ignore_if_missing => true)
      end
    end
  end

  # List of PML basic blocks in a function
  class BlockList < ProgramPointList
    def initialize(function, data)
      super(data.map { |b| Block.new(function, b) })
      @data = data
    end
    def first
      @list.first
    end
    def [](name)
      by_name[name]
    end
  end

  # List of PML instructions in a block
  class InstructionList < ProgramPointList
    def initialize(block, data)
      super(data.map { |i| Instruction.new(block, i) })
      @data = data
    end
    def [](index)
      @list[index]
    end
  end
  
  # References to Program Points (functions, blocks, instructions)
  class ProgramPointProxy < Proxy
    attr_reader :name, :qname
    def address
      @data['address']
    end
    def address=(value)
      @data['address']=value
    end
    def ==(other)
      qname == other.qname
    end
    def <=>(other)
      qname <=> other.qname
    end
    def eql?(other); self == other ; end
  end

  #  PML function wrapper
  class Function < ProgramPointProxy
    attr_reader :blocks, :loops
    def initialize(mf)
      @data = mf
      @name = @data['name']
      @qname = name
      @hash = name.hash
      @loops = []
      @blocks = BlockList.new(self, @data['blocks'])
      blocks.each do |block|
        if(block.loopheader?)
          @loops.push(block)
        end
      end
    end
    def ref
      FunctionRef.new(self)
    end
    def [](k)
      assert("Function: do not access blocks/loops directly") { k!='blocks'&&k!='loops'}
      @data[k]
    end
    def hash; @hash ; end
    def to_s
      "#{@data['mapsto']}/#{name}"
    end
    def address
      @data['address'] || blocks.first.address
    end
    def label
      @data['label'] || @data['mapsto'] || blocks.first.label
    end
    def each_callsite
      blocks.each do |block|
        block.callsites.each do |cs|
          yield cs
        end
      end
    end
  # end of class Function
  end


  # Class representing PML Basic Blocks
  class Block < ProgramPointProxy
    attr_reader :function,:instructions,:loopnest
    def initialize(function,mbb)
      @data = mbb
      @function = function
      @name = @data['name']
      @qname = label
      @hash = qname.hash

      loopnames = @data['loops'] || []
      @loopnest = loopnames.length
      @is_loopheader = loopnames.first == self.name

      die("No instructions in #{@name}") unless @data['instructions']
      @instructions = InstructionList.new(self, @data['instructions'])
    end
    def [](k)
      assert("Do not access instructions via []") { k != 'instructions' }
      assert("Do not access predecessors/successors directly") { k != 'predecessors' && k != 'successors' } 
      assert("Do not access loops directly") { k != 'loops' } 
      @data[k]
    end
    # loops: not ready at initialization time    
    def loops
      return @loops if @loops
      @loops = (@data['loops']||[]).map { |l| function.blocks.by_name(l) }
    end

    # block predecessors; not ready at initialization time
    def predecessors
      return @predecessors if @predecessors
      @predecessors = (@data['predecessors']||[]).map { |s| function.blocks.by_name(s) }.uniq.freeze
    end
    # block successors; not ready at initialization time
    def successors
      return @successors if @successors
      @successors = (@data['successors']||[]).map { |s| function.blocks.by_name(s) }.uniq.freeze
    end
    def ref
      BlockRef.new(self)
    end
    def to_s
      "#{function['mapsto']}/#{qname}"
    end
    def hash; @hash ; end
    def loopheader? ; @is_loopheader ; end
    def callsites
      instructions.list.select { |i| (i['callees']||[]).length > 0 }
    end
    def calls?
      ! callsites.empty?
    end
    def loopref
      assert("Block#loopref: not a loop header") { self.loopheader? }
      LoopRef.new(self)
    end
    # LLVM specific (arch specific?)
    def label
      Block.get_label(function.name, name)
    end
    def Block.get_label(fname,bname)
      ".LBB#{fname}_#{bname}"
    end
  end

  # Proxy for PML instructions
  class Instruction < ProgramPointProxy
    attr_reader :data, :block
    def initialize(block,ins)
      @block = block
      @data = ins
      @name = index
      @qname = "#{block.label}+#{@name}"
      @hash = @qname.hash
    end
    def ref
      InstructionRef.new(self)
    end
    def function
      block.function
    end
    def [](k)
      @data[k]
    end
    def to_s
      "#{function['mapsto']}/#{qname}"
    end
    def hash; @hash ; end
    def index ; @data['index']; end
  end

  # List of flowfacts (modifiable)
  class FlowFactList < ListProxy
    def initialize(list, data = nil)
      assert("list is nil") { list }
      @list = list
      @data = data ? data : list.map { |ff| ff.to_pml }
      build_index
    end
    def FlowFactList.from_pml(pml, data)
      FlowFactList.new(data.map { |d| FlowFact.from_pml(pml,d) }, data)
    end
    def add(ff)
      @list.push(ff)
      @data.push(ff.data)
      add_index(ff)
    end
    private
    def build_index
      @by_class = {}
      @list.each { |ff| add_index(ff) }
    end
    def add_index(ff)
      (@by_class[ff.classification]||=[]).push(ff)
    end
  end

  # List of Terms
  class TermList < ListProxy
    def initialize(list,data=nil)
      @list = list
      @data = data ? data : to_pml
    end
    def to_pml
      list.map { |t| t.to_pml }
    end
  end

  # Term (ProgramPoint, Factor)
  class Term < Proxy
    attr_reader :ppref, :factor
    def initialize(ppref,factor)
      @ppref,@factor = ppref,factor
      @data = data ? data : to_pml
    end
    def to_pml
      { 'factor' => factor, 'program-point' => ppref.data }
    end
    def Term.from_pml(mod,data)
      Term.new(Reference.from_pml(mod,data['program-point']), data['factor'])
    end
  end

  # Flow Fact utility class
  class FlowFact < Proxy
    ATTRIBUTES = %w{classification level origin}
    attr_reader :scope, :lhs, :op, :rhs
    def initialize(scope, lhs, op, rhs, data = nil)
      assert("scope not a reference") { scope.kind_of?(Reference) }
      assert("lhs not a list proxy") { lhs.kind_of?(ListProxy) }
      @scope, @lhs, @op, @rhs = scope, lhs, op, rhs
      @attributes = {}
      if data
        @data = data
        @data.each do |k,v|
          add_attribute(k,v) if ATTRIBUTES.include?(k)
        end
      else
        @data = to_pml
      end
    end
    def FlowFact.from_pml(pml, data)
      mod = if data['level'] == 'bitcode' 
              pml.bitcode_functions
            elsif data['level'] == 'machinecode'
              pml.machine_functions
            else
              raise Exception.new("Unsupported representation level: #{data['level']}")
            end
      scope = Reference.from_pml(mod,data['scope'])
      lhs = TermList.new(data['lhs'].map { |t| Term.from_pml(mod,t) })
      ff = FlowFact.new(scope, lhs, data['op'], data['rhs'], data)
    end
    def add_attribute(k,v)
      assert("Bad attribute #{k}") { ATTRIBUTES.include?(k) }
      @data[k] = v
      @attributes[k] = v
    end
    def add_attributes(attrs,moreattrs={})
      attrs.merge(moreattrs).each { |k,v| add_attribute(k,v) }
    end
    def classification
      @attributes['classification']
    end
    def [](k)
      @attributes[k]
    end
    def to_pml
      { 'scope' => scope.data,
        'lhs' => lhs.to_pml,
        'op' => op,
        'rhs' => rhs,
      }.merge(@attributes)
    end

    # Flow fact builders
    def FlowFact.block_frequency(scoperef, block, freq, fact_context, classification)
      terms = [ Term.new(block.ref, 1) ]
      flowfact = FlowFact.new(scoperef, TermList.new(terms),'less-eqal',freq.max)
      flowfact.add_attributes(fact_context, 'classification' => classification)
      flowfact
    end

    def FlowFact.calltargets(scoperef, cs, receiverset, fact_context, classification)
      terms = [ Term.new(cs.ref, -1) ]
      receiverset.each do |function| 
        terms.push(Term.new(function.ref, 1))
      end      
      flowfact = FlowFact.new(scoperef,TermList.new(terms),'equal',0)
      flowfact.add_attributes(fact_context, 'classification' => classification)
      flowfact
    end

    # Dynamic classification and simplification of special purpose flowfacts

    # if this is a flowfact constraining the frequency of a single block,
    # return [scope, block, freq]
    #  block  ... BlockRef
    #  freq   ... Integer
    def get_block_frequency_bound
      return nil unless lhs.list.length == 1
      term = lhs.list.first
      return nil unless term.factor == 1
      [scope, term.ppref, rhs]
    end

    # if this is a calltarget-* flowfact, return [scope, cs, targets]:
    #   cs      ... InstructionRef
    #   targets ... [FunctionRef]
    def get_calltargets
      callsite_candidate = lhs.list.select { |term|
        term.factor.abs == 1 && term.ppref.kind_of?(InstructionRef)
      }
      return nil unless callsite_candidate.length == 1
      callsite = callsite_candidate.first.ppref
      opposite_factor = callsite_candidate.first.factor
      targets = []
      lhs.each { |term|
        next if term == callsite_candidate.first
        return nil unless term.factor == -opposite_factor
        return nil unless term.ppref.kind_of?(FunctionRef)
        targets.push(term.ppref.function)
      }
      [scope, callsite, targets]
    end
  end

  # timing entries are used to record WCET analysis results or measurement results
  class TimingEntry < Proxy
    def initialize(scope, cycles, context)
      @data = context.dup
      @data['scope'] ||= scope.data
      @data['cycles'] = cycles
    end
    def to_s
      @data.to_s
    end
  end
# end of module PML
end