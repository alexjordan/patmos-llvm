#
# platin toolkit
#
# The pml tool is used to
# - validate PML files
# - merge PML files into a single file
# - print statistics for a PML file
# - visualize PML files
#
require 'set'
require 'platin'
include PML

begin
  require 'kwalify'
rescue Exception => details
  warn "Failed to load library kwalify"
  info "  ==> gem1.9 install kwalify"
  die "Failed to load required ruby libraries"
end

class PMLTool
  attr_reader :pml, :options
  def initialize(pml, options)
    @pml, @options = pml, options
  end

  # validate input PML file
  def validate
    schema_file = options.pml_schema_file
    unless schema_file
      platin_lib_dir = File.dirname(File.dirname(File.absolute_path(__FILE__)))
      schema_file = File.join(platin_lib_dir,"core","pml.yml")
    end
    schema = YAML.load_file(schema_file)
    # create validator
    validator = Kwalify::Validator.new(schema)
    # validate
    validation_errors = validator.validate(pml.data)
    # show errors
    if validation_errors && !validation_errors.empty?
      for e in validation_errors
        warn "[#{e.path}] #{e.message}"
      end
    end
    die("Invalid PML file") unless validation_errors.empty?
    info("No YAML validation errors")

    # additional semantic validations
    validate_rgs(pml.relation_graphs)
    validate_timing(pml.timing)
  end

  def validate_rgs(rgs)
    rgs.each { |rg|
      if rg.status != 'valid'
        warn("Problematic relation graph (#{rg.status}): #{rg}")
      end
    }
  end

  # semantic validation of PML/timing
  def validate_timing(entries)
    trace_timing = entries.by_origin('trace')
    trace_timing = trace_timing.first if trace_timing
    entries.each { |te|
      next unless te.profile
      next unless te.cycles >= 0
      total_cycles, accum_cycles, simple_cycles = te.cycles, 0, 0
      te.profile.each { |pe|
        next unless pe.wcetfreq
        accum_cycles        += pe.wcet_contribution
        simple_cycles       += pe.cycles * pe.wcetfreq
      }
      if trace_timing && trace_timing.cycles > te.cycles
        warn("Timing entry #{te}: WCET cycles are less than cycles from origin <trace>")
      end
      if total_cycles != accum_cycles
        warn("Timing entry #{te}: cycles in profile sum up to #{accum_cycles}, which is different to WCET #{total_cycles}")
      elsif total_cycles < simple_cycles
        info("Timing entry #{te}: weighted sum of block WCETs is #{simple_cycles} "+
             "(factor: #{simple_cycles.to_f / total_cycles})")
      end
      if simple_cycles < accum_cycles
        warn("Timing entry #{te}: weighted sum of block WCETs #{simple_cycles} in profile is less than "+
             "sum of cummulative WCETs #{accum_cycles}")
      end
    }
  end

  def print_flowfacts(io = $stdout)
    print_by_origin(pml.flowfacts.list, "flowfacts", io) { |ffs|
      ffs.group_by { |ff|
        ff.classification_group(@pml)
      }.each { |klass,ffs2|
        puts "--- #{klass} ---"
        ffs2.each { |ff|
          puts ff
        }
      }
    }
  end

  def print_valuefacts(io = $stdout)
    print_by_origin(pml.valuefacts.list, "valuefacts", io) { |vfs|
      vfs.each { |vf| puts vf }
    }
  end

  def print_timings(print_profiles, io = $stdout)
    print_by_origin(pml.timing.list, "timings", io) { |tes|
      tes.each { |te|
        puts te
        te.profile.each { |pe|
          puts "  #{pe.to_s}"
        } if print_profiles & te.profile
      }
    }
  end

  def print_by_origin(set, setname, io)
    set.group_by { |info|
      info.origin
    }.each { |origin,infos|
      io.puts "=== #{setname} generate by #{origin} ==="
      yield infos
    }
    puts "" unless set.empty?
  end

  def PMLTool.run(pml,options)
    tool = PMLTool.new(pml, options)
    if(options.validate)
      tool.validate
    end

    tool.print_flowfacts if options.print_flowfacts
    tool.print_valuefacts if options.print_valuefacts
    tool.print_timings(options.print_profiles) if options.print_timings || options.print_profiles

    if(options.stats)
      stats = {}
      stats['machine code functions'] = pml.machine_functions.length
      stats['machine code blocks'] = pml.machine_functions.map { |mf| mf.blocks.length}.inject(0,:+)
      stats['bitcode functions'] = pml.bitcode_functions.length
      stats['bitcode blocks'] = pml.bitcode_functions.map { |b| b.blocks.length}.inject(0,:+)
      stats['relation graphs'] = pml.relation_graphs.length
      stats['relation graph nodes'] = pml.relation_graphs.map { |rg| rg.nodes.length}.inject(0,:+)
      stats['timing entries'] = pml.timing.length
      stats['valuefacts'] = pml.valuefacts.length
      stats['flowfacts'] = pml.flowfacts.length
      pml.flowfacts.stats(pml).each { |level,by_group|
        by_group.each { |group, by_class|
          next if group == :cnt
          stats["flowfacts/#{level}/#{group}"] = by_class[:cnt]
        }
      }
      statistics("PML", stats)
    end
    pml
  end
  def PMLTool.add_config_options(opts)
    opts.on("--schema FILE", "PML schema") { |f| opts.options.pml_schema_file = f }
  end
  def PMLTool.add_options(opts)
    PMLTool.add_config_options(opts)
    opts.writes_pml # output option => merge
    opts.on("--validate", "validate PML file") { opts.options.validate=true }
    opts.on("--print-flowfacts", "print flowfacts in PML file") { opts.options.print_flowfacts = true }
    opts.on("--print-valuefacts", "print valuefacts in PML file") { opts.options.print_valuefacts = true }
    opts.on("--print-timings", "print timings in PML file") { opts.options.print_timings = true }
    opts.on("--print-profiles", "print timing profiles in PML file") { opts.options.print_profiles = true }
    opts.on("--print-all", "print all analysis results stored in PML file") {
      opts.options.print_flowfacts = opts.options.print_valuefacts = opts.options.print_timing = true
    }
  end
end

if __FILE__ == $0
  synopsis="Validate, inspect and/or merge PML documents"
  options, args = PML::optparse([], "", synopsis) do |opts|
    opts.needs_pml
    PMLTool.add_options(opts)
  end
  updated_pml = PMLTool.run(PMLDoc.from_files(options.input), options)
  updated_pml.dump_to_file(options.output) if options.output
end
