//===- lib/Support/PMLExport.h -----------------------------------------===//
//
//               YAML definitions for exporting LLVM datastructures
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_PML_EXPORT_H_
#define LLVM_PML_EXPORT_H_

#include "llvm/Module.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/YAMLParser.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/YAMLTraits.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Target/TargetInstrInfo.h"


/// YAML serialization for LLVM modules (machinecode,bitcode)
/// produces one or more documents of type llvm::yaml::Doc.
/// Serializing to a sequence of documents reduces the memory
/// footprint; during analysis, documents are usually linked into
/// a single document.

/// Utility for declaring that a std::vector of a particular *pointer*type
/// should be considered a YAML sequence. Must only be used in namespace
/// llvm/yaml.
#define IS_PTR_SEQUENCE_VECTOR(_type)                                        \
    template<>                                                               \
    struct SequenceTraits< std::vector<_type*> > {                           \
      static size_t size(IO &io, std::vector<_type*> &seq) {                 \
        return seq.size();                                                   \
      }                                                                      \
      static _type& element(IO &io, std::vector<_type*> &seq, size_t index) {\
        if ( index >= seq.size() )                                           \
          seq.resize(index+1);                                               \
        return *seq[index];                                                  \
      }                                                                      \
    };
#define IS_PTR_SEQUENCE_VECTOR_1(_type)                                      \
    template<typename _member_type>                                          \
    struct SequenceTraits< std::vector<_type<_member_type>*> > {             \
      static size_t size(IO &io, std::vector<_type<_member_type>*> &seq) {   \
          return seq.size();                                                 \
      }                                                                      \
      static _type<_member_type>& element(IO &io,                            \
          std::vector<_type<_member_type>*> &seq, size_t index) {            \
          if ( index >= seq.size() )                                         \
            seq.resize(index+1);                                             \
          return *seq[index];                                                \
      }                                                                      \
    };


/// Utility for deleting owned members of an object
#define DELETE_MEMBERS(vec) \
    while(! vec.empty()) { \
      delete vec.back(); \
      vec.pop_back(); \
    } \

namespace llvm {
namespace yaml {

/// A string representing an identifier (string,index,address)
struct Name {
    // String representation
    std::string NameStr;
    // Empty Name
    Name() : NameStr("") {}
    /// Name from string
    Name(const StringRef& name) : NameStr(name.str()) {}
    /// Name from unsigned integer
    Name(uint64_t name) : NameStr(utostr(name)) {}
    /// get name as string
    StringRef getName() const {
        return StringRef(NameStr);
    }
    /// get name as unsigned integer
    uint64_t getNameAsInteger(unsigned Radix = 10) const {
        uint64_t IntName;
        getName().getAsInteger(Radix, IntName);
        return IntName;
    }
};

/// Comparing two names
bool operator==(const Name n1, const Name n2) {
    return n1.NameStr == n2.NameStr;
}

template<>
struct ScalarTraits<Name> {
    static void output(const Name &value, void*, llvm::raw_ostream &out) {
        out << value.getName();
    }
    static StringRef input(StringRef scalar, void*, Name &value) {
        value.NameStr = scalar.str();
        return StringRef();
    }
};
template <> struct SequenceTraits< std::vector<Name> > {
    static size_t size(IO &io, std::vector<Name> &seq) {
        return seq.size();
      }
      static Name& element(IO &io, std::vector<Name> &seq, size_t index) {
        if ( index >= seq.size() )
          seq.resize(index+1);
        return seq[index];
      }
      static const bool flow = true;
};

/// Representation Level (source, bitcode, machinecode)
enum ReprLevel { level_bitcode, level_machinecode };
template <>
struct ScalarEnumerationTraits<ReprLevel> {
    static void enumeration(IO &io, ReprLevel& level) {
        io.enumCase(level, "bitcode", level_bitcode);
        io.enumCase(level, "machinecode", level_machinecode);
    }
};

/// Instruction Specification (generic)
struct Instruction {
    uint64_t Index;
    int64_t Opcode;
    std::vector<Name> Callees;
    Instruction(uint64_t index) : Index(index), Opcode(0) {}
    void addCallee(const StringRef function) {
        Callees.push_back(yaml::Name(function));
    }
    bool hasCallees() {
        return ! Callees.empty();
    }
};
template <>
struct MappingTraits<Instruction> {
    static void mapping(IO &io, Instruction& Ins) {
        io.mapRequired("index",   Ins.Index);
        io.mapOptional("opcode",  Ins.Opcode, (int64_t) -1);
        io.mapOptional("callees", Ins.Callees);
    }
};
IS_PTR_SEQUENCE_VECTOR(Instruction)

/// Generic MachineInstruction Specification
enum BranchType { branch_none, branch_unconditional, branch_conditional, branch_any };
template <>
struct ScalarEnumerationTraits<BranchType> {
    static void enumeration(IO &io, BranchType& branchtype) {
        io.enumCase(branchtype, "", branch_none);
        io.enumCase(branchtype, "unconditional", branch_unconditional);
        io.enumCase(branchtype, "conditional", branch_conditional);
        io.enumCase(branchtype, "any", branch_any);
    }
};
struct GenericMachineInstruction : Instruction {
    uint64_t Size;
    enum BranchType BranchType;
    std::vector<Name> BranchTargets;
    GenericMachineInstruction(uint64_t Index) :
      Instruction(Index), Size(0), BranchType(branch_none) {}
};
template <>
struct MappingTraits<GenericMachineInstruction> {
    static void mapping(IO &io, GenericMachineInstruction& Ins) {
        MappingTraits<Instruction>::mapping(io,Ins);
        io.mapOptional("size",          Ins.Size);
        io.mapOptional("branch-type",   Ins.BranchType, branch_none);
        io.mapOptional("branch-targets",Ins.BranchTargets, std::vector<Name>());
    }
};
IS_PTR_SEQUENCE_VECTOR(GenericMachineInstruction)

/// Basic Block Specification (generic)
template<typename InstructionT>
struct Block {
    Name BlockName;
    Name MapsTo;
    std::vector<Name> Successors;
    std::vector<Name> Predecessors;
    std::vector<Name> Loops;
    std::vector<InstructionT*> Instructions;
    Block(StringRef name): BlockName(name) {}
    Block(uint64_t index) : BlockName(index) {}
    ~Block() { DELETE_MEMBERS(Instructions); }
    /// Add an instruction to the block
    /// Block takes ownership of instruction
    InstructionT* addInstruction(InstructionT* Ins) {
        Instructions.push_back(Ins);
        return Ins;
    }
};

template <typename InstructionT>
struct MappingTraits< Block<InstructionT> > {
    static void mapping(IO &io, Block<InstructionT>& Block) {
        io.mapRequired("name",         Block.BlockName);
        io.mapRequired("successors",   Block.Successors);
        io.mapRequired("predecessors", Block.Predecessors);
        io.mapOptional("loops",        Block.Loops);
        io.mapOptional("mapsto",       Block.MapsTo, Name(""));
        io.mapOptional("instructions", Block.Instructions);
    }
};
IS_PTR_SEQUENCE_VECTOR_1(Block)

/// basic functions
template <typename BlockT>
struct Function {
    Name FunctionName;
    ReprLevel Level;
    Name MapsTo;
    StringRef Hash;
    std::vector<BlockT*> Blocks;
    Function(StringRef name) : FunctionName(name) {}
    Function(uint64_t name) : FunctionName(name) {}
    ~Function() { DELETE_MEMBERS(Blocks); }
    BlockT* addBlock(BlockT *B) {
        Blocks.push_back(B);
        return B;
    }
};
template <typename BlockT>
struct MappingTraits< Function<BlockT> > {
    static void mapping(IO &io, Function<BlockT>& fn) {
        io.mapRequired("name",    fn.FunctionName);
        io.mapRequired("level",   fn.Level);
        io.mapOptional("mapsto",  fn.MapsTo, Name(""));
        io.mapOptional("hash",    fn.Hash);
        io.mapRequired("blocks",  fn.Blocks);
    }
};
IS_PTR_SEQUENCE_VECTOR_1(Function)

typedef Block<Instruction> BitcodeBlock;
typedef Function<BitcodeBlock> BitcodeFunction;

/// Relation Node Type
enum RelationNodeType { rnt_entry, rnt_exit, rnt_progress, rnt_src, rnt_dst };
template <>
struct ScalarEnumerationTraits<RelationNodeType> {
    static void enumeration(IO &io, RelationNodeType& rnty) {
        io.enumCase(rnty, "entry", rnt_entry);
        io.enumCase(rnty, "exit", rnt_exit);
        io.enumCase(rnty, "progress", rnt_progress);
        io.enumCase(rnty, "src", rnt_src);
        io.enumCase(rnty, "dst", rnt_dst);
    }
};

/// Relation Graph Nodes
struct RelationNode {
    Name NodeName;
    RelationNodeType NodeType;
    Name SrcBlock;
    Name DstBlock;
    std::vector<Name> SrcSuccessors;
    std::vector<Name> DstSuccessors;
    RelationNode(Name name, RelationNodeType type)
      : NodeName(name), NodeType(type) {}
    void addSuccessor(RelationNode *RN, bool IsSrcNode) {
        if(IsSrcNode)
            SrcSuccessors.push_back(RN->NodeName);
        else
            DstSuccessors.push_back(RN->NodeName);
    }
    void setBlock(Name N, bool IsSrcBlock) {
        if(IsSrcBlock) setSrcBlock(N);
        else setDstBlock(N);
    }
    void setSrcBlock(Name N) { SrcBlock = N; }
    void setDstBlock(Name N) { DstBlock = N; }
};

template <>
struct MappingTraits< RelationNode > {
    static void mapping(IO &io, RelationNode &node) {
        io.mapRequired("name",           node.NodeName);
        io.mapRequired("type",           node.NodeType);
        io.mapOptional("src-block",      node.SrcBlock, Name(""));
        io.mapOptional("dst-block",      node.DstBlock, Name(""));
        io.mapOptional("src-successors", node.SrcSuccessors, std::vector<Name>());
        io.mapOptional("dst-successors", node.DstSuccessors, std::vector<Name>());
    }
};
IS_PTR_SEQUENCE_VECTOR(RelationNode)

/// Relation Graph Scope
struct RelationScope {
    Name Function; // XXX: should be a scope, really
    ReprLevel Level;
    RelationScope(Name f, ReprLevel level) : Function(f), Level(level) {}
};
template <>
struct MappingTraits< RelationScope > {
    static void mapping(IO &io, RelationScope &scope) {
        io.mapRequired("function", scope.Function);
        io.mapRequired("level",scope.Level);
    }
};

/// Relation Graphs
struct RelationGraph {
    static const int EntryIndex = 0;
    static const int ExitIndex  = 1;
    int NextIndex;
    RelationScope *SrcScope;
    RelationScope *DstScope;
    std::vector<RelationNode*> RelationNodes;
    RelationGraph(RelationScope *src, RelationScope *dst) : SrcScope(src), DstScope(dst) {
        RelationNodes.push_back(new RelationNode(yaml::Name(EntryIndex),rnt_entry));
        RelationNodes.push_back(new RelationNode(yaml::Name(ExitIndex),rnt_exit));
        NextIndex = 2;
    }
    ~RelationGraph() {
        delete SrcScope;
        delete DstScope;
        DELETE_MEMBERS(RelationNodes);
    }
    RelationNode *getEntryNode() { return RelationNodes[EntryIndex]; }
    RelationNode *getExitNode()  { return RelationNodes[ExitIndex]; }
    /// add a relation node (owned by graph)
    RelationNode* addNode(RelationNodeType ty) {
        RelationNode *N = new RelationNode(yaml::Name(NextIndex++),ty);
        RelationNodes.push_back(N);
        return N;
    }
};
template <>
struct MappingTraits< RelationGraph > {
    static void mapping(IO &io, RelationGraph &RG) {
        io.mapRequired("src",   *RG.SrcScope);
        io.mapRequired("dst",   *RG.DstScope);
        io.mapRequired("nodes", RG.RelationNodes);
    }
};
IS_PTR_SEQUENCE_VECTOR(RelationGraph)


/// Each document defines a version of the format, and either the
/// generic architecture, or a specialized one. Architecture specific
/// properties are defined in the architecture description.
struct GenericArchitecture {
    static const std::string Version;
    static const std::string ArchName;
    typedef GenericMachineInstruction MachineInstruction;
    typedef Block<MachineInstruction> MachineBlock;
    typedef Function<MachineBlock> MachineFunction;
};


template <typename Arch> struct Doc {
    StringRef FormatVersion;
    StringRef Architecture;
    StringRef TargetTriple;
    std::vector<BitcodeFunction*> BitcodeFunctions;
    std::vector<typename Arch::MachineFunction*> MachineFunctions;
    std::vector<RelationGraph*> RelationGraphs;

    Doc(StringRef TargetTriple)
      : FormatVersion(Arch::Version), Architecture(Arch::ArchName),
        TargetTriple(TargetTriple) {}
    ~Doc() {
        DELETE_MEMBERS(BitcodeFunctions);
        DELETE_MEMBERS(MachineFunctions);
        DELETE_MEMBERS(RelationGraphs);
    }
    /// Add a function, which is owned by the document afterwards
    void addFunction(BitcodeFunction *F) {
        BitcodeFunctions.push_back(F);
    }
    /// Add a machine function, which is owned by the document afterwards
    void addMachineFunction(typename Arch::MachineFunction* MF) {
        MachineFunctions.push_back(MF);
    }
    /// Add a relation graph, which is owned by the document afterwards
    void addRelationGraph(RelationGraph* RG) {
        RelationGraphs.push_back(RG);
    }
};
template <typename Arch>
struct MappingTraits< Doc<Arch> > {
    static void mapping(IO &io, Doc<Arch>& doc) {
        io.mapRequired("format",   doc.FormatVersion);
        // TODO this is actually more like a format-extension name
        io.mapRequired("arch",     doc.Architecture);
        io.mapRequired("triple",   doc.TargetTriple);
        io.mapOptional("bitcode-functions",doc.BitcodeFunctions);
        io.mapOptional("machine-functions",doc.MachineFunctions);
        io.mapOptional("relation-graphs",doc.RelationGraphs);
    }
};


} // end namespace yaml
} // end namespace llvm

namespace llvm {

  /// Base class for all exporters
  class PMLExport {
  public:
    PMLExport(TargetMachine *tm) {}

    virtual ~PMLExport() {}

    virtual void initialize(Module &M, yaml::Output *Output) { };

    virtual void finalize(Module &M, yaml::Output *Output) {};

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Output *Output) =0;
  };

  /// Base class for exporters that work on modules and functions
  /// On machine functions, this exports the corresponding function if available
  class PMLBitcodeExport : public PMLExport {
  public:
    PMLBitcodeExport(TargetMachine* tm) : PMLExport(tm) {}

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Output *Output);

    virtual void serializeFunction(const Function &F, yaml::Output *Output) =0;

  protected:
    const Function* getFunctionForMF(MachineFunction &MF) const;
  };

  /// Base class for exporters that use the GenericArchitecture
  template <typename ArchTrait>
  class PMLArchExport : public PMLExport {
    TargetMachine *TM;

  public:
    PMLArchExport(TargetMachine *tm) : PMLExport(tm), TM(tm) {}

    TargetMachine* getTargetMachine() { return TM; }

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Output *Output)
    {
      yaml::Doc<ArchTrait> YDoc(TM->getTargetTriple());
      serialize(MF, LI, YDoc);
      *Output << YDoc;
    }

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Doc<ArchTrait>& doc) =0;
  };

  template <typename ArchTrait>
  class PMLBitcodeArchExport : public PMLArchExport<ArchTrait>,
                                      PMLBitcodeExport
  {
    TargetMachine *TM;

  public:
    PMLBitcodeArchExport(TargetMachine *tm)
      : PMLArchExport<ArchTrait>(tm), PMLBitcodeExport(tm), TM(tm) {}

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Output *Output) {
      if (const Function *F = getFunctionForMF(MF)) {
        serializeFunction(*F, Output);
      }
    }

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Doc<ArchTrait>& doc) {
      if (const Function *F = getFunctionForMF(MF)) {
        serializeFunction(*F, doc);
      }
    }

    virtual void serializeModule(Module &M, yaml::Output *Output)
    {
      yaml::Doc<ArchTrait> YDoc(TM->getTargetTriple());
      for (Module::iterator it=M.begin(),ie=M.end(); it != ie; ++it) {
        serializeFunction(*it, YDoc);
      }
      *Output << YDoc;
    }

    virtual void serializeFunction(const Function &F, yaml::Output *Output)
    {
      yaml::Doc<ArchTrait> YDoc(TM->getTargetTriple());
      serializeFunction(F, YDoc);
      *Output << YDoc;
    }

    virtual void serializeFunction(const Function &F,
                                   yaml::Doc<ArchTrait>& doc) =0;
  };

  /// Execute several exports using the same architecture on one document.
  template <typename ArchTrait>
  class PMLExportProxy : public PMLArchExport<ArchTrait> {
    typedef std::vector<PMLArchExport<ArchTrait>*> ExporterList;
    ExporterList Exporters;
  public:
    PMLExportProxy(TargetMachine *tm) : PMLArchExport<ArchTrait>(tm) {}

    virtual ~PMLExportProxy() { DELETE_MEMBERS(Exporters); }

    void addExporter(PMLArchExport<ArchTrait>* exporter) {
      Exporters.push_back(exporter);
    }

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Doc<ArchTrait>& doc)
    {
      for (typename ExporterList::iterator it=Exporters.begin(),
           end=Exporters.end(); it != end; ++it)
      {
        (*it)->serialize(MF, LI, doc);
      }
    }
  };

  template <typename ArchTrait>
  class PMLBitcodeExportProxy : public PMLBitcodeArchExport<ArchTrait> {
    typedef std::vector<PMLArchExport<ArchTrait>*> ExporterList;
    ExporterList Exporters;
  public:
    PMLBitcodeExportProxy(TargetMachine *tm)
      : PMLBitcodeArchExport<ArchTrait>(tm) {}

    virtual ~PMLBitcodeExportProxy() { DELETE_MEMBERS(Exporters); }

    void addExporter(PMLBitcodeArchExport<ArchTrait>* exporter) {
      Exporters.push_back(exporter);
    }

    virtual void serialize(const Function &F, yaml::Doc<ArchTrait>& doc)
    {
      for (typename ExporterList::iterator it=Exporters.begin(),
           end=Exporters.end(); it != end; ++it)
      {
        (*it)->serializeFunction(F, doc);
      }
    }
  };

  typedef PMLArchExport <yaml::GenericArchitecture> PMLGenericExport;
  typedef PMLExportProxy<yaml::GenericArchitecture> PMLGenericExportProxy;
  typedef PMLBitcodeArchExport <yaml::GenericArchitecture>
                                                   PMLGenericBitcodeExport;
  typedef PMLBitcodeExportProxy<yaml::GenericArchitecture>
                                                   PMLGenericBitcodeExportProxy;


  // --------------- Standard exporters --------------------- //

  // TODO if needed, we could factor out most of the code in serialize and
  // split the Doc template related stuff into a separate class to make
  // it reusable for different architectures

  class PMLFunctionExport : public PMLGenericBitcodeExport {
  public:
    PMLFunctionExport(TargetMachine *TM) : PMLGenericBitcodeExport(TM) {}

    virtual void serializeFunction(const Function &F,
                           yaml::Doc<yaml::GenericArchitecture>& doc);

  };

  class PMLMachineFunctionExport : public PMLGenericExport {

  public:
    PMLMachineFunctionExport(TargetMachine *TM) : PMLGenericExport(TM) {}

    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Doc<yaml::GenericArchitecture>& doc);

  };

  class PMLRelationGraphExport : public PMLGenericExport {
    MachineLoopInfo *LI;

  public:
    PMLRelationGraphExport(TargetMachine *TM) : PMLGenericExport(TM), LI(0) {}

    /// Build the Control-Flow Relation Graph connection machine code and bitcode
    virtual void serialize(MachineFunction &MF, MachineLoopInfo* LI,
                           yaml::Doc<yaml::GenericArchitecture>& doc);

  private:

    /// Generate (heuristic) MachineBlock->EventName and IR-Block->EventName maps
    /// (1) if all forward-CFG predecessors of (MBB originating from BB) map to no or a different IR block,
    ///     MBB generates a BB event.
    /// (2) if there is a MBB generating a event BB, the basic block BB also generates this event
    void buildEventMaps(MachineFunction &MF,
                        std::map<const BasicBlock*,StringRef> &BitcodeEventMap,
                        std::map<MachineBasicBlock*,StringRef> &MachineEventMap,
                        std::set<StringRef> &TabuList);

    /// Check whether Source -> Target is a backedge
    bool isBackEdge(MachineBasicBlock *Source, MachineBasicBlock *Target);
  };

  // TODO Define FunctionPass that runs only BitcodeExporter
  // TODO Optionally export all functions in module in ExportPass at init?

  /// PMLExportPass - This is a pass to export a machine function to
  /// YAML (using the PML schema define at (TODO: cite report))
  class PMLExportPass : public MachineFunctionPass {

    static char ID;

    std::vector<PMLExport*> Exporters;

  protected:
    TargetMachine *TM;

    std::string OutFileName;
    tool_output_file *OutFile;
    yaml::Output *Output;

    PMLExportPass(char &id, std::string& filename, TargetMachine *tm)
      : MachineFunctionPass(id), TM(tm), OutFileName(filename),
        OutFile(0), Output(0)
        {}

  public:
    PMLExportPass(std::string& filename, TargetMachine *tm,
                  bool AddDefaultExporter = true)
      : MachineFunctionPass(ID), TM(tm), OutFileName(filename),
       OutFile(0), Output(0)
    {
      if (AddDefaultExporter) addDefaultExporter();
    }

    virtual ~PMLExportPass();

    /// addDefaultExporter - Add a set of standard PML exporter.
    /// Not virtual on purpose (overloading will not work).
    void addDefaultExporter();

    void addExporter(PMLExport *PE) { Exporters.push_back(PE); }

    // ----------------- Pass Interface  ----------------- //

    virtual const char *getPassName() const { return "YAML/PML Export"; }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const;

    virtual bool doInitialization(Module &M);

    virtual bool doFinalization(Module &M);

    /// Serialize using configured exporter. This uses
    /// the GenericArchitecture trait.
    virtual bool runOnMachineFunction(MachineFunction &MF);
  };

} // end namespace llvm

#endif
