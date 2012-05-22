set(LLVM_LINK_COMPONENTS ${LLVM_TARGETS_TO_BUILD} bitreader asmparser instrumentation ipo)

add_llvm_tool(sca
  sca.cpp
  )
