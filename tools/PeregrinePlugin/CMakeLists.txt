add_llvm_library(PeregrinePlugin MODULE PeregrinePlugin.cpp PLUGIN_TOOL clang)

if(LLVM_ENABLE_PLUGINS AND (WIN32 OR CYGWIN))
  target_link_libraries(PeregrinePlugin PRIVATE
    clangAST
    clangBasic
    clangFrontend
    LLVMSupport
    )
endif()
