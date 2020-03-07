package kiml.frontend

import java.io.File

enum class CodegenTarget {
    Wasm,
    Interpet
}

data class Config(val codegenTarget: CodegenTarget, val outputDirectory: String)

class Pipeline {
    fun compileModules(files: List<File>, config: Config) {

    }
}