package kiml.backend

import asmble.ast.Node
import asmble.ast.Node.Module
import asmble.ast.Node.Func
import asmble.ast.Node.Instr
import asmble.ast.Node.Export
import asmble.ast.Node.ExternalKind
import asmble.io.AstToBinary
import asmble.io.ByteWriter
import java.io.ByteArrayOutputStream
import java.io.File

fun gen(): Module {
    return Module(
        startFuncIndex = 0,
        funcs = listOf(
            Func(
                Node.Type.Func(emptyList(), Node.Type.Value.I32),
                emptyList(),
                listOf(
                    Instr.I32Const(21),
                    Instr.I32Const(21),
                    Instr.I32Add
                )
            )
        ),
        exports = listOf(Export("main", ExternalKind.FUNCTION, 0))
    )
}

class Codegen {
    val funcs: HashMap<String, Func> = hashMapOf()
}

fun main(): Unit {
    val mod = gen()
    val buf = ByteArrayOutputStream()
    AstToBinary().fromModule(ByteWriter.OutputStream(buf), mod)
    File("out.wasm").writeBytes(buf.toByteArray())
}