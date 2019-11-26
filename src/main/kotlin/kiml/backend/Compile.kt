package kiml.backend

import asmble.ast.Node
import asmble.ast.Node.Module
import asmble.ast.Node.Func
import asmble.ast.Node.Instr
import asmble.ast.Node.Export
import asmble.ast.Node.ExternalKind
import asmble.ast.Node.Type.Value
import asmble.io.AstToBinary
import asmble.io.AstToSExpr
import asmble.io.ByteWriter
import kiml.syntax.Expression
import java.io.ByteArrayOutputStream
import java.io.File
import kotlin.reflect.jvm.internal.ReflectProperties

fun gen(): Module {
    return Module(
        startFuncIndex = 0,
        funcs = listOf(
            Func(
                Node.Type.Func(emptyList(), Value.I32),
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
    val globals: MutableList<Pair<String, Node.Global>> = mutableListOf()
    val types: MutableList<Pair<String, Node.Type.Func>> = mutableListOf()
    val funcs: MutableList<Pair<String, Func>> = mutableListOf()
    var locals: MutableList<Pair<String, Value>> = mutableListOf()

    fun init_rts(): Pair<Int, Int> {
        val watermark =
            register_global("watermark", Node.Global(Node.Type.Global(Value.I32, true), listOf(Instr.I32Const(0))))
        val allocate = make_fn1("allocate", "bytes" to Value.I32) { bytes ->
            listOf(
                Instr.GetGlobal(watermark),
                Instr.GetGlobal(watermark),
                Instr.GetLocal(bytes),
                Instr.I32Add,
                Instr.SetGlobal(watermark)
            )
        }
        val mk_closure =
            make_fn2("make_closure", "arity" to Value.I32, "code_pointer" to Value.I32) { arity, code_pointer ->
                val closure_start = register_local("closure_start", Value.I32)
                listOf(
                    Instr.I32Const(4),
                    Instr.GetLocal(arity),
                    Instr.I32Mul,
                    Instr.I32Const(8), // arity + applied + code_pointer
                    Instr.I32Add,
                    Instr.Call(allocate),
                    Instr.SetLocal(closure_start),
                    Instr.GetLocal(closure_start),
                    Instr.GetLocal(arity),
                    Instr.I32Store16(1, 0),
                    Instr.GetLocal(closure_start),
                    Instr.I32Const(4),
                    Instr.I32Add,
                    Instr.GetLocal(code_pointer),
                    Instr.I32Store(2, 0),
                    Instr.GetLocal(closure_start)
                )
            }
        val apply_closure = make_fn2(
            "apply_closure",
            "closure_start" to Value.I32,
            "argument" to Value.I32
        ) { closure_start, argument ->
            val arity = register_local("arity", Value.I32)
            val applied = register_local("applied", Value.I32)
            val code_pointer = register_local("code_pointer", Value.I32)
            listOf(
                Instr.GetLocal(closure_start),
                Instr.I32Load16S(1, 0),
                Instr.SetLocal(arity),

                Instr.GetLocal(closure_start),
                Instr.I32Const(2),
                Instr.I32Add,
                Instr.I32Load16S(1, 0),
                Instr.SetLocal(applied),

                Instr.GetLocal(closure_start),
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.I32Load(2, 0),
                Instr.SetLocal(code_pointer),

                Instr.I32Const(8),
                Instr.I32Const(4),
                Instr.GetLocal(applied),
                Instr.I32Mul,
                Instr.I32Add,
                Instr.GetLocal(argument),
                Instr.I32Store(2, 0),

                Instr.GetLocal(applied),
                Instr.I32Const(1),
                Instr.I32Add,
                Instr.GetLocal(arity),
                Instr.I32LtS,

                Instr.If(Value.I32),
                // Location of applied
                Instr.GetLocal(closure_start),
                Instr.I32Const(2),
                Instr.I32Add,
                // applied++
                Instr.GetLocal(applied),
                Instr.I32Const(1),
                Instr.I32Add,
                Instr.I32Store16(1, 0),

                // Not all arguments were applied so we return the closure
                Instr.GetLocal(closure_start),
                Instr.Else,
                // Location of arguments
                Instr.GetLocal(closure_start),
                Instr.I32Const(8),
                Instr.I32Add,

                Instr.GetLocal(code_pointer),
                Instr.CallIndirect(
                    register_type("int_to_int", Node.Type.Func(listOf(Value.I32), Value.I32)),
                    false
                ),
                Instr.End
            )
        }

        return mk_closure to apply_closure
    }

    fun register_local(name: String, ty: Value): Int {
        val res = this.locals.size
        locals.add(name to ty)
        return res
    }

    fun register_func(name: String, func: Func): Int {
        val res = this.funcs.size
        funcs.add(name to func)
        return res
    }

    fun register_global(name: String, global: Node.Global): Int {
        val res = this.globals.size
        globals.add(name to global)
        return res
    }

    fun register_type(name: String, typ: Node.Type.Func): Int {
        val res = this.types.size
        types.add(name to typ)
        return res
    }

    private fun make_fn1(name: String, arg: Pair<String, Value>, body: (Int) -> List<Instr>): Int {
        locals = mutableListOf(arg)
        val instrs = body(0)
        val new_func = Func(Node.Type.Func(listOf(arg.second), Value.I32), locals.drop(1).map { it.second }, instrs)
        locals = mutableListOf()
        return register_func(name, new_func)
    }

    private fun make_fn2(
        name: String,
        arg1: Pair<String, Value>,
        arg2: Pair<String, Value>,
        body: (Int, Int) -> List<Instr>
    ): Int {
        locals = mutableListOf(arg1, arg2)
        val instrs = body(0, 1)
        val new_func =
            Func(Node.Type.Func(listOf(arg1.second, arg2.second), Value.I32), locals.drop(2).map { it.second }, instrs)
        locals = mutableListOf()
        return register_func(name, new_func)
    }

    fun func_index(name: String): Int = funcs.indexOfFirst { name == it.first }

    fun compileExpression(expr: Expression): List<Instr> {
        return when (expr) {
            is Expression.Int -> listOf(Instr.I32Const(expr.int))
            is Expression.Bool -> listOf(Instr.I32Const(if (expr.bool) 1 else 0))
            is Expression.Var -> TODO()
            is Expression.Lambda -> TODO()
            is Expression.App -> TODO()
            is Expression.Let -> TODO()
            is Expression.LetRec -> TODO()
            is Expression.If -> TODO()
            is Expression.Construction -> TODO()
            is Expression.Match -> TODO()
        }
    }

    fun compile_module(): Module {
        val (make_closure, apply_closure) = init_rts()
        val add3 = make_fn1("add3", "x" to Value.I32) { x ->
            listOf(
                Instr.I32Const(3),
                Instr.GetLocal(x),
                Instr.I32Add
            )
        }

        val my_add = make_fn1("my_add", "arg_pointer" to Value.I32) { arg_pointer ->
            val x = register_local("x", Value.I32)
            val y = register_local("y", Value.I32)
            listOf(
                Instr.GetLocal(arg_pointer),
                Instr.I32Load(2, 0),
                Instr.SetLocal(x),
                Instr.GetLocal(arg_pointer),
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.I32Load(2, 0),
                Instr.SetLocal(y),

                Instr.GetLocal(x),
                Instr.GetLocal(y),
                Instr.I32Add
            )
        }

        val main = register_func(
            "main", Func(
                Node.Type.Func(listOf(), Value.I32), listOf(), listOf(
                    Instr.I32Const(2), // arity
                    Instr.I32Const(0), // code pointer
                    Instr.Call(make_closure),

                    Instr.I32Const(10),
                    Instr.Call(apply_closure),
                    Instr.I32Const(20),
                    Instr.Call(apply_closure)
                )
            )
        )
        return Module(
            memories = listOf(Node.Type.Memory(Node.ResizableLimits(1, null))),
            globals = globals.map { it.second },
            tables = listOf(Node.Type.Table(Node.ElemType.ANYFUNC, Node.ResizableLimits(1, null))),
            elems = listOf(Node.Elem(0, listOf(Instr.I32Const(0)), listOf(my_add))),
            exports = listOf(
                Export("main", ExternalKind.FUNCTION, main)
            ) + funcs.mapIndexed { ix, (name, _) ->
                Export(name, ExternalKind.FUNCTION, ix)
            },
            funcs = funcs.map { it.second },
            types = types.map { it.second }
        )
    }
}


fun main(): Unit {
    val mod = Codegen().compile_module()
    val ast = AstToSExpr().fromModule(mod)

    println(ast)
    val buf = ByteArrayOutputStream()
    AstToBinary().fromModule(ByteWriter.OutputStream(buf), mod)
    File("out.wasm").writeBytes(buf.toByteArray())
}