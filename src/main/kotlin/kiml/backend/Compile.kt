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

class Locals(vararg params: Value) {
    private var list: MutableList<Value> = params.toMutableList()
    private var nParams: Int = params.size

    fun register(type: Value): Int = list.size.also { list.add(type) }

    // All the locals the user registered
    fun getLocals(): List<Value> = list.drop(nParams)
}

class Codegen {
    val globals: MutableList<Pair<String, Node.Global>> = mutableListOf()
    val types: MutableList<Pair<String, Node.Type.Func>> = mutableListOf()
    val global_funcs: MutableList<Pair<String, Func>> = mutableListOf()
    val table_funcs: MutableList<String> = mutableListOf()

    fun init_rts(): Pair<Int, Int> {
        val watermark =
            register_global("watermark", Node.Global(Node.Type.Global(Value.I32, true), listOf(Instr.I32Const(0))))
        val allocate = make_fn1("allocate", Value.I32) { _, bytes ->
            listOf(
                Instr.GetGlobal(watermark),
                Instr.GetGlobal(watermark),
                Instr.GetLocal(bytes),
                Instr.I32Add,
                Instr.SetGlobal(watermark)
            )
        }
        val mk_closure =
            make_fn2("make_closure", Value.I32, Value.I32) { locals, arity, code_pointer ->
                val closure_start = locals.register(Value.I32)
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
            Value.I32,
            Value.I32
        ) { locals, closure_start, argument ->
            val arity = locals.register(Value.I32)
            val applied = locals.register(Value.I32)
            val code_pointer = locals.register(Value.I32)
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

    fun register_global_func(name: String, func: Func): Int =
        global_funcs.size.also { global_funcs.add(name to func) }

    fun register_table_func(name: String): Int =
        table_funcs.size.also { table_funcs.add(name) }

    fun register_global(name: String, global: Node.Global): Int =
        globals.size.also { globals.add(name to global) }

    fun register_type(name: String, typ: Node.Type.Func): Int =
        types.size.also { types.add(name to typ) }

    private fun make_fn1(name: String, arg: Value, body: (Locals, Int) -> List<Instr>): Int {
        val locals = Locals(arg)
        val instrs = body(locals, 0)
        val new_func = Func(Node.Type.Func(listOf(arg), Value.I32), locals.getLocals(), instrs)
        return register_global_func(name, new_func)
    }

    private fun make_fn2(
        name: String,
        arg1: Value,
        arg2: Value,
        body: (Locals, Int, Int) -> List<Instr>
    ): Int {
        val locals = Locals(arg1, arg2)
        val instrs = body(locals, 0, 1)
        val new_func =
            Func(Node.Type.Func(listOf(arg1, arg2), Value.I32), locals.getLocals(), instrs)
        return register_global_func(name, new_func)
    }

    fun func_index(name: String): Int {
        val res = global_funcs.indexOfFirst { name == it.first }
        return if (res == -1) throw Exception("Failed to find function index for: $name") else res
    }

    fun compile_module(): Module {
        val (make_closure, apply_closure) = init_rts()
        val add3 = make_fn1("add3", Value.I32) { _, x ->
            listOf(
                Instr.I32Const(3),
                Instr.GetLocal(x),
                Instr.I32Add
            )
        }

        val my_add = make_fn1("my_add", Value.I32) { locals, arg_pointer ->
            val x = locals.register(Value.I32)
            val y = locals.register(Value.I32)
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

        val code_pointer = register_table_func("my_add")

        val main = register_global_func(
            "main", Func(
                Node.Type.Func(listOf(), Value.I32), listOf(), listOf(
                    Instr.I32Const(2), // arity
                    Instr.I32Const(code_pointer), // code pointer
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
            tables = listOf(Node.Type.Table(Node.ElemType.ANYFUNC, Node.ResizableLimits(table_funcs.size, null))),
            elems = listOf(Node.Elem(0, listOf(Instr.I32Const(0)), table_funcs.map { func_index(it) })),
            exports = global_funcs.mapIndexed { ix, (name, _) -> Export(name, ExternalKind.FUNCTION, ix) },
            funcs = global_funcs.map { it.second },
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