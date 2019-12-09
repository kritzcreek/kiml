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
import kiml.frontend.Lexer
import kiml.frontend.Parser
import kiml.frontend.TypeInfo
import kiml.frontend.TypeMap
import pretty.pretty
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

    fun init_rts() {
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
        make_fn2(
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

                // Write the argument
                Instr.I32Const(4),
                Instr.GetLocal(applied),
                Instr.I32Mul,
                Instr.I32Const(8),
                Instr.I32Add,
                Instr.GetLocal(closure_start),
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

        val add_inner = make_fn2("add\$inner", Value.I32, Value.I32) { _, x, y ->
            listOf(
                Instr.GetLocal(x),
                Instr.GetLocal(y),
                Instr.I32Add
            )
        }

        make_fn1("add", Value.I32) { _, arg_pointer ->
            listOf(
                Instr.GetLocal(arg_pointer),
                Instr.I32Load(2, 0),
                Instr.GetLocal(arg_pointer),
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.I32Load(2, 0),
                Instr.Call(add_inner)
            )
        }
        register_table_func("add")
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

    private fun make_fnN(
        name: String,
        args: List<Value>,
        body: (Locals, List<Int>) -> List<Instr>
    ): Int {
        val locals = Locals(*args.toTypedArray())
        val instrs = body(locals, args.indices.toList())
        val new_func =
            Func(Node.Type.Func(args, Value.I32), locals.getLocals(), instrs)
        return register_global_func(name, new_func)
    }

    fun func_index(name: String): Int {
        val res = global_funcs.indexOfFirst { name == it.first }
        return if (res == -1) throw Exception("Failed to find function index for: $name") else res
    }

    fun table_func_index(name: String): Int {
        val res = table_funcs.indexOfFirst { name == it }
        return if (res == -1) throw Exception("Failed to find function index for: $name") else res
    }

    fun compile_prog(prog: List<IR.Declaration>): Module {
        prog.forEach { decl ->
            compile_decl(decl)
        }
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

    fun compile_decl(decl: IR.Declaration) {
        val arity = decl.arguments.size
        val inner = make_fnN(decl.name.v + "\$inner", decl.arguments.map { Value.I32 }) { locals, params ->
            compile_expr(locals, decl.body.instantiate(params.map { IR.Expression.GetLocal(it) }))
        }
        make_fn1(decl.name.v, Value.I32) { _, arg_pointer ->
            val instrs = mutableListOf<Instr>()
            for (i in 0 until arity) {
                instrs.addAll(
                    listOf(
                        Instr.GetLocal(arg_pointer),
                        Instr.I32Const(4 * i),
                        Instr.I32Add,
                        Instr.I32Load(2, 0)
                    )
                )
            }
            instrs.add(Instr.Call(inner))
            instrs
        }
        register_table_func(decl.name.v)

    }

    private fun compile_expr(locals: Locals, expr: IR.Expression): List<Instr> {
        return when (expr) {
            is IR.Expression.Int -> listOf(Instr.I32Const(expr.int))
            is IR.Expression.Bool -> listOf(Instr.I32Const(if (expr.bool) 1 else 0))
            is IR.Expression.Var -> when (expr.name) {
                is LNName.Bound -> throw Exception("Should've been instantiated: ${expr.name}")
                is LNName.Free -> {
                    val arity = global_funcs[func_index(expr.name.v.v + "\$inner")]
                        .second
                        .type
                        .params
                        .size
                    listOf<Instr>(
                        Instr.I32Const(arity),
                        Instr.I32Const(table_func_index(expr.name.v.v)),
                        Instr.Call(func_index("make_closure"))
                    )
                }
            }
            is IR.Expression.Application ->
                compile_expr(locals, expr.func) +
                        compile_expr(locals, expr.argument) +
                        listOf(Instr.Call(func_index("apply_closure")))
            is IR.Expression.Pack -> TODO()
            is IR.Expression.Match -> TODO()
            is IR.Expression.If ->
                compile_expr(locals, expr.condition) +
                        listOf(Instr.If(Value.I32)) +
                        compile_expr(locals, expr.thenCase) +
                        listOf(Instr.Else) +
                        compile_expr(locals, expr.elseCase) +
                        listOf(Instr.End)
            is IR.Expression.Let -> {
                val binder = locals.register(Value.I32)
                val body = expr.body.instantiate(listOf(IR.Expression.GetLocal(binder)))
                compile_expr(locals, expr.expr) +
                        listOf(Instr.SetLocal(binder)) +
                        compile_expr(locals, body)
            }
            // is IR.Expression.MakeClosure -> TODO()
            is IR.Expression.GetLocal -> listOf(Instr.GetLocal(expr.ix))
        }
    }
}


fun main(): Unit {
    val input =
        """
let y = 4 in
let f = \x. add x y in
f 10
"""
    val (tys, expr) = Parser(Lexer(input)).parseInput()

    val typeMap = TypeMap(HashMap())
    tys.forEach { typeMap.tm.put(it.name, TypeInfo(it.typeVariables, it.dataConstructors)) }

    val lowering = Lowering(typeMap)
    val prog = lowering.lowerProg(expr)
    prog.forEach { decl -> println(decl.pretty())}

    val codegen = Codegen()
    codegen.init_rts()
    val mod = codegen.compile_prog(prog)
    val ast = AstToSExpr().fromModule(mod)

    println(ast)
    val buf = ByteArrayOutputStream()
    AstToBinary().fromModule(ByteWriter.OutputStream(buf), mod)
    File("out.wasm").writeBytes(buf.toByteArray())
}
