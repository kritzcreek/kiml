package kiml.backend

import asmble.ast.Node.*
import asmble.ast.Node.Type.Value
import asmble.io.AstToBinary
import asmble.io.AstToSExpr
import asmble.io.ByteWriter
import kiml.frontend.*
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
    private val globals: MutableList<Pair<String, Global>> = mutableListOf()
    private val types: MutableList<Pair<String, Type.Func>> = mutableListOf()
    private val globalFuncs: MutableList<Pair<String, Func>> = mutableListOf()
    private val tableFuncs: MutableList<String> = mutableListOf()

    private fun tableName(name: String): String = "$name\$table"

    private fun defineBuiltinBinary(name: String, instr: Instr) {
        val fn = makeFn2(name, Value.I32, Value.I32) { _, x, y ->
            listOf(
                Instr.GetLocal(x),
                Instr.GetLocal(y),
                instr
            )
        }

        makeFn1(tableName(name), Value.I32) { _, arg_pointer ->
            listOf(
                Instr.GetLocal(arg_pointer),
                Instr.I32Load(2, 0),
                Instr.GetLocal(arg_pointer),
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.I32Load(2, 0),
                Instr.Call(fn)
            )
        }
        registerTableFunc(tableName(name))
    }

    fun initRts() {
        val watermark =
            registerGlobal("watermark", Global(Type.Global(Value.I32, true), listOf(Instr.I32Const(0))))
        val allocate = makeFn1("allocate", Value.I32) { _, bytes ->
            listOf(
                Instr.GetGlobal(watermark),
                Instr.GetGlobal(watermark),
                Instr.GetLocal(bytes),
                Instr.I32Add,
                Instr.SetGlobal(watermark)
            )
        }

        makeFn2("make_closure", Value.I32, Value.I32) { locals, arity, code_pointer ->
            val closureStart = locals.register(Value.I32)
            listOf(
                Instr.I32Const(4),
                Instr.GetLocal(arity),
                Instr.I32Mul,
                Instr.I32Const(8), // arity + applied + code_pointer
                Instr.I32Add,
                Instr.Call(allocate),
                Instr.TeeLocal(closureStart),
                Instr.GetLocal(arity),
                Instr.I32Store16(1, 0),
                Instr.GetLocal(closureStart),
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.GetLocal(code_pointer),
                Instr.I32Store(2, 0),
                Instr.GetLocal(closureStart)
            )
        }


//  (func $copy_closure (param $closure i32) (result i32)
        val copyClosure = makeFn1(
            "copy_closure",
            Value.I32
        ) { locals, closure ->
            //    (local $new_closure i32) (local $size i32) (local $arity i32) (local $x i32)
            val newClosure = locals.register(Value.I32)
            val size = locals.register(Value.I32)
            val arity = locals.register(Value.I32)
            val x = locals.register(Value.I32)
            listOf(
//    local.get $closure
                Instr.GetLocal(closure),
//    i32.load16_s
                Instr.I32Load16S(1, 0),
//    local.tee $arity
                Instr.TeeLocal(arity),
//    i32.const 4
                Instr.I32Const(4),
//    i32.mul
                Instr.I32Mul,
//    i32.const 8
                Instr.I32Const(8),
//    i32.add
                Instr.I32Add,
//    local.tee $size
                Instr.TeeLocal(size),
//    call $allocate
                Instr.Call(allocate),
//    local.set $new_closure
                Instr.SetLocal(newClosure),
//    i32.const 0
                Instr.I32Const(0),
//    local.set $x
                Instr.SetLocal(x),
//    block  ;; label = @1
                Instr.Block(null),
//      loop  ;; label = @2
                Instr.Loop(null),
//        local.get $x
                Instr.GetLocal(x),
//        local.get $size
                Instr.GetLocal(size),
//        i32.ge_s
                Instr.I32GeS,
//        br_if 1 (;@1;)
                Instr.BrIf(1),
//        local.get $x
                Instr.GetLocal(x),
//        local.get $new_closure
                Instr.GetLocal(newClosure),
//        i32.add
                Instr.I32Add,
//        local.get $x
                Instr.GetLocal(x),
//        local.get $closure
                Instr.GetLocal(closure),
//        i32.add
                Instr.I32Add,
//        i32.load
                Instr.I32Load(2, 0),
//        i32.store
                Instr.I32Store(2, 0),
//        i32.const 4
                Instr.I32Const(4),
//        local.get $x
                Instr.GetLocal(x),
//        i32.add
                Instr.I32Add,
//        local.set $x
                Instr.SetLocal(x),
//        br 0 (;@2;)
                Instr.Br(0),
//      end
                Instr.End,
//    end
                Instr.End,
//    local.get $new_closure)
                Instr.GetLocal(newClosure)
            )
        }

        makeFn2(
            "apply_closure",
            Value.I32,
            Value.I32
        ) { locals, closure_start, argument ->
            val arity = locals.register(Value.I32)
            val applied = locals.register(Value.I32)
            val codePointer = locals.register(Value.I32)
            listOf(
                Instr.GetLocal(closure_start),
                Instr.Call(copyClosure),
                Instr.TeeLocal(closure_start),
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
                Instr.SetLocal(codePointer),

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

                Instr.GetLocal(codePointer),
                Instr.CallIndirect(
                    registerType("int_to_int", Type.Func(listOf(Value.I32), Value.I32)),
                    false
                ),
                Instr.End
            )
        }

        // Pack Layout:
        // | tag 2byte | arity 2byte | values n*4byte |

        makeFn2("make_pack", Value.I32, Value.I32) { locals, tag, arity ->
            val packStart = locals.register(Value.I32)
            listOf(
                // allocate 4*arity + 4
                Instr.GetLocal(arity),
                Instr.I32Const(4),
                Instr.I32Mul,
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.Call(allocate),
                // Write tag and arity
                Instr.TeeLocal(packStart),
                Instr.GetLocal(tag),
                Instr.I32Store16(1, 0),
                Instr.GetLocal(packStart),
                Instr.I32Const(2),
                Instr.I32Add,
                Instr.GetLocal(arity),
                Instr.I32Store16(1, 0),
                Instr.GetLocal(packStart)
            )
        }

        makeFnN("write_pack_field", listOf(Value.I32, Value.I32, Value.I32)) { _, args ->
            val pack = args[0]
            val offset = args[1]
            val field = args[2]
            listOf(
                Instr.GetLocal(pack),
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.GetLocal(offset),
                Instr.I32Const(4),
                Instr.I32Mul,
                Instr.I32Add,
                Instr.GetLocal(field),
                Instr.I32Store(2, 0),
                // After writing the field put the pack pointer back on the stack
                Instr.GetLocal(pack)
            )
        }

        makeFn2("read_pack_field", Value.I32, Value.I32) { _, pack, offset ->
            listOf(
                Instr.GetLocal(pack),
                Instr.I32Const(4),
                Instr.I32Add,
                Instr.GetLocal(offset),
                Instr.I32Const(4),
                Instr.I32Mul,
                Instr.I32Add,
                Instr.I32Load(2, 0)
            )
        }

        makeFn1("read_pack_tag", Value.I32) { _, pack ->
            listOf(
                Instr.GetLocal(pack),
                Instr.I32Load16S(1, 0)
            )
        }

        defineBuiltinBinary("add", Instr.I32Add)
        defineBuiltinBinary("eq_int", Instr.I32Eq)
        defineBuiltinBinary("sub", Instr.I32Sub)
        defineBuiltinBinary("div", Instr.I32DivS)
    }

    private fun getArity(funcName: String): Int =
        globalFuncs[funcIndex(funcName)]
            .second
            .type
            .params
            .size


    private fun registerGlobalFunc(name: String, func: Func): Int =
        globalFuncs.size.also { globalFuncs += name to func }

    private fun registerTableFunc(name: String): Int =
        tableFuncs.size.also { tableFuncs.add(name) }

    private fun registerGlobal(name: String, global: Global): Int =
        globals.size.also { globals.add(name to global) }

    private fun registerType(name: String, typ: Type.Func): Int =
        types.size.also { types.add(name to typ) }

    private fun dummyFunc(arity: Int) =
        Func(Type.Func((0 until arity).map { Value.I32 }, null), listOf(), listOf(Instr.Unreachable))

    private fun makeFn1(name: String, arg: Value, body: (Locals, Int) -> List<Instr>): Int {
        val self = registerGlobalFunc(name, dummyFunc(1))
        val locals = Locals(arg)
        val instrs = body(locals, 0)
        val newFunc = Func(Type.Func(listOf(arg), Value.I32), locals.getLocals(), instrs)
        globalFuncs[self] = name to newFunc
        return self
    }

    private fun makeFn2(
        name: String,
        arg1: Value,
        arg2: Value,
        body: (Locals, Int, Int) -> List<Instr>
    ): Int {
        val self = registerGlobalFunc(name, dummyFunc(2))
        val locals = Locals(arg1, arg2)
        val instrs = body(locals, 0, 1)
        val newFunc =
            Func(Type.Func(listOf(arg1, arg2), Value.I32), locals.getLocals(), instrs)
        globalFuncs[self] = name to newFunc
        return self
    }

    private fun makeFnN(
        name: String,
        args: List<Value>,
        body: (Locals, List<Int>) -> List<Instr>
    ): Int {
        val self = registerGlobalFunc(name, dummyFunc(args.size))
        val locals = Locals(*args.toTypedArray())
        val instrs = body(locals, args.indices.toList())
        val newFunc =
            Func(Type.Func(args, Value.I32), locals.getLocals(), instrs)
        globalFuncs[self] = name to newFunc
        return self
    }

    private fun funcIndex(name: String): Int {
        val res = globalFuncs.indexOfFirst { name == it.first }
        return if (res == -1) throw Exception("Failed to find function index for: $name") else res
    }

    private fun tableFuncIndex(name: String): Int {
        val res = tableFuncs.indexOfFirst { name == it }
        return if (res == -1) throw Exception("Failed to find function index for: $name") else res
    }

    fun compileProg(prog: List<IR.Declaration>): Module {
        prog.forEach { decl ->
            compileDecl(decl)
        }
        return Module(
            memories = listOf(Type.Memory(ResizableLimits(65535, null))),
            globals = globals.map { it.second },
            tables = listOf(Type.Table(ElemType.ANYFUNC, ResizableLimits(tableFuncs.size, null))),
            elems = listOf(Elem(0, listOf(Instr.I32Const(0)), tableFuncs.map { funcIndex(it) })),
            exports = globalFuncs.mapIndexed { ix, (name, _) -> Export(name, ExternalKind.FUNCTION, ix) },
            funcs = globalFuncs.map { it.second },
            types = types.map { it.second }
        )
    }

    private fun compileDecl(decl: IR.Declaration) {
        val arity = decl.arguments.size
        println("Compiling Decl: ${decl.name.v} @ $arity")
        registerTableFunc(tableName(decl.name.v))

        val fn = makeFnN(decl.name.v, decl.arguments.map { Value.I32 }) { locals, params ->
            println("${decl.pretty()} => $params")
            compileExpr(locals, decl.body.instantiate(params.map { IR.Expression.GetLocal(it) }))
        }
        makeFn1(tableName(decl.name.v), Value.I32) { _, arg_pointer ->
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
            instrs.add(Instr.Call(fn))
            instrs
        }

    }

    private fun compileExpr(locals: Locals, expr: IR.Expression): List<Instr> {
        return when (expr) {
            is IR.Expression.Int -> listOf(Instr.I32Const(expr.int))
            is IR.Expression.Bool -> listOf(Instr.I32Const(if (expr.bool) 1 else 0))
            is IR.Expression.Var -> when (expr.name) {
                is LNName.Bound -> throw Exception("Should've been instantiated: ${expr.name}")
                is LNName.Free -> {
                    val arity = getArity(expr.name.v.v)
                    listOf<Instr>(
                        Instr.I32Const(arity),
                        Instr.I32Const(tableFuncIndex(tableName(expr.name.v.v))),
                        Instr.Call(funcIndex("make_closure"))
                    )
                }
            }
            is IR.Expression.Application -> {
                // Optimization: If the called function is a known function with the same arity as the number of given
                // arguments we can call its stack based variant rather than building up a closure in memory
                val (fn, args) = expr.unfoldApps()
                if (fn is IR.Expression.Var && fn.name is LNName.Free && getArity(fn.name.v.v) == args.size) {
                    args.flatMap { compileExpr(locals, it) } + Instr.Call(funcIndex(fn.name.v.v))
                } else {
                    compileExpr(locals, expr.func) +
                            compileExpr(locals, expr.argument) +
                            listOf(Instr.Call(funcIndex("apply_closure")))
                }
            }
            is IR.Expression.Pack -> {
                listOf<Instr>(
                    Instr.I32Const(expr.tag),
                    Instr.I32Const(expr.values.size),
                    Instr.Call(funcIndex("make_pack"))
                ) + expr.values.withIndex().flatMap { (ix, field) ->
                    listOf(Instr.I32Const(ix)) +
                            compileExpr(locals, field) +
                            listOf(Instr.Call(funcIndex("write_pack_field")))
                }
            }
            is IR.Expression.Match -> {
                val scrutinee = locals.register(Value.I32)
                val tag = locals.register(Value.I32)
                compileExpr(locals, expr.scrutinee) +
                        listOf<Instr>(
                            Instr.TeeLocal(scrutinee),
                            Instr.Call(funcIndex("read_pack_tag")),
                            Instr.SetLocal(tag)
                        ) + expr.cases.fold(listOf<Instr>(Instr.Unreachable)) { acc, case ->
                    compileCase(locals, scrutinee, tag, case, acc)
                }

            }
            is IR.Expression.If ->
                compileExpr(locals, expr.condition) +
                        listOf(Instr.If(Value.I32)) +
                        compileExpr(locals, expr.thenCase) +
                        listOf(Instr.Else) +
                        compileExpr(locals, expr.elseCase) +
                        listOf(Instr.End)
            is IR.Expression.Let -> {
                val binder = locals.register(Value.I32)
                val body = expr.body.instantiate(listOf(IR.Expression.GetLocal(binder)))
                compileExpr(locals, expr.expr) +
                        listOf(Instr.SetLocal(binder)) +
                        compileExpr(locals, body)
            }
            is IR.Expression.GetLocal -> listOf(Instr.GetLocal(expr.ix))
        }
    }

    private fun compileCase(locals: Locals, scrutinee: Int, tag: Int, case: IR.Case, cont: List<Instr>): List<Instr> {
        val binders = case.binders.map { locals.register(Value.I32) }
        return listOf<Instr>(
            Instr.GetLocal(tag),
            Instr.I32Const(case.tag),
            Instr.I32Eq,
            Instr.If(Value.I32)
        ) + binders.mapIndexed { ix, b ->
            listOf<Instr>(
                Instr.GetLocal(scrutinee),
                Instr.I32Const(ix),
                Instr.Call(funcIndex("read_pack_field")),
                Instr.SetLocal(b)
            )
        }.flatten() +
                compileExpr(locals, case.body.instantiate(binders.map(IR.Expression::GetLocal))) +
                listOf<Instr>(Instr.Else) +
                cont +
                listOf(
                    Instr.End
                )
    }
}


fun main() {
    val input =
        """
type Maybe<a> { Nothing(), Just(a) }
type Either<a, b> { Left(a), Right(b) }
type List<a> { Cons(a, List<a>), Nil() }

let isEven : Int -> Bool =
  \x. eq_int (div x 2) 0 in
let fromMaybe : forall a. a -> Maybe<a> -> a =
  \def. \x. match x {
    Maybe::Just(x) -> x,
    Maybe::Nothing() -> def
  } in
let rec map : forall a b. (a -> b) -> List<a> -> List<b> = 
  \f. \ls. match ls {
    List::Nil() -> List::Nil(),
    List::Cons(x, xs) -> List::Cons(f x, map f xs),
  } in
let rec sum : List<Int> -> Int =
  \ls. match ls {
    List::Cons(x, xs) -> add x (sum xs),
    List::Nil() -> 0,
  } in
sum (map (\x. sub x 1) List::Cons(1, List::Cons(2, List::Nil())))
"""

    val input2 =
        """
            let rec fib = 
                \x. if eq_int x 1 
                    then 1 
                    else if eq_int x 2 
                        then 1 
                        else add (fib (sub x 1)) (fib (sub x 2)) in 
            fib 45
        """
    val (tys, expr) = Parser(Lexer(input2)).parseInput()

    val typeMap = TypeMap(HashMap())
    tys.forEach { typeMap.tm[it.name] = TypeInfo(it.typeVariables, it.dataConstructors) }

    val typeChecker = TypeChecker(CheckState.initial())
    typeChecker.checkState.typeMap = typeMap
    println("Inferred: ${typeChecker.inferExpr(expr)}")

    val lowering = Lowering(typeMap)
    val prog = lowering.lowerProg(expr)
    prog.forEach { decl -> println(decl.pretty()) }

    val codegen = Codegen()
    codegen.initRts()
    val mod = codegen.compileProg(prog)
    val ast = AstToSExpr().fromModule(mod)

    println(ast)
    val buf = ByteArrayOutputStream()
    AstToBinary().fromModule(ByteWriter.OutputStream(buf), mod)
    File("out.wasm").writeBytes(buf.toByteArray())
}
