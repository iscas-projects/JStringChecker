import soot.*
import soot.jimple.*
import soot.jimple.internal.JIdentityStmt
import soot.util.Numberable
import kotlin.math.floor

fun Slicer.smtExpand(): String {
    // the symbol that are defined and referred in the bytecode, should change to SSA form
    val publicSymbols = mutableMapOf<String, Any>()
    // search according to the value its corresponding public symbol
    val reversePublicSymbols = mutableMapOf<Any, String>()
    // affiliate variables (in inner scope, for example)
    val privateSymbols = mutableListOf<String>()
    // SSA transformation (the scope system is assumed to hold, otherwise a variable might be accessed out of scope)
    val assignOnceSymbols = mutableMapOf<String, List<String>>()
    val functions = mutableMapOf<String, Pair<List<Any>, Any>>()
    // placeholder codes like null definition and class object
    val placeholderDeclarations = mutableMapOf<String, Any>()
    fun grabRandomName(): String {
        var name: String
        do {
            name = ("var" + floor(Math.random() * 4000.0).toInt())
        } while (name in publicSymbols.keys || name in privateSymbols)
        return name
    }

    fun transformName(varName: Any): String {
        val derefName = if (varName is RefType) varName.sootClass else varName
        when (derefName) {
            IntType.v() -> return "Int"
            VoidType.v() -> return "void"
            CharType.v() -> return "Int"
            Scene.v().getSootClass("java.lang.String") -> return "String"
            ArrayType.v(CharType.v(), 1) -> return "(Array Int Int)" // to be added
            BooleanType.v() -> return "Bool"
        }
        val sym = reversePublicSymbols[derefName]
        if (sym == null) {
            val name = grabRandomName()
            publicSymbols[name] = derefName
            reversePublicSymbols[derefName] = name
            assignOnceSymbols[name] = listOf(name)
            return name
        } else {
            return assignOnceSymbols[sym]!![0]
        }
    }

    // deal with multiple assign of one variable (to be SSA)
    fun transformDefinitionName(varName: Value): String {
        val sym = reversePublicSymbols[varName]
        if (sym == null) {
            return transformName(varName)
        } else {
            val newName = "${sym}!${assignOnceSymbols[sym]!!.size}"
            assignOnceSymbols[sym] = listOf(newName) + assignOnceSymbols[sym]!!
            return newName
        }
    }

    var pre: String
    var post: String

    fun transformValue(value: Value): String {
        // compromise to Kotlin's not allowing local function mutual recursion
        fun coerce(value: Value, types: List<Numberable>): String {
            if (types.size == 1 && value.type != types[0]) {
                val typeToCoerce = types[0]
                val castFuncName = "cast-from-${
                    transformName(value.type)
                }-to-${
                    transformName(typeToCoerce)
                }"
                functions.putIfAbsent(
                    castFuncName,
                    (listOf(value.type)) to typeToCoerce
                )
                if (value.type !is NullType)
                    return "($castFuncName ${transformValue(value)})"
                // else go to below
            }
            if (value.type is NullType) { // default to cast the null's
                val ty = types.first { it !is NullType }
                placeholderDeclarations["null-${transformName(ty)}"] = ty
                return "null-${transformName(ty)}"
            }
            // TODO: make more clean, distinguish the one-type usage above and the merge-to-super usage below
            if (types.map { if (it is RefType) it.sootClass else it }.let { it.all { item -> item == it[0] } })
                return transformValue(value)
            if (types.contains(BooleanType.v()) && value.type is IntType)
                return "(ite (= 1 ${transformValue(value)}) true false)" // special downcast

            return transformValue(value)
        }

        // smtlib doesn't know subtypes, so the arguments must be upcast
        fun registerFunctionAndUpcastArguments(funcName: String, args: List<Value>, paramTypes: List<Numberable>, retType: Type): String {
            functions.putIfAbsent(
                funcName,
                paramTypes to retType
            )

            val argsString = args.zip(functions[funcName]!!.first)
                .joinToString(" ") { (arg, type) -> coerce(arg, listOf(type as Numberable)) }
            return "($funcName $argsString)"
        }

        return when (value) {
            is NewExpr -> {
                val funcName = "${transformName(value.baseType)}-init"
                functions.putIfAbsent(funcName, listOf<Any>() to value.baseType)
                funcName
            }

            is InstanceFieldRef -> {
//            val className = transformTypeToCppCompatWithStructPrefix(value.type)
                val className = value.field.declaringClass
                val fieldName = value.field.name + "/${className.hashCode()}" // TODO: check if inherited field works
                registerFunctionAndUpcastArguments(fieldName, listOf(value.base), listOf(className), value.field.type)
            }

            is StaticFieldRef -> {
                placeholderDeclarations["${transformName(value.fieldRef.declaringClass())}-${value.fieldRef.name()}"] =
                    value.type
                "${transformName(value.fieldRef.declaringClass())}-${value.fieldRef.name()}"
            }

            is InterfaceInvokeExpr -> {
                val funcName = "${
                    transformName(value.method.declaringClass.type)
                }_${
                    value.method.name
                }/${value.method.signature.hashCode()}"

                registerFunctionAndUpcastArguments(funcName, (listOf(value.base) + value.args),
                    (listOf(value.method.declaringClass) + value.method.parameterTypes), value.method.returnType)
            }

            is InstanceInvokeExpr -> { // treat virtual and special the same
                val funcName = value.method.name + "/" + value.method.signature.hashCode()

                val condition = preconditionOfFunctions(funcName, (listOf(value.base) + value.args).map { transformValue(it) })
                if (condition != null) pre = condition.toString() + "\n"
                registerFunctionAndUpcastArguments(funcName, (listOf(value.base) + value.args),
                    (listOf(value.method.declaringClass) + value.method.parameterTypes), value.method.returnType)

//                if (funcName.contains("read")) { // TODO: remove magic word "read" here
//                    val objectsToReassign = listOf(value.base)
//                    post = objectsToReassign.joinToString("") {
//                        "\n(declare-const ${transformDefinitionName(it)} ${transformName(it.type)})"
//                    }
//                }
            }

            //is GNewInvokeExpr -> "${value.baseType}_${value.method.name}(${(value.args).joinToString(", ")})"
            is StaticInvokeExpr -> {
                val funcName = "${transformName(value.method.declaringClass.type)}_${value.method.name}/${value.method.signature.hashCode()}"

                registerFunctionAndUpcastArguments(funcName, value.args, value.method.parameterTypes, value.method.returnType)
            }

//        is DynamicInvokeExpr -> "${value.method.name}(${ TODO: add this back
//            (value.bootstrapArgs).joinToString(" ") { transformValueToCppCompat(it) }
//        }, __FENCE__, ${
//            value.args.joinToString(
//                " "
//            ) { transformValueToCppCompat(it) }
//        })"

            is InstanceOfExpr -> {
                "***" // TODO: temporarily can't deal
            }

//            is LengthExpr TODO: add this

            is ClassConstant -> "${transformName(value.toSootType())}!class"
            is StringConstant -> value.toString()
            is NegExpr -> "(- ${transformValue(value.op)})"
            is BinopExpr -> when (value.symbol) {
                " != " -> {
                    val types = listOf(value.op1.type, value.op2.type)
                    // compromise to bytecode's comparison of integers to booleans
                    "(not (= ${coerce(value.op1, types)} ${coerce(value.op2, types)}))"
                }

                " == " -> {
                    val types = listOf(value.op1.type, value.op2.type)
                    // compromise to bytecode's comparison of integers to booleans
                    "(= ${coerce(value.op1, types)} ${coerce(value.op2, types)})"
                }

                else -> "(${value.symbol} ${transformValue(value.op1)} ${transformValue(value.op2)})"
            }

            is Local -> transformName(value)
            is CastExpr -> {
                functions.putIfAbsent(
                    "cast-from-${
                        transformName(value.op.type)
                    }-to-${
                        transformName(value.castType)
                    }",
                    (listOf(value.op.type)) to value.castType
                )
                "(cast-from-${transformName(value.op.type)}-to-${transformName(value.castType)} ${transformValue(value.op)})"
            }

            is ArrayRef -> {
                val arrayType = value.base.type as ArrayType
                val arrayTySig = "Arr-${transformName(arrayType.baseType)}-${arrayType.numDimensions}"
                if (arrayType.numDimensions == 1) {
                    functions.putIfAbsent(
                        "getIndex-${arrayTySig}",
                        listOf(
                            IntType.v(),
                            ArrayType.v(arrayType.baseType, arrayType.numDimensions)
                        ) to arrayType.baseType
                    )
                } else {
                    functions.putIfAbsent(
                        "getIndex-${arrayTySig}",
                        listOf(IntType.v(), ArrayType.v(arrayType.baseType, arrayType.numDimensions)) to ArrayType.v(
                            arrayType.baseType,
                            arrayType.numDimensions - 1
                        )
                    )
                }
                "(getIndex-${arrayTySig} ${transformValue(value.index)} ${transformValue(value.base)})"
            }

            else -> value.toString()// + value.javaClass
        }
    }

    fun transformDefine(ty: Type, lvalue: Value, rvalue: Value? = null): String = if (rvalue == null) {
        // enforce the eval order to get rid of self-reference
        val literal1 = transformName(ty)
        "(declare-const ${transformDefinitionName(lvalue)} $literal1)"
    } else {
        val literal1 = transformName(ty)
        val literal2 = transformValue(rvalue)

        fun coercedInitializer(ty: Type, rvalue: Value, initializer: String) = // TODO: merge with the coerce things
            if (ty is BooleanType && rvalue.type is IntType) // compromise to bytecode's assignment of integers to boolean type variables
                "(ite (= 1 $initializer) true false)"
            else if (ty != rvalue.type) {
                // TODO: temporarily use a cast here
                val castFuncName = "cast-from-${
                    transformName(rvalue.type)
                }-to-${
                    transformName(ty)
                }"
                functions.putIfAbsent(
                    castFuncName,
                    (listOf(rvalue.type)) to ty
                )
                "($castFuncName $initializer)"
            } else
                initializer

        when (lvalue) { // deal with reassigning fields, where we create a new variable not for the field but for the base
            is ArrayRef -> {
                val redeclareBase = transformDefine(lvalue.base.type, lvalue.base)
                val newLvalue = transformValue(lvalue)
                "$redeclareBase\n(assert (= $newLvalue ${coercedInitializer(ty, rvalue, literal2)}))"
            }
            is InstanceFieldRef -> { // TODO: identical branches
                val redeclareBase = transformDefine(lvalue.base.type, lvalue.base)
                val newLvalue = transformValue(lvalue)
                "$redeclareBase\n(assert (= $newLvalue ${coercedInitializer(ty, rvalue, literal2)}))"
            }
            //is StaticFieldRef -> "" TODO: make it linked to a class object
            else -> {
                assert(lvalue is Local)
                "(define-const ${transformDefinitionName(lvalue)} $literal1 ${coercedInitializer(ty, rvalue, literal2)})"
            }
        }
    }

    // second method after entry
    fun transformStmt(stmt: Stmt) = when (stmt) {
        is JIdentityStmt -> transformDefine(stmt.rightOp.type, stmt.leftOp)
        is AssignStmt -> transformDefine(stmt.leftOp.type, stmt.leftOp, stmt.rightOp)
        is IfStmt -> ""
        is GotoStmt -> ""
        is ThrowStmt -> ""
        is ReturnStmt -> ""
        is ReturnVoidStmt -> ""
        is LookupSwitchStmt -> ""
        is InvokeStmt -> {
            val ie = stmt.invokeExpr
            val objectsToReassign = (if (ie is InstanceInvokeExpr)
                listOf(ie.base)
            else listOf()) + stmt.invokeExpr.args

            // enforce the eval order
            val prog = transformValue(stmt.invokeExpr)
            post = objectsToReassign.joinToString("") {
                "\n(declare-const ${transformDefinitionName(it)} ${transformName(it.type)})"
            }
            ";(assert $prog)"
        } // TODO: more about the side effect
        else -> "!!!!!!${stmt.javaClass} "
    }

    fun conditionExpander(condition: Condition): String = when (condition) {
        is Intersect -> "(and ${conditionExpander(condition.leftCond)} ${conditionExpander(condition.rightCond)})"
        is Negate -> "(not ${conditionExpander(condition.cond)})"
        is Nop -> "true"
        is Single -> transformValue(condition.value)
        is Union -> "(or ${conditionExpander(condition.leftCond)} ${conditionExpander(condition.rightCond)}"
    }

    // entry point
    val body = this.getPath().joinToString("\n") { entry ->
        pre = ""
        post = ""
        val prog = when (entry) {
            is Condition -> "(assert ${conditionExpander(entry)}) ; $entry"
            is Statement -> "${transformStmt(entry.stmt)} ; $entry"
        }
        pre + prog + post
    }

    val predefines = predefineFunctions()
    // enforce the eval order of parsing functions before adding sorts
    var header = functions.map { (name, types) ->
        if (predefines.containsKey(name)) predefines[name]!!.toStringWithTransformedName {
            if (it is String) it
            else transformName(it)
        } + "\n"
        else "(declare-fun $name (${types.first.joinToString(" ") { transformName(it) }}) ${
            transformName(
                types.second
            )
        })\n"
    }.joinToString("") +
            placeholderDeclarations.map { (name, ty) -> "(declare-const $name ${transformName(ty)})\n" }
                .joinToString("")
    // if the code uses the class constants, add the SootClasses also as concrete values
    val reflectionClass = if (publicSymbols.values.toString().contains("java.lang.Class"))
        transformName(Scene.v().getSootClass("java.lang.Class"))
    else ""
    header =
                "(set-option :produce-unsat-cores true) ; enable generation of unsat cores\n" +
                "(set-option :produce-models true) ; enable model generation\n" +
                "(set-option :produce-proofs true) ; enable proof generation\n" + "(set-logic ALL)\n" +
                publicSymbols.keys.filter { publicSymbols[it] is Type || publicSymbols[it] is SootClass }
                    .joinToString("") { "(declare-sort $it)\n" } +
                "(declare-sort void)\n" +  // TODO: temporarily use a customized void type
                (if (reflectionClass.isNotEmpty())
                    publicSymbols.keys.filter { publicSymbols[it] is Type || publicSymbols[it] is SootClass }
                        .joinToString("") { "(declare-const $it!class $reflectionClass)\n" }
                else "") +
                header
    val trailer =
        "\n(check-sat)\n; " + functions.toString() + "\n; " + publicSymbols.toString() + "\n; " + reversePublicSymbols.toString()
    return header + body + trailer
}