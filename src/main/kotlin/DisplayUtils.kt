import soot.*
import soot.jimple.*
import soot.jimple.internal.JIdentityStmt
import soot.util.Numberable
import kotlin.math.floor

fun Slicer.smtExpand(): Pair<String, List<String>> {
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

    // an inner class as a wrapper of some transform functions, mainly to let each function be able to refer to another
    class TransformFunctionBundle {
        /**
         * global configurations of an SMT file, namely special assertions or sort declarations for now
         */
        var header = "(declare-sort void)\n(declare-sort Iterator)\n" // TODO: temporarily use a customized void type
        // TODO: move some on-the-fly sort declaration to one place
        var trailor = ""
        /**
         * pre-condition and post-condition of a statement, for example, `(assert (not (= this null)))` for some
         * statement `this.someMethod()` as a pre-condition
         *
         * they are inserted into the stream of SMT sentences directly before or after the corresponding sentences
         */
        var pre = ""
        var post = ""

        fun transformName(varName: Any): String {
            val derefName = if (varName is RefType) varName.sootClass else varName
            when (derefName) {
                IntType.v() -> return "Int"
                ByteType.v() -> return "Int" // TODO: temporarily use int for program int and byte type
                VoidType.v() -> return "void"
                CharType.v() -> return "Int"
                Scene.v().getSootClass("java.lang.String") -> return "String"
                Scene.v().getSootClass("java.lang.StringBuilder") -> return "String"
                Scene.v().getSootClass("java.lang.StringBuffer") -> return "String"
                Scene.v().getSootClass("java.util.Iterator") -> return "Iterator"
//                Scene.v().getSootClass("java.util.List") -> return ""
                ArrayType.v(CharType.v(), 1) -> return "(Array Int Int)" // to be added
                ArrayType.v(RefType.v("java.lang.String"), 1) -> return "(Array Int String)"
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

        // produce a type cast for the value to the top of types
        fun coerce(valueToBeCoerced: Value, types: List<Numberable>): String {
            val typeClasses =
                types.map { if (it is SootClass) RefType.v(it) else it }.filterNot { it == valueToBeCoerced.type }

            if (typeClasses.contains(BooleanType.v()) && valueToBeCoerced.type is IntType)
                return "(ite (= 1 ${transformValue(valueToBeCoerced)}) true false)" // special downcast
            if (typeClasses.size == 1 && isNotSameTypeButCastable(valueToBeCoerced.type, typeClasses[0] as Type)
            ) { // only upcast for now
                val typeToCoerce = typeClasses[0]
                val castFuncName = "cast-from-${
                    transformName(valueToBeCoerced.type).replace(
                        "[( )]".toRegex(),
                        "__"
                    ) // deal with compound (array) type
                }-to-${
                    transformName(typeToCoerce).replace("[( )]".toRegex(), "__")
                }"
                functions.putIfAbsent(
                    castFuncName,
                    (listOf(valueToBeCoerced.type)) to typeToCoerce
                )
                if (valueToBeCoerced.type !is NullType)
                    return "($castFuncName ${transformValue(valueToBeCoerced)})"
                // else go to below
            }
            if (valueToBeCoerced.type is NullType) { // default to cast the null's
                val ty = typeClasses.first { it !is NullType }
                val nullName = "null-${transformName(ty).replace("[( )]".toRegex(), "__")}"
                // TODO: make sure null not equal to any concrete instance
                placeholderDeclarations[nullName] = ty
                return nullName
            }

            return transformValue(valueToBeCoerced)
        }

        fun transformValue(value: Value): String {
            // smtlib doesn't know subtypes, so the arguments must be upcast
            fun registerFunctionAndUpcastArguments(
                funcName: String,
                args: List<Value>,
                paramTypes: List<Numberable>,
                retType: Type
            ): String {
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
                    val funcName = "${transformName(value.baseType)}-init" // placeholder value
                    functions.putIfAbsent(funcName, listOf<Any>() to value.baseType)
                    funcName
                }

                is NewArrayExpr -> {
                    // TODO: multi-dimension array
                    val funcName = "arr-${transformName(value.baseType)}-init"
                    // TODO: array bound
                    functions.putIfAbsent(funcName, listOf<Any>() to ArrayType.v(value.baseType, 1))
                    funcName
                }

                is InstanceFieldRef -> {
//            val className = transformTypeToCppCompatWithStructPrefix(value.type)
                    val className = value.field.declaringClass
                    val fieldName =
                        value.field.name + "/${className.hashCode()}" // TODO: check if inherited field works
                    registerFunctionAndUpcastArguments(
                        fieldName,
                        listOf(value.base),
                        listOf(className),
                        value.field.type
                    )
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

                    // enforce eval order
                    val ret = registerFunctionAndUpcastArguments(
                        funcName, (listOf(value.base) + value.args),
                        (listOf(value.method.declaringClass) + value.method.parameterTypes), value.method.returnType
                    )

                    post = postconditionOfFunctions(
                        funcName.dropWhile { it != '_' }.drop(1), // trim interface name
                        (listOf(value.base) + value.args),
                        ::transformValue
                    ) { v -> transformDefine(v.type, v) } ?.toStringWithTransformedName(::transformName) ?: ""

                    ret
                }

                is InstanceInvokeExpr -> { // treat virtual and special the same
                    val funcName = value.method.name + "/" + value.method.signature.hashCode()

                    val argNames = (listOf(value.base) + value.args).map { transformValue(it) }
                    val preCond =
                        preconditionOfFunctions(funcName, argNames)
                    val checkBaseNullity =
                        "(not (= ${transformValue(value.base)} ${coerce(NullConstant.v(), listOf(value.base.type))}))"
                    pre = if (preCond != null) {
                        // TODO: check the statement if it includes essential checks, including function exception and null check
                        // and plug to some of exprs above
                        "(and $checkBaseNullity $preCond)"
                    } else {
                        checkBaseNullity
                    }

                // TODO: add post condition check here

                    registerFunctionAndUpcastArguments(
                        funcName, (listOf(value.base) + value.args),
                        (listOf(value.method.declaringClass) + value.method.parameterTypes), value.method.returnType
                    )

//                if (funcName.contains("read")) { // TODO: remove magic word "read" here
//                    val objectsToReassign = listOf(value.base)
//                    post = objectsToReassign.joinToString("") {
//                        "\n(declare-const ${transformDefinitionName(it)} ${transformName(it.type)})"
//                    }
//                }
                }

                //is GNewInvokeExpr -> "${value.baseType}_${value.method.name}(${(value.args).joinToString(", ")})"
                is StaticInvokeExpr -> {
                    val funcName =
                        "${transformName(value.method.declaringClass.type)}_${value.method.name}/${value.method.signature.hashCode()}"

                    registerFunctionAndUpcastArguments(
                        funcName,
                        value.args,
                        value.method.parameterTypes,
                        value.method.returnType
                    )
                }

                is DynamicInvokeExpr -> {
                    val method = value.method
                    if (method.name.contains("makeConcatWithConstants")) {
                        "(str.++ ${
                            (value.bootstrapArgs).joinToString(" ") { transformValue(it) }
                        } ${
                            value.args.joinToString(
                                " "
                            ) { coerce(it, listOf(Scene.v().getSootClass("java.lang.String"))) }
                        })"
                    } else {
                        "(${value.method.name} ${
                            (value.bootstrapArgs).joinToString(" ") { transformValue(it) }
                        } ${
                            value.args.joinToString(
                                " "
                            ) { transformValue(it) }
                        })"
                    }
                }

                is InstanceOfExpr -> {
                    (value.op.type == value.checkType || isNotSameTypeButCastable(
                        value.op.type,
                        value.checkType,
                        true
                    )).toString() // TODO: temporarily can't deal
                }

                is LengthExpr -> {
                    val baseTy = value.op.type
//                if (baseTy is ArrayType && baseTy.baseType is CharType)
//                    "(str.len ${transformValue(value.op)})"
                    if (baseTy is ArrayType) {
                        val arrayTySig = "Arr-${transformName(baseTy.baseType)}-${baseTy.numDimensions}"
                        functions.putIfAbsent(
                            "getLength-${arrayTySig}",
                            listOf(baseTy) to IntType.v()
                        )
                        "(getLength-${arrayTySig} ${transformValue(value.op)})"
                    } else {
                        print(baseTy); "***"
                    }
                }

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
                    val castFuncName = "cast-from-${
                        transformName(value.op.type).replace("[( ]".toRegex(), "__")
                    }-to-${
                        transformName(value.castType).replace("[( ]".toRegex(), "__")
                    }"
                    functions.putIfAbsent(
                        castFuncName,
                        (listOf(value.op.type)) to value.castType
                    )
                    "($castFuncName ${transformValue(value.op)})"
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
                            listOf(
                                IntType.v(),
                                ArrayType.v(arrayType.baseType, arrayType.numDimensions)
                            ) to ArrayType.v(
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

        /**
         * declare a name (`lvalue`) or define a name (`lvalue`)  to be `rvalue`, given the type `ty` of `lvalue` as
         * it might already be a field of some object and carry a specific type.
         */
        fun transformDefine(ty: Type, lvalue: Value, rvalue: Value? = null): String = if (rvalue == null) {
            // enforce the eval order to get rid of self-reference
            val literal1 = transformName(ty)
            "(declare-const ${transformDefinitionName(lvalue)} $literal1)"
        } else {
            val literal1 = transformName(ty)

            val initializer = coerce(rvalue, listOf(ty))
            // TODO: refactor below to the pre-condition parts
            when (lvalue) { // deal with reassigning fields, where we create a new variable not for the field but for the base
                is ArrayRef -> {
                    val redeclareBase = transformDefine(lvalue.base.type, lvalue.base)
                    val nonNullAssertion = "(assert (not (= ${transformValue(lvalue.base)} ${coerce(NullConstant.v(), listOf(lvalue.base.type))})))"
                    val newLvalue = transformValue(lvalue)
                    "$redeclareBase\n$nonNullAssertion\n(assert (= $newLvalue $initializer))"
                }

                is InstanceFieldRef -> { // TODO: identical branches but of different type
                    val redeclareBase = transformDefine(lvalue.base.type, lvalue.base)
                    val nonNullAssertion = "(assert (not (= ${transformValue(lvalue.base)} ${coerce(NullConstant.v(), listOf(lvalue.base.type))})))"
                    val newLvalue = transformValue(lvalue)
                    "$redeclareBase\n$nonNullAssertion\n(assert (= $newLvalue $initializer))"
                }
                //is StaticFieldRef -> "" TODO: make it linked to a class object
                else -> {
                    assert(lvalue is Local)
                    "(define-const ${transformDefinitionName(lvalue)} $literal1 $initializer)"
                }
            }
        }

        // second method after entry
        fun transformStmt(stmt: Stmt) = when (stmt) {
            is IdentityStmt -> {
                val res = transformDefine(stmt.rightOp.type, stmt.leftOp)
                if (stmt.rightOp is ThisRef) // this object should not be null by definition
                    post = "(assert (not (= ${transformName(stmt.leftOp)} ${coerce(NullConstant.v(), listOf(stmt.leftOp.type))})))"
                if (stmt.rightOp is ParameterRef) // TODO: assume params are not null, but only as an option
                    post += "\n(assert (not (= ${transformName(stmt.leftOp)} ${coerce(NullConstant.v(), listOf(stmt.leftOp.type))})))"
                res
            }
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
                if (post.isEmpty())
                    post = objectsToReassign.joinToString("") {
                        "\n(declare-const ${transformDefinitionName(it)} ${transformName(it.type)})"
                    }
                ";(assert $prog)"
            } // TODO: more about the side effect
            else -> "!!!!!!${stmt.javaClass} "
        }
    }

    val bundle = TransformFunctionBundle()

    fun conditionExpander(condition: Condition): String = when (condition) {
        is Intersect -> "(and ${conditionExpander(condition.leftCond)} ${conditionExpander(condition.rightCond)})"
        is Negate -> "(not ${conditionExpander(condition.cond)})"
        is Nop -> "true"
        is Single -> bundle.transformValue(condition.value)
        is Union -> "(or ${conditionExpander(condition.leftCond)} ${conditionExpander(condition.rightCond)}"
    }

    // entry point
    val lines = this.getPath().map { entry ->
        bundle.pre = "" // the statement to assert, e.g. "(isNull myObject)", instead of a complete assert sentence
        bundle.post = ""
        val prog = when (entry) {
            is Condition -> "(assert ${conditionExpander(entry)}) ; $entry"
            is Statement -> "${bundle.transformStmt(entry.stmt)} ; $entry"
        }
        bundle.post = if (bundle.post.isNotEmpty()) "\n" + bundle.post else ""
        bundle.pre to (prog + bundle.post)
    }

    // statement series reverting the last pre-condition
    val deviants = lines.indices.map { lines.subList(0, it + 1) } // every sublist starting at 0
        .filter { it.last().first.isNotEmpty() } // with last element containing a pre-condition
        .map { statementsWithOptionalPreconditions ->
            statementsWithOptionalPreconditions.dropLast(1)
                .joinToString("\n") { (pre, prog) -> (if (pre.isNotEmpty()) "(assert $pre)\n" else "") + prog } + "\n" +
                    statementsWithOptionalPreconditions.last().first.let { "(assert (not ${it}))" }
        }
    val body = lines.joinToString("\n") { (pre, prog) -> (if (pre.isNotEmpty()) "(assert $pre)\n" else "") + prog }

    // enforce the eval order of parsing functions before adding sorts
    var header = predefineFunctions(functions).joinToString("") { sExpression ->
        sExpression.toStringWithTransformedName {
            bundle.transformName(it)
        } + "\n"
    } + placeholderDeclarations.map { (name, ty) -> "(declare-const $name ${bundle.transformName(ty)})\n" }
        .joinToString("")
    // if the code uses the class constants, add the SootClasses also as concrete values
    val reflectionClass = if (publicSymbols.values.toString().contains("java.lang.Class"))
        bundle.transformName(Scene.v().getSootClass("java.lang.Class"))
    else ""
    header =
                "(set-option :produce-unsat-cores true) ; enable generation of unsat cores\n" +
                "(set-option :produce-models true) ; enable model generation\n" +
                "(set-option :produce-proofs true) ; enable proof generation\n" + "(set-logic ALL)\n" +
                publicSymbols.keys.filter { publicSymbols[it] is Type || publicSymbols[it] is SootClass }
                    .joinToString("") { "(declare-sort $it)\n" } + bundle.header +
                (if (reflectionClass.isNotEmpty())
                    publicSymbols.keys.filter { publicSymbols[it] is Type || publicSymbols[it] is SootClass }
                        .joinToString("") { "(declare-const $it!class $reflectionClass)\n" }
                else "") +
                header
    val trailer =
        "\n(check-sat)\n(get-model)\n(get-unsat-core)\n; " + functions.toString() + "\n; " + publicSymbols.toString() + "\n; " + reversePublicSymbols.toString()
    return (header + body + trailer) to deviants.map { header + it + trailer }
}