import soot.*
import soot.grimp.internal.GNewInvokeExpr
import soot.jimple.*
import soot.jimple.internal.JIdentityStmt
import soot.jimple.internal.JInstanceFieldRef
import soot.jimple.internal.JReturnStmt
import soot.jimple.internal.JReturnVoidStmt
import soot.jimple.internal.JStaticInvokeExpr
import soot.util.Numberable
import kotlin.math.floor

val structFields = mutableMapOf<SootClass, MutableList<SootField>>()

fun transformTypeToCppCompatWithStructPrefix(ty: Type): String {
    return if ("$ty" in listOf("int", "char", "boolean") ||
        ((ty is ArrayType && "${ty.baseType}" in listOf("int", "char", "boolean")))) "$ty"
    else if (ty is ArrayType && ty.baseType is RefType) {
        structFields[(ty.baseType as RefType).sootClass] = mutableListOf()
        "struct $ty *".replace('.', '_')
    }
    else if (ty is RefType) {
        structFields[ty.sootClass] = mutableListOf()
        "struct $ty *".replace('.', '_')
    } else {
        "struct $ty *".replace('.', '_')
    }
}

/// only for type prefix in a function like "String_append"
fun transformTypeToCppCompat(ty: Type): String {
    return "$ty".replace('.', '_')
}

fun transformValueToCppCompat(value: Value): String {
    return when (value) {
        is NewExpr -> "${transformTypeToCppCompatWithStructPrefix(value.baseType)}{}"
        is JInstanceFieldRef -> {
//            val className = transformTypeToCppCompatWithStructPrefix(value.type)
            val className = value.field.declaringClass
            if (structFields.containsKey(className)) {
                structFields[className]!!.add(value.field)
            } else {
                structFields[className] = mutableListOf(value.field)
            }
            "${transformValueToCppCompat(value.base)}->${value.field.name}"
        }
        is StaticFieldRef -> "${value.fieldRef.declaringClass().toString().replace('.', '_')}_${value.fieldRef.name()}"
        is VirtualInvokeExpr -> "${value.method.name}(${(listOf(value.base) + value.args).joinToString(", ")})"
        is GNewInvokeExpr -> "${value.baseType}_${value.method.name}(${(value.args).joinToString(", ")})"
        is JStaticInvokeExpr -> "${transformTypeToCppCompat(value.method.declaringClass.type)}_${value.method.name}(${(value.args).joinToString(", ")})"
        is SpecialInvokeExpr -> "${transformValueToCppCompat(value.base)}_${value.method.name}(${(value.args).joinToString(", ")})"
        is DynamicInvokeExpr -> "${value.method.name}(${
                (value.bootstrapArgs).joinToString(", ") { transformValueToCppCompat(it) }
            }, __FENCE__, ${
                value.args.joinToString(
                    ", "
                ) { transformValueToCppCompat(it) }
            })"
        is InterfaceInvokeExpr -> "${
            transformTypeToCppCompat(value.method.declaringClass.type)
            }_${
                value.method.name
            }(${
                (listOf(value.base) + value.args).joinToString(", ") { transformValueToCppCompat(it) }
            })"
        is InvokeExpr -> value.toString()
        is ClassConstant -> transformTypeToCppCompatWithStructPrefix(value.toSootType())
        is StringConstant -> value.toString()
        is NegExpr -> "-(${transformValueToCppCompat(value.op)})"
        else -> value.toString()
    }

}

private fun formatFieldOrArrayDeclToCppCompat(name: String, ty: Type) = (if (ty is FieldRef) transformValueToCppCompat(ty)
else if (ty is ArrayType)
    transformTypeToCppCompatWithStructPrefix(ty).let {
        "${it.substringBefore('[')}* $name[${it.substringAfter('[')}"
            .replace("[]", "[10]")
    }
else ("${transformTypeToCppCompatWithStructPrefix(ty)} $name"))

fun Slicer.smtExpand(): String {
    // the symbol that are defined and referred in the bytecode, should change to SSA form
    val publicSymbols = mutableMapOf<String, Any>()
    // search according to the value its corresponding public symbol
    val reversePublicSymbols = mutableMapOf<Any, String>()
    // affiliate variables (in inner scope, for example)
    val privateSymbols = mutableListOf<String>()
    // SSA transformation (the scope system is assumed to hold, otherwise a variable might be accessed out of scope)
    val assignOnceSymbols = mutableMapOf<String, List<String>>()
    // functions
    val functions = mutableMapOf<String, Pair<List<Any>, Any>>()
    // placeholder codes like null definition
    var placeholderDeclarations = ""
    fun grabRandomName(): String {
        var name: String
        do {
            name = ("var" + floor(Math.random() * 4000.0).toInt())
        } while (name in publicSymbols.keys || name in privateSymbols)
        return name
    }

    fun transformName(varName: Any): String {
        when (varName) {
            IntType.v() -> return "Int"
            VoidType.v() -> return "void"
            CharType.v() -> return "Int"
            ArrayType.v(CharType.v(), 1) -> return "(Array Int Int)" // to be added
            BooleanType.v() -> return "Bool"
        }
        val derefName = if (varName is RefType) varName.sootClass else varName
        val sym = reversePublicSymbols[derefName]
        if (sym == null) {
            val name = grabRandomName()
            publicSymbols[name] = derefName
            reversePublicSymbols[derefName] = name
            return name
        } else {
            return if (assignOnceSymbols.containsKey(sym))
                assignOnceSymbols[sym]!![0]
            else sym
        }
    }

    fun transformDefinitionName(varName: Value): String {
        val sym = reversePublicSymbols[varName]
        if (sym == null) {
            val name = grabRandomName()
            publicSymbols[name] = varName
            reversePublicSymbols[varName] = name
            assignOnceSymbols[name] = listOf(name)
            return name
        } else {
            val newName = "${sym}!${assignOnceSymbols[sym]!!.size}"
            assignOnceSymbols[sym] = listOf(newName) + assignOnceSymbols[sym]!!
            return newName
        }
    }

    fun transformValue(value: Value): String {
        // compromise to Kotlin's not allowing local function mutual recursion
        fun coerce(value: Value, types: List<Numberable>): String {
            if (types.map { if (it is RefType) it.sootClass else it }.let { it.all { item -> item == it[0] } })
                return transformValue(value)
            if (types.contains(BooleanType.v()) && value.type is IntType)
                return "(ite (= 1 ${transformValue(value)}) true false)" // special downcast
            if (value.type is NullType) { // default to cast the null's
                val ty = types.first { it !is NullType }
                placeholderDeclarations += "(declare-const null-${transformName(ty)} ${transformName(ty)})\n"
                return "null-${transformName(ty)}"
            }
            return transformValue(value)
        }

        return when (value) {
            is NewExpr -> {
                functions.putIfAbsent("${transformName(value.baseType)}-init", listOf<Any>() to value.baseType)
                "${transformName(value.baseType)}-init"
            }

            is InstanceFieldRef -> {
//            val className = transformTypeToCppCompatWithStructPrefix(value.type)
                val className = value.field.declaringClass
                val fieldName = value.field.name
                functions.putIfAbsent(fieldName, listOf(className) to value.field.type)
                "($fieldName ${transformName(value.base)})"
            }

            is StaticFieldRef -> {
                placeholderDeclarations += "(declare-const ${transformName(value.fieldRef.declaringClass())}-${value.fieldRef.name()} ${
                    transformName(
                        value.type
                    )
                })\n"
                "${transformName(value.fieldRef.declaringClass())}-${value.fieldRef.name()}"
            }

            is VirtualInvokeExpr -> {
                functions.putIfAbsent(
                    value.method.name,
                    (listOf(value.base) + value.args).map { it.type } to value.method.returnType)
                "(${value.method.name} ${(listOf(value.base) + value.args).joinToString(" ") { transformValue(it) }})"
            }
            // same with virtual for now
            is SpecialInvokeExpr -> {
                functions.putIfAbsent(
                    value.method.name,
                    (listOf(value.base) + value.args).map { it.type } to value.method.returnType)
                "(${value.method.name} ${(listOf(value.base) + value.args).joinToString(" ") { transformValue(it) }})"
            }

            //is GNewInvokeExpr -> "${value.baseType}_${value.method.name}(${(value.args).joinToString(", ")})"
            is StaticInvokeExpr -> {
                functions.putIfAbsent(
                    "${transformName(value.method.declaringClass.type)}_${value.method.name}",
                    value.args.map { it.type } to value.method.returnType)
                "(${transformName(value.method.declaringClass.type)}_${value.method.name} ${
                    (value.args).joinToString(
                        " "
                    ) { transformValue(it) }
                })"
            }

//        is DynamicInvokeExpr -> "${value.method.name}(${
//            (value.bootstrapArgs).joinToString(" ") { transformValueToCppCompat(it) }
//        }, __FENCE__, ${
//            value.args.joinToString(
//                " "
//            ) { transformValueToCppCompat(it) }
//        })"

            is InterfaceInvokeExpr -> {
                functions.putIfAbsent(
                    "${
                        transformName(value.method.declaringClass.type)
                    }_${
                        value.method.name
                    }",
                    (listOf(value.base) + value.args).map { it.type } to value.method.returnType)
                "(${
                    transformName(value.method.declaringClass.type)
                }_${
                    value.method.name
                } ${
                    (listOf(value.base) + value.args).joinToString(" ") { transformValue(it) }
                })"
            }

            is InstanceOfExpr -> {
//            functions.putIfAbsent("instanceof", )
                "true" // TODO: temporarily can't deal
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
            is CastExpr -> transformValue(value.op)

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
                            arrayType.numDimensions
                        )
                    )
                }
                "(getIndex-${arrayTySig} ${transformValue(value.index)} ${transformValue(value.base)})"
            }

            else -> value.toString()// + value.javaClass
        }
    }

    fun transformDefine(ty: Type, lvalue: Value, rvalue: Value? = null) = if (rvalue == null) {
        // enforce the eval order to get rid of self-reference
        val literal1 = transformName(ty)
        "(declare-const ${transformDefinitionName(lvalue)} $literal1)"
    } else {
        val literal1 = transformName(ty)
        val literal2 = transformValue(rvalue)
        // compromise to bytecode's assignment of integers to boolean type variables
        // TODO: merge with the coerce things
        if (ty is BooleanType && rvalue.type is IntType)
            "(define-const ${transformDefinitionName(lvalue)} $literal1 (ite (= 1 $literal2) true false))"
        else
            "(define-const ${transformDefinitionName(lvalue)} $literal1 $literal2)"
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
        is InvokeStmt -> ";(assert ${transformValue(stmt.invokeExpr)})" // temporarily unable to figure out the side effect
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
        when (entry) {
            is Condition -> "(assert ${conditionExpander(entry)}) ; $entry"
            is Statement -> "${transformStmt(entry.stmt)} ; $entry"
        }
    }

    // enforce the eval order
    var header = functions.map { (name, types) ->
        "(declare-fun $name (${types.first.joinToString(" ") { transformName(it) }}) ${
            transformName(
                types.second
            )
        })\n"
    }.joinToString("") + placeholderDeclarations
    // if the code uses the class constants, add the SootClasses also as concrete values
    val reflectionClass = if (publicSymbols.values.toString().contains("java.lang.Class"))
        transformName(Scene.v().getSootClass("java.lang.Class"))
    else ""
    header =
        "(set-logic ALL)\n" + publicSymbols.keys.filter { publicSymbols[it] is Type || publicSymbols[it] is SootClass }
            .joinToString("") { "(declare-sort $it)\n" } +
                "(declare-sort void)\n" +  // TODO: temporarily use a customized void type
                (if (reflectionClass.isNotEmpty())
                    publicSymbols.keys.filter { publicSymbols[it] is Type || publicSymbols[it] is SootClass }
                        .joinToString("") { "(declare-const $it!class $reflectionClass)\n" }
                else "") +
                header
    val trailer =
        "\n(check-sat)\n(get-model)\n; " + functions.toString() + "\n; " + publicSymbols.toString() + "\n; " + reversePublicSymbols.toString()
    return header + body + trailer
}