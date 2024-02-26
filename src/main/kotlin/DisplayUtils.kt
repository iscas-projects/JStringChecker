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

fun String.postProcess() = // trim the $, <, >, and other symbols
    this.let { noDecl ->
//            Regex("^struct \\S* ").findAll(noDecl)
//                .map { it.value + "{${
//                    structFields[it.value]?.joinToString("\n") { field ->
//                        "${transformTypeToCppCompatWithStructPrefix(field.type)} ${field.name};"
//                    } ?: ""
//                }};" }
//                .toSet()
//                .joinToString("\n") + "\n" + noDecl
        structFields.map { (cl, fields) ->
            fields.map { if (it.type is ArrayType) (it.type as ArrayType).baseType else it.type }.filter { it !is PrimType }
            "struct ${transformTypeToCppCompat(cl.type)} {${
            fields.toSet()
                .joinToString("\n") { field -> formatFieldOrArrayDeclToCppCompat(field.name, field.type) + ";" }
        }};" }.joinToString("\n") + "\n" + noDecl
    }
        .replace("$", "___")
        .replace("<clinit>", "__clinit__")
        .replace("<init>", "__init__")
        .replace("@();", "") // trim unnecessary conditions

fun Slicer.smtExpand(): String {
    // the symbol that are defined and referred in the bytecode, should change to SSA form
    val publicSymbols = mutableMapOf<String, Any>()
    // search according to the value its corresponding public symbol
    val reversePublicSymbols = mutableMapOf<Any, String>()
    // affiliate variables (in inner scope, for example)
    val privateSymbols = mutableListOf<String>()
    // functions
    val functions = mutableMapOf<String, Pair<List<Any>, Any>>()
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
            return sym
        }
    }

    fun transformValue(value: Value): String = when (value) {
        is NewExpr -> "${transformTypeToCppCompatWithStructPrefix(value.baseType)}{}"
        is JInstanceFieldRef -> {
//            val className = transformTypeToCppCompatWithStructPrefix(value.type)
            val className = value.field.declaringClass
            val fieldName = value.field.name
            functions.putIfAbsent(fieldName, listOf(className) to value.field.type)
            "($fieldName ${transformName(value.base)})"
        }

        is StaticFieldRef -> "${value.fieldRef.declaringClass().toString().replace('.', '_')}_${value.fieldRef.name()}"
        is VirtualInvokeExpr -> {
            functions.putIfAbsent(value.method.name, (listOf(value.base) + value.args).map { it.type } to value.method.returnType)
            "(${value.method.name} ${(listOf(value.base) + value.args).joinToString(", ") { transformValue(it) }})"
        }

        is GNewInvokeExpr -> "${value.baseType}_${value.method.name}(${(value.args).joinToString(", ")})"
        is JStaticInvokeExpr -> "${transformTypeToCppCompat(value.method.declaringClass.type)}_${value.method.name}(${
            (value.args).joinToString(
                ", "
            )
        })"

        is SpecialInvokeExpr -> "${transformValueToCppCompat(value.base)}_${value.method.name}(${
            (value.args).joinToString(
                ", "
            )
        })"

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

        is ClassConstant -> transformTypeToCppCompatWithStructPrefix(value.toSootType())
        is StringConstant -> value.toString()
        is NegExpr -> "-(${transformValueToCppCompat(value.op)})"
        is BinopExpr -> when (value.symbol) {
            " != " -> "(not (= ${transformValue(value.op1)} ${transformValue(value.op2)}))"
            " = " -> "(= ${transformValue(value.op1)} ${transformValue(value.op2)})"
            else -> "(${value.symbol} ${transformValue(value.op1)} ${transformValue(value.op2)})"
        }

        is Local -> transformName(value)
        is CastExpr -> transformValue(value.op)
        else -> value.toString()
    }

    fun transformInvoke(invoke: InvokeExpr) = ""

    fun transformDefine(ty: Type, lvalue: Value, rvalue: Value? = null) = if (rvalue == null)
        "(declare-const ${transformName(lvalue)} ${transformName(ty)})"
    else
        "(define-const ${transformName(lvalue)} ${transformName(ty)} ${transformValue(rvalue)})"

    fun transformStmt(stmt: Stmt) = when (stmt) {
        is JIdentityStmt -> transformDefine(stmt.rightOp.type, stmt.leftOp)
        is AssignStmt -> transformDefine(stmt.leftOp.type, stmt.leftOp, stmt.rightOp)
        is IfStmt -> ""
        is GotoStmt -> ""
        is ThrowStmt -> ""
        is JReturnStmt -> ""
        is JReturnVoidStmt -> ""
        is InvokeStmt -> transformInvoke(stmt.invokeExpr)
        else -> "!!!!!!"
    }

    fun conditionExpander(condition: Condition): String = when (condition) {
        is Intersect -> "(and ${conditionExpander(condition.leftCond)} ${conditionExpander(condition.rightCond)})"
        is Negate -> "(not ${conditionExpander(condition.cond)})"
        is Nop -> "true"
        is Single -> transformValue(condition.value)
        is Union -> "(or ${conditionExpander(condition.leftCond)} ${conditionExpander(condition.rightCond)}"
    }

    val body = this.getPath().joinToString("\n") { entry ->
        when (entry) {
            is Condition -> "(assert ${conditionExpander(entry)}) ; $entry"
            is Statement -> "${transformStmt(entry.stmt)} ; $entry"
        }
    }

    val header = "(set-logic ALL)\n" + publicSymbols.values.filterIsInstance<Type>()
        .joinToString("") { "(declare-sort ${reversePublicSymbols[it]})\n" } +
            functions.map { (name, types) ->
                "(declare-fun $name (${types.first.joinToString { transformName(it) }}) ${
                    transformName(
                        types.second
                    )
                })\n"
            }.joinToString("")
    val trailer = "\n(check-sat)\n(get-model)\n; " + functions.toString() + "\n; " + publicSymbols.toString() + "\n; " + reversePublicSymbols.toString()
    return header + body + trailer
}