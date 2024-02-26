import soot.*
import soot.grimp.internal.GNewInvokeExpr
import soot.jimple.*
import soot.jimple.internal.JIdentityStmt
import soot.jimple.internal.JInstanceFieldRef
import soot.jimple.internal.JReturnStmt
import soot.jimple.internal.JReturnVoidStmt
import soot.jimple.internal.JStaticInvokeExpr
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

fun transformSingleStmtToCppCompat(stmt: Stmt): String {
    return when (stmt) {
        is JIdentityStmt -> transformTypeToCppCompatWithStructPrefix(stmt.rightOp.type) /* ThisRef / ParameterRef */ + " " + stmt.leftOp + ";"
        is AssignStmt -> formatFieldOrArrayDeclToCppCompat(transformValueToCppCompat(stmt.leftOp), stmt.leftOp.type) +
                     " = " + transformValueToCppCompat(stmt.rightOp) + "; // $stmt"
        is IfStmt -> ""
        is GotoStmt -> ""
        is ThrowStmt -> "exit(); // $stmt"
        is JReturnStmt -> "$stmt;"
        is JReturnVoidStmt -> "return;"
        is InvokeStmt -> "${transformValueToCppCompat(stmt.invokeExpr)}; // $stmt"
        else -> "$stmt // $stmt"
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
    // the symbol that are defined and referred in the bytecode
    val publicSymbols = mutableMapOf<String, Value>()
    // search according to the value its corresponding public symbol
    val reversePublicSymbols = mutableMapOf<Value, String>()
    // affiliate variables (in inner scope, for example)
    val privateSymbols = mutableListOf<String>()
    fun grabRandomName(): String {
        var name: String
        do {
            name = ("var" + floor(Math.random() * 4000.0).toInt())
        } while (name in publicSymbols.keys || name in privateSymbols)
        return name
    }

    fun transformName(varName: Local): String {
        val sym = reversePublicSymbols[varName]
        if (sym == null) {
            val name = grabRandomName()
            publicSymbols[name] = varName
            reversePublicSymbols[varName] = name
            return name
        } else { return sym }
    }

    fun transformValue(value: Value) = ""

    fun transformInvoke(invoke: InvokeExpr) = ""

    fun transformDefine(ty: Type, lvalue: Value, rvalue: Value? = null) = ""

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

    val header = "(set-logic ALL)\n"
    val trailer = "\n(check-sat)\n(get-model)\n"
    return header + body + trailer
}