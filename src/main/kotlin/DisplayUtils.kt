import soot.ArrayType
import soot.Type
import soot.Value
import soot.grimp.internal.GNewInvokeExpr
import soot.jimple.*
import soot.jimple.internal.JIdentityStmt
import soot.jimple.internal.JInstanceFieldRef
import soot.jimple.internal.JReturnStmt
import soot.jimple.internal.JReturnVoidStmt
import soot.jimple.internal.JStaticInvokeExpr
import java.io.File

@JvmOverloads
fun<T> Collection<List<T>>.displayCollectionToFile(header: String, logFilePath: String = ".\\path.txt") {
    var content = header + "\n";
    content += this.mapIndexed { index, path ->
        "\n*****************\n\n" +
        "path $index\n" +
        path.asReversed().joinToString { "$it\n" } +
        "\n*****************\n\n"
    }.joinToString()
    displayToFile(content, logFilePath)
}

fun<T> List<T>.displaySummary() {
    this.forEach { print(" " + it.hashCode()) }
    println("")
}

//
//fun<T> List<List<T>>.displaySummary() {
//    this.forEachIndexed { index, path ->
//        println("path $index")
//        path.forEach { print(" " + it.hashCode()) }
//    }
//}

fun<T> Collection<List<T>>.display() {
    this.forEachIndexed { index, path ->
        println("path $index")
        path.asReversed().forEach { print(" " + it.toString()) }
    }
}

@JvmOverloads
fun<T, E> Collection<List<T>>.displayZippedToFile(header: String, tags: List<List<E>>, logFilePath: String = ".\\path.txt") {
    var content = header + "\n"
    content += this.zip(tags).mapIndexed { index, (path, tag) ->
            "\n*****************\n\n" +
            "path $index\n" +
            path.asReversed().zipWithNext().zip(tag).joinToString { "\n$it\n\n" } +

            "\n\nthen begins the complete path and constraint chain\n\n\n" +
            path.asReversed() + "\n" +
            tag + "\n" +

            "\n*****************\n"
        }.joinToString()
    displayToFile(content, logFilePath)
}



fun inlineStringOps(expr: InvokeExpr): String {
//    Scene.v().loadClassAndSupport("java.lang.String")
//    val stringClass = Scene.v().getSootClass("java.lang.String")
    return if (expr.methodRef.declaringClass.name.contains("java.lang.String")) {
        with (expr.methodRef.declaringClass.name) {
            when {
                else -> expr.method.toString() + "(${expr.args})"
            }
        }
    } else {
        expr.method.toString() + "(${expr.args})"
    }
}

fun transformTypeToCppCompatWithStructPrefix(ty: Type): String {
    return if ("$ty" in listOf("int", "char", "boolean") ||
        ((ty is ArrayType && "${ty.baseType}" in listOf("int", "char", "boolean")))) "$ty"
    else "struct $ty *".replace('.', '_')
}

/// only for type prefix in a function like "String_append"
fun transformTypeToCppCompat(ty: Type): String {
    return "$ty".replace('.', '_')
}

fun transformValueToCppCompat(value: Value): String {
    return when (value) {
        is NewExpr -> "${transformTypeToCppCompatWithStructPrefix(value.baseType)}{}"
        is JInstanceFieldRef -> "${transformValueToCppCompat(value.base)}->${value.field.name}"
        is StaticFieldRef -> "${value.fieldRef.declaringClass().toString().replace('.', '_')}.${value.fieldRef.name()}"
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
        is AssignStmt -> (if (stmt.leftOp is FieldRef) transformValueToCppCompat(stmt.leftOp)
            else if (stmt.leftOp.type is ArrayType)
                transformTypeToCppCompatWithStructPrefix(stmt.leftOp.type).let {
                    "${it.substringBefore('[')}* ${transformValueToCppCompat(stmt.leftOp)}[${it.substringAfter('[')}"
                        .replace("[]", "[10]")
                }
            else ("${transformTypeToCppCompatWithStructPrefix(stmt.leftOp.type)} ${transformValueToCppCompat(stmt.leftOp)}")) +
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

fun transformSingleCondToCppCompat(cond: Condition): String {
    return when (cond) {
        is Single -> "@(${cond.value});"
        is Negate -> "@!(" + cond.cond + ");"
        is Nop -> ""
        else -> cond.toString()
    }
}

fun String.postProcess() = // trim the $, <, >, and other symbols
    this.replace("$", "___")
        .replace("<clinit>", "__clinit__")
        .replace("<init>", "__init__")
        .replace("@();", "") // trim unnecessary conditions
        .let { noDecl ->
            Regex("^struct \\S* ").findAll(noDecl)
                .map { it.value + "{};" }
                .toSet()
                .joinToString("\n") + "\n" + noDecl
        }

fun displayToFile(content: String, logFilePath: String = ".\\path.txt") {
    File(logFilePath).printWriter().use { out ->
        out.println(content.postProcess())
    }
}

fun emitCppCompatPath(slicers: List<Slicer>) {
    slicers.forEach { slicer ->
        val conditionPlusNull = slicer.getPathConstraints() + Nop()
        displayToFile(slicer.programPath.asReversed().zip(conditionPlusNull).joinToString("\n") { (bl, c) ->
            bl.joinToString("\n") { transformSingleStmtToCppCompat(it as Stmt) } + "\n" +
                    transformSingleCondToCppCompat(c)
        } + slicer.programPath.asReversed())
    }
}


//fun getPathConstraints(paths: Collection<List<Block>>): Collection<List<Condition>> {
//    return paths.map {
//        it.asReversed().zipWithNext().map { (prev, next) ->
//            prev.tail.let { jumpStatement ->
//                if (jumpStatement is IfStmt && jumpStatement.fallsThrough())
//                    if (jumpStatement.target == next.head)
//                        Single(jumpStatement.condition)
//                    else Negate(Single(jumpStatement.condition))
//                else if (jumpStatement is GotoStmt)
//                    Nop()
//                else Nop("DEBUG: $jumpStatement")
//            }
//        }
//    }
//}