import soot.Value
import soot.jimple.Stmt

// TODO: is there something like enum in Rust to wrap this
sealed interface PathItem

class Statement(val stmt: Stmt, private val debugInfo: String = ""): PathItem {
    override fun toString(): String {
        return "Statement: $stmt $debugInfo"
    }
}

sealed interface Condition: PathItem {
    fun getValues(): List<Value>
}
class Single(val cond: Value, private val debugInfo: String = ""): Condition {
    override fun toString(): String {
        return "Cond: $cond $debugInfo"
    }

    override fun getValues(): List<Value> {
        return listOf(cond)
    }
}

class Negate(val cond: Condition, private val debugInfo: String = ""): Condition {
    override fun toString(): String {
        return "Negate: $cond $debugInfo"
    }

    override fun getValues(): List<Value> {
        return cond.getValues()
    }
}

class Union(val leftCond: Condition, val rightCond: Condition, private val debugInfo: String = ""):
    Condition {
    override fun toString(): String {
        return "Union: $leftCond and $rightCond $debugInfo"
    }

    override fun getValues(): List<Value> {
        return leftCond.getValues() + rightCond.getValues()
    }
}

class Intersect(val leftCond: Condition, val rightCond: Condition, private val debugInfo: String = ""):
    Condition {
    override fun toString(): String {
        return "Intersect: $leftCond and $rightCond $debugInfo"
    }

    override fun getValues(): List<Value> {
        return leftCond.getValues() + rightCond.getValues()
    }
}

class Nop(private val debugInfo: String = ""): Condition {
    override fun toString(): String {
        return "Non Conditional"//debugInfo.ifEmpty { "" }
    }

    override fun getValues(): List<Value> {
        return listOf()
    }
}