
import com.github.javaparser.StaticJavaParser
import com.github.javaparser.ast.CompilationUnit
import java.nio.file.Files
import java.nio.file.Paths

val cu: CompilationUnit = StaticJavaParser.parse("public void main() { return 0; }")

fun main() {
    print(cu)
}
