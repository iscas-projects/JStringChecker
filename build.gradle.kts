plugins {
    kotlin("jvm") version "1.9.22"
}

repositories {
    mavenCentral()
}


dependencies {
    implementation("org.soot-oss:soot:4.4.1")
    implementation("com.github.javaparser:javaparser-symbol-solver-core:3.25.8")
}