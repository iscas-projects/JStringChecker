plugins {
    kotlin("multiplatform") version "1.9.22"
}

repositories {
    mavenCentral()
}


dependencies {
    "commonMainApi"("org.soot-oss:soot:4.4.1")
}

kotlin {
    sourceSets {
        val commonMain by getting {
            dependencies {
                api("org.soot-oss:soot:4.4.1")
            }
        }
    }

    mingwX64("native") {
        binaries {
            sharedLib {
                baseName = "libnative"
            }
        }
    }
}

tasks.wrapper {
    gradleVersion = "8.1.1"
    distributionType = Wrapper.DistributionType.ALL
}