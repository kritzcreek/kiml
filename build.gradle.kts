import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    kotlin("jvm") version "1.3.50"
}

group = "creek"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
    jcenter()
    maven("https://dl.bintray.com/jannis/kotlin-pretty")
}

dependencies {
    implementation(kotlin("stdlib-jdk8"))
    compile("com.github.cretz.asmble:asmble-compiler:0.4.0")
    implementation("kotlin-pretty:kotlin-pretty:0.5.2")
    implementation("io.arrow-kt:arrow-core:0.10.5")
    implementation("org.jetbrains.kotlinx:kotlinx-collections-immutable-jvm:0.3.2")
}

tasks.withType<KotlinCompile> {
    kotlinOptions.jvmTarget = "1.8"
}
val compileKotlin: KotlinCompile by tasks
compileKotlin.kotlinOptions {
    freeCompilerArgs = listOf("-XXLanguage:+InlineClasses")
}