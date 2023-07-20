fun main() {
    // Create a new typechecker
    val typechecker = Typechecker()

    // Define some example types and unknowns
    val intType = Monotype.Integer
    val boolType = Monotype.Bool
    val unknownType1 = typechecker.freshUnknown()
    val unknownType2 = typechecker.freshUnknown()

    // Print the initial types and unknowns
    println("Initial Types:")
    println("Int Type: ${intType.print()}")
    println("Bool Type: ${boolType.print()}")
    println("Unknown Type 1: ${unknownType1.print()}")
    println("Unknown Type 2: ${unknownType2.print()}")
    println()

    // Unify the types
    typechecker.unify(intType, unknownType1)
    typechecker.unify(boolType, unknownType2)

    // Print the unified types
    println("Unified Types:")
    println("Int Type: ${typechecker.applySolution(intType).print()}")
    println("Bool Type: ${typechecker.applySolution(boolType).print()}")
    println("Unknown Type 1: ${typechecker.applySolution(unknownType1).print()}")
    println("Unknown Type 2: ${typechecker.applySolution(unknownType2).print()}")
}