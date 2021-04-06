# Outline

## Introduction

- Present self
- Present Galois
- Disclaimer that opinions are mine! :D
- High-level goals of the presentation:
    * Gently introduce type-level contexts, from abstract data types to
      dependent types,
    * with examples less boring than the usual natural numbers and
      length-indexed vectors,

## Part 1: Algebraic Data Types

- Introduce a regular ADT 'Expr' of expressions, including literal booleans and
  integers, as well as an if-then-else construct and some integer arithmetic
  operation.

- Introduce the type signature of a function `eval : Expr -> Expr` that
  evaluates an expression.

- Show that Idris can generate the pattern-matching code for `eval` from just
  typing `eval e = ?v`.

- Show how it's awkward because nothing prevents me from not evaluating
  anything.  Ask the audience how I could make it so that the function is at
  least forced to do some work on the `IfThenElse` and `Plus` constructors of
  `Expr`.

- Introduce a type `Value` of values, including boolean and integer values.

- Show that Idris can also generate the output of the function via proof search.
  Show an example where it gets lucky `eval (BoolLiteral b)`, and an example
  where it cheats `eval (IntLiteral i)`.

- Focus on `IfThenElse`, show that it is awkward in that the condition is not
  guaranteed to be a boolean.  Also mention how the two branches can be of
  different types!

- Time to learn our first technique to prevent most of the awkwardness from this
  section.

## Part 2: Generalized Algebraic Data Types

- Explain that instead of having the type `Expr` within which all values
  constructed via one of our constructors live, we can instead make it a family
  of types, indexed by a representation of the type of values at different
  indices.

- Consider the `BoolLiteral`, figure out with the audience in what family the
  values it construct should live.  They all live at `BoolType`.

- Consider the `IntLiteral` constructor, likewise, all at `IntType`.

- Consider the `IfThenElse` constructor, and make the audience realize that it
  does not always live at one of the base types, but rather, it depends on its
  arguments.  Note that the **type** of the input influences the **type** of the
  output.

- Update the `Value` type to also be indexed.  Write the function `eval : Expr t
  -> Value t`.  Mention the absence of `Maybe` in the return type!

## Part 2.5: Type-level functions

- Mention that in languages like Idris, we can write functions that take
  **types** as inputs, and return **types** as outputs.  Maybe mention that
  there are restrictions, for instance you cannot pattern-match directly on a
  type since it is part of an open-ended universe of types, but we can do
  something cool.

- It would be cool to have a function which, given a descriptor of a type of our
  language, tells us the type of corresponding values in Idris.  `BoolType`
  corresponds to `Bool`, `IntType` to `Int`, etc.

- Write the function `IdrisType : ExprType -> Type`.

- Now rewrite `eval : Expr t -> IdrisType t`.  Maybe show the holes at different
  branches.  Maybe show the automation if it works.
