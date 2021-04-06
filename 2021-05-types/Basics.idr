-- Presentation given by Valentin Robert for the May 2021 Lambda Lille meetup.

module Basics

import Data.List
import Data.List.Elem

-- We will assume you are familiar with algebraic data type declarations as
-- found in OCaml/Haskell/...

namespace ADT

    data Expr : Type where

        BoolLiteral : Bool -> Expr

        IntLiteral : Int -> Expr

        IfThenElse : Expr -> Expr -> Expr -> Expr


    -- While this allows representing some interesting expressions, it also allows
    -- many unpleasant expressions, such as:

    badExpr : Expr
    badExpr =
        IfThenElse
            (IntLiteral 27)
            (BoolLiteral False)
            (IntLiteral 18)


    -- Regardless of the adequacy of this language, let's have a look at what an
    -- evaluator for it would look like.

    data Value
        = BoolValue Bool
        | IntValue Int

    eval : Expr -> Maybe Value
    eval (BoolLiteral b) = Just (BoolValue b)
    eval (IntLiteral i) = Just (IntValue i)
    eval (IfThenElse cond thenBranch elseBranch) =
        do
            -- Here, evaluating the condition may fail!
            vcond <- eval cond
            case vcond of
                BoolValue b =>
                    if b
                    then eval thenBranch
                    else eval elseBranch
                -- And the condition may evaluate to an integer!
                IntValue _ => Nothing


-- Come in generalized algebraic data types: by allowing you to index
-- expressions with some types, you get to enforce some static invariants.

namespace GADT

    -- We need a type-level description for types of our expression language. In
    -- Haskell, you'd likely use 'DataKinds' to lift some data type at the type
    -- level.

    data ExprType
        = BoolType
        | IntType


    data Expr : ExprType -> Type where

        BoolLiteral : Bool -> Expr BoolType

        IntLiteral : Int -> Expr IntType

        IfThenElse : Expr BoolType -> Expr a -> Expr a -> Expr a

        -- But how would we implement well-scoped, well-typed variables?
        -- Var : ??? -> Expr ???


    -- Now, to each 'ExprType', we can associate the corresponding Idris type.
    -- This is a type-level function, which can be done in Haskell via type
    -- families.
    IdrisType : ExprType -> Type
    IdrisType BoolType = Bool
    IdrisType IntType = Int


    -- Now, our evaluation function is simplified a lot: we don't need a sum
    -- type to hold the results as they come at the specified type, and
    -- expressions do not fail to evaluate!
    eval : Expr t -> IdrisType t
    eval (BoolLiteral b) = b
    eval (IntLiteral i) = i
    eval (IfThenElse cond thenBranch elseBranch) =
        if eval cond
        then eval thenBranch
        else eval elseBranch


    -- TODO: maybe try to add variables live, and show how this makes it so that
    -- evaluation can fail upon encountering a free variable.



namespace TypeFamilies

    data ExprType
        = BoolType
        | IntType


    -- In order to guarantee the terms are well scoped and well typed, we need
    -- to keep track of what variables are available, and what their type is.
    -- A 'Context' is a type-level list of type descriptions.
    Context : Type
    Context = List ExprType


    -- An example context where three variables are available, a boolean, an
    -- integer, and another boolean.
    ExampleContext : Context
    ExampleContext = [BoolType, IntType, BoolType]


    -- Note that to avoid dealing with names and substitutions, variable
    -- references will be done by a proof of membership in that list,
    -- effectively storing a (well-typed) index into this list, like so:
    someBoolIndex : Elem BoolType ExampleContext
    someBoolIndex = Here
    someIntIndex : Elem IntType ExampleContext
    someIntIndex = There Here
    otherBoolIndex : Elem BoolType ExampleContext
    otherBoolIndex = There (There Here)


    -- Our datatype of expressions will know be indexed not only by the type it
    -- returns, but also by the context in which the expression was defined.
    -- This context is relevant in the 'Var' case, where a variable can only be
    -- created via a proof of membership guaranteeing both its presence *and*
    -- its type in the context.
    data Expr : Context -> ExprType -> Type where

        BoolLiteral : Bool -> Expr ctx BoolType

        IntLiteral : Int -> Expr ctx IntType

        IfThenElse : Expr ctx BoolType -> Expr ctx a -> Expr ctx a -> Expr ctx a

        Var : Elem varType ctx -> Expr ctx varType
        --         ^^^^^^^                 ^^^^^^^
        -- the type of the expression is the type dictated by the context


    expr : Expr [BoolType, IntType, IntType] IntType
    expr =
        IfThenElse
            (Var Here)
            (Var (There Here))
            (Var (There (There Here)))


    infixr 10 :+

    -- Now in order to evaluate an expression, we must carry around the actual
    -- values of variables that enter the context.  We call the mapping that
    -- relates some slot in the context to the value of the associated variable
    -- an assignment of values to variables.
    --
    -- Here we abstract over 'f', the type-level function that assigns a type to
    -- each expression.  It can be instantiated to be 'IdrisType', our
    -- type-level function that associated the corresponding Idris type to our
    -- language's types, but there are other use cases we may see later!
    data Assignment : (ExprType -> Type) -> Context -> Type where

        EmptyAssignment : Assignment f []

        (:+) :
            {f : ExprType -> Type} ->
            f t ->
            Assignment f ctx ->
            Assignment f (t :: ctx)


    -- Again, to each 'ExprType', we can associate the corresponding Idris type.
    IdrisType : ExprType -> Type
    IdrisType BoolType = Bool
    IdrisType IntType = Int


    -- This is an example assignment: for each 'ExprType' in the context (let's
    -- call it 't'), we must provide a value of type 'IdrisType t'.  So only a
    -- 'Bool' will do in the first slot, an 'Int' in the second slot, and
    -- another 'Bool' in the third slot.
    --
    -- Also note that by construction, the length of the 'Assignment' must be
    -- equal to the length of the 'Context' (see the definition of 'Assignment'
    -- to understand how that is the case).
    a : Assignment IdrisType [BoolType, IntType, IntType]
    a = True :+ 32 :+ 16 :+ EmptyAssignment


    -- Now we are going to need a function to retrieve the value of a given
    -- variable from an 'Assignment'.
    assign : Assignment f ctx -> Elem t ctx -> f t
    assign (ft :+ _) Here = ft
    assign (_ :+ ctx) (There later) = assign ctx later
    -- Notice that this is covering even though we never consider an
    -- EmptyAssigment!  The very existence of an 'Elem t ctx' proof is guarantee
    -- that 'ctx' is not empty.


    -- Now we can write an evaluator for the well-typed, well-scoped 'Expr ctx
    -- t'.  Notice that we no longer need to return a 'Maybe', since there is
    -- no room for failure by construction!
    eval : Assignment IdrisType ctx -> Expr ctx t -> IdrisType t
    eval _ (BoolLiteral b) = b
    eval _ (IntLiteral i) = i
    eval ctx (IfThenElse cond thenBranch elseBranch) =
        if eval ctx cond
        then eval ctx thenBranch
        else eval ctx elseBranch
    eval ctx (Var location) = assign ctx location


    -- Fun fact: we haven't even used dependent types yet!  Those were all
    -- type-level tricks with no dependency on data.


-- Dependent types give us even more power: not only can we do type-level
-- computations, but the input of these computations can come not only from the
-- other *types* in a function's arguments, but also from *values* the function
-- receives!

namespace DT

    data ExprType
        = BoolType
        | FunctionType ExprType ExprType
        | IntType
        | UnitType
        | VoidType


    Context : Type
    Context = List ExprType


    -- ApplicationType : Context -> ExprType -> ExprType
    -- ApplicationType [] ret = ret
    -- ApplicationType (_ :: rest) ret = FunctionType rest ret


    data Expr : Context -> ExprType -> Type where
        BoolLiteral : Bool -> Expr ctx BoolType
        IntLiteral : Int -> Expr ctx IntType
        UnitLiteral : Expr ctx UnitType
        IfThenElse : Expr ctx BoolType -> Expr ctx a -> Expr ctx a -> Expr ctx a
        Var : Elem varType ctx -> Expr ctx varType

        Lambda :
            {ctx : Context} ->
            Expr (arg :: ctx) ret ->
            Expr ctx (FunctionType arg ret)

        Application :
            Expr ctx (FunctionType arg ret) ->
            Expr ctx arg ->
            Expr ctx ret


    expr : Expr [BoolType, IntType, IntType] BoolType
    expr = Application (Lambda (Var (There Here))) (Var Here)


    infixr 10 :+

    -- Now in order to evaluate an expression, we must carry around the actual
    -- values of variables that enter the context.  We call the mapping that
    -- relates some slot in the context to the value of the associated variable
    -- an assignment of values to variables.
    --
    -- Here we abstract over 'f', the type-level function that assigns a type to
    -- each expression.  It can be instantiated to be 'IdrisType', our
    -- type-level function that associated the corresponding Idris type to our
    -- language's types, but there are other use cases we may see later!
    data Assignment : (ExprType -> Type) -> Context -> Type where

        EmptyAssignment : Assignment f []

        (:+) :
            {f : ExprType -> Type} ->
            f t ->
            Assignment f ctx ->
            Assignment f (t :: ctx)


    -- Here we use a feature called induction-recursion to mutually define the
    -- inductive type 'FunctionValue' together with the recursive function
    -- 'IdrisType'.  This neat feature is why I chose Idris over Coq for this
    -- presentation, as Coq does not support induction-recursion and would have
    -- required some tricks to make an equivalent definition.

    mutual


        -- Again, to each 'ExprType', we can associate the corresponding Idris type.
        IdrisType : ExprType -> Type
        IdrisType BoolType = Bool
        IdrisType (FunctionType args ret) = FunctionValue args ret
        IdrisType IntType = Int
        IdrisType UnitType = ()
        IdrisType VoidType = Void


        data FunctionValue : ExprType -> ExprType -> Type where

            Closure :
                (asn : Assignment IdrisType ctx) ->
                (body : Expr (arg :: ctx) ret) ->
                FunctionValue arg ret

            -- PartiallyAppliedClosure :
            --     (layer : FunctionValue (arg :: args) ret) ->
            --     (argVal : IdrisType arg) ->
            --     FunctionValue args ret


    -- This is an example assignment: for each 'ExprType' in the context (let's
    -- call it 't'), we must provide a value of type 'IdrisType t'.  So only a
    -- 'Bool' will do in the first slot, an 'Int' in the second slot, and
    -- another 'Bool' in the third slot.
    --
    -- Also note that by construction, the length of the 'Assignment' must be
    -- equal to the length of the 'Context' (see the definition of 'Assignment'
    -- to understand how that is the case).
    a : Assignment IdrisType [BoolType, IntType, IntType]
    a = True :+ 32 :+ 16 :+ EmptyAssignment


    -- Now we are going to need a function to retrieve the value of a given
    -- variable from an 'Assignment'.
    assign : Assignment f ctx -> Elem t ctx -> f t
    assign (ft :+ _) Here = ft
    assign (_ :+ ctx) (There later) = assign ctx later
    -- Notice that this is covering even though we never consider an
    -- EmptyAssigment!  The very existence of an 'Elem t ctx' proof is guarantee
    -- that 'ctx' is not empty.


    -- Now we can write an evaluator for the well-typed, well-scoped 'Expr ctx
    -- t'.  Notice that we no longer need to return a 'Maybe', since there is
    -- no room for failure by construction!
    eval : Assignment IdrisType ctx -> Expr ctx t -> IdrisType t

    -- old code unchanged
    eval _ (BoolLiteral b) = b
    eval _ (IntLiteral i) = i
    eval asn UnitLiteral = ()
    eval asn (IfThenElse cond thenBranch elseBranch) =
        if eval asn cond
        then eval asn thenBranch
        else eval asn elseBranch
    eval asn (Var location) = assign asn location

    -- new code

    -- Evaluating a 'Lambda' just builds a 'Closure' capturing the function body
    -- and the assignment of variables at the location the function is defined.
    eval asn (Lambda body) = Closure asn body

    -- Evaluating a function 'Application' always yields a 'Closure' for the
    -- function expression (follow the types!), after which we just need to
    -- evaluate the argument of the function and supply its value to the
    -- evaluation of the body, in the correct assignments for each context.
    eval asn (Application fnExpr lastArg) =
        case eval asn fnExpr of
            Closure closureAsn body =>
                eval (eval asn lastArg :+ closureAsn) body
