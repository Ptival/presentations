-- Presentation given by Valentin Robert for the May 2021 Lambda Lille meetup.

module Advanced

import Control.Monad.Identity
import Control.Monad.Reader
import Data.List
import Data.List.Elem


mutual


    data ExprType
        = BoolType
        | FunctionType Context ExprType
        | IntType
        | UnitType
        | VoidType


    Context : Type
    Context = List ExprType


infixr 10 :+

-- This time we will need 'Assignment' even earlier, to define 'Expr'!
data Assignment : (ExprType -> Type) -> Context -> Type where

    EmptyAssignment : Assignment f []

    (:+) :
        {f : ExprType -> Type} ->
        f t ->
        Assignment f ctx ->
        Assignment f (t :: ctx)


assign : Assignment f ctx -> Elem t ctx -> f t
assign (ft :+ _) Here = ft
assign (_ :+ ctx) (There later) = assign ctx later


mutual

    data Expr : Context -> ExprType -> Type where
        BoolLiteral : Bool -> Expr ctx BoolType
        IntLiteral : Int -> Expr ctx IntType
        UnitLiteral : Expr ctx UnitType
        IfThenElse : Expr ctx BoolType -> Expr ctx a -> Expr ctx a -> Expr ctx a
        Var : Elem varType ctx -> Expr ctx varType
        -- It turns out we can lift any Idris value whose type we can describe:
        -- this supersedes all 'Literal' constructors!
        LiftIdris :
            (type : ExprType) ->
            (value : IdrisType type) ->
            Expr ctx type



    -- This type, a function type will take multiple arguments
    IdrisType : ExprType -> Type
    IdrisType BoolType = Bool
    IdrisType (FunctionType args ret) = FunctionValue args ret
    IdrisType IntType = Int
    IdrisType UnitType = ()
    IdrisType VoidType = Void


    functionType : Context -> ExprType -> Type
    functionType [] ret = IdrisType ret
    functionType (arg :: args) ret = IdrisType arg -> functionType args ret


    data FunctionValue : Context -> ExprType -> Type where

        Closure :
            (closed : FunctionValue (arg :: args) ret) ->
            IdrisType arg ->
            FunctionValue args ret

        Function :
            (body : StmtSeq args ret) ->
            FunctionValue args ret

        IdrisFunction :
            (function : functionType args ret) ->
            FunctionValue args ret



    data Stmt : Context -> Context -> Type where

        CallFunction :
            Elem (FunctionType args ret) ctx ->
            Assignment IdrisType args ->
            Stmt ctx (ret :: ctx)

        SetReg :
            Expr ctx type ->
            Stmt ctx (type :: ctx)


    data TermStmt : Context -> ExprType -> Type where

        Return :
            Elem ret ctx ->
            TermStmt ctx ret


    data StmtSeq : Context -> ExprType -> Type where

        ConsStmtSeq :
            Stmt ctx ctx' ->
            StmtSeq ctx' ret ->
            StmtSeq ctx ret

        TermStmtSeq :
            TermStmt ctx ret ->
            StmtSeq ctx ret


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

eval asn (LiftIdris desc value) = value

-- A 'ReturnHandler callerCtx calleeRet callerRet rtp' contains all the
-- information we need to restore the parent call frame given we have computed
-- the output of the callee.
record ReturnHandler (calleeRet : ExprType) (callerCtx : Context) (callerRet : ExprType) (rtp : Type) where
    constructor MkReturnHandler
    continuation : StmtSeq (calleeRet :: callerCtx) callerRet


record CallFrame (args : Context) (ret : ExprType) where
    constructor MkCallFrame
    frameRegisters : Assignment IdrisType args
    frameStatements : StmtSeq args ret


data CallStack : ExprType -> Type -> Type where

    CallStackCall :
        (callerFrame : CallFrame callerArgs callerRet) ->
        (returnHandler : ReturnHandler calleeRet callerArgs callerRet rtp) ->
        (previousCallStack : CallStack callerRet rtp) ->
        CallStack calleeRet rtp

    CallStackEnd :
        CallStack ret (IdrisType ret)


record SimState (args : Context) (ret : ExprType) (rtp : Type) where
    constructor MkSimState
    activeFrame : CallFrame args ret
    callStack : CallStack ret rtp


record ResolvedCall (ret : ExprType) where
    constructor MkResolvedCall
    callFrame : CallFrame args ret


data ExecState : Type -> Type where

    ResultState : rtp -> ExecState rtp

    CallState :
        ReturnHandler calleeRet callerArgs callerRet rtp ->
        ResolvedCall calleeRet ->
        SimState callerArgs callerRet rtp ->
        ExecState rtp

    ReturnState :
        CallStack ret rtp ->
        IdrisType ret ->
        SimState args ret rtp ->
        ExecState rtp

    RunningState :
        SimState args ret rtp ->
        ExecState rtp


evalReg :
    MonadReader (SimState ctx ret rtp) m =>
    Elem type ctx ->
    m (IdrisType type)
evalReg elem =
    do
        s <- ask
        pure (assign s.activeFrame.frameRegisters elem)


callIdrisFunction : functionType args ret -> Assignment IdrisType args -> IdrisType ret
callIdrisFunction ret EmptyAssignment = ret
callIdrisFunction fn (arg :+ args) = callIdrisFunction (fn arg) args


resolveCall :
    FunctionValue args ret ->
    Assignment IdrisType args ->
    ResolvedCall ret
resolveCall (Closure closed arg) args = resolveCall closed (arg :+ args)
resolveCall (Function body) args = MkResolvedCall (MkCallFrame args body)
resolveCall (IdrisFunction function) args =
    MkResolvedCall
        (MkCallFrame
            (callIdrisFunction function args :+ args)
            (TermStmtSeq (Return Here))
        )


extendFrame :
    IdrisType type ->
    StmtSeq (type :: ctx) ret ->
    CallFrame ctx ret ->
    CallFrame (type :: ctx) ret
extendFrame v s f =
    { frameRegisters $= (v :+)
    , frameStatements := s
    } f


ExecCont : Context -> ExprType -> Type -> Type
ExecCont ctx ret rtp = Reader (SimState ctx ret rtp) (ExecState rtp)


callFunction :
    FunctionValue args ret ->
    Assignment IdrisType args ->
    ReturnHandler ret callerCtx callerRet rtp ->
    ExecCont callerCtx callerRet rtp
callFunction fn args rh = CallState rh (resolveCall fn args) <$> ask


-- The following works, but it will probably be quite hard to explain!


mutual


    stepStmt : Stmt ctx ctx' -> StmtSeq ctx' ret -> ExecCont ctx ret rtp

    stepStmt (CallFunction idx args) rest =
        do
            fnHandle <- evalReg idx
            let resolved = resolveCall fnHandle args
            callFunction fnHandle args (MkReturnHandler rest)

    stepStmt (SetReg {type} expr) rest =
        do
            s <- ask
            let v = eval s.activeFrame.frameRegisters expr
            continueWith { activeFrame $= extendFrame v rest }


    continueWith :
        (SimState args ret rtp -> SimState ctx ret rtp) ->
        ExecCont args ret rtp
    continueWith simStateModifier =
        do
            s <- ask
            pure (runIdentity (runReaderT (simStateModifier s) checkConsTerm))


    checkConsTerm : ExecCont ctx ret rtp
    checkConsTerm =
        do
            s <- ask
            case s.activeFrame.frameStatements of
                ConsStmtSeq stmt stmts => stepStmt stmt stmts
                TermStmtSeq term => pure (RunningState s)


stepTerm :
    TermStmt ctx ret ->
    ExecCont ctx ret rtp
stepTerm (Return idx) =
    do
        s <- ask
        ret <- evalReg idx
        pure (ReturnState s.callStack ret s)


pushCallFrame :
    ReturnHandler calleeRet callerArgs callerRet rtp ->
    CallFrame calleeArgs calleeRet ->
    SimState callerArgs callerRet rtp ->
    SimState calleeArgs calleeRet rtp
pushCallFrame returnHandler simFrame simState =
    { activeFrame := simFrame
    , callStack $= CallStackCall simState.activeFrame returnHandler
    } simState


-- I have inline the following functions in 'dispatchExecState' for brevity:


-- performFunctionCall :
--     ReturnHandler calleeRet callerArgs callerRet rtp ->
--     ResolvedCall calleeRet ->
--     ExecCont callerArgs callerRet rtp
-- performFunctionCall returnHandler resolvedCall =
--     do
--         s <- ask
--         pure (RunningState (pushCallFrame returnHandler resolvedCall.callFrame s))


-- performReturn :
--     CallStack calleeRet rtp ->
--     IdrisType calleeRet ->
--     ExecCont someArgs callerRet rtp
-- performReturn (CallStackCall callerFrame (MkReturnHandler rest) callingContext) ret =
--     do
--         s <- ask
--         let s' = MkSimState
--                     (extendFrame ret rest callerFrame)
--                     callingContext
--         pure (RunningState s')
-- performReturn CallStackEnd ret = pure (ResultState ret)


stepBasicBlock :
    ExecCont ctx ret rtp
stepBasicBlock =
    do
        s <- ask
        case s.activeFrame.frameStatements of
            ConsStmtSeq stmt stmts => stepStmt stmt stmts
            TermStmtSeq term => stepTerm term


dispatchExecState :
    (forall args, ret. SimState args ret rtp -> ExecCont args ret rtp -> a) ->
    (rtp -> a) ->
    ExecState rtp ->
    a

dispatchExecState _ k (ResultState result) =
    k result

dispatchExecState k _ (CallState returnHandler resolvedCall simState) =
    k simState $
        do
            s <- ask
            pure (RunningState (pushCallFrame returnHandler resolvedCall.callFrame s))

dispatchExecState k _ (ReturnState callStack ret simState) =
    k simState $
        case callStack of
            CallStackCall callerFrame returnHandler callingContext =>
                do
                    s <- ask
                    let s' = MkSimState
                                (extendFrame ret returnHandler.continuation callerFrame)
                                callingContext
                    pure (RunningState s')
            CallStackEnd => pure (ResultState ret)

dispatchExecState k _ (RunningState simState) =
    k simState stepBasicBlock


advanceSimulation : SimState args ret rtp -> ExecCont args ret rtp -> ExecState rtp
advanceSimulation simState cont = runIdentity (runReaderT simState cont)


singleStep : ExecState rtp -> ExecState rtp
singleStep = dispatchExecState advanceSimulation ResultState


sum : Expr ctx (FunctionType [IntType, IntType] IntType)
sum = LiftIdris (FunctionType [IntType, IntType] IntType) (IdrisFunction ((+) {ty=Int}))


infixr 10 #


(#) : Stmt ctx ctx' -> StmtSeq ctx' ret -> StmtSeq ctx ret
(#) = ConsStmtSeq


test : StmtSeq [] IntType
test =
    SetReg sum
    # CallFunction Here (1 :+ 2 :+ EmptyAssignment)
    # TermStmtSeq (Return Here)


startState : Assignment IdrisType ctx -> StmtSeq ctx rtp -> ExecState (IdrisType rtp)
startState registers code =
    RunningState (MkSimState (MkCallFrame registers code) CallStackEnd)


nSteps : Int -> ExecState Int
nSteps 0 = startState EmptyAssignment test
nSteps n = singleStep (nSteps (n - 1))
