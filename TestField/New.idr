module TestField.New
import Data.Vect

data Level : Type where
  LZ : Level
  LS : Level -> Level
  
mutual
  data Ty : (ctxLen:Nat) -> Type where
    TVar : Fin n -> Ty n
    Uni : Level -> Ty n
    NatTy : Ty n
    BoolTy : Ty n
    Pi : Ty n -> Ty (S n) -> Ty n
    AppTy : {c:Ctx n} -> (x:Ty n) -> (parseArg {c} x) -> Ty n  -- NEEDS {c}
    IndName : String -> Ty n
    Induct : (name : String) -> (tel : Ctx arity) -> (l:Level) -> 
             (cons : List (Con arity name)) -> Ty n

  data Ctx : Nat -> Type where
    Nil : Ctx 0
    (::) : Ctx n -> Ty n -> Ctx (S n)

  weakenCtx : Ctx n -> Ctx (S n)

  weaken : Ty n -> Ty (S n)
  weaken NatTy = NatTy
  weaken BoolTy = BoolTy
  weaken (Uni l) = Uni l
  weaken _ = ?h

  data Con : Nat -> String -> Type where
    Constructor : (name:String) -> 
                  (arity : Nat) ->
                  (tel : Ctx arity) ->
                  (ret : Ty (arity+1)) -> Con arity name


  index : Fin n -> Ctx n -> Ty n
  index FZ (ctx::x) = weaken x 
  index (FS i) (ctx::x) = weaken (index i ctx)

  data Term : Ctx n -> Ty n -> Type where
    Var : (idx : Fin n) -> Term c (index idx c)
    UniTerm : Level -> Term c (Uni (LS l))  -- Fixed: Uni (LS l) not Uni l
    NatTerm : Nat -> Term c NatTy 
    BoolTerm : Bool -> Term c BoolTy
    Lambda : (x : Ty n) -> 
           (body : Term (ctx::x) retTy) -> 
           Term ctx (Pi x retTy)


  strengthen : Ty (S n) -> Ty n

  parseTy : (c:Ctx n) -> (param : Ctx n) -> Type
  parseTy c [] = ?g
  parseTy ctx (x :: y) = (Term ctx (weaken y), parseTy ctx (weakenCtx x))
  
  parseArg : {n:Nat} -> {c:Ctx n} -> Ty n -> Type
  parseArg {c} (Induct name indices _ _) = parseTy c indices
  parseArg _ = ()

  refZero : Ty (S n) -> Bool
  refZero = ?refZeroImpl

reflect : {c:Ctx n} -> {t:Ty n} -> Term c ty -> Ty n
reflect {t} _ = t

-- #examples
idFunc : {c:Ctx n} -> Term c (Pi NatTy NatTy)
idFunc = Lambda NatTy (Var FZ)

vect
