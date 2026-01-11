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
    AppTy : (x:Ty n) -> (parseArg x) -> Ty n  -- Type-level application
    Induct : (String) -> (indices : List (Ty n)) -> Ty n 


  data Ctx : Nat -> Type where
    Nil : Ctx 0
    (::) : Ctx n -> Ty n -> Ctx (S n)

  index : Fin n -> Ctx n -> Ty n
  index FZ (ctx::x) = weaken x 
  index (FS i) (ctx::x) = weaken (index i ctx)

  data Term : Ctx n -> Ty n -> Type where
    Var : (idx : Fin n) -> Term c (index idx c)
    UniTerm : Level -> Term c (Uni (LS l))
    NatTerm : Nat -> Term c NatTy 
    BoolTerm : Bool -> Term c BoolTy
    Lambda : (x : Ty n) -> 
           (body : Term (ctx::x) retTy) -> 
           Term ctx (Pi x retTy)

  parseTy : {n:Nat} -> {c:Ctx n} -> List (Ty n) -> Type
  parseTy {c} [] = Term c NatTy  -- Default to Nat for empty
  parseTy {c} [NatTy] = Term c NatTy
  parseTy {c} [BoolTy] = Term c BoolTy
  parseTy {c} [Uni l] = Term c (Uni l)
  parseTy {c} [t] = Term c t  -- Generic fallback
  parseTy {c} (NatTy::xs) = (Term c NatTy, parseTy {c=c} xs)
  parseTy {c} (BoolTy::xs) = (Term c BoolTy, parseTy {c=c} xs)
  parseTy {c} (Uni l::xs) = (Term c (Uni l), parseTy {c=c} xs)
  parseTy {c} (t::xs) = (Term c t, parseTy {c=c} xs)  -- Generic case
  
  parseArg : {n:Nat} -> {c:Ctx n}-> Ty n -> Type
  parseArg (Induct _ indices) = parseTy {c} indices 
  parseArg _ = ()

  weaken : Ty n -> Ty (S n)
  weaken NatTy = NatTy
  weaken _ = ?h

  refZero : Ty (S n) -> Bool
  refZero = ?refZeroImpl


reflect : {c:Ctx n} -> {t:Ty n} -> Term c ty -> Ty n
reflect {c} {t} _ = t

idFunc : {c:Ctx n} -> Term c (Pi NatTy NatTy)
idFunc = Lambda NatTy (Var FZ)

vect : Ty k
vect = (Induct "Vector" [NatTy,Uni LZ])
-- Vector type constructor
vectTy : Ty k
vectTy = Induct "Vector" [NatTy, Uni LZ]

vectNat3 : Ty k
vectNat3 = AppTy vectTy (NatTy, NatTy)





