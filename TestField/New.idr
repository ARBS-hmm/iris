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
    Induct : (String) -> (indices : List (Ty n)) -> Ty n 

  data Ctx : Nat -> Type where
    Nil : Ctx 0
    (::) : Ctx n -> Ty n -> Ctx (S n)

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

  parseTy : {n:Nat} -> {c:Ctx n} -> List (Ty n) -> Type
  parseTy {c} [] = Term c NatTy
  parseTy {c} [Uni LZ] = Ty n
  parseTy {c} [Uni l] = Term c (Uni (LS l))  -- l ≠ LZ
  parseTy {c} [x] = Term c x  -- x ≠ Uni _
  parseTy {c} (Uni LZ::xs) = (Ty n, parseTy {c} xs)
  parseTy {c} (Uni l::xs) = (Term c (Uni (LS l)), parseTy {c} xs)  -- l ≠ LZ
  parseTy {c} (x::xs) = (Term c x, parseTy {c} xs)  -- x ≠ Uni _
  
  parseArg : {n:Nat} -> {c:Ctx n} -> Ty n -> Type
  parseArg {c} (Induct _ indices) = parseTy {c} indices 
  parseArg _ = ()

  weaken : Ty n -> Ty (S n)
  weaken NatTy = NatTy
  weaken BoolTy = BoolTy
  weaken (Uni l) = Uni l
  weaken _ = ?h

  refZero : Ty (S n) -> Bool
  refZero = ?refZeroImpl

reflect : {c:Ctx n} -> {t:Ty n} -> Term c ty -> Ty n
reflect {t} _ = t

-- #examples

idFunc : {c:Ctx n} -> Term c (Pi NatTy NatTy)
idFunc = Lambda NatTy (Var FZ)

vectBool : (c:Ctx k) -> Ty k
vectBool c = AppTy {c=c} (Induct "" [NatTy, Uni LZ]) 
  (NatTerm 3, BoolTy)

constFunc : {c:Ctx n} -> Term c (Pi NatTy (Pi BoolTy NatTy))
constFunc = Lambda NatTy (Lambda BoolTy (Var (FS FZ)))

listNat : (c:Ctx k) -> Ty k
listNat c = AppTy {c=c} (Induct "List" [Uni LZ]) NatTy

typeOfTypes : (c:Ctx k) -> Ty k
typeOfTypes c = AppTy {c=c} (Induct "Container" [Uni (LS LZ)])
  (UniTerm LZ)

vectLengthCheck : {c:Ctx n} -> Term c 
  (Pi NatTy 
    (Pi (AppTy (Induct "Vector" [NatTy, Uni LZ]) (NatTerm 0, BoolTy))
        BoolTy))
--vectLengthCheck {c }=Lambda NatTy 
  --(Lambda (AppTy {c} (Induct "Vector" [NatTy, Uni LZ]) (NatTerm , BoolTy))
    --(BoolTerm True))
