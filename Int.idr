module Int 
import Data.Vect
import Decidable.Equality
%default total

public export
data Level : Type where
  LZ : Level
  LS : Level -> Level

public export
maxLevel : Level -> Level -> Level
maxLevel LZ LZ = LZ
maxLevel LZ (LS x) = LS x
maxLevel (LS x) LZ = LS x
maxLevel (LS x) (LS y) = maxLevel x y

mutual
  public export
  data Ctx : Nat -> Type where
    Nil : Ctx 0
    (::) : Term n -> (ctx : Ctx n) -> Ctx (S n)

  public export
  data Term : (n : Nat) -> Type where  -- Term now knows its context size
    SortT : Level -> Term n
    NatTy : Term n
    NatTerm : Nat -> Term n
    BoolTy : Term n
    BoolTerm : Bool -> Term n
    VarT : Fin n -> Term n
    PiT : Term n -> Term (S n) -> Term n
    LambdaT : Term n -> Term (S n) -> Term n
    App : Term n -> Term n -> Term n

  public export
  subst : (idx : Nat) -> (rep : Term k) -> (target : Term k) -> Term k
  subst idx rep (SortT x) = SortT x
  subst idx rep NatTy = NatTy
  subst idx rep (NatTerm j) = NatTerm j
  subst idx rep BoolTy = BoolTy
  subst idx rep (BoolTerm x) = BoolTerm x
  subst idx rep (VarT FZ) = rep
  subst idx rep (VarT (FS x)) = 
    let xNat = finToNat x in
    if idx == xNat 
      then rep 
      else VarT (FS x)
  subst idx rep (PiT dom body) = 
    PiT (subst idx rep dom) 
        (subst (S idx) (weakenTerm rep) body)
  subst idx rep (LambdaT ty body) = 
    LambdaT (subst idx rep ty) 
            (subst (S idx) (weakenTerm rep) body)
  subst idx rep (App f x) = 
    App (subst idx rep f) (subst idx rep x)

  public export
  data Judge : Ctx n -> Term n -> (ty : Term n) -> Type where
    SortType : Judge c (SortT l) (SortT (LS l))
    NatType : Judge c NatTy (SortT LZ)
    BoolType : Judge c BoolTy (SortT LZ)
    JNat : Judge c (NatTerm n) NatTy
    JBool : Judge c (BoolTerm b) BoolTy
    JVar : (idx : Fin n) -> Judge c (VarT idx) (indexTy c idx)
    Weak : (term : Judge c x xty) -> (wellTyped : Judge c y yty) -> Judge (yty::c) (weakenTerm x) (weakenTerm xty)

    Form : Judge c ty (SortT l) -> Judge (ty::c) (tyb) (SortT m) ->
           Judge c (PiT ty tyb) (SortT (maxLevel l m))

    Abst : (piExists : Judge c (PiT a b) (SortT k)) ->
           (Judge (a::c) body bty) -> 
           Judge c (LambdaT a body) (PiT a bty)
    Appl : (pi: Judge c fn (PiT domty (weakenTerm bty))) ->
           (Judge c arg domty) -> Judge c (App fn arg) (subst 0 arg bty)


  public export
  weakenTerm : Term n -> Term (S n)
  weakenTerm (VarT idx) = VarT (FS idx)
  weakenTerm (SortT l) = SortT l
  weakenTerm NatTy = NatTy
  weakenTerm (NatTerm k) = NatTerm k
  weakenTerm BoolTy = BoolTy
  weakenTerm (BoolTerm b) = BoolTerm b
  weakenTerm (PiT a b) = PiT (weakenTerm a) (weakenTerm b)
  weakenTerm (LambdaT a b) = LambdaT (weakenTerm a) (weakenTerm b)
  weakenTerm (App f a) = App (weakenTerm f) (weakenTerm a)

  public export
  indexTy : (c : Ctx n) -> Fin n -> Term n 
  indexTy [] FZ impossible
  indexTy [] (FS x) impossible
  indexTy (x :: ctx) FZ = weakenTerm x
  indexTy (x :: ctx) (FS y) = weakenTerm (indexTy ctx y)

-- ##############################33

emptyCtx : Ctx 0
emptyCtx = []

five : Judge Nil (NatTerm 5) NatTy
five = JNat

innerPi : Judge (NatTy::[]) (PiT NatTy NatTy) (SortT LZ)
innerPi = Form NatType (Weak NatType (JVar 0))

innerLambda : Judge (NatTy::[]) (LambdaT NatTy (VarT 0)) (PiT NatTy NatTy)
innerLambda = Abst innerPi bodyProof where
      bodyProof : Judge (NatTy::NatTy::[]) (VarT 0) (weakenTerm NatTy)
      bodyProof = JVar 0

func : Judge [] (LambdaT NatTy (LambdaT NatTy (VarT 0))) (PiT NatTy (PiT NatTy NatTy))
func = Abst outerPi innerLambda where
      outerPi : Judge [] (PiT NatTy (PiT NatTy NatTy)) (SortT LZ)
      outerPi = Form NatType innerPi  -- innerPi is the proof of PiT NatTy NatTy in context (NatTy::[])

idk : Judge [] (LambdaT NatTy (VarT 0)) (PiT NatTy NatTy)
idk = Abst piNatNat (JVar 0)  -- Not Weak!
  where
    piNatNat : Judge [] (PiT NatTy NatTy) (SortT LZ)
    piNatNat = Form NatType NatType

