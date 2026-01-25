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
  shift : (idx,thres: Nat) -> Term k -> Term (k+idx)
  shift idx thres (SortT x) = SortT x
  shift idx thres NatTy = NatTy
  shift idx thres (NatTerm j) = NatTerm j
  shift idx thres BoolTy = BoolTy
  shift idx thres (BoolTerm x) = BoolTerm x
  shift idx thres (PiT x y) = PiT (shift idx thres x) (shift idx (S thres) y)
  shift idx thres (LambdaT x y) = LambdaT (shift idx thres x) (shift idx (S thres) y)
  shift idx thres (App x y) = App (shift idx thres x) (shift idx thres y)
  shift idx thres (VarT x) = 
    if (finToNat x) < thres then (VarT (weakenN idx x))
                 else (VarT (shiftFree idx x)) where
                   shiftFree : (idx:Nat) -> Fin k -> Fin (k + idx) 
                   shiftFree 0 f = rewrite (plusZeroRightNeutral k) in f
                   shiftFree (S j) f = rewrite sym (plusSuccRightSucc k j) in
                     FS (shiftFree j f)
  strengthen : Fin (S k) -> Fin k
  strengthen f = ?h

  public export
  subst : (idx : Nat) -> (rep : Term k) -> (target : Term (S k)) -> Term k
  subst idx sub (SortT x) = SortT x
  subst idx sub NatTy = NatTy
  subst idx sub (NatTerm j) = NatTerm j
  subst idx sub BoolTy = BoolTy
  subst idx sub (BoolTerm x) = BoolTerm x
  subst idx sub (PiT x y) = PiT (subst idx sub x) (subst (S idx) (shift 1 0 sub) y)
  subst idx sub (LambdaT x y) = LambdaT (subst idx sub x) (subst (S idx) sub y)
  subst idx sub (App x y) = App (subst idx sub x) (subst idx sub y)
  subst idx sub (VarT x) = case compare (finToNat x) idx of
                                EQ => shift idx 0 sub
                                LT => VarT x
                                GT => VarT (strengthen x)

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

