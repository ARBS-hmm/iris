module Term 
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

public export
Eq Level where
  (==) LZ LZ = True
  (==) (LS l) (LS m) = (l==m)
  (==) _ _ = False

public export
DecEq Level where
  decEq LZ LZ = Yes Refl
  decEq LZ (LS _) = No (\case Refl impossible)
  decEq (LS _) LZ = No (\case Refl impossible)
  decEq (LS l) (LS m) with (decEq l m)
    decEq (LS l) (LS l) | Yes Refl = Yes Refl  -- Note: same variable name
    decEq (LS l) (LS m) | No contra = No (\Refl => contra Refl)

mutual
  public export
  data Ctx : Nat -> Type where
    Nil : Ctx 0
    (::) : Term -> (ctx : Ctx n) -> Ctx (S n)

  public export
  data Term : Type where
    SortT : Level -> Term
    NatTy : Term
    NatTerm : Nat -> Term
    BoolTy : Term
    BoolTerm : Bool -> Term
    VarT :Nat ->  Term
    PiT : Term -> Term -> Term
    LambdaT : Term -> Term -> Term
    App : Term -> Term -> Term
  
  public export
  shift : (inc,thres: Nat) -> (t:Term) -> Term
  shift inc thres (SortT x) = SortT x
  shift inc thres NatTy = NatTy
  shift inc thres (NatTerm k) = NatTerm k
  shift inc thres BoolTy = BoolTy
  shift inc thres (BoolTerm x) = BoolTerm x
  shift inc thres (PiT x y) = PiT (shift inc thres x) (shift inc (S thres) y)
  shift inc thres (LambdaT x y) = LambdaT (shift inc thres x) (shift inc (S thres) y)
  shift inc thres (App x y) = App (shift inc thres x) (shift inc thres y)
  shift inc thres (VarT k) = 
    case (compare k thres) of 
         EQ => VarT k
         LT => VarT k
         GT => VarT (k + inc)

  public export
  subst : (idx : Nat) -> (rep : Term) -> (target : Term) -> Term
  subst idx rep (SortT x) = SortT x
  subst idx rep NatTy = NatTy
  subst idx rep (NatTerm k) = NatTerm k
  subst idx rep BoolTy = BoolTy
  subst idx rep (BoolTerm x) = BoolTerm x
  subst idx rep (PiT x y) = PiT (subst idx rep x) (subst (S idx) (shift 1 0 rep) y)
  subst idx rep (LambdaT x y) = LambdaT (subst idx rep x) (subst (S idx) (shift 1 0 rep) y)
  subst idx rep (App x y) = App (subst idx rep x) (subst idx rep y)
  subst idx rep (VarT k) = 
    case (compare k idx) of 
         EQ => shift k 0 rep 
         LT => VarT (minus 1 k)
         GT => VarT k

  public export
  data Judge : Ctx n -> Term -> (ty : Term) -> Type where
    SortType : Judge c (SortT l) (SortT (LS l))
    NatType : Judge c NatTy (SortT LZ)
    BoolType : Judge c BoolTy (SortT LZ)
    JNat : Judge c (NatTerm n) NatTy
    JBool : Judge c (BoolTerm b) BoolTy

    JVar : {c : Ctx n} -> (k : Nat) -> 
           (f : Fin n) -> (natToFin k n = Just f) ->
           Judge c (VarT k) (indexTy c f)

    Weak : (term : Judge c x xty) -> (wellTyped : Judge c y yty) -> Judge (yty::c) x xty
    Form : Judge c ty (SortT l) -> Judge (ty::c) (tyb) (SortT m) ->
           Judge c (PiT ty tyb) (SortT (maxLevel l m))
    Abst : (piExists : Judge c (PiT a b) (SortT k)) ->
           (Judge (a::c) body bty) -> 
           Judge c (LambdaT a body) (PiT a bty)
    Appl : (pi: Judge c fn (PiT domty bty)) ->
           (Judge c arg domty) -> Judge c (App fn arg) (subst 0 arg bty)

  public export
  indexTy : (c : Ctx n) -> (Fin n) -> Term 
  indexTy [] FZ impossible
  indexTy [] (FS x) impossible
  indexTy (x :: ctx) FZ = x
  indexTy (x :: ctx) (FS y) = indexTy ctx y

data Conv : Term -> Term -> Type where
  CBeta  : Conv (App (LambdaT a m) n) (subst 0 n m)
  CEta   : Conv (LambdaT a (App (shift 1 0 m) (VarT 0))) m
  CTrans : Conv a b -> Conv b c -> Conv a c
