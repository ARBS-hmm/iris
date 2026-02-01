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

public export
DecEq Term where
  decEq (SortT l1) (SortT l2) with (decEq l1 l2)
    decEq (SortT l) (SortT l) | Yes Refl = Yes Refl
    decEq (SortT l1) (SortT l2) | No contra = No (\Refl => contra Refl)
  
  decEq NatTy NatTy = Yes Refl
  
  decEq (NatTerm n1) (NatTerm n2) with (decEq n1 n2)
    decEq (NatTerm n) (NatTerm n) | Yes Refl = Yes Refl
    decEq (NatTerm n1) (NatTerm n2) | No contra = No (\Refl => contra Refl)
  
  decEq BoolTy BoolTy = Yes Refl
  
  decEq (BoolTerm b1) (BoolTerm b2) with (decEq b1 b2)
    decEq (BoolTerm b) (BoolTerm b) | Yes Refl = Yes Refl
    decEq (BoolTerm b1) (BoolTerm b2) | No contra = No (\Refl => contra Refl)
  
  decEq (VarT k1) (VarT k2) with (decEq k1 k2)
    decEq (VarT k) (VarT k) | Yes Refl = Yes Refl
    decEq (VarT k1) (VarT k2) | No contra = No (\Refl => contra Refl)
  
  decEq (PiT a1 b1) (PiT a2 b2) with (decEq a1 a2)
    decEq (PiT a b1) (PiT a b2) | Yes Refl with (decEq b1 b2)
      decEq (PiT a b) (PiT a b) | Yes Refl | Yes Refl = Yes Refl
      decEq (PiT a b1) (PiT a b2) | Yes Refl | No contra = No (\Refl => contra Refl)
    decEq (PiT a1 b1) (PiT a2 b2) | No contra = No (\Refl => contra Refl)
  
  decEq (LambdaT a1 b1) (LambdaT a2 b2) with (decEq a1 a2)
    decEq (LambdaT a b1) (LambdaT a b2) | Yes Refl with (decEq b1 b2)
      decEq (LambdaT a b) (LambdaT a b) | Yes Refl | Yes Refl = Yes Refl
      decEq (LambdaT a b1) (LambdaT a b2) | Yes Refl | No contra = No (\Refl => contra Refl)
    decEq (LambdaT a1 b1) (LambdaT a2 b2) | No contra = No (\Refl => contra Refl)
  
  decEq (App f1 a1) (App f2 a2) with (decEq f1 f2)
    decEq (App f a1) (App f a2) | Yes Refl with (decEq a1 a2)
      decEq (App f a) (App f a) | Yes Refl | Yes Refl = Yes Refl
      decEq (App f a1) (App f a2) | Yes Refl | No contra = No (\Refl => contra Refl)
    decEq (App f1 a1) (App f2 a2) | No contra = No (\Refl => contra Refl)
  
  decEq (SortT _) NatTy = No $ \Refl impossible
  decEq (SortT _) (NatTerm _) = No $ \Refl impossible
  decEq (SortT _) BoolTy = No $ \Refl impossible
  decEq (SortT _) (BoolTerm _) = No $ \Refl impossible
  decEq (SortT _) (VarT _) = No $ \Refl impossible
  decEq (SortT _) (PiT _ _) = No $ \Refl impossible
  decEq (SortT _) (LambdaT _ _) = No $ \Refl impossible
  decEq (SortT _) (App _ _) = No $ \Refl impossible
  
  decEq NatTy (SortT _) = No $ \Refl impossible
  decEq NatTy (NatTerm _) = No $ \Refl impossible
  decEq NatTy BoolTy = No $ \Refl impossible
  decEq NatTy (BoolTerm _) = No $ \Refl impossible
  decEq NatTy (VarT _) = No $ \Refl impossible
  decEq NatTy (PiT _ _) = No $ \Refl impossible
  decEq NatTy (LambdaT _ _) = No $ \Refl impossible
  decEq NatTy (App _ _) = No $ \Refl impossible
  
  decEq (NatTerm _) (SortT _) = No $ \Refl impossible
  decEq (NatTerm _) NatTy = No $ \Refl impossible
  decEq (NatTerm _) BoolTy = No $ \Refl impossible
  decEq (NatTerm _) (BoolTerm _) = No $ \Refl impossible
  decEq (NatTerm _) (VarT _) = No $ \Refl impossible
  decEq (NatTerm _) (PiT _ _) = No $ \Refl impossible
  decEq (NatTerm _) (LambdaT _ _) = No $ \Refl impossible
  decEq (NatTerm _) (App _ _) = No $ \Refl impossible
  
  decEq BoolTy (SortT _) = No $ \Refl impossible
  decEq BoolTy (NatTerm _) = No $ \Refl impossible
  decEq BoolTy (BoolTerm _) = No $ \Refl impossible
  decEq BoolTy (VarT _) = No $ \Refl impossible
  decEq BoolTy (PiT _ _) = No $ \Refl impossible
  decEq BoolTy (LambdaT _ _) = No $ \Refl impossible
  decEq BoolTy (App _ _) = No $ \Refl impossible
  decEq BoolTy NatTy = No $ \Refl impossible
  
  decEq (BoolTerm _) (SortT _) = No $ \Refl impossible
  decEq (BoolTerm _) NatTy = No $ \Refl impossible
  decEq (BoolTerm _) BoolTy = No $ \Refl impossible
  decEq (BoolTerm _) (NatTerm _) = No $ \Refl impossible
  decEq (BoolTerm _) (VarT _) = No $ \Refl impossible
  decEq (BoolTerm _) (PiT _ _) = No $ \Refl impossible
  decEq (BoolTerm _) (LambdaT _ _) = No $ \Refl impossible
  decEq (BoolTerm _) (App _ _) = No $ \Refl impossible
  
  decEq (VarT _) (SortT _) = No $ \Refl impossible
  decEq (VarT _) NatTy = No $ \Refl impossible
  decEq (VarT _) (NatTerm _) = No $ \Refl impossible
  decEq (VarT _) BoolTy = No $ \Refl impossible
  decEq (VarT _) (BoolTerm _) = No $ \Refl impossible
  decEq (VarT _) (PiT _ _) = No $ \Refl impossible
  decEq (VarT _) (LambdaT _ _) = No $ \Refl impossible
  decEq (VarT _) (App _ _) = No $ \Refl impossible
  
  decEq (PiT _ _) (SortT _) = No $ \Refl impossible
  decEq (PiT _ _) NatTy = No $ \Refl impossible
  decEq (PiT _ _) (NatTerm _) = No $ \Refl impossible
  decEq (PiT _ _) BoolTy = No $ \Refl impossible
  decEq (PiT _ _) (BoolTerm _) = No $ \Refl impossible
  decEq (PiT _ _) (VarT _) = No $ \Refl impossible
  decEq (PiT _ _) (LambdaT _ _) = No $ \Refl impossible
  decEq (PiT _ _) (App _ _) = No $ \Refl impossible
  
  decEq (LambdaT _ _) (SortT _) = No $ \Refl impossible
  decEq (LambdaT _ _) NatTy = No $ \Refl impossible
  decEq (LambdaT _ _) (NatTerm _) = No $ \Refl impossible
  decEq (LambdaT _ _) BoolTy = No $ \Refl impossible
  decEq (LambdaT _ _) (BoolTerm _) = No $ \Refl impossible
  decEq (LambdaT _ _) (VarT _) = No $ \Refl impossible
  decEq (LambdaT _ _) (App _ _) = No $ \Refl impossible
  decEq (LambdaT _ _) (PiT _ _) = No $ \Refl impossible
  
  decEq (App _ _) (SortT _) = No $ \Refl impossible
  decEq (App _ _) NatTy = No $ \Refl impossible
  decEq (App _ _) (NatTerm _) = No $ \Refl impossible
  decEq (App _ _) BoolTy = No $ \Refl impossible
  decEq (App _ _) (BoolTerm _) = No $ \Refl impossible
  decEq (App _ _) (VarT _) = No $ \Refl impossible
  decEq (App _ _) (PiT _ _) = No $ \Refl impossible
  decEq (App _ _) (LambdaT _ _) = No $ \Refl impossible
