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
    decEq (LS l) (LS l) | Yes Refl = Yes Refl
    decEq (LS l) (LS m) | No contra = No (\Refl => contra Refl)

data IoPrim : Type where 
  SysCmd : String -> IoPrim
  SysCall : String -> IoPrim
  GetEnv : String -> IoPrim
  SetEnv : String -> String -> IoPrim
  ReadFile : String -> IoPrim
  WriteFile : (filename : String) -> String -> IoPrim 
  ReadLine : IoPrim
  Exit : Int -> IoPrim 

public export
data Term : Type where
  SortT : Level -> Term
  NatTy : Term
  NatTerm : Nat -> Term
  BoolTy : Term
  BoolTerm : Bool -> Term

  VarT : Nat -> Term
  PiT : Term -> Term -> Term
  LambdaT : Term -> Term -> Term
  App : Term -> Term -> Term

  IOTy : Term -> Term
  IOBind : Term -> Term -> Term
  PureIO : Term -> Term
  ThenIO : Term -> Term -> Term
  Syscall : IoPrim -> Term

public export
data Ctx : Nat -> Type where
  Nil : Ctx 0
  (::) : Term -> (ctx : Ctx n) -> Ctx (S n)

shift : (inc : Nat) -> (thres : Nat) -> (t : Term) -> Term
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
shift inc thres (IOTy x) = IOTy (shift inc thres x)
shift inc thres (IOBind m f) = IOBind (shift inc thres m) (shift inc thres f)
shift inc thres (PureIO x) = PureIO (shift inc thres x)
shift inc thres (ThenIO u v) = ThenIO (shift inc thres u) (shift inc thres v)
shift inc thres (Syscall p) = Syscall p

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
subst idx rep (IOTy x) = IOTy (subst idx rep x)
subst idx rep (IOBind m f) = IOBind (subst idx rep m) (subst idx rep f)
subst idx rep (PureIO x) = PureIO (subst idx rep x)
subst idx rep (ThenIO u v) = ThenIO (subst idx rep u) (subst idx rep v)
subst idx rep (Syscall p) = Syscall p

public export
indexTy : (c : Ctx n) -> (Fin n) -> Term 
indexTy [] FZ impossible
indexTy [] (FS x) impossible
indexTy (x :: ctx) FZ = x
indexTy (x :: ctx) (FS y) = indexTy ctx y

public export
data Judge : Ctx n -> Term -> (ty : Term) -> Type where
  SortType : Judge c (SortT l) (SortT (LS l))
  NatType : Judge c NatTy (SortT LZ)
  BoolType : Judge c BoolTy (SortT LZ)
  JNat : Judge c (NatTerm n) NatTy
  JBool : Judge c (BoolTerm b) BoolTy

  JVar : {c : Ctx n} -> (k : Nat) -> (f : Fin n) -> (natToFin k n = Just f) -> Judge c (VarT k) (indexTy c f)
  Weak : {x : Term} -> {xty : Term} -> {yty : Term} -> Judge c x xty -> Judge c y yty -> Judge (yty::c) x xty

  Form : Judge c ty (SortT l) -> Judge (ty::c) tyb (SortT m) -> 
         Judge c (PiT ty tyb) (SortT (maxLevel l m))
  Abst : Judge c (PiT a b) (SortT k) -> Judge (a::c) body bty -> 
         Judge c (LambdaT a body) (PiT a bty)
  Appl : {domty : Term} -> {bty : Term} -> Judge c fn (PiT domty bty) -> Judge c arg domty -> 
         Judge c (App fn arg) (subst 0 arg bty)

  JIoForm : Judge c a (SortT l) -> Judge c (IOTy a) (SortT (maxLevel l (LS LZ)))
  JIoPure : Judge c x a -> Judge c (PureIO x) (IOTy a)
  JIoBind : {a : Term} -> {b : Term} -> Judge c m (IOTy a) -> Judge c f (PiT a (IOTy b)) -> 
            Judge c (IOBind m f) (IOTy b)
  JIoThen : {a : Term} -> {b : Term} -> Judge c u (IOTy a) -> Judge c v (IOTy b) -> 
            Judge c (ThenIO u v) (IOTy b)
  JIOPrim : (prim : IoPrim) -> (ty : Term) -> 
            Judge c (Syscall prim) (IOTy ty)
