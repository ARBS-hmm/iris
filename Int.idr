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

Eq Level where
  (==) LZ LZ = True
  (==) (LS l) (LS m) = (l==m)
  (==) _ _ = False

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

termEq : Term -> Term -> Bool
termEq (SortT l1) (SortT l2) = l1 == l2  -- Assuming Level has Eq
termEq NatTy NatTy = True
termEq (NatTerm n1) (NatTerm n2) = n1 == n2
termEq BoolTy BoolTy = True
termEq (BoolTerm b1) (BoolTerm b2) = b1 == b2
termEq (VarT k1) (VarT k2) = k1 == k2
termEq (PiT a1 b1) (PiT a2 b2) = termEq a1 a2 && termEq b1 b2
termEq (LambdaT a1 b1) (LambdaT a2 b2) = termEq a1 a2 && termEq b1 b2
termEq (App f1 a1) (App f2 a2) = termEq f1 f2 && termEq a1 a2
termEq _ _ = False

typeCheck :{n:Nat} -> (c:Ctx n) -> (t:Term) -> Maybe (ty**(Judge c t ty))
typeCheck c (SortT x) = Just ((SortT (LS x))**(SortType))
typeCheck c NatTy = Just ((SortT LZ)**NatType)
typeCheck c (NatTerm k) = Just (NatTy**JNat)
typeCheck c BoolTy = Just ((SortT LZ)**(BoolType))
typeCheck c (BoolTerm x) = Just (BoolTy**JBool)
typeCheck c (PiT x y) = do 
  ((SortT l)**jx) <- typeCheck c x 
  | _ => Nothing
  ((SortT m)**jy) <- typeCheck (x::c) y
  | _ => Nothing
  pure ((SortT (maxLevel l m))**(Form jx jy))

typeCheck c (LambdaT x y) = assert_total $ do -- #PENDING UNSAFE 
  (yTy**yJudge) <- typeCheck (x::c) y
  (piTy**piJudge) <- typeCheck c (PiT x yTy)
  case piJudge of
    Form domJudge codJudge => 
      Just ((PiT x yTy) ** Abst piJudge yJudge)
    _ => Nothing 

typeCheck c (App f y) = do 
  ((PiT a b)**jf) <- typeCheck c f
  | _ => Nothing
  (yty**jy) <- typeCheck c y
  if (termEq a yty) then 
                let jy' : Judge c y a
                    jy' = believe_me jy
                in Just ((subst 0 y b)** (Appl jf jy'))
              else Nothing

typeCheck {n} c (VarT k) with (natToFin k n)
  typeCheck c (VarT k) | Nothing = Nothing
  typeCheck c (VarT k) | Just x = 
    let pf : (natToFin k n = Just x)
        pf = believe_me (the (x = x) Refl)
    in Just ((indexTy c x) ** (JVar k x pf))

-- ##############################33

emptyCtx : Ctx 0
emptyCtx = []

five : Judge Nil (NatTerm 5) NatTy
five = JNat

identityNat : Term
identityNat = LambdaT NatTy (VarT 0)

piNN : Judge [] (PiT NatTy NatTy) (SortT LZ)
piNN = Form NatType NatType



