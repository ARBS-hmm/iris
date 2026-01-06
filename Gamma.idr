module Gamma
import Data.Vect
import Decidable.Equality

public export
data Level : Type where
  LZ : Level
  LS : Level -> Level

public export
DecEq Level where
  decEq LZ LZ = Yes Refl
  decEq LZ (LS _) = No (\eq => case eq of {})
  decEq (LS _) LZ = No (\eq => case eq of {})
  decEq (LS l1) (LS l2) with (decEq l1 l2)
    decEq (LS l1) (LS l1) | (Yes Refl) = Yes Refl
    decEq (LS l1) (LS l2) | (No contra) = 
      No (\eq => case eq of Refl => contra Refl)

public export
maxLevel : Level -> Level -> Level
maxLevel LZ LZ = LZ 
maxLevel LZ l = l
maxLevel (LS l1) LZ = LS l1
maxLevel (LS l1) (LS l2) = LS (maxLevel l1 l2)

mutual
  public export
  data Ty : Type where
    Uni : Level -> Ty
    NatTy : Ty
    BoolTy : Ty
    Pi : Ty -> Ty -> Ty

  public export
  levelOf : Ty -> Level
  levelOf (Uni l) = LS l
  levelOf NatTy = LZ
  levelOf BoolTy = LZ
  levelOf (Pi x y) = LS (maxLevel (levelOf x) (levelOf y))

public export
Ctx : Nat -> Type
Ctx n = Vect n Ty

public export
data HasType : Ctx n -> Fin n -> Ty -> Type where
  Here : HasType (ty::c) FZ ty
  There: HasType ctx idx ty -> HasType (x::ctx) (FS idx) ty

public export
data Term : (c : Ctx n) -> Ty -> Type where
  UniTerm : (l:Level) -> Term ctx (Uni l)
  Var : {ctx:Ctx n} ->(idx:Fin n) ->  Term ctx (index idx ctx)
  Lambda : forall ctx. (ty : Ty) ->
         (body : (Term (ty :: ctx) retTy)) ->
         (Term ctx (Pi ty retTy))
  App : Term ctx (Pi dom cod) ->
      Term ctx dom -> 
      Term ctx cod

example : Term [NatTy] (Pi NatTy NatTy)
example = Lambda NatTy (Var 0)

example2 : Term [BoolTy] (Pi NatTy BoolTy)
example2 = Lambda NatTy (Var 1)

appl : Term [(Pi NatTy BoolTy),NatTy] BoolTy
appl = App (Var 0) (Var 1)


public export
data TyEq : Ty -> Ty -> Type where
  TyRefl : TyEq ty ty
  PiCong : TyEq a a' -> TyEq b b' -> TyEq (Pi a b) (Pi a' b')
  UniCong : (l = l') -> TyEq (Uni l) (Uni l')

public export
checkConv : (ty1 : Ty) -> (ty2 : Ty) -> Maybe (TyEq ty1 ty2)
checkConv (Uni l) (Uni l') with (decEq l l')
  checkConv (Uni l) (Uni l) | (Yes Refl) = Just (UniCong Refl)
  checkConv (Uni l) (Uni l') | (No _) = Nothing
checkConv NatTy NatTy = Just TyRefl
checkConv BoolTy BoolTy = Just TyRefl
checkConv (Pi a b) (Pi a' b') = do
  eqA <- checkConv a a'
  eqB <- checkConv b b'
  Just (PiCong eqA eqB)
checkConv _ _ = Nothing

public export
check : {actualty : Ty} -> Term ctx actualTy -> (expected : Ty) -> Bool
check {actualty} term expected = case (checkConv actualty expected) of 
                        Just _ => True
                        Nothing => False

