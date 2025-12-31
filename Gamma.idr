module Gamma
import Data.Fin

public export
data Level : Type where
  LZ : Level
  LS : Level -> Level

public export
Literal : Type
Literal = String

maxLevel : Level -> Level -> Level
maxLevel LZ l = l
maxLevel (LS l1) LZ = LS l1
maxLevel (LS l1) (LS l2) = LS (maxLevel l1 l2)

mutual
  public export
  data Ctx : Nat -> Type where
    CtxNil : Ctx 0
    (.): forall l. (c : Ctx n) -> Ty l-> Ctx (S n)

  public export
  data Ty : (level:Level) -> Type where
    Uni : (l:Level) -> Ty (LS l)
    NatTy : Ty LZ
    BoolTy : Ty LZ
    Pi : Ty l -> Ty m -> Ty (maxLevel l m)

  levelOf : Ty l -> Level 
  lookup : Fin n -> Ctx n -> Ty l

  data Bound : Ctx n -> Ty l -> Type where
    This : Bound (c . x) x
    That : Bound c x -> Bound (c . new) x

  public export
  data Term : (l : Level) -> (c : Ctx n) -> Ty l-> Type where
    FreeVar : (idx:Fin n) -> Term (levelOf (lookup idx c)) c (lookup idx c)
    BoundVar :{ty : Ty l} -> Bound c ty -> Term l c ty
    Zero : forall c . Term LZ c NatTy
    Suc : forall c . Term LZ c NatTy -> Term LZ c NatTy
    True : forall c . Term LZ c BoolTy
    False : forall c . Term LZ c BoolTy
    Lambda : {c : Ctx n} -> 
             (ty : Ty l)->
             (body : Term m (c . ty) opty) -> 
             Term (maxLevel l m) c (Pi ty opty)

test : Term LZ CtxNil (Pi NatTy BoolTy)
test = Lambda (NatTy) True

nest : Term LZ CtxNil (Pi (Pi NatTy BoolTy) BoolTy)
nest = Lambda (Pi NatTy BoolTy) True

