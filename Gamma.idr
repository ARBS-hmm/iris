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
maxLevel LZ LZ = LZ 
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
    This : forall c.  Bound (c . x) x
    That : forall c. Bound c x -> Bound (c . new) x

  public export
  data Term : {l : Level} -> (c : Ctx n) -> Ty l-> Type where
    FreeVar : (idx:Fin n) -> Term c (lookup idx c)
    BoundVar :{ty : Ty l} -> Bound c ty -> Term c ty
    Zero : forall c . Term c NatTy
    Suc : forall c . Term c NatTy -> Term c NatTy
    True : forall c . Term c BoolTy
    False : forall c . Term c BoolTy
    Lambda : (c : Ctx n) -> 
             (ty : Ty l)->
             (body : Term (c . ty) opty) -> 
             Term c (Pi ty opty)
    App : forall l, m. {c:Ctx n} -> {dom : Ty l} -> {cod : Ty m} ->
          Term c (Pi dom cod) ->
          Term c dom ->
          Term c cod


test : (c:Ctx n) -> Term c (Pi NatTy NatTy)
test c = Lambda c (NatTy) (
    BoundVar (This)
  )
  
nest : (c:Ctx n) -> Term c (Pi NatTy (Pi BoolTy NatTy))
nest c = Lambda c NatTy 
  (Lambda (c . NatTy) BoolTy 
  (BoundVar (That This)))

nesti : (c:Ctx n) -> Term c (Pi NatTy (Pi BoolTy BoolTy))
nesti c = Lambda c NatTy 
  (Lambda (c . NatTy) BoolTy 
  (BoundVar This))

