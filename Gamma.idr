module Gamma

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

  data Ty : (level:Level) -> Type where
    Uni : (l:Level) -> Ty l
    NatTy : Ty LZ
    BoolTy : Ty LZ
    Pi : Ty l -> Ty m -> Ty (maxLevel l m)

  data Term : (l : Level) -> (c : Ctx n) -> Ty l-> Type where
    NatVar : forall c . Term LZ c NatTy
    BoolVar : forall c . Term LZ c BoolTy
    Lambda : {c : Ctx n} -> 
             (ty : Ty l) ->
             (body : Term m (c . ty) opty) -> 
             Term (maxLevel l m) c (Pi ty opty)

test : Term LZ CtxNil (Pi NatTy BoolTy)
test = Lambda NatTy BoolVar

