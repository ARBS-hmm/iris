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
    (.) : (c:Ctx n) -> (Ty l c) -> Ctx (S n)

  data Ty : forall n. Level -> Ctx n -> Type where
    Uni : (l:Level) -> Ty l c
    NatTy : Ty LZ CtxNil
    BoolTy : Ty LZ CtxNil
    Pi : (a:Ty l1 c) -> (b:Ty l2 (c . a)) -> Ty (maxLevel l1 l2) c
    

  data Term : forall n. (l:Level) -> (c:Ctx n)-> Ty l c -> Type where
    NatVar : Term LZ CtxNil NatTy
    BoolVar : Term LZ CtxNil BoolTy
    Lambda : forall n. {c:Ctx n} -> {l : Level} -> (ty : Ty l c) -> 
             (opty : Ty m (c . ty)) ->
             (body : Term m (c . ty) opty) -> 
             Term (maxLevel l m) c (Pi ty opty)












