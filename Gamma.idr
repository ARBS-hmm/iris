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
  record Declaration where
    constructor MkDec
    type : Ty

  public export
  data Ctx : Nat -> Type where
    CtxNil : Ctx 0
    (.): (c : Ctx n) -> Declaration -> Ctx (S n)

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
  lookup : Fin n -> Ctx n -> Ty
  lookup FZ CtxNil impossible
  lookup (FS x) CtxNil impossible
  lookup FZ (c . (MkDec type)) = type
  lookup (FS y) (c . dec) = lookup y c

  public export
  data Term : (c : Ctx n) -> Ty -> Type where
    Var : {c : Ctx n} -> (idx : Fin n) -> Term c (lookup idx c)
    Lambda : {c : Ctx n} -> 
             (ty : Ty) ->
             (body : Term (c . (MkDec ty)) retTy) -> 
             Term c (Pi ty retTy)
    App : {c : Ctx n} -> {dom : Ty} -> {cod : Ty} ->
          Term c (Pi dom cod) ->
          Term c dom ->
          Term c cod

--
