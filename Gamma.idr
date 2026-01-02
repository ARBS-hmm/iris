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
    Var : (idx : Fin n) -> Term c (lookup idx c)
    Lambda : {c : Ctx n} -> 
             (ty : Ty) ->
             (body : Term (c . (MkDec ty)) retTy) -> 
             Term c (Pi ty retTy)
    App : {c : Ctx n} -> {dom : Ty} -> {cod : Ty} ->
          Term c (Pi dom cod) ->
          Term c dom ->
          Term c cod
  public export
  data Ext : Ctx n -> Ctx m -> Type where
    Base : Ext c c
    Undermine : forall decl. Ext c d -> Ext (c . decl) (d . decl)
    Skip : forall decl. Ext c d -> Ext c (d . decl)

export
extIdx : {c : Ctx n} -> {d : Ctx m} -> Ext c d -> Fin n -> Fin m
extIdx Base idx = idx
extIdx (Undermine ext) FZ = FZ
extIdx (Undermine ext) (FS idx) = FS (extIdx ext idx)
extIdx (Skip ext) idx = FS (extIdx ext idx)

test : {c : Ctx n} -> Term c (Pi NatTy NatTy)
test = Lambda NatTy (Var FZ)

nest : {c : Ctx n} -> Term c (Pi NatTy (Pi BoolTy NatTy))
nest = Lambda NatTy 
       (Lambda BoolTy 
         (Var (FS FZ)))

nesti : {c : Ctx n} -> Term c (Pi NatTy (Pi BoolTy BoolTy))
nesti = Lambda NatTy 
        (Lambda BoolTy 
          (Var FZ))

hmm : Term (((CtxNil . (MkDec NatTy)) . (MkDec BoolTy))) (Pi NatTy BoolTy)
hmm = Lambda NatTy (Var (FS FZ))

