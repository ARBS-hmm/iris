module Gamma
import Data.Vect

public export
data Level : Type where
  L0 : Level
  LS : Level -> Level

public export
Literal : Type
Literal = String

maxLevel : Level -> Level -> Level
maxLevel L0 l = l
maxLevel (LS l1) L0 = LS l1
maxLevel (LS l1) (LS l2) = LS (maxLevel l1 l2)


mutual 
  public export
  data Ctx : Nat -> Type where
    Nil : Ctx 0
    (.) : (c:Ctx n) -> (Term c l) -> Ctx (S n)
    
  lengthctx : Ctx n -> Nat
  data Term : Ctx n -> Level -> Type where 
    NatTy : Term [] (LS L0)
    BoolTy : Term [] (LS L0)
    Uni : (l:Level) -> Term [] l

    Var : (i:Fin n) -> Term c (getlevel c i)
    Lambda : Term c l -> Term c l -> Term c (maxLevel l m)
    Pi : Term c l -> Term c m -> Term c (maxLevel l m) 
    Sigma : Term c l -> Term c m -> Term c (maxLevel l m)
    App : (K:Nat) -> (t:Term c (LS l)) -> Vect k (Fin (lengthctx c)) -> Term c l 

    (>>) : Term c l -> Term c m -> Term c (maxLevel l m)

  levelof : Term c l -> Level
  levelof = ?h


  getlevel : Ctx n -> Fin n -> Level
  getlevel (c . x) FZ = levelof x
  getlevel (c . x) (FS i) = getlevel c i
--

data Telescope : Ctx n -> Type where
  TNil : Telescope c
  (::) : (tel : Telescope c) ->
         (ty : Term c l) ->
         Telescope (c . ty) 

record Cons (c:Ctx n) (l : Level) where
  constructor MkCons
  name : String





