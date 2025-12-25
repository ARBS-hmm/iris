module Gamma
import Data.Vect

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
    Nil : Ctx 0
    (.) : (c:Ctx n) -> (Ty l) -> Ctx (S n)

  data Ty :Level -> Type where
    Uni : (l:Level) -> Ty l
    NatTy : Ty LZ
    BoolTy : Ty LZ

    Pi : (a : Ty l1) -> Ty l2 -> Ty (LS (maxLevel l1 l2))
    (>>) : (a:Ty l1) -> (b:Ty l2) -> Ty (maxLevel l1 l2)
    

  data Term : forall n. (l:Level) -> (c:Ctx n)-> Ty l -> Type where
    NatVar : Term LZ [] NatTy
    BoolVar : Term LZ [] BoolTy
    Lambda : {l : Level} -> (ty : Ty l) -> 
             (body : Term m (c . ty) opty) -> 
             Term (maxLevel l m) c (ty >> opty)
