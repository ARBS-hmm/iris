module Gamma
import Data.Vect

public export
data Level : Type where
  LZ : Level
  LS : Level -> Level

public export
Literal : Type
Literal = String

mutual 
  public export
  data Ty : Level -> Type where
    TypeVar : Fin n -> (l:Level) -> Ty l
    Uni : (l:Level) -> Ty (LS l)
    NatTy : Ty LZ
    StringTy : Ty LZ
    (>>) : Ty l -> Ty l -> Ty (LS l)
    Pi : (Term l,Ty (LS l)) -> Ty l -> Ty l'
    Sigma : Telescope -> Ty l -> Ty l'

  public export
  data Telescope : Type where
    X : Telescope
    (::) : Telescope -> (Literal, (l**Ty l)) -> Telescope

  public export
  data Term : Level ->  Type where 
    NatTerm : Term LZ
    StringTerm : Term LZ
    NewTerm : Literal -> (l:Level) -> Term l
    Var : Fin n -> (l:Level) -> Term l
    App : forall l,m,n. Term l -> Term m -> Term n
    Lambda : Literal -> Term m -> Term (LS m)-> Term (LS m)

--  
