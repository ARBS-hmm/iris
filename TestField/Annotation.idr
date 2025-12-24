module TestField.Annotation
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
  data Term : Level ->  Type where 
    Natterm : Term l0 -- infer 1 less ig ... idk tf
    Stringterm : Term l0
    Boolterm : Term l0
    Natty : Term (LS l0)
    Stringty : Term (LS l0)
    Boolty : Term (LS L0)
    Uni : (l:Level) -> Term l
    (>>) : Term l -> Term m -> Term (maxLevel l m)
    Pi : Telescope -> Term l -> Term (LS l)
    Appl : (n:Nat) -> (t : Term (LS l)) -> 
                  arity t (Fin n) -> Term l  

  data Telescope : Type where

  arity : Term l -> type

level : Term l -> Level
typeof : Term l -> Term (LS l)

