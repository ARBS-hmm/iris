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

  data Telescope : Type where
  arity : Term l -> type

level : Term l -> Level
level Natterm = L0
level Stringterm = L0
level Boolterm = L0
level Natty = LS L0
level Stringty = LS L0
level Boolty = LS L0
level (Uni l) = LS l
level (x >> y) = LS (maxLevel (level x) (level y))
level (Pi a b) = ?hmm

typeof : Term l -> Term (LS l)

--  
