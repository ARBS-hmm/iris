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
    NatTerm : Term L0 -- infer 1 less ig ... idk tf
    StringTerm : Term L0
    BoolTerm : Term L0
    NatTy : Term (LS L0)
    StringTy : Term (LS L0)
    BoolTy : Term (LS L0)
    Uni : (l:Level) -> Term l
    (>>) : Term l -> Term m -> Term (maxLevel l m)
    Pi : Telescope -> Term l -> Term (LS l)

  arity : Term l -> Type

  public export
  data Ann : Level -> Type where
    NatAnn : Ann (L0)
    StringAnn : Ann (L0)
    BoolAnn : Ann (L0)
  public export
  data Telescope : Type where
    X : Telescope
    --(::)

level : Term l -> Level
level NatTerm = L0
level StringTerm = L0
level BoolTerm = L0
level NatTy = LS L0
level StringTy = LS L0
level BoolTy = LS L0
level (Uni l) = LS l
level (x >> y) = LS (maxLevel (level x) (level y))

typeof : Term l -> Term (LS l)
typeof NatTerm = NatTy
typeof StringTerm = StringTy 
typeof BoolTerm = BoolTy
typeof NatTy = Uni (LS (LS(L0)))
typeof StringTy = Uni (LS (LS(L0)))
typeof BoolTy = Uni (LS (LS L0))
typeof (Uni l) = Uni (LS l)
typeof (a>>b) = 


