module Gamma

data Level : Type where
  LZ : Level
  LS : Level -> Level

data Literal : Type where
  Lit : String -> Literal

mutual 
  data Ty : Level -> Type where
    Uni : (l:Level) -> Ty (LS l)
    NatTy : Ty LZ
    StringTy : Ty LZ
    Pi : Telescope -> Ty l -> Ty l'
    Sigma : Telescope -> Ty l -> Ty l'

  data Telescope : Type where
    Empty : Telescope
    (::) : Telescope -> (Literal, (l**Ty l)) -> Telescope

  data Term : Type where 
    NatTerm : Term
    StringTerm : Term
    Lambda : Literal -> Term -> Term

testTel : Telescope
testTel = ((Empty :: 
             (Lit "x", (LZ**NatTy))) ::
             (Lit "y",(LZ**
               (Pi (Empty::
                (Lit "x", (LZ**NatTy))) NatTy
               ))))

testTerm : Term
testTerm = Lambda (Lit "add") (NatTerm)
--  
