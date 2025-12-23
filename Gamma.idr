module Gamma
import Data.Vect

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
    X : Telescope
    (::) : Telescope -> (Literal, (l**Ty l)) -> Telescope

  data Term : Type where 
    NatTerm : Term
    StringTerm : Term
    Var : Fin n -> Term 
    App : Term -> Term -> Term
    NatLit : Nat -> Term
    Lambda : Literal -> Telescope -> Term -> Term

testTel : Telescope
testTel = ((X:: 
             (Lit "x", (LZ**NatTy))) ::
             (Lit "y",(LZ**(Pi (X::(Lit "x", (LZ**NatTy))) NatTy
               ))
           ))

testTerm : Term
testTerm = Lambda (Lit "add") testTel (NatTerm)
--  
