module TestField.Tree

data Ty : Type where
  NatTy : Ty
  BoolTy : Ty
  Sort : Nat -> Ty

data Ctx : Nat -> Type where
  Nil : Ctx 0
  (::) : Ty -> Ctx n -> Ctx (S n)


  
