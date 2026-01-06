module Int
import Gamma
import Data.Vect

mutual
  data Env : Ctx n -> Type where
    Nil : Env []
    Cons : Value ty -> Env ctx -> Env (ty :: ctx)

  data Value : Ty -> Type where
    UniVal : Level -> Value (Uni l)
    NatVal : Nat -> Value NatTy
    BoolVal : Bool -> Value BoolTy
    Closure : (ty : Ty) -> 
              (body : Term (ty :: ctx) retTy) ->
              (env : Env ctx) -> 
              Value (Pi ty retTy)

lookupEnv : Env ctx -> (idx : Fin n) -> Value (index idx ctx)
lookupEnv [] FZ impossible
lookupEnv [] (FS x) impossible
lookupEnv (Cons x y) FZ = x
lookupEnv (Cons x y) (FS z) = lookupEnv y z

eval : Env ctx -> Term ctx ty -> Value ty
eval env (UniTerm l) = UniVal l
eval env (Var idx) = lookupEnv env idx
eval env (Lambda ty body) = Closure ty body env
eval env (App f arg) = 
  let Closure ty body closureEnv = eval env f -- pattern matching syntax
      argVal = eval env arg
      extendedEnv = Cons argVal closureEnv
  in eval extendedEnv body
