module Int
import Gamma
import Data.Vect

Show Level where
  show LZ = "0"
  show (LS l) = ("S("++ show l ++ ")")

Show Ty where
  show (Uni x) = "Uni "++(show x)
  show NatTy = "Nat"
  show BoolTy = "Boool"
  show (Pi x y) = (show x) ++ ">>" ++ (show y)

Show (Ctx n) where
  show ctx = show (toList ctx)

Show (Term c ty) where
  show (NatLit k) = show k
  show (BoolLit b) = show b
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Mult x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (x && y) = "(" ++ show x ++ " && " ++ show y ++ ")"
  show (x || y) = "(" ++ show x ++ " || " ++ show y ++ ")"
  show (If cond t e) = "if " ++ show cond ++ " then " ++ show t ++ " else " ++ show e
  show (UniTerm l) = "U" ++ show l
  show (Var idx) = "x" ++ show (finToNat idx)
  show (Lambda ty body) = "λ" ++ show ty ++ ". " ++ show body
  show (App f arg) = "(" ++ show f ++ " " ++ show arg ++ ")"

mutual
  public export
  data Env : Ctx n -> Type where
    Nil : Env []
    Cons : Value ty -> Env ctx -> Env (ty :: ctx)

  public export
  data Value : Ty -> Type where
    UniVal : Level -> Value (Uni l)
    NatVal : Nat -> Value NatTy
    BoolVal : Bool -> Value BoolTy
    Closure : (ty : Ty) -> 
              (body : Term (ty :: ctx) retTy) ->
              (env : Env ctx) -> 
              Value (Pi ty retTy)


Show (Value ty) where
  show (UniVal x) = "Uni " ++ show(x)
  show (NatVal k) = show k
  show (BoolVal x) = show x
  show (Closure x body env) = "lambda " ++ show(x) ++ "." ++ show(body) 

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
  let Closure ty body closureEnv = eval env f
      argVal = eval env arg
      extendedEnv = Cons argVal closureEnv
  in eval extendedEnv body

eval env (NatLit n) = NatVal n
eval env (BoolLit b) = BoolVal b
eval env (Add x y) = 
  let NatVal nx = eval env x
      NatVal ny = eval env y
  in NatVal (nx + ny)
eval env (Mult x y) = 
  let NatVal nx = eval env x
      NatVal ny = eval env y
  in NatVal (nx * ny)
eval env ((&&) x y) = 
  let BoolVal bx = eval env x
      BoolVal by = eval env y
  in BoolVal (bx && by)
eval env ((||) x y) = 
  let BoolVal bx = eval env x
      BoolVal by = eval env y
  in BoolVal (bx || by)
eval env (If cond thenBranch elseBranch) = 
  case eval env cond of
    BoolVal True => eval env thenBranch
    BoolVal False => eval env elseBranch

run : Term [] ty -> Value ty
run term = eval Nil term

runShow : Term [] ty -> String
runShow term = show (run term)

example : Term [NatTy] (Pi NatTy NatTy)
example = Lambda NatTy (Var 0)

func : Term [NatTy] (Pi NatTy NatTy)
func = Lambda NatTy (Add (Var 0) (Var 1))

fromTerm : Term ctx ty -> Env ctx
fromTerm t = ?h

main : IO ()
main = do
  let program = App func (NatLit 1)
  let env = Cons (NatVal 3) Nil
  let result = eval env program
  putStrLn $ "Result: " ++ show result
