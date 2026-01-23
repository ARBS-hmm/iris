module Int
import Data.Vect
%default total

data Level : Type where
  LZ : Level
  LS : Level -> Level

maxLevel : Level -> Level -> Level
maxLevel LZ LZ = LZ
maxLevel LZ (LS x) = LS x
maxLevel (LS x) LZ = LS x
maxLevel (LS x) (LS y) = maxLevel x y
mutual
  data Ctx : Nat -> Type where
    Nil : Ctx 0
    (::) : Term n -> (ctx : Ctx n) -> Ctx (S n)

  data Term : (n : Nat) -> Type where  -- Term now knows its context size
    SortT : Level -> Term n
    NatTy : Term n
    NatTerm : Nat -> Term n
    BoolTy : Term n
    BoolTerm : Bool -> Term n
    VarT : Fin n -> Term n  -- Now n is bound!
    PiT : Term n -> Term (S n) -> Term n
    LambdaT : Term n -> Term (S n) -> Term n
    App : Term n -> Term n -> Term n

  -- #Pending
  subst : (tosub:Term k) -> (prev:Term (S k)) -> Term k
  subst tosub (VarT FZ) = tosub
  subst tosub (VarT (FS x)) = VarT x
  subst tosub (SortT x) = SortT x
  subst tosub NatTy = NatTy
  subst tosub (NatTerm j) = NatTerm j
  subst tosub BoolTy = BoolTy
  subst tosub (BoolTerm x) = BoolTerm x
  subst tosub (PiT x y) = PiT (subst tosub x) (subst (weakenTerm tosub) y)
  subst tosub (LambdaT x y) = LambdaT (subst tosub x) (subst (weakenTerm tosub) y)
  subst tosub (App x y) = App (subst tosub x) (subst tosub y)

  data Judge : Ctx n -> Term n -> (ty : Term n) -> Type where
    SortType : Judge c (SortT l) (SortT (LS l))
    NatType : Judge c NatTy (SortT LZ)
    BoolType : Judge c BoolTy (SortT LZ)
    JNat : Judge c (NatTerm n) NatTy
    JBool : Judge c (BoolTerm b) BoolTy
    JVar : (idx : Fin n) -> Judge c (VarT idx) (indexTy c idx)
    Weak : (term : Judge c x xty) -> (wellTyped : Judge c y yty) -> Judge (yty::c) (weakenTerm x) (weakenTerm xty)

    Form : Judge c ty (SortT l) -> Judge (ty::c) (tyb) (SortT m) ->
           Judge c (PiT ty tyb) (SortT (maxLevel l m))

    Abst : (piExists : Judge c (PiT a b) (SortT k)) ->
           (Judge (a::c) body (b)) -> 
           Judge c (LambdaT a body) (PiT a b)

    Appl : (f : Judge c term (PiT domty codty)) -> 
           (t : Judge c dom domty) -> 
           Judge c (App term dom) (subst dom codty)

  weakenTerm : Term n -> Term (S n)
  weakenTerm (VarT idx) = VarT (FS idx)
  weakenTerm (SortT l) = SortT l
  weakenTerm NatTy = NatTy
  weakenTerm (NatTerm k) = NatTerm k
  weakenTerm BoolTy = BoolTy
  weakenTerm (BoolTerm b) = BoolTerm b
  weakenTerm (PiT a b) = PiT (weakenTerm a) (weakenTerm b)
  weakenTerm (LambdaT a b) = LambdaT (weakenTerm a) (weakenTerm b)
  weakenTerm (App f a) = App (weakenTerm f) (weakenTerm a)

  indexTy : (c : Ctx n) -> Fin n -> Term n 
  indexTy [] FZ impossible
  indexTy [] (FS x) impossible
  indexTy (x :: ctx) FZ = weakenTerm x
  indexTy (x :: ctx) (FS y) = weakenTerm (indexTy ctx y)

emptyCtx : Ctx 0
emptyCtx = []

five : Judge Nil (NatTerm 5) NatTy
five = JNat

innerPi : Judge (NatTy::[]) (PiT NatTy NatTy) (SortT LZ)
innerPi = Form NatType (Weak NatType (JVar 0))

innerLambda : Judge (NatTy::[]) (LambdaT NatTy (VarT 1)) (PiT NatTy NatTy)
innerLambda = Abst innerPi bodyProof where
      bodyProof : Judge (NatTy::NatTy::[]) (VarT 1) (weakenTerm NatTy)
      bodyProof = JVar 1

func : Judge [] (LambdaT NatTy (LambdaT NatTy (VarT 1))) (PiT NatTy (PiT NatTy NatTy))
func = Abst outerPi innerLambda where
      outerPi : Judge [] (PiT NatTy (PiT NatTy NatTy)) (SortT LZ)
      outerPi = Form NatType innerPi  -- innerPi is the proof of PiT NatTy NatTy in context (NatTy::[])

idk : Judge [] (LambdaT NatTy (VarT 0)) (PiT NatTy NatTy)
idk = Abst piNatNat (JVar 0)  -- Not Weak!
  where
    piNatNat : Judge [] (PiT NatTy NatTy) (SortT LZ)
    piNatNat = Form NatType NatType

testPiSubst : Term 0
testPiSubst = subst (NatTerm 42) (PiT NatTy (VarT FZ))

constFunc : Term 0
constFunc = LambdaT NatTy (LambdaT NatTy (VarT (FS FZ)))  -- λx:Nat. λy:Nat. x

test1 : Term 0
test1 = subst (NatTerm 5) (PiT NatTy (VarT FZ))

test2 : Term 0
test2 = subst (NatTerm 10) (PiT NatTy (PiT (VarT FZ) (VarT (FS FZ))))

test3 : Term 0
test3 = subst (NatTerm 7) (LambdaT NatTy (PiT (VarT FZ) NatTy))

test4 : Term 0
test4 = subst (LambdaT NatTy (VarT FZ))  -- λx. x
            (PiT NatTy (App (VarT FZ) (NatTerm 3)))

test:Term 1
test = LambdaT (PiT NatTy (VarT 1)) (VarT 0)
