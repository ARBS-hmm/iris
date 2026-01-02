module Tests
import Gamma
import Data.Fin

test : {c : Ctx n} -> Term c (Pi NatTy NatTy)
test = Lambda NatTy (Var FZ)

nest : {c : Ctx n} -> Term c (Pi NatTy (Pi BoolTy NatTy))
nest = Lambda NatTy 
       (Lambda BoolTy 
         (Var (FS FZ)))

nesti : {c : Ctx n} -> Term c (Pi NatTy (Pi BoolTy BoolTy))
nesti = Lambda NatTy 
        (Lambda BoolTy 
          (Var FZ))

hmm : Term (((CtxNil . (MkDec NatTy)) . (MkDec BoolTy))) (Pi NatTy BoolTy)
hmm = Lambda NatTy (Var (FS FZ))




