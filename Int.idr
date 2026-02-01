module Int
import Term
import Data.Fin
import Decidable.Equality
%default total

termEq : Term -> Term -> Bool
termEq (SortT l1) (SortT l2) = l1 == l2  -- Assuming Level has Eq
termEq NatTy NatTy = True
termEq (NatTerm n1) (NatTerm n2) = n1 == n2
termEq BoolTy BoolTy = True
termEq (BoolTerm b1) (BoolTerm b2) = b1 == b2
termEq (VarT k1) (VarT k2) = k1 == k2
termEq (PiT a1 b1) (PiT a2 b2) = termEq a1 a2 && termEq b1 b2
termEq (LambdaT a1 b1) (LambdaT a2 b2) = termEq a1 a2 && termEq b1 b2
termEq (App f1 a1) (App f2 a2) = termEq f1 f2 && termEq a1 a2
termEq _ _ = False

typeCheck :{n:Nat} -> (c:Ctx n) -> (t:Term) -> Maybe (ty**(Judge c t ty))
typeCheck c (SortT x) = Just ((SortT (LS x))**(SortType))
typeCheck c NatTy = Just ((SortT LZ)**NatType)
typeCheck c (NatTerm k) = Just (NatTy**JNat)
typeCheck c BoolTy = Just ((SortT LZ)**(BoolType))
typeCheck c (BoolTerm x) = Just (BoolTy**JBool)
typeCheck c (PiT x y) = do 
  ((SortT l)**jx) <- typeCheck c x 
  | _ => Nothing
  ((SortT m)**jy) <- typeCheck (x::c) y
  | _ => Nothing
  pure ((SortT (maxLevel l m))**(Form jx jy))

typeCheck c (LambdaT x y) = assert_total $ do -- #PENDING UNSAFE 
  (yTy**yJudge) <- typeCheck (x::c) y
  (piTy**piJudge) <- typeCheck c (PiT x yTy)
  case piJudge of
    Form domJudge codJudge => 
      Just ((PiT x yTy) ** Abst piJudge yJudge)
    _ => Nothing 

typeCheck c (App f y) = do 
  ((PiT a b)**jf) <- typeCheck c f
    | _ => Nothing
  (yty**jy) <- typeCheck c y
  
  -- Use decidable equality
  case decEq a yty of
       Yes Refl => 
         -- jy has type Judge c y yty, but we need Judge c y a
         -- Since we have Refl : a = yty, we can transport
         let jy' = replace {p = \ty => Judge c y ty} (sym Refl) jy
         in Just ((subst 0 y b)** (Appl jf jy'))
       No _ => Nothing

typeCheck {n} c (VarT k) with (natToFin k n)
  typeCheck c (VarT k) | Nothing = Nothing
  typeCheck c (VarT k) | Just x = 
    let pf : (natToFin k n = Just x)
        pf = believe_me (the (x = x) Refl)
    in Just ((indexTy c x) ** (JVar k x pf))

-- ##############################33

emptyCtx : Ctx 0
emptyCtx = []

five : Judge Nil (NatTerm 5) NatTy
five = JNat

identityNat : Term
identityNat = LambdaT NatTy (VarT 0)

piNN : Judge [] (PiT NatTy NatTy) (SortT LZ)
piNN = Form NatType NatType



