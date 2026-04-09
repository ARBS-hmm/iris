import Term
import Decidable.Equality

public export
DecEq Term where
  decEq (SortT l1) (SortT l2) with (decEq l1 l2)
    decEq (SortT l) (SortT l) | Yes Refl = Yes Refl
    decEq (SortT l1) (SortT l2) | No contra = No (\Refl => contra Refl)
  
  decEq NatTy NatTy = Yes Refl
  
  decEq (NatTerm n1) (NatTerm n2) with (decEq n1 n2)
    decEq (NatTerm n) (NatTerm n) | Yes Refl = Yes Refl
    decEq (NatTerm n1) (NatTerm n2) | No contra = No (\Refl => contra Refl)
  
  decEq BoolTy BoolTy = Yes Refl
  
  decEq (BoolTerm b1) (BoolTerm b2) with (decEq b1 b2)
    decEq (BoolTerm b) (BoolTerm b) | Yes Refl = Yes Refl
    decEq (BoolTerm b1) (BoolTerm b2) | No contra = No (\Refl => contra Refl)
  
  decEq (VarT k1) (VarT k2) with (decEq k1 k2)
    decEq (VarT k) (VarT k) | Yes Refl = Yes Refl
    decEq (VarT k1) (VarT k2) | No contra = No (\Refl => contra Refl)
  
  decEq (PiT a1 b1) (PiT a2 b2) with (decEq a1 a2)
    decEq (PiT a b1) (PiT a b2) | Yes Refl with (decEq b1 b2)
      decEq (PiT a b) (PiT a b) | Yes Refl | Yes Refl = Yes Refl
      decEq (PiT a b1) (PiT a b2) | Yes Refl | No contra = No (\Refl => contra Refl)
    decEq (PiT a1 b1) (PiT a2 b2) | No contra = No (\Refl => contra Refl)
  
  decEq (LambdaT a1 b1) (LambdaT a2 b2) with (decEq a1 a2)
    decEq (LambdaT a b1) (LambdaT a b2) | Yes Refl with (decEq b1 b2)
      decEq (LambdaT a b) (LambdaT a b) | Yes Refl | Yes Refl = Yes Refl
      decEq (LambdaT a b1) (LambdaT a b2) | Yes Refl | No contra = No (\Refl => contra Refl)
    decEq (LambdaT a1 b1) (LambdaT a2 b2) | No contra = No (\Refl => contra Refl)
  
  decEq (App f1 a1) (App f2 a2) with (decEq f1 f2)
    decEq (App f a1) (App f a2) | Yes Refl with (decEq a1 a2)
      decEq (App f a) (App f a) | Yes Refl | Yes Refl = Yes Refl
      decEq (App f a1) (App f a2) | Yes Refl | No contra = No (\Refl => contra Refl)
    decEq (App f1 a1) (App f2 a2) | No contra = No (\Refl => contra Refl)
  
  decEq (SortT _) NatTy = No $ \Refl impossible
  decEq (SortT _) (NatTerm _) = No $ \Refl impossible
  decEq (SortT _) BoolTy = No $ \Refl impossible
  decEq (SortT _) (BoolTerm _) = No $ \Refl impossible
  decEq (SortT _) (VarT _) = No $ \Refl impossible
  decEq (SortT _) (PiT _ _) = No $ \Refl impossible
  decEq (SortT _) (LambdaT _ _) = No $ \Refl impossible
  decEq (SortT _) (App _ _) = No $ \Refl impossible
  
  decEq NatTy (SortT _) = No $ \Refl impossible
  decEq NatTy (NatTerm _) = No $ \Refl impossible
  decEq NatTy BoolTy = No $ \Refl impossible
  decEq NatTy (BoolTerm _) = No $ \Refl impossible
  decEq NatTy (VarT _) = No $ \Refl impossible
  decEq NatTy (PiT _ _) = No $ \Refl impossible
  decEq NatTy (LambdaT _ _) = No $ \Refl impossible
  decEq NatTy (App _ _) = No $ \Refl impossible
  
  decEq (NatTerm _) (SortT _) = No $ \Refl impossible
  decEq (NatTerm _) NatTy = No $ \Refl impossible
  decEq (NatTerm _) BoolTy = No $ \Refl impossible
  decEq (NatTerm _) (BoolTerm _) = No $ \Refl impossible
  decEq (NatTerm _) (VarT _) = No $ \Refl impossible
  decEq (NatTerm _) (PiT _ _) = No $ \Refl impossible
  decEq (NatTerm _) (LambdaT _ _) = No $ \Refl impossible
  decEq (NatTerm _) (App _ _) = No $ \Refl impossible
  
  decEq BoolTy (SortT _) = No $ \Refl impossible
  decEq BoolTy (NatTerm _) = No $ \Refl impossible
  decEq BoolTy (BoolTerm _) = No $ \Refl impossible
  decEq BoolTy (VarT _) = No $ \Refl impossible
  decEq BoolTy (PiT _ _) = No $ \Refl impossible
  decEq BoolTy (LambdaT _ _) = No $ \Refl impossible
  decEq BoolTy (App _ _) = No $ \Refl impossible
  decEq BoolTy NatTy = No $ \Refl impossible
  
  decEq (BoolTerm _) (SortT _) = No $ \Refl impossible
  decEq (BoolTerm _) NatTy = No $ \Refl impossible
  decEq (BoolTerm _) BoolTy = No $ \Refl impossible
  decEq (BoolTerm _) (NatTerm _) = No $ \Refl impossible
  decEq (BoolTerm _) (VarT _) = No $ \Refl impossible
  decEq (BoolTerm _) (PiT _ _) = No $ \Refl impossible
  decEq (BoolTerm _) (LambdaT _ _) = No $ \Refl impossible
  decEq (BoolTerm _) (App _ _) = No $ \Refl impossible
  
  decEq (VarT _) (SortT _) = No $ \Refl impossible
  decEq (VarT _) NatTy = No $ \Refl impossible
  decEq (VarT _) (NatTerm _) = No $ \Refl impossible
  decEq (VarT _) BoolTy = No $ \Refl impossible
  decEq (VarT _) (BoolTerm _) = No $ \Refl impossible
  decEq (VarT _) (PiT _ _) = No $ \Refl impossible
  decEq (VarT _) (LambdaT _ _) = No $ \Refl impossible
  decEq (VarT _) (App _ _) = No $ \Refl impossible
  
  decEq (PiT _ _) (SortT _) = No $ \Refl impossible
  decEq (PiT _ _) NatTy = No $ \Refl impossible
  decEq (PiT _ _) (NatTerm _) = No $ \Refl impossible
  decEq (PiT _ _) BoolTy = No $ \Refl impossible
  decEq (PiT _ _) (BoolTerm _) = No $ \Refl impossible
  decEq (PiT _ _) (VarT _) = No $ \Refl impossible
  decEq (PiT _ _) (LambdaT _ _) = No $ \Refl impossible
  decEq (PiT _ _) (App _ _) = No $ \Refl impossible
  
  decEq (LambdaT _ _) (SortT _) = No $ \Refl impossible
  decEq (LambdaT _ _) NatTy = No $ \Refl impossible
  decEq (LambdaT _ _) (NatTerm _) = No $ \Refl impossible
  decEq (LambdaT _ _) BoolTy = No $ \Refl impossible
  decEq (LambdaT _ _) (BoolTerm _) = No $ \Refl impossible
  decEq (LambdaT _ _) (VarT _) = No $ \Refl impossible
  decEq (LambdaT _ _) (App _ _) = No $ \Refl impossible
  decEq (LambdaT _ _) (PiT _ _) = No $ \Refl impossible
  
  decEq (App _ _) (SortT _) = No $ \Refl impossible
  decEq (App _ _) NatTy = No $ \Refl impossible
  decEq (App _ _) (NatTerm _) = No $ \Refl impossible
  decEq (App _ _) BoolTy = No $ \Refl impossible
  decEq (App _ _) (BoolTerm _) = No $ \Refl impossible
  decEq (App _ _) (VarT _) = No $ \Refl impossible
  decEq (App _ _) (PiT _ _) = No $ \Refl impossible
  decEq (App _ _) (LambdaT _ _) = No $ \Refl impossible

