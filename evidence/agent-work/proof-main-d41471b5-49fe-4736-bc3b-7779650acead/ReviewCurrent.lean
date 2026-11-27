import Mathlib.Algebra.Category.ModuleCat.Ulift
import MackeyDiagrams
import Proofs.Bimodule

set_option maxHeartbeats 2000000

#check Bimodule
#check CategoryTheory.NatTrans.naturality
#check LinearEquiv.ofBijective

def reviewedType : Prop :=
∀ (A : Type u) (B : Type v) [Ring A] [Ring B],
  let Bimod := Sigma (fun M : ModuleCat.{w} B =>
    { D : Bimodule.1 B A M // D.1 = (inferInstance : Module B M) })
  let right := fun (M : Bimod) (m : M.1) (a : A) =>
    letI : Module (MulOpposite A) M.1 := M.2.1.2.1
    MulOpposite.op a • m
  let AMod := ModuleCat.{max u x} A
  let BMod := ModuleCat.{max u w x} B
  let regular := ModuleCat.of A (ULift.{x} A)
  let Balanced := fun (M : Bimod) (X : AMod) (Y : BMod)
      (p : ↥M.1 → X → Y) =>
    (∀ m n : ↥M.1, ∀ a : X, p (m + n) a = p m a + p n a) ∧
    (∀ m : ↥M.1, ∀ a b : X, p m (a + b) = p m a + p m b) ∧
    (∀ b : B, ∀ m : ↥M.1, ∀ a : X, p (b • m) a = b • p m a) ∧
    (∀ a : A, ∀ m : ↥M.1, ∀ y : X, p (right M m a) y = p m (a • y))
  let TensorFunctor := fun M : Bimod =>
    {D : Sigma (fun F : CategoryTheory.Functor AMod BMod =>
          ∀ X : AMod, ↥M.1 → X → F.obj X) //
      (∀ X : AMod, Balanced M X (D.1.obj X) (D.2 X)) ∧
      (∀ (X : AMod) (Y : BMod) (p : ↥M.1 → X → Y),
        Balanced M X Y p →
          ∃! k : LinearMap (RingHom.id B) (D.1.obj X) Y,
            ∀ (m : ↥M.1) (y : X), k (D.2 X m y) = p m y) ∧
      (∀ (X Y : AMod) (h : ModuleCat.Hom X Y) (m : ↥M.1) (y : X),
        (ModuleCat.Hom.hom (D.1.map h)) (D.2 X m y) = D.2 Y m ((ModuleCat.Hom.hom h) y))}
  let Hom := fun (M N : Bimod) =>
    {f : LinearMap (RingHom.id B) M.1 N.1 //
      ∀ (m : ↥M.1) (a : A), f (right M m a) = right N (f m) a}
  let NatCode := Hom
  let Unitor := fun (M : Bimod) (T : TensorFunctor M) =>
    LinearEquiv (RingHom.id B) (T.1.1.obj regular) M.1
  let IsUnitor := fun (M : Bimod) (T : TensorFunctor M) (rho : Unitor M T) =>
    (∀ (m : ↥M.1) (a : A), rho (T.1.2 regular m (ULift.up a)) = right M m a) ∧
    (∀ m : ↥M.1, rho.symm m = T.1.2 regular m (ULift.up (1 : A)))
  let eval := fun (M N : Bimod) (T : TensorFunctor M) (S : TensorFunctor N)
      (rho : Unitor M T) (sigma : Unitor N S) (eta : CategoryTheory.NatTrans T.1.1 S.1.1) =>
    LinearMap.comp sigma.toLinearMap
      (LinearMap.comp (ModuleCat.Hom.hom (eta.app regular)) rho.symm.toLinearMap)
  let Represents := fun (M N : Bimod) (T : TensorFunctor M) (S : TensorFunctor N)
      (rho : Unitor M T) (sigma : Unitor N S)
      (eta : CategoryTheory.NatTrans T.1.1 S.1.1) (f : NatCode M N) =>
    f.1 = eval M N T S rho sigma eta ∧
    (∀ m : ↥M.1, f.1 m =
      sigma ((ModuleCat.Hom.hom (eta.app regular)) (T.1.2 regular m (ULift.up (1 : A))))) ∧
    (∀ (X : AMod) (m : ↥M.1) (y : X),
      (ModuleCat.Hom.hom (eta.app X)) (T.1.2 X m y) = S.1.2 X (f.1 m) y)
  let InverseAssignments := fun (M N : Bimod) (T : TensorFunctor M) (S : TensorFunctor N)
      (rho : Unitor M T) (sigma : Unitor N S) =>
    (∀ eta : CategoryTheory.NatTrans T.1.1 S.1.1, ∃! f : NatCode M N, Represents M N T S rho sigma eta f) ∧
    (∀ f : NatCode M N, ∃! eta : CategoryTheory.NatTrans T.1.1 S.1.1, Represents M N T S rho sigma eta f)
  ∀ (M N P : Bimod) (T : TensorFunctor M) (S : TensorFunctor N) (U : TensorFunctor P),
    ∃ (rho : Unitor M T) (sigma : Unitor N S) (tau : Unitor P U),
      IsUnitor M T rho ∧ IsUnitor N S sigma ∧ IsUnitor P U tau ∧
      InverseAssignments M N T S rho sigma ∧
      InverseAssignments N P S U sigma tau ∧
      InverseAssignments M P T U rho tau ∧
      (∀ eta theta : CategoryTheory.NatTrans T.1.1 S.1.1,
        ∃ sum : CategoryTheory.NatTrans T.1.1 S.1.1,
          (∀ X : AMod, ModuleCat.Hom.hom (sum.app X) =
            ModuleCat.Hom.hom (eta.app X) + ModuleCat.Hom.hom (theta.app X)) ∧
          eval M N T S rho sigma sum =
            eval M N T S rho sigma eta + eval M N T S rho sigma theta) ∧
      (∃ identity : CategoryTheory.NatTrans T.1.1 T.1.1,
        (∀ X : AMod, ModuleCat.Hom.hom (identity.app X) = LinearMap.id) ∧
        eval M M T T rho rho identity = LinearMap.id) ∧
      (∀ (eta : CategoryTheory.NatTrans T.1.1 S.1.1) (theta : CategoryTheory.NatTrans S.1.1 U.1.1),
        ∃ composite : CategoryTheory.NatTrans T.1.1 U.1.1,
          (∀ X : AMod, ModuleCat.Hom.hom (composite.app X) =
            LinearMap.comp (ModuleCat.Hom.hom (theta.app X)) (ModuleCat.Hom.hom (eta.app X))) ∧
          eval M P T U rho tau composite =
            LinearMap.comp (eval N P S U sigma tau theta) (eval M N T S rho sigma eta))

#print axioms reviewedType
