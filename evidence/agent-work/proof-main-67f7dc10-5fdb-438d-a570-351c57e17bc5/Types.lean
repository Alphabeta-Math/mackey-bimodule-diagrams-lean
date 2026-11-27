import Mathlib.Algebra.Category.ModuleCat.Ulift
import MackeyDiagrams
import Proofs.Bimodule

set_option maxHeartbeats 2000000
namespace NaturalTransformationsOfTensorFunctorsProof

universe u v w x
variable {A : Type u} {B : Type v} [Ring A] [Ring B]

private abbrev Bimod (A : Type u) (B : Type v) [Ring A] [Ring B] :=
  Sigma (fun M : ModuleCat.{w} B =>
    { D : Bimodule.1 B A M // D.1 = (inferInstance : Module B M) })

private abbrev AMod (A : Type u) [Ring A] := ModuleCat.{max u x} A
private abbrev BMod (A : Type u) (B : Type v) := ModuleCat.{max u w x} B

private abbrev regular (A : Type u) [Ring A] : AMod.{u,x} A :=
  ModuleCat.of A (ULift.{x} A)

private def right (M : Bimod.{u,v,w} A B) (m : M.1) (a : A) : M.1 :=
  letI : Module (MulOpposite A) M.1 := M.2.1.2.1
  MulOpposite.op a • m

private def Balanced (M : Bimod.{u,v,w} A B) (X : AMod.{u,x} A)
    (Y : BMod.{u,v,w,x} A B) (p : ↥M.1 → X → Y) : Prop :=
  (∀ m n : ↥M.1, ∀ a : X, p (m + n) a = p m a + p n a) ∧
  (∀ m : ↥M.1, ∀ a b : X, p m (a + b) = p m a + p m b) ∧
  (∀ b : B, ∀ m : ↥M.1, ∀ a : X, p (b • m) a = b • p m a) ∧
  (∀ a : A, ∀ m : ↥M.1, ∀ y : X, p (right M m a) y = p m (a • y))

private abbrev TensorFunctor (M : Bimod.{u,v,w} A B) :=
  { D : Sigma (fun F : CategoryTheory.Functor (AMod.{u,x} A) (BMod.{u,v,w,x} A B) =>
      ∀ X : AMod.{u,x} A, ↥M.1 → X → F.obj X) //
    (∀ X : AMod.{u,x} A, Balanced M X (D.1.obj X) (D.2 X)) ∧
    (∀ (X : AMod.{u,x} A) (Y : BMod.{u,v,w,x} A B) (p : ↥M.1 → X → Y),
      Balanced M X Y p →
      ∃! k : (D.1.obj X) →ₗ[B] Y,
        ∀ (m : ↥M.1) (y : X), k (D.2 X m y) = p m y) ∧
    (∀ (X Y : AMod.{u,x} A) (h : ModuleCat.Hom X Y) (m : ↥M.1) (y : X),
      (ModuleCat.Hom.hom (D.1.map h)) (D.2 X m y) = D.2 Y m ((ModuleCat.Hom.hom h) y)) }

variable {M N P : Bimod.{u,v,w} A B}
variable {T : TensorFunctor.{u,v,w,x} M} {S : TensorFunctor.{u,v,w,x} N}
variable {U : TensorFunctor.{u,v,w,x} P}

private abbrev NatCode (M N : Bimod.{u,v,w} A B) :=
  {f : M.1 →ₗ[B] N.1 // ∀ (m : ↥M.1) (a : A), f (right M m a) = right N (f m) a}

private abbrev Component (T : TensorFunctor.{u,v,w,x} M)
    (S : TensorFunctor.{u,v,w,x} N) (X : AMod.{u,x} A) :=
  T.1.1.obj X →ₗ[B] S.1.1.obj X

private abbrev NatGraph (T : TensorFunctor.{u,v,w,x} M) (S : TensorFunctor.{u,v,w,x} N) :=
  { G : ∀ X : AMod.{u,x} A, Component T S X → Prop //
    (∀ X : AMod.{u,x} A, ∃! k : Component T S X, G X k) ∧
    (∀ (X Y : AMod.{u,x} A) (h : ModuleCat.Hom X Y)
        (k : Component T S X) (l : Component T S Y),
      G X k → G Y l →
      (ModuleCat.Hom.hom (S.1.1.map h)).comp k =
        l.comp (ModuleCat.Hom.hom (T.1.1.map h))) }

private abbrev Unitor (T : TensorFunctor.{u,v,w,x} M) :=
  T.1.1.obj (regular.{u,x} A) ≃ₗ[B] M.1

private def IsUnitor (rho : Unitor T) : Prop :=
  (∀ (m : ↥M.1) (a : A), rho (T.1.2 (regular A) m (ULift.up a)) = right M m a) ∧
  (∀ m : ↥M.1, rho.symm m = T.1.2 (regular A) m (ULift.up (1 : A)))

private def eval (rho : Unitor T) (sigma : Unitor S) (k : Component T S (regular A)) :
    M.1 →ₗ[B] N.1 :=
  sigma.toLinearMap.comp (k.comp rho.symm.toLinearMap)

private def Pure (f : NatCode M N) (X : AMod.{u,x} A) (k : Component T S X) : Prop :=
  ∀ (m : ↥M.1) (y : X), k (T.1.2 X m y) = S.1.2 X (f.1 m) y

private def Represents (rho : Unitor T) (sigma : Unitor S) (eta : NatGraph T S)
    (f : NatCode M N) : Prop :=
  (∀ k : Component T S (regular A), eta.1 (regular A) k →
    f.1 = eval rho sigma k ∧
    ∀ m : ↥M.1, f.1 m = sigma (k (T.1.2 (regular A) m (ULift.up (1 : A))))) ∧
  (∀ (X : AMod.{u,x} A) (k : Component T S X), eta.1 X k → Pure f X k)

private def InverseAssignments (rho : Unitor T) (sigma : Unitor S) : Prop :=
  (∀ eta : NatGraph T S, ∃! f : NatCode M N, Represents rho sigma eta f) ∧
  (∀ f : NatCode M N, ∃! eta : NatGraph T S, Represents rho sigma eta f)

private def Addition (rho : Unitor T) (sigma : Unitor S) : Prop :=
  ∀ eta theta : NatGraph T S,
    ∃ sum : NatGraph T S,
      (∀ (X : AMod.{u,x} A) (k l : Component T S X),
        eta.1 X k → theta.1 X l → sum.1 X (k + l)) ∧
      (∀ (k l : Component T S (regular A)),
        eta.1 (regular A) k → theta.1 (regular A) l →
        eval rho sigma (k + l) = eval rho sigma k + eval rho sigma l)

private def Identity (rho : Unitor T) : Prop :=
  ∃ identity : NatGraph T T,
    (∀ X : AMod.{u,x} A, identity.1 X LinearMap.id) ∧
    eval rho rho LinearMap.id = LinearMap.id

private def Composition (rho : Unitor T) (sigma : Unitor S) (tau : Unitor U) : Prop :=
  ∀ (eta : NatGraph T S) (theta : NatGraph S U),
    ∃ composite : NatGraph T U,
      (∀ (X : AMod.{u,x} A) (k : Component T S X) (l : Component S U X),
        eta.1 X k → theta.1 X l → composite.1 X (l.comp k)) ∧
      (∀ (k : Component T S (regular A)) (l : Component S U (regular A)),
        eta.1 (regular A) k → theta.1 (regular A) l →
        eval rho tau (l.comp k) = (eval sigma tau l).comp (eval rho sigma k))
