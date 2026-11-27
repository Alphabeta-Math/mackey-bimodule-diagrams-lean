import NotesProofs.WattsAllComparison
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.NatIso

/-! Natural Eilenberg–Watts comparison for arbitrary rings, with explicit
cokernel and coproduct preservation assumptions, in a fixed universe. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs

universe u
open CategoryTheory

variable {A B : Type u} [Ring A] [Ring B]
variable (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive]

/-- Cokernel preservation, expressed by the actual universal property. -/
def WattsPreservesCokernels : Prop :=
  ∀ (L P X : ModuleCat.{u} A) (f : L ⟶ P) (q : P ⟶ X),
    f ≫ q = ModuleCat.ofHom 0 →
    (∀ (Z : ModuleCat.{u} A) (g : P ⟶ Z),
      f ≫ g = ModuleCat.ofHom 0 → ∃! d : X ⟶ Z, q ≫ d = g) →
    F.map f ≫ F.map q = ModuleCat.ofHom 0 ∧
    ∀ (Z : ModuleCat.{u} B) (g : F.obj P ⟶ Z),
      F.map f ≫ g = ModuleCat.ofHom 0 → ∃! d : F.obj X ⟶ Z, F.map q ≫ d = g

/-- Preservation of set-indexed module coproducts. -/
def WattsPreservesCoproducts : Prop :=
  ∀ (I : Type u) (D : I → ModuleCat.{u} A) (P : ModuleCat.{u} A) (ι : ∀ i, D i ⟶ P),
    (∀ (Q : ModuleCat.{u} A) (legs : ∀ i, D i ⟶ Q),
      ∃! d : P ⟶ Q, ∀ i, ι i ≫ d = legs i) →
    ∀ (Q : ModuleCat.{u} B) (legs : ∀ i, F.obj (D i) ⟶ Q),
      ∃! d : F.obj P ⟶ Q, ∀ i, F.map (ι i) ≫ d = legs i

/-- The comparison is the map `m ⊗ x ↦ F(λ_x)(m)` on pure tensors. -/
def wattsComparisonNatTrans : ChoiceFreeWatts.tensorFunctor F ⟶ F where
  app X := @ModuleCat.ofHom B _ (ChoiceFreeWatts.tensorObj F X) (F.obj X) _ _ _ _ (ChoiceFreeWatts.comparison F X)
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    exact ChoiceFreeWatts.comparison_naturality F f

/-- Classical Eilenberg–Watts natural isomorphism for arbitrary unital rings,
with the explicit preservation assumptions above and source and target module
categories in the same Lean universe. -/
noncomputable def wattsNaturalIso
    (hcokern : WattsPreservesCokernels F) (hcoprod : WattsPreservesCoproducts F) :
    ChoiceFreeWatts.tensorFunctor F ≅ F := by
  let τ := wattsComparisonNatTrans F
  haveI : ∀ X : ModuleCat.{u} A, IsIso (τ.app X) := fun X => by
    apply (ConcreteCategory.isIso_iff_bijective (τ.app X)).2
    change Function.Bijective (ChoiceFreeWatts.comparison F X)
    exact watts_comparison_bijective F hcokern hcoprod X
  haveI := NatIso.isIso_of_isIso_app τ
  exact asIso τ

#print axioms wattsComparisonNatTrans
#print axioms wattsNaturalIso

end NotesProofs
