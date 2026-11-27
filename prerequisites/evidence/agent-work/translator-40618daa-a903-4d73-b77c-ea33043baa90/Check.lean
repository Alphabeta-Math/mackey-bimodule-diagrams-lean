import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

universe u v w

namespace GeneratorPresentationCheck

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [HasCoproducts.{w} C]

noncomputable def evaluation (P X : C) : (∐ fun _ : Shrink.{w} (P ⟶ X) => P) ⟶ X :=
  Sigma.desc ((equivShrink (P ⟶ X)).symm : Shrink.{w} (P ⟶ X) → (P ⟶ X))

lemma evaluation_epi {P : C} (hP : IsSeparator P) (X : C) : Epi (evaluation P X) := by
  constructor
  intro Y f g hfg
  apply hP.def f g
  intro k
  have h := congrArg (fun z => Sigma.ι (fun _ : Shrink.{w} (P ⟶ X) => P)
    (equivShrink (P ⟶ X) k) ≫ z) hfg
  simpa [evaluation, ← Category.assoc] using h

variable [Abelian C]

lemma evaluation_presentation {P : C} (hP : IsSeparator P) (X : C) :
    ∃ (I J : Type w),
      let copower := fun K : Type w => sigmaObj (fun _ : K => P)
      ∃ (d : copower J ⟶ copower I) (q : copower I ⟶ X) (h : d ≫ q = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ q h)) := by
  let q := evaluation P X
  have : Epi q := evaluation_epi hP X
  let t := evaluation P (kernel q)
  have : Epi t := evaluation_epi hP (kernel q)
  let k := kernel.ι q
  have hq := Abelian.epiIsCokernelOfKernel (KernelFork.ofι k (kernel.condition q))
    (kernelIsKernel q)
  have h : ∀ ⦃Y : C⦄ (g : _ ⟶ Y), k ≫ g = 0 ↔ (t ≫ k) ≫ g = 0 := by
    intro Y g
    rw [Category.assoc]
    constructor
    · intro hg
      rw [hg, comp_zero]
    · intro hg
      apply (cancel_epi t).mp
      simpa only [comp_zero] using hg
  refine ⟨Shrink.{w} (P ⟶ X), Shrink.{w} (P ⟶ kernel q), t ≫ k, q,
    h q |>.mp (kernel.condition q), ⟨?_⟩⟩
  exact CokernelCofork.isColimitOfIsColimitOfIff' hq (t ≫ k) h

end GeneratorPresentationCheck

theorem GeneratorCokernelPresentations :
∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.LocallySmall.{w} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{w} C]
    (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type w) (A : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid
        (β := fun i => Quiver.Hom P (A i))
        (γ := Quiver.Hom P (CategoryTheory.Limits.sigmaObj A))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι A i)))) →
  ∀ X : C,
    ∃ (I J : Type w),
      let copower := fun K : Type w => CategoryTheory.Limits.sigmaObj (fun _ : K => P)
      ∃ (d : Quiver.Hom (copower J) (copower I)) (q : Quiver.Hom (copower I) X)
        (h : CategoryTheory.CategoryStruct.comp d q = 0),
        Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.CokernelCofork.ofπ q h))
:= by
  intro C _ _ _ _ P _ hP _ X
  exact GeneratorPresentationCheck.evaluation_presentation hP X

#print axioms GeneratorCokernelPresentations
