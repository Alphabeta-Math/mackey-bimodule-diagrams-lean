import MackeyDiagrams
import WattsFoundation.ConcreteTensorBimoduleMap
import WattsFoundation.WattsMathlibReverse
import WattsFoundation.General.OriginalBimoduleAdapter
import WattsFoundation.ClassicalReconstruction
import WattsFoundation.NormalMorphismsInAbelianCategories

set_option maxHeartbeats 2000000

universe u v w

open CategoryTheory CategoryTheory.Limits

theorem GeneratorCokernelPresentations : (
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
) :=
(by
  intro C _ _ _ _ P _ hP _ X
  -- Lemma 8.4 indexes the evaluation coproduct by Hom(P, Y). Shrink places
  -- this Hom type in the coproduct index universe using local smallness.
  -- This construction only needs the separator clause of Definition 8.1.
  let copower (I : Type w) := sigmaObj (fun _ : I => P)
  let evaluation (Y : C) : copower (Shrink.{w} (P ⟶ Y)) ⟶ Y :=
    Sigma.desc ((equivShrink (P ⟶ Y)).symm : Shrink.{w} (P ⟶ Y) → (P ⟶ Y))
  have evaluation_epi (Y : C) : Epi (evaluation Y) := by
    constructor
    intro Z f g hfg
    apply hP.def f g
    intro a
    have h := congrArg (fun z =>
      Sigma.ι (fun _ : Shrink.{w} (P ⟶ Y) => P) (equivShrink (P ⟶ Y) a) ≫ z) hfg
    simpa [evaluation, ← Category.assoc] using h
  let q := evaluation X
  have : Epi q := evaluation_epi X
  let t := evaluation (kernel q)
  have : Epi t := evaluation_epi (kernel q)
  let k := kernel.ι q
  -- Alphabeta Math's proof of normality in abelian categories, step 3.1, gives the cokernel
  -- property by dualizing step 2.1 in the opposite abelian category.
  -- The supplier's epi clause uses Abelian.epiIsCokernelOfKernel.
  -- Its hypotheses are the evaluation epi and the chosen limit kernel fork.
  obtain ⟨hq⟩ :=
    (NormalMorphismsInAbelianCategories C q).2.1
      (KernelFork.ofι k (kernel.condition q)) (kernelIsKernel q)
  -- The two relation arrows have the same annihilators by cancellation
  -- of t. Transport the cokernel witness with its projection q fixed.
  have annihilates_iff ⦃Y : C⦄ (g : copower (Shrink.{w} (P ⟶ X)) ⟶ Y) :
      k ≫ g = 0 ↔ (t ≫ k) ≫ g = 0 := by
    rw [Category.assoc]
    constructor
    · intro hg
      rw [hg, comp_zero]
    · intro hg
      exact (cancel_epi t).mp (by simpa only [comp_zero] using hg)
  refine ⟨Shrink.{w} (P ⟶ X), Shrink.{w} (P ⟶ kernel q), t ≫ k, q,
    (annihilates_iff q).mp (kernel.condition q), ⟨?_⟩⟩
  exact CokernelCofork.isColimitOfIsColimitOfIff' hq (t ≫ k) annihilates_iff)
