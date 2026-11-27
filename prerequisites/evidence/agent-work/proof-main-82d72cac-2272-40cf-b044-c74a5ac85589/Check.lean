import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Generator.Preadditive
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.CancellationAndZeroKernels
import NotesProofs.NormalMorphismsInAbelianCategories
import NotesProofs.ModuleProductsAndCoproducts

set_option maxHeartbeats 2000000

theorem GeneratorHomExactnessAndDetection : (
∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
  [CategoryTheory.Limits.HasCoproducts.{w} C] (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type w) (X : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι X i)))) →
  let H := CategoryTheory.preadditiveCoyonedaObj P
  (∀ {X Y : C} (f : Quiver.Hom X Y),
    CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) H) ∧
  (∀ {X Y : C} (f : Quiver.Hom X Y),
    CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) H) ∧
  (∀ (I : Type w), CategoryTheory.Limits.PreservesColimitsOfShape
    (CategoryTheory.Discrete I) H) ∧
  CategoryTheory.Functor.Faithful H ∧
  CategoryTheory.Functor.ReflectsIsomorphisms H
) :=
(open CategoryTheory CategoryTheory.Limits in
by
  intro C _ _ _ P _ hGenerator hSmall
  dsimp only
  -- Lecture notes Lemma 8.3 uses the ordinary-choice setting of Chapter 8.
  -- Alphabeta Math step 5.1 addresses its separate choice-free formulation.
  -- Alphabeta Math step 1.1 is implemented by preadditiveCoyonedaObj.
  -- It uses precomposition for the opposite-ring action and postcomposition for maps.
  let H := preadditiveCoyonedaObj P
  let _ : PreservesLimits H := preservesLimits_preadditiveCoyonedaObj P
  let _ : PreservesFiniteColimits H :=
    preservesFiniteColimits_preadditiveCoyonedaObj_of_projective P
  -- The generator condition in step 1.2 is exactly the separator criterion.
  let _ : H.Faithful := (isSeparator_iff_faithful_preadditiveCoyonedaObj P).mp hGenerator
  -- Steps 2.2, 3.1 and 4.1 use representability and projectivity for exactness.
  -- The pinned instances implement these arguments. The two parallel-pair
  -- diagrams in the article endpoint encode the kernel and cokernel.
  refine ⟨fun f => inferInstance, fun f => inferInstance, ?_, inferInstance, ?_⟩
  · intro I
    let _ : ∀ X : I → C, PreservesColimit (Discrete.functor X) H := by
      intro X
      let _ : DecidableEq I := Classical.decEq I
      let R := (End P)ᵐᵒᵖ
      let M := fun i => H.obj (X i)
      let A := H.obj (∐ X)
      let leg : ∀ i, M i ⟶ A := fun i => H.map (Sigma.ι X i)
      let comparison : DirectSum I (fun i => ↥(M i)) →ₗ[R] A :=
        DirectSum.toModule R I A (fun i => (leg i).hom)
      -- Step 2.1 uses smallness on the underlying additive groups.
      -- Even when I lives above the Hom universe, the sum can serve as a
      -- linear-map domain and the image cofan apex stays in the Hom universe.
      -- ModuleProductsAndCoproducts bundles the sum in a universe at least
      -- as large as the index universe. Using the linear universal property
      -- directly avoids imposing that universe bound on H's target.
      have hComparison : Function.Bijective comparison := by
        exact hSmall I X
      have comparison_lof (i : I) (x : M i) :
          comparison (DirectSum.lof R I (fun j => ↥(M j)) i x) = (leg i).hom x := by
        simp only [comparison, DirectSum.toModule_lof]
      let e := LinearEquiv.ofBijective comparison hComparison
      have hinj (i : I) (x : M i) :
          e.symm ((leg i).hom x) = DirectSum.lof R I (fun j => ↥(M j)) i x := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact (comparison_lof i x).symm
      have hCofan : IsColimit (Cofan.mk A leg) := by
        let extend (s : Cofan M) :=
          DirectSum.toModule R I s.pt (fun i => (s.inj i).hom)
        refine Cofan.IsColimit.mk (Cofan.mk A leg)
          (fun s => ModuleCat.ofHom ((extend s).comp e.symm.toLinearMap)) ?_ ?_
        · intro s i
          apply ModuleCat.hom_ext
          ext x
          change extend s (e.symm ((leg i).hom x)) = (s.inj i).hom x
          rw [hinj]
          simp only [extend, DirectSum.toModule_lof]
        · intro s m hm
          have hExt : m.hom.comp e.toLinearMap = extend s := by
            apply DirectSum.linearMap_ext
            intro i
            ext x
            change m.hom (comparison (DirectSum.lof R I (fun j => ↥(M j)) i x)) =
              extend s (DirectSum.lof R I (fun j => ↥(M j)) i x)
            rw [comparison_lof]
            change (CategoryStruct.comp (leg i) m).hom x = _
            rw [show CategoryStruct.comp (leg i) m = s.inj i from hm i]
            simp only [extend, DirectSum.toModule_lof]
          apply ModuleCat.hom_ext
          ext y
          change m.hom y = extend s (e.symm y)
          have hy := DFunLike.congr_fun hExt (e.symm y)
          change m.hom (e (e.symm y)) = extend s (e.symm y) at hy
          simpa only [e.apply_symm_apply] using hy
      exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
        ((isColimitMapCoconeCofanMkEquiv H X (Sigma.ι X)).symm hCofan)
    exact preservesColimitsOfShape_of_discrete H
  · -- For step 1.3, the notes detect a zero object using faithfulness
    -- from step 1.2 on its identity and zero endomorphism. This needs no
    -- copower indexed by the Hom set and works for independent universes.
    have detectZero (Z : C) (hZ : IsZero (H.obj Z)) : IsZero Z := by
      apply (IsZero.iff_id_eq_zero Z).mpr
      apply H.map_injective
      rw [H.map_id, H.map_zero]
      exact (IsZero.iff_id_eq_zero _).mp hZ
    -- The end of Lemma 8.3 applies this detection to the preserved
    -- kernel and cokernel of an arrow with invertible image.
    constructor
    intro X Y f hf
    have hKernel : IsZero (H.obj (kernel f)) :=
      KernelFork.IsLimit.isZero_of_mono (isLimitOfHasKernelOfPreservesLimit H f)
    have hCokernel : IsZero (H.obj (cokernel f)) :=
      CokernelCofork.IsColimit.isZero_of_epi (isColimitOfHasCokernelOfPreservesColimit H f)
    -- Abelianity supplies the finite biproducts needed by the registered
    -- cancellation theorem. The registered normality theorem gives balancedness.
    let _ : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
    have criteria := CancellationAndZeroKernels C f f
    let _ : Mono f := criteria.1.mpr (detectZero (kernel f) hKernel)
    let _ : Epi f := criteria.2.1.mpr (detectZero (cokernel f) hCokernel)
    exact (NormalMorphismsInAbelianCategories C f).2.2)

#print axioms GeneratorHomExactnessAndDetection
