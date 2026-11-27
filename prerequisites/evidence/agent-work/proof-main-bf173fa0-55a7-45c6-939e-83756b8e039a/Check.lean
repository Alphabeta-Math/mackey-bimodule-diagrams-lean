import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.GeneratorHomFullyFaithful
import NotesProofs.GeneratorHomExactnessAndDetection
import NotesProofs.FreeModulesAndPresentations

set_option maxHeartbeats 2000000

theorem ReconstructionFromSmallProjectiveGenerator : (
∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.LocallySmall.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{v} C]
    (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type v) (X : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid
        (β := fun i => Quiver.Hom P (X i))
        (γ := Quiver.Hom P (CategoryTheory.Limits.sigmaObj X))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι X i)))) →
  let R := MulOpposite (CategoryTheory.End P)
  let H : CategoryTheory.Functor C (ModuleCat.{v} R) :=
    CategoryTheory.preadditiveCoyonedaObj P
  ∃ L : CategoryTheory.Functor (ModuleCat.{v} R) C,
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp L H)
      (CategoryTheory.Functor.id (ModuleCat.{v} R))) ∧
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp H L)
      (CategoryTheory.Functor.id C))
) :=
((open CategoryTheory CategoryTheory.Limits in
by
  intro C _ _ _ _ P _ hGenerator hSmall
  dsimp only
  let R := (End P)ᵐᵒᵖ
  let H : Functor C (ModuleCat.{v} R) := preadditiveCoyonedaObj P
  change ∃ L : Functor (ModuleCat.{v} R) C,
    Nonempty (Iso (Functor.comp L H) (Functor.id (ModuleCat.{v} R))) ∧
    Nonempty (Iso (Functor.comp H L) (Functor.id C))
  have hHom : ∀ X Y, Function.Bijective (H.map (X := X) (Y := Y)) :=
    GeneratorHomFullyFaithful C P hGenerator hSmall
  let _ : H.Full := ⟨fun {X Y} => (hHom X Y).2⟩
  let _ : H.Faithful := ⟨fun {X Y} => (hHom X Y).1⟩
  have hExact := GeneratorHomExactnessAndDetection C P hGenerator hSmall

  -- Alphabeta Math, step 1.1. The portal starts with an adjunction and
  -- computes its unit on free modules. Here we construct the underlying
  -- free-term comparison, as in Lemma 8.5 of the lecture notes. Unop
  -- identifies the regular left module with H(P): multiplication in R
  -- becomes precomposition. The linear sum of mapped coproduct legs
  -- has the same underlying additive map as the smallness hypothesis.
  -- The coefficient-one vector in a summand therefore maps to its
  -- coproduct injection, and the comparison also covers the empty sum.
  have hFree (I : Type v) :
      Nonempty (ModuleCat.of R (I →₀ R) ≅ H.obj (sigmaObj (fun _ : I => P))) := by
    let _ : DecidableEq I := Classical.decEq I
    let A : I → C := fun _ => P
    let unopAdd : R ≃+ H.obj P := MulOpposite.opAddEquiv.symm.trans End.addEquiv
    let regular : R ≃ₗ[R] H.obj P :=
      { unopAdd with map_smul' := fun _ _ => rfl }
    let sumComparison : DirectSum I (fun _ => ↥(H.obj P)) →ₗ[R] H.obj (sigmaObj A) :=
      DirectSum.toModule R I (H.obj (sigmaObj A))
        (fun i => (H.map (Sigma.ι A i)).hom)
    have hSum : Function.Bijective sumComparison := hSmall I A
    let freeSum : (I →₀ R) ≃ₗ[R] DirectSum I (fun _ => ↥(H.obj P)) :=
      (finsuppLEquivDirectSum R R I).trans (DirectSum.congrLinearEquiv fun _ => regular)
    exact ⟨(freeSum.trans (LinearEquiv.ofBijective sumComparison hSum)).toModuleIso⟩

  -- Alphabeta Math, step 2.1. Theorem 5.8 supplies the free terms and
  -- the cokernel universal property. The ring, module carriers, both
  -- index types, and the factorization targets are in universe v.
  -- The earlier checked ClassicalReconstruction result
  -- requires a supplied L with an adjunction and a unit formula.
  have hImage (V : ModuleCat.{v} R) : ∃ X : C, Nonempty (H.obj X ≅ V) := by
    have hPresent := FreeModulesAndPresentations.{v, v, v, v, v} R V
    obtain ⟨I, J, d, q, hRange, hSurj⟩ := hPresent.2.1
    obtain ⟨hZero, hFactor⟩ := (hPresent.2.2 d q).mp ⟨hRange, hSurj⟩
    let d' : ModuleCat.of R (J →₀ R) ⟶ ModuleCat.of R (I →₀ R) := ModuleCat.ofHom d
    let q' : ModuleCat.of R (I →₀ R) ⟶ V := ModuleCat.ofHom q
    have hdq : CategoryStruct.comp d' q' = 0 := ModuleCat.hom_ext hZero
    let _ : Epi q' := (ModuleCat.epi_iff_surjective q').2 hSurj
    have hV : IsColimit (CokernelCofork.ofπ q' hdq) := by
      refine CokernelCofork.IsColimit.ofπ' q' hdq (fun {N} g hg => ?_)
      have hZeroG : g.hom.comp d = 0 := congrArg ModuleCat.Hom.hom hg
      let factor := Classical.indefiniteDescription _ (hFactor N g.hom hZeroG).exists
      exact ⟨ModuleCat.ofHom factor.1, ModuleCat.hom_ext factor.2⟩

    -- Lift the relation map conjugated by the free comparisons. The
    -- two resulting coforks are colimiting by Lemma 8.3 and Theorem 5.8.
    obtain ⟨thetaI⟩ := hFree I
    obtain ⟨thetaJ⟩ := hFree J
    let lifted := H.preimage (CategoryStruct.comp thetaJ.inv (CategoryStruct.comp d' thetaI.hom))
    have hSquare : CategoryStruct.comp thetaJ.hom (H.map lifted) =
        CategoryStruct.comp d' thetaI.hom := by
      simp [lifted]
    let _ : PreservesColimit (parallelPair lifted 0) H := hExact.2.1 lifted
    have hMapped := isColimitOfHasCokernelOfPreservesColimit H lifted
    exact ⟨cokernel lifted, ⟨(CokernelCofork.mapIsoOfIsColimit hV hMapped
      (Arrow.isoMk' d' (H.map lifted) thetaJ thetaI hSquare)).symm⟩⟩

  -- Alphabeta Math, steps 3.1 and 4.1 conclude via the given
  -- adjunction. Theorem 8.6 asks for a quasi-inverse and both natural
  -- isomorphisms. Mathlib chooses the preimages above and defines the
  -- inverse on maps by conjugation and fullness. Faithfulness gives
  -- the functor laws and naturality of the comparison lifted to C.
  -- This packages the notes’ pointwise cokernel construction with
  -- classical choice of preimages under §8.1. The reviewed endpoint
  -- only requires the resulting functor and natural isomorphisms.
  let _ : H.EssSurj := ⟨hImage⟩
  let _ : H.IsEquivalence := { }
  let e := H.asEquivalence
  exact ⟨e.inverse, ⟨e.counitIso⟩, ⟨e.unitIso.symm⟩⟩))
