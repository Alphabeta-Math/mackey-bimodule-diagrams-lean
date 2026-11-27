import Mathlib.CategoryTheory.Adjunction.Additive
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.AdditiveFunctorsAndBiproducts
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits
private theorem abelianEquivalenceSmallness
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] (e : C ≌ D) [e.functor.Additive]
    {I : Type w} [DecidableEq I] [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (P : C) (Y : I → D)
    (h : Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => P ⟶ e.inverse.obj (Y i))
        (fun i => Preadditive.rightComp P (Sigma.ι (fun j => e.inverse.obj (Y j)) i)))) :
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => e.functor.obj P ⟶ Y i)
        (fun i => Preadditive.rightComp (e.functor.obj P) (Sigma.ι Y i))) := by
  -- Alphabeta Math's progenerator corollary, steps 1.1 and 2.2, uses the
  -- adjoint-equivalence transposition and coproduct preservation by the inverse.
  -- https://alphabetamath.cc/item/lem-equivalences-preserve-progenerators
  let : PreservesColimitsOfShape (Discrete I) e.inverse :=
    (Adjunction.isEquivalence_preservesColimits e.inverse).preservesColimitsOfShape
  let X := fun i => e.inverse.obj (Y i)
  let compareC := DirectSum.toAddMonoid (β := fun i => P ⟶ X i)
    (fun i => Preadditive.rightComp P (Sigma.ι X i))
  let compareD := DirectSum.toAddMonoid (β := fun i => e.functor.obj P ⟶ Y i)
    (fun i => Preadditive.rightComp (e.functor.obj P) (Sigma.ι Y i))
  let mapSummand := fun i => e.toAdjunction.homAddEquiv P (Y i)
  let mapSum : DirectSum I (fun i => e.functor.obj P ⟶ Y i) ≃+
      DirectSum I (fun i => P ⟶ X i) :=
    DFinsupp.mapRange.addEquiv mapSummand
  let coproductIso := (asIso (sigmaComparison e.inverse Y)).symm
  let postcompose : (P ⟶ e.inverse.obj (∐ Y)) ≃+ (P ⟶ ∐ X) :=
    { coproductIso.homToEquiv with
      map_add' := fun f g => Preadditive.add_comp _ _ _ f g coproductIso.hom }
  let mapCoproduct := (e.toAdjunction.homAddEquiv P (∐ Y)).trans postcompose

  -- Identify the actual comparison in Lemma 10.3 by checking the inclusions.
  have hSquare : mapCoproduct.toAddMonoidHom.comp compareD =
      compareC.comp mapSum.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    have hSummand :
        mapSum (DirectSum.of (fun j => e.functor.obj P ⟶ Y j) i f) =
          DirectSum.of (fun j => P ⟶ X j) i (mapSummand i f) := by
      change DFinsupp.mapRange.addEquiv mapSummand (DFinsupp.single i f) =
        DFinsupp.single i (mapSummand i f)
      rw [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_single]
    change mapCoproduct (compareD (DirectSum.of (fun j => e.functor.obj P ⟶ Y j) i f)) =
      compareC (mapSum (DirectSum.of (fun j => e.functor.obj P ⟶ Y j) i f))
    simp only [hSummand, compareC, compareD, DirectSum.toAddMonoid_of]
    change e.toAdjunction.homEquiv P (∐ Y) (f ≫ Sigma.ι Y i) ≫ coproductIso.hom =
      e.toAdjunction.homEquiv P (Y i) f ≫ Sigma.ι X i
    rw [e.toAdjunction.homEquiv_naturality_right, Category.assoc]
    congr 1
    exact map_ι_comp_inv_sigmaComparison e.inverse Y i
  apply (mapCoproduct.bijective.of_comp_iff' compareD).mp
  change Function.Bijective (⇑(mapCoproduct.toAddMonoidHom.comp compareD))
  rw [hSquare]
  exact h.comp mapSum.bijective

theorem AbelianEquivalencesPreserveFunctorHypotheses : (∀ {C : Type u₁} {D : Type u₂}
  [CategoryTheory.Category.{v₁} C] [CategoryTheory.Category.{v₂} D]
  [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
  (e : CategoryTheory.Equivalence C D),
  let F := CategoryTheory.Equivalence.functor e
  CategoryTheory.Functor.Additive F ∧
  (∀ {X Y : C} (f : Quiver.Hom X Y),
    CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) F ∧
    CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F) ∧
  (∀ (I : Type w),
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F) ∧
  (∀ [CategoryTheory.Functor.Additive F] (S : CategoryTheory.ShortComplex C),
    CategoryTheory.ShortComplex.Exact S →
      CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.map S F)) ∧
  (∀ [CategoryTheory.Limits.HasCoproducts.{w} C],
    ∃ hD : CategoryTheory.Limits.HasCoproducts.{w} D,
    letI : CategoryTheory.Limits.HasCoproducts.{w} D := hD
    ∀ (P : C),
      CategoryTheory.Projective P →
      CategoryTheory.IsSeparator P →
      (∀ (I : Type w) (X : I → C),
        letI : DecidableEq I := Classical.decEq I
        Function.Bijective
          (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
            (fun i => CategoryTheory.Preadditive.rightComp P
              (CategoryTheory.Limits.Sigma.ι X i)))) →
      CategoryTheory.Projective (CategoryTheory.Functor.obj F P) ∧
      CategoryTheory.IsSeparator (CategoryTheory.Functor.obj F P) ∧
      (∀ (I : Type w) (Y : I → D),
        letI : DecidableEq I := Classical.decEq I
        Function.Bijective
          (DirectSum.toAddMonoid
            (β := fun i => Quiver.Hom (CategoryTheory.Functor.obj F P) (Y i))
            (fun i => CategoryTheory.Preadditive.rightComp (CategoryTheory.Functor.obj F P)
              (CategoryTheory.Limits.Sigma.ι Y i)))))) :=
(by
  intro C D _ _ _ _ e
  dsimp only
  -- Alphabeta Math's exact-equivalence proof, step 1.1. The equivalence
  -- preserves all existing limits and colimits, so use the parallel-pair
  -- shapes for kernels and cokernels and every discrete shape for coproducts.
  -- https://alphabetamath.cc/item/thm-an-equivalence-between-abelian-categories-is-exact
  let preservesLimits : PreservesLimitsOfSize.{0, 0} e.functor :=
    Adjunction.isEquivalencePreservesLimits e.functor
  let preservesColimits : PreservesColimitsOfSize.{0, 0} e.functor :=
    Adjunction.isEquivalence_preservesColimits e.functor
  have hLimits : ∀ {A B : C} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) e.functor ∧
        PreservesColimit (parallelPair f 0) e.functor :=
    fun _ => ⟨preservesLimits.preservesLimitsOfShape.preservesLimit,
      preservesColimits.preservesColimitsOfShape.preservesColimit⟩
  have hCoproducts : ∀ (I : Type w), PreservesColimitsOfShape (Discrete I) e.functor :=
    fun I => (Adjunction.isEquivalence_preservesColimits e.functor).preservesColimitsOfShape
  -- Step 2.1 uses the additive categories underlying the abelian categories.
  -- The compiled supplier takes zero-object and finite (co)product preservation.
  have hZero (X : C) (hX : IsZero X) : IsZero (e.functor.obj X) := by
    let : PreservesLimit (Functor.empty C) e.functor :=
      preservesLimits.preservesLimitsOfShape.preservesLimit
    exact (hX.isTerminal.isTerminalObj e.functor).isZero
  let : PreservesFiniteLimits e.functor :=
    PreservesLimitsOfSize0.preservesFiniteLimits e.functor
  let : PreservesFiniteColimits e.functor :=
    PreservesColimitsOfSize0.preservesFiniteColimits e.functor
  let : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  let : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
  let : e.functor.Additive :=
    (AdditiveFunctorsAndBiproducts e.functor).2 hZero inferInstance inferInstance
  refine ⟨inferInstance, hLimits, hCoproducts, ?_, ?_⟩
  · -- The reviewed endpoint uses exact short complexes. Finite limit and
    -- colimit preservation gives both homology preservation instances for Exact.map.
    intro _ S hS
    exact hS.map e.functor
  · -- The progenerator corollary, steps 2.4 and 3.1, transports existence for
    -- the discrete shapes required here. Steps 2.1 and 2.3 give the two object
    -- properties through the projective-object and separator suppliers.
    intro hC
    let hD : HasCoproducts.{w} D :=
      fun I => Adjunction.hasColimitsOfShape_of_equivalence (J := Discrete I) e.inverse
    refine ⟨hD, ?_⟩
    intro P hProjective hSeparator hSmall
    refine ⟨Functor.PreservesProjectiveObjects.projective_obj (F := e.functor) hProjective,
      hSeparator.of_equivalence e, ?_⟩
    intro I Y
    -- Use the reviewed comparison's classical decidable equality on the index type.
    let : DecidableEq I := Classical.decEq I
    exact abelianEquivalenceSmallness e P Y (hSmall I (fun i => e.inverse.obj (Y i))))

#print axioms AbelianEquivalencesPreserveFunctorHypotheses
