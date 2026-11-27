open CategoryTheory CategoryTheory.Limits

namespace NotesCategoricalDictionary

open CategoryTheory CategoryTheory.Limits

-- Theorem 10.4 packages the comparisons on the full subcategories. Fullness
-- lifts their components and faithfulness reduces naturality to the original
-- naturality on the ambient categories.
private noncomputable def restrictEquivalence
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (e : C ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ X, P X → Q (e.functor.obj X))
    (hG : ∀ Y, Q Y → P (e.inverse.obj Y)) :
    P.FullSubcategory ≌ Q.FullSubcategory := by
  let F := Q.lift (P.ι ⋙ e.functor) (fun X => hF X.obj X.property)
  let G := P.lift (Q.ι ⋙ e.inverse) (fun Y => hG Y.obj Y.property)
  let η : 𝟭 P.FullSubcategory ≅ F ⋙ G :=
    NatIso.ofComponents (fun X => P.isoMk (e.unitIso.app X.obj)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact e.unitIso.hom.naturality f.hom)
  let ε : G ⋙ F ≅ 𝟭 Q.FullSubcategory :=
    NatIso.ofComponents (fun Y => Q.isoMk (e.counitIso.app Y.obj)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact e.counitIso.hom.naturality f.hom)
  exact CategoryTheory.Equivalence.mk F G η ε

-- Additivity takes the second arrow of the parallel pair to zero.
-- This diagram comparison allows composition of the two preservation
-- witnesses even though their diagrams are presented differently.
private theorem comp_preservesCokernels
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    (hF : ∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F)
    (hG : ∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) G)
    {X Y : C} (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) (F ⋙ G) := by
  let := hF f
  let := hG (F.map f)
  have diagram : parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 := by
    simpa only [parallelPair_map_left, parallelPair_map_right, Functor.comp_map,
      Functor.map_zero] using diagramIsoParallelPair (parallelPair f 0 ⋙ F)
  let : PreservesColimit (parallelPair f 0 ⋙ F) G :=
    preservesColimit_of_iso_diagram G diagram.symm
  infer_instance

private abbrev abstractGood {C : Type u₁} {D : Type u₂}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D] :
    ObjectProperty (C ⥤ D) := fun F =>
  F.Additive ∧
    (∀ {X Y : C} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F) ∧
    ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F

private theorem whiskerGood
    {A : Type u₁} {D : Type u₂} {C : Type u₃} {E : Type u₄}
    [Category.{v} A] [Category.{v} D] [Category.{v} C] [Category.{v} E]
    [Abelian A] [Abelian D] [Abelian C] [Abelian E]
    (left : C ≌ A) (right : D ≌ E) (F : A ⥤ D)
    (hF : abstractGood F) : abstractGood (left.functor ⋙ F ⋙ right.functor) := by
  -- Alphabeta Math, exactness of abelian equivalences, step 1.1.
  -- Use the registered Lemma 10.3 with the abelian structures on all four
  -- categories, including the two module categories in either whiskering.
  have hL := AbelianEquivalencesPreserveFunctorHypotheses.{u₃,u₁,v,v,v} left
  have hR := AbelianEquivalencesPreserveFunctorHypotheses.{u₂,u₄,v,v,v} right
  let : left.functor.Additive := hL.1
  let : right.functor.Additive := hR.1
  let : F.Additive := hF.1
  refine ⟨inferInstance, ?_, ?_⟩
  · exact comp_preservesCokernels left.functor (F ⋙ right.functor)
      (fun f => (hL.2.1 f).2)
      (comp_preservesCokernels F right.functor hF.2.1 (fun f => (hR.2.1 f).2))
  · intro I
    let := hL.2.2.1 I
    let := hF.2.2 I
    let := hR.2.2.1 I
    infer_instance


-- Whiskering uses the four supplied reconstruction functors. The abstract
-- endpoint tests cokernels individually. Corollary 9.6 packages that
-- condition as finite-colimit preservation on the module side.
private noncomputable def transport
    {A : Type u₁} {D : Type u₂}
    [Category.{v} A] [Category.{v} D] [Abelian A] [Abelian D]
    {R S : Type v} [Ring R] [Ring S]
    (eA : A ≌ ModuleCat.{v} R) (eD : D ≌ ModuleCat.{v} S) :
    (abstractGood (C := A) (D := D)).FullSubcategory ≌
      NotesProofs.General.ConcreteBimodule.GoodFunctors.{v,0} R S := by
  let e := (eA.congrLeft (E := D)).trans (eD.congrRight (E := ModuleCat.{v} R))
  apply restrictEquivalence e
  · intro F hF
    have h := whiskerGood eA.symm eD F hF
    let : (e.functor.obj F).Additive := h.1
    let : ∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) (e.functor.obj F) :=
      h.2.1
    exact ⟨h.1, (e.functor.obj F).preservesFiniteColimits_of_preservesCokernels, h.2.2⟩
  · intro T hT
    change NotesProofs.General.ConcreteBimodule.Good.{v,0} R S T at hT
    let : PreservesFiniteColimits T := hT.2.1
    have hCokernel {X Y : ModuleCat.{v} R} (f : X ⟶ Y) :
        PreservesColimit (parallelPair f 0) T := inferInstance
    exact whiskerGood eA eD.symm T ⟨hT.1, @hCokernel, hT.2.2⟩

end NotesCategoricalDictionary
