import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.ReconstructionFromSmallProjectiveGenerator
import NotesProofs.BimoduleFunctorHomEquivalence
import NotesProofs.AbelianEquivalencesPreserveFunctorHypotheses
import NotesProofs.TensorDictionaryCompositionAndIdentities

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
  exact Equivalence.mk F G η ε

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
  letI := hF f
  letI := hG (F.map f)
  have diagram : parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 := by
    simpa only [parallelPair_map_left, parallelPair_map_right, Functor.comp_map,
      Functor.map_zero] using diagramIsoParallelPair (parallelPair f 0 ⋙ F)
  letI : PreservesColimit (parallelPair f 0 ⋙ F) G :=
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
  have hL := AbelianEquivalencesPreserveFunctorHypotheses
    (w := v) left
  have hR := AbelianEquivalencesPreserveFunctorHypotheses
    (w := v) right
  letI : left.functor.Additive := hL.1
  letI : right.functor.Additive := hR.1
  letI : F.Additive := hF.1
  refine ⟨inferInstance, ?_, ?_⟩
  · exact comp_preservesCokernels left.functor (F ⋙ right.functor)
      (fun f => (hL.2.1 f).2)
      (comp_preservesCokernels F right.functor hF.2.1 (fun f => (hR.2.1 f).2))
  · intro I
    letI := hL.2.2.1 I
    letI := hF.2.2 I
    letI := hR.2.2.1 I
    infer_instance

end NotesCategoricalDictionary
