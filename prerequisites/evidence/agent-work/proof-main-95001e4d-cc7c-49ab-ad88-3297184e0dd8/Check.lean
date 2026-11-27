import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.ReconstructionFromSmallProjectiveGenerator
import NotesProofs.BimoduleFunctorHomEquivalence
import NotesProofs.AbelianEquivalencesPreserveFunctorHypotheses
import NotesProofs.TensorDictionaryCompositionAndIdentities

set_option maxHeartbeats 2000000

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

 theorem CategoricalBimoduleDictionary : (
∀ (A : Type uA) (D : Type uD)
    [CategoryTheory.Category.{v} A] [CategoryTheory.Category.{v} D]
    [CategoryTheory.LocallySmall.{v} A] [CategoryTheory.LocallySmall.{v} D]
    [CategoryTheory.Abelian A] [CategoryTheory.Abelian D]
    [CategoryTheory.Limits.HasCoproducts.{v} A] [CategoryTheory.Limits.HasCoproducts.{v} D]
    (P : A) (Q : D) [CategoryTheory.Projective P] [CategoryTheory.Projective Q],
  CategoryTheory.IsSeparator P →
  CategoryTheory.IsSeparator Q →
  (∀ (I : Type v) (X : I → A),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
        (fun i => CategoryTheory.Preadditive.rightComp P (CategoryTheory.Limits.Sigma.ι X i)))) →
  (∀ (I : Type v) (Y : I → D),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom Q (Y i))
        (fun i => CategoryTheory.Preadditive.rightComp Q (CategoryTheory.Limits.Sigma.ι Y i)))) →
  let R := MulOpposite (CategoryTheory.End P)
  let S := MulOpposite (CategoryTheory.End Q)
  let HA : CategoryTheory.Functor A (ModuleCat.{v} R) :=
    CategoryTheory.preadditiveCoyonedaObj P
  let HD : CategoryTheory.Functor D (ModuleCat.{v} S) :=
    CategoryTheory.preadditiveCoyonedaObj Q
  let Good := CategoryTheory.ObjectProperty.FullSubcategory
    (fun F : CategoryTheory.Functor A D =>
      CategoryTheory.Functor.Additive F ∧
      (∀ {X Y : A} (f : Quiver.Hom X Y),
        CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F) ∧
      (∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F))
  let Bimod := NotesProofs.General.ConcreteBimodule.{v,0} R S
  Nonempty (CategoryTheory.Equivalence Good Bimod) ∧
  ∀ (LA : CategoryTheory.Functor (ModuleCat.{v} R) A)
    (LD : CategoryTheory.Functor (ModuleCat.{v} S) D),
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp LA HA)
      (CategoryTheory.Functor.id (ModuleCat.{v} R))) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp HA LA)
      (CategoryTheory.Functor.id A)) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp LD HD)
      (CategoryTheory.Functor.id (ModuleCat.{v} S))) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp HD LD)
      (CategoryTheory.Functor.id D)) →
    ∃ E : CategoryTheory.Equivalence Good Bimod,
      (∀ F : Good,
        let W := CategoryTheory.Functor.comp LA
          (CategoryTheory.Functor.comp (CategoryTheory.ObjectProperty.FullSubcategory.obj F) HD)
        let BF := CategoryTheory.Functor.obj (CategoryTheory.Equivalence.functor E) F
        let M := NotesProofs.General.ConcreteBimodule.carrier BF
        ModuleCat.of S M = CategoryTheory.Functor.obj W (ChoiceFreeWatts.regular.{v,0} R) ∧
        ∀ r : R,
          HEq (fun m : M => SMul.smul (MulOpposite.op r) m)
            (fun x => ChoiceFreeWatts.right W r x)) ∧
      (∀ B : Bimod,
        CategoryTheory.ObjectProperty.FullSubcategory.obj
          (CategoryTheory.Functor.obj (CategoryTheory.Equivalence.inverse E) B) =
          CategoryTheory.Functor.comp HA
            (CategoryTheory.Functor.comp
              (NotesProofs.General.concreteTensorFunctor.{v,0} (R := R) (S := S)
                (NotesProofs.General.ConcreteBimodule.carrier B)) LD))
) :=
(open NotesCategoricalDictionary in
by
  intro A D _ _ _ _ _ _ _ _ P Q _ _ hP hQ hSmallP hSmallQ
  dsimp only
  let R := MulOpposite (End P)
  let S := MulOpposite (End Q)
  let HA : A ⥤ ModuleCat.{v} R := preadditiveCoyonedaObj P
  let HD : D ⥤ ModuleCat.{v} S := preadditiveCoyonedaObj Q
  -- Alphabeta Math, module-category reconstruction, steps 1.1, 2.1,
  -- 3.1 and 4.1. The registered Chapter 8 result supplies the inverse
  -- functors and both natural comparisons from the separators, projectivity,
  -- and precisely the two coproduct comparisons above.
  -- The lecture notes' §8.1 permits the choice used by that construction.
  have reconA := ReconstructionFromSmallProjectiveGenerator A P hP hSmallP
  have reconD := ReconstructionFromSmallProjectiveGenerator D Q hQ hSmallQ

  -- Use Corollary 9.6 at the carrier universe v. Its registered result
  -- supplies the actual tensor functor and regular-evaluation object
  -- formula on the same ConcreteBimodule category as this endpoint.
  obtain ⟨_, _, _, T, hTensor, hEval, _, _, _⟩ :=
    BimoduleFunctorHomEquivalence.{v,0} R S
  let liftDictionary (LA : ModuleCat.{v} R ⥤ A) (LD : ModuleCat.{v} S ⥤ D)
      (cA : LA ⋙ HA ≅ 𝟭 (ModuleCat.{v} R)) (uA : HA ⋙ LA ≅ 𝟭 A)
      (cD : LD ⋙ HD ≅ 𝟭 (ModuleCat.{v} S)) (uD : HD ⋙ LD ≅ 𝟭 D) :=
    (transport (CategoryTheory.Equivalence.mk HA LA uA.symm cA)
      (CategoryTheory.Equivalence.mk HD LD uD.symm cD)).trans T.symm

  refine ⟨?_, ?_⟩
  · obtain ⟨LA, ⟨cA⟩, ⟨uA⟩⟩ := reconA
    obtain ⟨LD, ⟨cD⟩, ⟨uD⟩⟩ := reconD
    exact ⟨liftDictionary LA LD cA uA cD uD⟩
  · rintro LA LD ⟨cA⟩ ⟨uA⟩ ⟨cD⟩ ⟨uD⟩
    let eA := CategoryTheory.Equivalence.mk HA LA uA.symm cA
    let eD := CategoryTheory.Equivalence.mk HD LD uD.symm cD
    let WU := transport eA eD
    refine ⟨liftDictionary LA LD cA uA cD uD, ?_, ?_⟩
    · intro F
      let W := LA ⋙ F.obj ⋙ HD
      let G := WU.functor.obj F
      let : W.Additive := G.property.1
      let evaluated := NotesProofs.General.ConcreteBimodule.wattsBimodule.{v,0} R S W
      have hB : T.inverse.obj G = evaluated := hEval G
      change ModuleCat.of S (T.inverse.obj G).carrier = W.obj (ChoiceFreeWatts.regular.{v,0} R) ∧
        ∀ r : R, HEq (fun m : (T.inverse.obj G).carrier => MulOpposite.op r • m)
          (fun x => ChoiceFreeWatts.right W r x)
      rw [hB]
      refine ⟨rfl, ?_⟩
      intro r
      exact heq_of_eq (funext (NotesProofs.wattsRight_apply W r))
    · intro B
      change (WU.inverse.obj (T.functor.obj B)).obj =
        HA ⋙ NotesProofs.General.concreteTensorFunctor.{v,0} (R := R) (S := S) B.carrier ⋙ LD
      rw [hTensor]
      rfl)

#print axioms CategoricalBimoduleDictionary
