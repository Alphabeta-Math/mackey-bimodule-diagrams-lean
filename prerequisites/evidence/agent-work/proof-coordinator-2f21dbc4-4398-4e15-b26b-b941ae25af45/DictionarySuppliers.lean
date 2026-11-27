import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import NotesProofs.ReconstructionFromSmallProjectiveGenerator
import NotesProofs.BimoduleFunctorHomEquivalence
import NotesProofs.AbelianEquivalencesPreserveFunctorHypotheses
import NotesProofs.TensorDictionaryCompositionAndIdentities
import NotesProofs.WattsActions

open CategoryTheory CategoryTheory.Limits
universe uA uD v

#check Equivalence.mk
#check Equivalence.trans
#check ObjectProperty.lift
#check ObjectProperty.isoMk
#check ObjectProperty.hom_ext
#check ObjectProperty.fullyFaithfulι
#check Functor.FullyFaithful.preimageIso
#check NatIso.ofComponents
#check diagramIsoParallelPair
#check preservesColimit_of_iso_diagram
#check Functor.assoc
#check NotesProofs.wattsRight_apply.{v,v,0,v}
#check @BimoduleFunctorHomEquivalence.{v,0}
#check @ReconstructionFromSmallProjectiveGenerator
#check @AbelianEquivalencesPreserveFunctorHypotheses

section
variable (A : Type uA) (D : Type uD) [Category.{v} A] [Category.{v} D]
  [Abelian A] [Abelian D] (R S : Type v) [Ring R] [Ring S]
variable (eA : A ≌ ModuleCat.{v} R) (eD : D ≌ ModuleCat.{v} S)

#check ((eA.congrLeft (E := D)).trans (eD.congrRight (E := ModuleCat.{v} R)) :
  (A ⥤ D) ≌ (ModuleCat.{v} R ⥤ ModuleCat.{v} S))

#synth PreservesFiniteColimits eA.functor
#synth PreservesFiniteColimits eA.inverse
#synth PreservesFiniteColimits eD.functor
#synth PreservesFiniteColimits eD.inverse

variable (I : Type v)
#synth PreservesColimitsOfShape (Discrete I) eA.functor
#synth PreservesColimitsOfShape (Discrete I) eA.inverse
#synth PreservesColimitsOfShape (Discrete I) eD.functor
#synth PreservesColimitsOfShape (Discrete I) eD.inverse

variable (F : A ⥤ D) [F.Additive]
variable [∀ {X Y : A} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F]
variable [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
#check Functor.preservesFiniteColimits_of_preservesCokernels F
#synth PreservesColimitsOfShape (Discrete I) (eA.inverse ⋙ F ⋙ eD.functor)
#check (letI : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesCokernels
  (inferInstance : PreservesFiniteColimits (eA.inverse ⋙ F ⋙ eD.functor)))
#check (AbelianEquivalencesPreserveFunctorHypotheses eA.symm).1
#check (AbelianEquivalencesPreserveFunctorHypotheses eD).1

variable (G : NotesProofs.General.ConcreteBimodule.GoodFunctors.{v,0} R S)
variable [PreservesFiniteColimits G.obj]
variable [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G.obj]
variable {X Y : A} (f : X ⟶ Y)
#synth PreservesColimit (parallelPair f 0) (eA.functor ⋙ G.obj ⋙ eD.inverse)
#synth PreservesColimitsOfShape (Discrete I) (eA.functor ⋙ G.obj ⋙ eD.inverse)
end
