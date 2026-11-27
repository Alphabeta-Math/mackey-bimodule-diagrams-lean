import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.AdditiveFunctorsAndBiproducts

open CategoryTheory CategoryTheory.Limits
#check AdditiveFunctorsAndBiproducts
#check Adjunction.isEquivalencePreservesLimits
#check Adjunction.isEquivalence_preservesColimits
#check Adjunction.hasColimitsOfShape_of_equivalence
#check Functor.preservesProjectiveObjects_of_isEquivalence
#check Functor.PreservesProjectiveObjects.projective_obj
#check IsSeparator.of_equivalence
#check ShortComplex.Exact.map
#check Adjunction.homAddEquiv
#check Adjunction.homEquiv_naturality_right
#check Equivalence.toAdjunction
#check IsZero.isTerminal
#check IsTerminal.isZero
#check IsTerminal.isZeroOfHasZero
#check IsTerminal.isZero_iff
#check IsTerminal.isZero
#check IsTerminal.isZero_of_zero
#check isTerminalOfPreserves
#check PreservesTerminal.iso
#check IsZero.of_iso
#check IsZero.of_isTerminal
#check PreservesCoproduct.iso
#check map_ι_comp_inv_sigmaComparison
#check Iso.homCongr
#check Iso.homToEquiv
#check Iso.homFromEquiv
#check DFinsupp.mapRange.addEquiv
#check DFinsupp.mapRange.addEquiv_apply
#check DFinsupp.mapRange_single
#check Function.Bijective.of_comp_iff
#check Function.Bijective.of_comp_iff'
#check Function.Bijective.of_comp_left
#check Function.Bijective.of_comp_right
#print HasCoproducts

universe u₁ u₂ v₁ v₂ w
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D] (e : C ≌ D)
#synth PreservesFiniteLimits e.functor
#synth PreservesFiniteColimits e.functor
#synth PreservesFiniteProducts e.functor
#synth PreservesFiniteCoproducts e.functor
#synth e.functor.PreservesProjectiveObjects
example [HasCoproducts.{w} C] : HasCoproducts.{w} D :=
  ⟨fun _ => Adjunction.hasColimitsOfShape_of_equivalence e.inverse⟩
