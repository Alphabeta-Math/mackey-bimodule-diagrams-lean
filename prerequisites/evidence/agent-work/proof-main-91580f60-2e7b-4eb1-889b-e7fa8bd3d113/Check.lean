import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BalancedTensorAssociativity
import NotesProofs.RegularModuleTensorUnits
open CategoryTheory NotesProofs
universe u
#check Module.toModuleEnd
#check Functor.mapEnd
#check ModuleCat.endRingEquiv
#check ModuleCat.hom_ext
#check LinearEquiv.toModuleIso
#check NatIso.ofComponents
#check NotesBalancedAssoc.assoc_pure
#check NotesProofs.General.originalAssocNatIso
example {R : Type u} [Ring R] (r x : R) : rightAction r x = x * r := rfl
example {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    ModuleCat.isModule ((concreteTensorFunctor (R := R) (S := R) R).obj M) =
      ChoiceFreeWatts.outerModule (X := M) (fun (r x : R) => x * r)
        (fun (r a x : R) => mul_assoc a x r) := rfl
#print axioms RegularModuleTensorUnits
#print axioms NotesBalancedAssoc.assoc
