import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Iso
import NotesProofs.ConcreteTensorFunctor

#check RingHom.op
#check Module.compHom
#check MulOpposite.instModule
#check @smul_eq_mul
#check @MulOpposite.smul_eq_mul_unop
#check MonoidAlgebra.mapDomainRingHom
#check Finsupp.mapDomain_apply
#check Finsupp.mapDomain_notin_range
#check Finsupp.mapDomain_apply_of_injective
#check ModuleCat.restrictScalars
#check Rep.resFunctor
#check Rep.ofModuleMonoidAlgebra
#check Rep.indResAdjunction
#check ChoiceFreeWatts.outerModule
#check ChoiceFreeWatts.tensorLift
#check ChoiceFreeWatts.tensorExt
#check ChoiceFreeWatts.pureBalanced
#check NotesProofs.concreteTensorFunctor
#check ModuleCat.Hom.hom
#synth Module ℤᵐᵒᵖ ℤ
