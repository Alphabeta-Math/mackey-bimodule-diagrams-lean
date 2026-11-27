import Mathlib.RepresentationTheory.Induced
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Proofs.ConjugationEmbeddingCentralizerCoset
import Proofs.ModuleTensorUniversalProperty
import MackeyDiagrams

open CategoryTheory
#check RingHom.op
#check LinearEquiv.toModuleIso
#check ModuleCat.Hom.hom
#check ModuleCat.comp_apply
#check ModuleCat.hom_ext
#check ModuleCat.ofHom
#check Equivalence.toAdjunction
#check Rep.equivalenceModuleMonoidAlgebra
#check MackeyDiagrams.Biset.actLinear_mul
#check MackeyDiagrams.Biset.actLinear_one
#check MonoidAlgebra.lhom_ext
#check MonoidAlgebra.algHom_ext
#check MonoidAlgebra.mapDomainAlgHom
#check MonoidAlgebra.coeff_smul
#check MonoidAlgebra.smul_mul
#check MonoidAlgebra.mul_smul
#check DFunLike.congr_fun
#check NatIso.ofComponents
#check Adjunction.unit_naturality
#check Adjunction.homEquiv_unit
#check Adjunction.ofNatIsoRight
#check MackeyDiagrams.Biset.Hom.horizontal_pairLinear
#print axioms ConjugationEmbeddingCentralizerCoset
#print axioms ModuleTensorUniversalProperty
