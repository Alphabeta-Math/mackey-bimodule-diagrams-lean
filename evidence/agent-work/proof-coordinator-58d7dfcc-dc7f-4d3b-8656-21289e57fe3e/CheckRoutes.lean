import Proofs.CommonMackeyIntersectionSum
import Proofs.MackeyIdentityDiagram
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.ExpansionIntoRightDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.ExtremalParabolicsOfFiniteGroup
import MackeyDiagrams.IndexedDrawing
import MackeyDiagrams.PointwiseIndexedDrawing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.QuotientGroup

#check MackeyDiagrams.IndexedDrawing.shape
#check MackeyDiagrams.IndexedDrawing.eval_apply
#print axioms MackeyDiagrams.IndexedDrawing.eval
#check MackeyDiagrams.PointwiseIndexedDrawing.shape
#check MackeyDiagrams.PointwiseIndexedDrawing.evalAt_eq_finsum
#check MackeyDiagrams.PointwiseIndexedDrawing.eval_apply
#print axioms MackeyDiagrams.PointwiseIndexedDrawing.eval
#print axioms CommonMackeyIntersectionSum
#check Fin.sum_univ_fun_getElem
#check List.sum_ofFn
#check Nat.card_zpowers
#check Nat.card_prod
#check Subgroup.relIndex_mul_card
#check Subgroup.relIndex_ne_zero
#check Subgroup.relIndex_le_of_le_left
#check Subgroup.topEquiv
#check Equiv.swap_apply_apply
#check MonoidHom.map_closure
#check MackeyDiagrams.ConjEmbedding.ext
#check Equiv.swap_mul_self
#check List.get_mem
#check List.getElem_mem
#check MackeyDiagrams.Biset.associateBasisEquiv
#check MackeyDiagrams.Biset.Hom.horizontal_id
