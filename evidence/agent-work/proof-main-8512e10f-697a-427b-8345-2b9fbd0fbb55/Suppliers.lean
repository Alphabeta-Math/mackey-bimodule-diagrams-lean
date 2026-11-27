import Core
import Batteries.Tactic.OpenPrivate

open MackeyDiagrams
open private index_formula rightDot leftDot pulls_left pulls_right of_pulls
  weighted_compact weighted_atLeft weighted_atRight weighted_parallel
  from Proofs.EvaluationForTwoProjections
#check index_formula
#check of_pulls
#check rightDot
#check leftDot
#check pulls_right
#check weighted_compact
#check Generator.mixedRange_eq_doubleCoset
#check Biset.Hom.transferBasis_sum
#check PlanarCode.length_eq
#check ScopedDiagram.eval_atBoundary_eq_iff
#check DoubleCoset.eq
#check Biset.Hom.transferBasis_apply
#check Biset.Hom.transfer_single
#check Subgroup.index_eq_one
#check Set.Finite.of_injective_surjOn
#check Set.Finite.of_injOn
#check Set.infinite_univ
#check Biset.pair
#check Quotient.exact
#check MackeyDiagrams.Word.eval_reorderToFrom
#check MackeyDiagrams.Word.eval_reorderFromTo
#print axioms EvaluationForTwoProjections
#print axioms CaseTwoLeftProjectionConstruction
