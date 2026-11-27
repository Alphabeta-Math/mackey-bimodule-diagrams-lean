import Proofs.LargestCommonMixedCrossingParabolic
import Proofs.MackeyIdentityDiagram
import MackeyDiagrams.IndexedDrawing
import MackeyDiagrams.PointwiseIndexedDrawing
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.QuotientGroup

#print axioms LargestCommonMixedCrossingParabolic
#print axioms MackeyIdentityDiagram
#check Equiv.Perm.subtypeEquivSubtypePerm
#check Equiv.Perm.Disjoint.commute
#check Equiv.Perm.mem_support_iff_of_commute
#check Equiv.Perm.support_swap
#check Equiv.swap_apply_apply
#check Finset.mem_Icc
#check Nat.card_Icc
#check Fintype.card_perm
#check Nat.card_zpowers
#check Subgroup.relIndex_mul_card
#check DoubleCoset.eq
#check Fintype.sum_equiv
#check MackeyDiagrams.Biset.Hom.ext
#check MackeyCrossingProof.compact_inclusion
#check MackeyCrossingProof.compact_projection
#check MackeyDiagrams.IndexedDrawing.eval_apply
#check MackeyDiagrams.PointwiseIndexedDrawing.evalAt_def
