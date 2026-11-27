import MackeyDiagrams
import Proofs.ParabolicExtremalOutsideRestrictionRegions
import Proofs.ParabolicCaseTwoProjectionFiberIndices

open MackeyDiagrams

open private crossingFiberSize from Proofs.ParabolicCaseTwoProjectionFiberIndices
open private leftBound conj from Proofs.ParabolicExtremalOutsideRestrictionRegions
#check crossingFiberSize
#check leftBound
#check conj
#check Equiv.Perm.ofSubtype_subtypePerm
#check Equiv.Perm.swap_induction_on
#check Equiv.Perm.ofSubtype_swap_eq
#check SubmonoidClass.swap_mem_trans
#check Subgroup.map_inf
#check Subgroup.map_inf_of_injective
#check Subgroup.relIndex_map_map_of_injective
#check Subgroup.coe_subtype
#check Subgroup.subtype_injective
#check Equiv.Perm.permCoe
#check Equiv.swap_comm
#check Equiv.swap_apply_left
#check Equiv.swap_apply_right
#check Equiv.swap_apply_of_ne_of_ne
#check Equiv.Perm.smul_def
#check MulAction.mem_stabilizer_iff
#check MulAction.mem_orbit_iff
#check MulAction.orbitEquivQuotientStabilizer
#check Subgroup.index_eq_card
#check Fintype.card_coe
#check Finset.card_erase_of_mem
#check Equiv.subtypeEquivRight
#check Finset.mem_erase
#check Finset.mem_insert
#check Finset.mem_singleton
#check Set.Finite.of_finite
#check Equiv.Perm.ofSubtype
