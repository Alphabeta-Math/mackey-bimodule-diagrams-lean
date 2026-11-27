import MackeyDiagrams
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks
#check Finset.biUnion
#check Finset.mem_biUnion
#check Equiv.swap_apply_def
#check Equiv.Perm.ofSubtype_swap_eq
#check SubmonoidClass.swap_mem_trans
#check Finset.Subset.antisymm
#check Finset.eq_of_subset_of_card_le
#check Finset.card_le_one
#check Finset.card_le_one_iff
#check Finset.image_insert
#check Finset.image_singleton
#check SimpleGraph.fromRel_adj
#check SimpleGraph.ConnectedComponent.exact
#check Finset.Nonempty.mono
#check Finset.disjoint_left
#check Finset.iSup_finset_image
#check Finset.coe_image
#check Finset.mem_coe
#check Finset.univ
#check Finset.mem_univ
#check SimpleGraph.Walk.nil
#check SimpleGraph.Walk.cons
example (i : Fin 4) : True := by
  fin_cases i <;> trivial
