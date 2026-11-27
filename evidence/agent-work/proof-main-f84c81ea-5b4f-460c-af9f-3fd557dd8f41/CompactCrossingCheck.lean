import MackeyDiagrams
import Proofs.LargestCommonMixedCrossingParabolic

open MackeyDiagrams

universe u

example {U : Type u} [Group U] {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
    (r : ConjEmbedding L H) (d : Dot (a.comp l) (b.comp r))
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (LabelledDrawing.vertical (LabelledDrawing.compactProjection a b l r [(1, ⟨d, hf⟩)])
      (LabelledDrawing.mixedMultiplication a b l r [(1, d)])).interpret.eval =
    (Diagram.vertical (Diagram.mixedProjection (R := Complex) a b l r d hf)
      (Diagram.mixedMultiplication a b l r d)).eval := by
  exact congrArg₂ (fun p i => p.vertical i)
    (MackeyCrossingProof.compact_projection a b l r d hf)
    (MackeyCrossingProof.compact_inclusion a b l r d)

#check DoubleCoset.eq
#check Fintype.card_perm
#check Subgroup.relIndex_mul_card
#check Equiv.Perm.mem_support_iff_of_commute
