import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
open MackeyDiagrams
universe u
variable {U : Type u} [Group U] {K H P L : Subgroup U}
variable (α : ConjEmbedding K P) (β : ConjEmbedding H P)
variable (η : ConjEmbedding L K) (θ : ConjEmbedding L H)
private abbrev meet (p : P) := α.toHom.range ⊓ Subgroup.map (MulAut.conj p).toMonoidHom β.toHom.range
example (p : Dot (α.comp η) (β.comp θ)) :
    (α.comp η).toHom.range ≤ meet α β p.element ∧
      ((∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis α β η θ p w = z}) ↔
        ((α.comp η).toHom.range.subgroupOf (meet α β p.element)).FiniteIndex) := by
  exact (EvaluationForTwoProjections α β (ConjEmbedding.id H) η (ConjEmbedding.id L) θ).1 p |>.1 |> fun h =>
    ⟨h, (EvaluationForTwoProjections α β (ConjEmbedding.id H) η (ConjEmbedding.id L) θ).1 p |>.2.1⟩

example (p : ProjectionDot.Mixed α β η θ) (z)
    (hz : z ∈ Set.range (Generator.mixedMultiplicationBasis α β η θ p.dot)) :
    Nat.card {w // Generator.mixedMultiplicationBasis α β η θ p.dot w = z} =
      (α.comp η).toHom.range.relIndex (meet α β p.dot.element) := by
  have hinj := (Generator.mixedEquiv α β).injective
  have h := (EvaluationForTwoProjections α β (ConjEmbedding.id H) η (ConjEmbedding.id L) θ).2.1 p
    (Generator.mixedProduct α β z) |>.2 (by obtain ⟨w, rfl⟩ := hz; exact ⟨w, rfl⟩)
  refine (Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))).trans h
  exact ⟨congrArg (Generator.mixedProduct α β), fun h => hinj h⟩
