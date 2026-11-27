universe u

namespace MixedCrossingCompositesAux

open MackeyDiagrams

-- The typed singleton labels have the ordinary crossing evaluations.
section Drawings

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))
variable (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z})

private theorem multiplication_eval :
    (LabelledDrawing.mixedMultiplication (R := Complex) a b l r [(1, d)]).interpret.eval =
      (Diagram.mixedMultiplication (R := Complex) a b l r d).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval]

private theorem projection_eval :
    (LabelledDrawing.compactProjection (R := Complex) a b l r [(1, ⟨d, hf⟩)]).interpret.eval =
      (Diagram.mixedProjection (R := Complex) a b l r d hf).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval]

end Drawings

private theorem fiberCard {X Y : Type*} (f : X → Y) (y : Y)
    (hf : Set.Finite {x | f x = y}) (S : Finset X)
    (hS : ∀ x, x ∈ S ↔ f x = y) :
    Nat.card {x | f x = y} = S.card := by
  have h : hf.toFinset = S := Finset.ext fun x => hf.mem_toFinset.trans (hS x).symm
  let := hf.fintype
  rw [Nat.card_eq_fintype_card, ← hf.card_toFinset, h]

private theorem sum_single_apply {X : Type*} [DecidableEq X] (S : Finset X) (w : X) :
    (S.sum (fun x => Finsupp.single x (1 : Complex))) w =
      if w ∈ S then 1 else 0 := by
  classical
  change (Finsupp.lapply w : (X →₀ Complex) →ₗ[Complex] Complex) _ = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply, Finset.sum_ite_eq']

end MixedCrossingCompositesAux
