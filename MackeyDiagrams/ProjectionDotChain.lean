import MackeyDiagrams.DotChain
import MackeyDiagrams.ProjectionFiber

/-! An expanded projection can keep several ordinary dots on its middle strand. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace RightCupTrace

theorem finiteAfter_congr {p q : Word K H} {a : ConjEmbedding L H}
    {d e : Diagram R (p.tensor (reverseCupWord a)) q} (he : d.eval = e.eval) :
    FiniteAfter d ↔ FiniteAfter e := by
  simp only [FiniteAfter, term, he]

theorem eval_congr {p q : Word K H} {a : ConjEmbedding L H}
    {d e : Diagram R (p.tensor (reverseCupWord a)) q} (he : d.eval = e.eval)
    (fd : FiniteAfter d) (fe : FiniteAfter e) :
    (ofFiniteAfter d fd).eval = (ofFiniteAfter e fe).eval := by
  classical
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  have hsingle : (ofFiniteAfter d fd).eval.toLinearMap (Finsupp.single x 1) =
      (ofFiniteAfter e fe).eval.toLinearMap (Finsupp.single x 1) := by
    rw [eval_single, eval_single]
    change basisSum d fd x = basisSum e fe x
    have ht (i : reverseCupUnitFiber a) : term d x i = term e x i := by
      simp only [term, he]
    have hs : (fd x).toFinset = (fe x).toFinset := by
      ext i
      rw [(fd x).mem_toFinset, (fe x).mem_toFinset]
      change term d x i ≠ 0 ↔ term e x i ≠ 0
      rw [ht]
    unfold basisSum
    rw [hs]
    exact Finset.sum_congr rfl (fun i _ => ht i)
  have hc : Finsupp.single x c = c • Finsupp.single x (1 : R) := by
    simp [Finsupp.smul_single, smul_eq_mul]
  rw [hc, map_smul, map_smul, hsingle]

end RightCupTrace

namespace ScopedDiagram

variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)

private theorem expandedProjectionChain_tail_eval (chain : DotChain (b.comp r) (a.comp l)) :
    (Diagram.mixedProjectionTailWithMiddle a b l r (chain.diagram (R := R))).eval =
      (Diagram.mixedProjectionTail (R := R) a b l r chain.product.inverse).eval := by
  have h : chain.product.inverse.inverse = chain.product := by
    apply Dot.ext
    exact inv_inv chain.product.element
  apply Diagram.eval_mixedProjectionTailWithMiddle_congr
  rw [h]
  exact chain.eval_diagram

def expandedProjectionChain (chain : DotChain (b.comp r) (a.comp l))
    (finite : ∀ x, Set.Finite {w |
      Generator.mixedMultiplicationBasis a b l r chain.product.inverse w = x}) :
    ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r)) :=
  let tail := Diagram.mixedProjectionTailWithMiddle a b l r (chain.diagram (R := R))
  .rightCupTrace (RightCupTrace.ofFiniteAfter tail
    ((RightCupTrace.finiteAfter_congr (expandedProjectionChain_tail_eval a b l r chain)).mpr
      (RightCupTrace.mixedProjectionTail_finiteAfter a b l r chain.product.inverse finite)))

theorem eval_expandedProjectionChain (chain : DotChain (b.comp r) (a.comp l))
    (finite : ∀ x, Set.Finite {w |
      Generator.mixedMultiplicationBasis a b l r chain.product.inverse w = x}) :
    (expandedProjectionChain (R := R) a b l r chain finite).eval =
      (Diagram.mixedProjection a b l r chain.product.inverse finite).eval := by
  rw [← eval_expandedMixedProjection (R := R) a b l r chain.product.inverse finite]
  exact RightCupTrace.eval_congr (expandedProjectionChain_tail_eval a b l r chain) _ _

end ScopedDiagram
end MackeyDiagrams

namespace MackeyDiagrams.ScopedDiagram

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (chain : LinearDotChain R (b.comp r) (a.comp l))

set_option maxHeartbeats 1000000 in
def expandedLinearDotProjection
    (finite : ∀ term ∈ chain.terms, ∀ x, Set.Finite {w |
      Generator.mixedMultiplicationBasis a b l r term.2.product.inverse w = x}) :
    ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r)) :=
  .linearCombination (chain.terms.attach.map fun (term : {x : R × DotChain (b.comp r) (a.comp l) // x ∈ chain.terms}) =>
    (term.val.1, expandedProjectionChain (R := R) a b l r term.val.2 (finite term.val term.property)))

theorem eval_expandedLinearDotProjection
    (finite : ∀ term ∈ chain.terms, ∀ x, Set.Finite {w |
      Generator.mixedMultiplicationBasis a b l r term.2.product.inverse w = x}) :
    (expandedLinearDotProjection a b l r chain finite).eval =
      (linearCombination (chain.terms.attach.map fun (term : {x : R × DotChain (b.comp r) (a.comp l) // x ∈ chain.terms}) =>
        (term.val.1, .ordinary (.mixedProjection a b l r term.val.2.product.inverse
          (finite term.val term.property))))).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold expandedLinearDotProjection
  rw [eval_linearCombination_apply, eval_linearCombination_apply]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change term.val.1 • ((expandedProjectionChain a b l r term.val.2
      (finite term.val term.property)).eval.toLinearMap x) =
    term.val.1 • ((Diagram.mixedProjection a b l r term.val.2.product.inverse
      (finite term.val term.property)).eval.toLinearMap x)
  rw [eval_expandedProjectionChain]

end MackeyDiagrams.ScopedDiagram
