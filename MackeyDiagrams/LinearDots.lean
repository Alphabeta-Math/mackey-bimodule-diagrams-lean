import MackeyDiagrams.Identities

/-! Finite linear combinations of admissible dots are typed diagrams. -/

namespace MackeyDiagrams.Diagram

universe u v

variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

def finiteSum {p q : Word K H} (ds : List (Diagram R p q)) : Diagram R p q :=
  ds.foldr Diagram.add (Diagram.zero p q)

theorem eval_finiteSum {p q : Word K H}
    (ds : List (Diagram R p q)) (z : p.basis.carrier →₀ R) :
    (finiteSum ds).eval.toLinearMap z = (ds.map (fun d => d.eval.toLinearMap z)).sum := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    change d.eval.toLinearMap z + (finiteSum ds).eval.toLinearMap z =
      d.eval.toLinearMap z + (ds.map (fun e => e.eval.toLinearMap z)).sum
    rw [ih]

variable {a b : ConjEmbedding H K}

noncomputable def linearUpDot (c : Dot a b →₀ R) : Diagram R (.up a) (.up b) :=
  finiteSum (c.support.toList.map fun d => Diagram.scale (c d) (.upDot d))

noncomputable def linearDownDot (c : Dot a b →₀ R) : Diagram R (.down a) (.down b) :=
  finiteSum (c.support.toList.map fun d => Diagram.scale (c d) (.downDot d))

theorem eval_linearUpDot_single (c : Dot a b →₀ R) (x : K) :
    (linearUpDot c).eval.toLinearMap (Finsupp.single x 1) =
      (c.support.toList.map (fun d => c d • Finsupp.single (x * d.element) 1)).sum := by
  rw [linearUpDot, eval_finiteSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  change c d • (upDot (R := R) d).eval.toLinearMap (Finsupp.single x 1) =
    c d • Finsupp.single (x * d.element) 1
  rw [eval_upDot_single (R := R) d x 1]

theorem eval_linearDownDot_single (c : Dot a b →₀ R) (x : K) :
    (linearDownDot c).eval.toLinearMap (Finsupp.single x 1) =
      (c.support.toList.map (fun d => c d • Finsupp.single (d.element⁻¹ * x) 1)).sum := by
  rw [linearDownDot, eval_finiteSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  change c d • (downDot (R := R) d).eval.toLinearMap (Finsupp.single x 1) =
    c d • Finsupp.single (d.element⁻¹ * x) 1
  rw [eval_downDot_single (R := R) d x 1]

end MackeyDiagrams.Diagram
