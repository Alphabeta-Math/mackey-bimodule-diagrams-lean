import MackeyDiagrams.LinearDotComposition
import MackeyDiagrams.ParallelDown
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! Contract two consecutive merge–dot–split expressions. -/

namespace MackeyDiagrams.Biset.Hom

universe u v

variable {K H : Type u} [Group K] [Group H] {R : Type v} [CommSemiring R]
variable {X Y Z A B C : Biset K H}

theorem merge_dot_split_comp
    (merge₀ : Hom R X A) (lower : Hom R A B) (split₁ : Hom R B Y)
    (merge₁ : Hom R Y B) (upper : Hom R B C) (split₂ : Hom R C Z)
    (product : Hom R A C)
    (middle : split₁.vertical merge₁ = id B) (dots : lower.vertical upper = product) :
    ((merge₀.vertical lower).vertical split₁).vertical
      ((merge₁.vertical upper).vertical split₂) =
      (merge₀.vertical product).vertical split₂ := by
  simp only [vertical_assoc]
  rw [← vertical_assoc split₁ merge₁, middle, id_vertical,
    ← vertical_assoc lower upper, dots]

end MackeyDiagrams.Biset.Hom

namespace MackeyDiagrams.Diagram

universe u v

variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

theorem eval_downDot_groupAlgebra {a b : ConjEmbedding H K}
    (d : Dot a b) (x : MonoidAlgebra R K) :
    (downDot (R := R) d).eval.toLinearMap x.coeff =
      (MonoidAlgebra.single d.element⁻¹ 1 * x).coeff := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [mul_add, hx, hy]
  | single k c =>
    change (downDot (R := R) d).eval.toLinearMap (Finsupp.single k c) =
      (MonoidAlgebra.single d.element⁻¹ 1 * MonoidAlgebra.single k c).coeff
    rw [eval_downDot_single (R := R) d k c, MonoidAlgebra.single_mul_single, one_mul]
    rfl

end MackeyDiagrams.Diagram
