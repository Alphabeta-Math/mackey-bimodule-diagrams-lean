import MackeyDiagrams.LinearDots

/-! Linear dot labels compose by taking all ordered products of supported dots. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace Dot

noncomputable def linearProduct {a b c : ConjEmbedding H K}
    (x : Dot a b →₀ R) (y : Dot b c →₀ R) : Dot a c →₀ R :=
  x.sum fun d r => y.sum fun e s => Finsupp.single (d.vertical e) (r * s)

end Dot

namespace Diagram

private theorem eval_weightedDots {ι : Type u} {p q : Word K H}
    (labels : ι →₀ R) (draw : ι → Diagram R p q) (z : p.basis.carrier →₀ R) :
    (finiteSum (labels.support.toList.map fun d => scale (labels d) (draw d))).eval.toLinearMap z =
      freeLift R (fun d => (draw d).eval.toLinearMap z) labels := by
  classical
  rw [eval_finiteSum, List.map_map]
  change (labels.support.val.toList.map (fun d => labels d • (draw d).eval.toLinearMap z)).sum = _
  rw [Multiset.sum_map_toList]
  change labels.sum (fun d r => r • (draw d).eval.toLinearMap z) = _
  rw [freeLift, Finsupp.lsum_apply]
  rfl

theorem eval_linearUpDot_apply {a b : ConjEmbedding H K}
    (labels : Dot a b →₀ R) (z : K →₀ R) :
    (linearUpDot labels).eval.toLinearMap z =
      freeLift R (fun (d : Dot a b) => (upDot (R := R) d).eval.toLinearMap z) labels :=
  eval_weightedDots labels upDot z

theorem eval_linearDownDot_apply {a b : ConjEmbedding H K}
    (labels : Dot a b →₀ R) (z : K →₀ R) :
    (linearDownDot labels).eval.toLinearMap z =
      freeLift R (fun (d : Dot a b) => (downDot (R := R) d).eval.toLinearMap z) labels :=
  eval_weightedDots labels downDot z

set_option maxHeartbeats 1000000 in
private theorem linearLabels_comp {ι κ τ : Type u}
    {p q s : Word K H}
    (f : ι → Diagram R p q) (g : κ → Diagram R q s) (h : τ → Diagram R p s)
    (compLabel : ι → κ → τ)
    (hComp : ∀ i j, ((f i).vertical (g j)).eval = (h (compLabel i j)).eval)
    (x : ι →₀ R) (y : κ →₀ R) (z : p.basis.carrier →₀ R) :
    (finiteSum (y.support.toList.map fun j => scale (y j) (g j))).eval.toLinearMap
      ((finiteSum (x.support.toList.map fun i => scale (x i) (f i))).eval.toLinearMap z) =
    freeLift R (fun t => (h t).eval.toLinearMap z)
      (x.sum fun i r => y.sum fun j s => Finsupp.single (compLabel i j) (r * s)) := by
  let G := (finiteSum (y.support.toList.map fun j => scale (y j) (g j))).eval.toLinearMap
  rw [eval_weightedDots x f]
  change G (freeLift R (fun i => (f i).eval.toLinearMap z) x) = _
  conv_lhs => rw [freeLift, Finsupp.lsum_apply]
  simp only [Finsupp.sum, LinearMap.toSpanSingleton_apply, map_sum, map_smul, freeLift_single]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [G]
  rw [eval_weightedDots]
  rw [freeLift, Finsupp.lsum_apply]
  simp only [Finsupp.sum, LinearMap.toSpanSingleton_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun m : Biset.Hom R p.basis s.basis =>
    (x i * y j) • m.toLinearMap z) (hComp i j)

theorem linearUpDot_vertical {a b c : ConjEmbedding H K}
    (x : Dot a b →₀ R) (y : Dot b c →₀ R) :
    ((linearUpDot x).vertical (linearUpDot y)).eval =
      (linearUpDot (Dot.linearProduct x y)).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (linearUpDot y).eval.toLinearMap ((linearUpDot x).eval.toLinearMap z) = _
  change K →₀ R at z
  rw [eval_linearUpDot_apply (Dot.linearProduct x y) z]
  exact linearLabels_comp _ _ _ Dot.vertical upDot_vertical x y z

theorem linearDownDot_vertical {a b c : ConjEmbedding H K}
    (x : Dot a b →₀ R) (y : Dot b c →₀ R) :
    ((linearDownDot x).vertical (linearDownDot y)).eval =
      (linearDownDot (Dot.linearProduct x y)).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (linearDownDot y).eval.toLinearMap ((linearDownDot x).eval.toLinearMap z) = _
  change K →₀ R at z
  rw [eval_linearDownDot_apply (Dot.linearProduct x y) z]
  exact linearLabels_comp _ _ _ Dot.vertical downDot_vertical x y z

end Diagram
end MackeyDiagrams
