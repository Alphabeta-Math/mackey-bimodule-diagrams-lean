import Connections
import Transfers
import Batteries.Tactic.OpenPrivate

namespace CaseTwoAudit
set_option maxHeartbeats 2500000
open MackeyDiagrams
open private rightDot pulls_right pulls_mixed rightDrawing ev atLeft before
  weighted weighted_compact weighted_atLeft map_weighted composeAround
  from Proofs.EvaluationForTwoProjections

private theorem singletonTermsRight {X : Type} (x : X) :
    terms (Finsupp.single x (1 : Complex)) = [((1 : Complex), x)] := by
  classical
  have hs := Finsupp.support_single x (one_ne_zero : (1 : Complex) ≠ 0)
  unfold terms
  rw [hs]
  simp

private theorem right_unit (q : A) :
    eval (rightDrawing a b c d e f u v w [(1,first)] [(1,mid q)] [(1,last)]) =
      Qstar (overall q) := by
  classical
  apply LinearMap.ext
  intro vec
  apply Finsupp.ext
  intro i
  refine Quotient.inductionOn i (fun ⟨g,h⟩ => ?_)
  have he : rightDot a b c d e f first (mid q) last = (overall q).dot := by
    apply Dot.ext
    change q * u.toHom 1 * (1 : A)⁻¹ = q
    rw [map_one, inv_one, mul_one, mul_one]
  have hp := pulls_right a b c d e f first (mid q) last g h
  rw [he] at hp
  exact (hp vec).trans ((pulls_mixed a bc de f (overall q) _ vec).symm)

noncomputable abbrev rhs :=
  right (Finsupp.single first 1) (Finsupp.single (mid 1) 1 + Finsupp.single (mid τ) 1)
    (Finsupp.single last 1)

theorem right_sum : eval rhs = Qstar (overall 1) + Qstar (overall τ) := by
  classical
  let S := Finsupp.single (mid 1) (1 : Complex) + Finsupp.single (mid τ) 1
  let stage (x : ProjectionLabel a u d v) :=
    atLeft (LabelledDrawing.compactProjection a u d v [(1,x)]) (up w)
  let D := atLeft (LabelledDrawing.compactProjection a u d v (terms S)) (up w)
  have hD : ev D = weighted (fun x => ev (stage x)) (terms S) :=
    weighted_atLeft _ _ _ (weighted_compact a u d v (terms S))
  have hpre : DotLabel.terms (Finsupp.single first (1 : Complex)) = [(1,first)] :=
    singletonTermsRight first
  have hlast := singletonTermsRight last
  have h0 : eval rhs = eval (rightDrawing a b c d e f u v w [(1,first)] (terms S) [(1,last)]) := by
    change eval (right (Finsupp.single first 1) S (Finsupp.single last 1)) = _
    unfold right
    rw [hpre, hlast]
  rw [h0]
  let pre := (ev (atRight (down a) (LabelledDrawing.parallelUp b c u w [(1,first)]))).comp
    (ev splitBottom)
  let post := (ev mergeTop).comp
    (ev (atRight (up d) (LabelledDrawing.compactProjection v w e f [(1,last)])))
  let frame := composeAround pre post
  change frame (ev D) = _
  rw [hD, map_weighted]
  have hs (x : ProjectionLabel a u d v) :
      frame (ev (stage x)) = eval (rightDrawing a b c d e f u v w [(1,first)] [(1,x)] [(1,last)]) := rfl
  simp only [hs]
  have as_sum {I M : Type} [AddCommMonoid M] [Module Complex M]
      (f : I → M) (l : I →₀ Complex) :
      weighted f (terms l) = l.sum (fun i c => c • f i) := by
    unfold weighted terms Finsupp.sum
    rw [List.map_map, Finset.sum_map_toList]
    rfl
  rw [as_sum]
  rw [← Finsupp.linearCombination_apply Complex]
  dsimp only [S]
  rw [map_add, Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  simp only [one_smul, right_unit]

end CaseTwoAudit
