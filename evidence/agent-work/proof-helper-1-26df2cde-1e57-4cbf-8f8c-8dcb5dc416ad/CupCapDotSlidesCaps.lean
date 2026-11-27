import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.DotLabels
import MackeyDiagrams.StructuralBasis

namespace MackeyDiagrams

open Diagram

private theorem compareLabelLifts {R I J M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (f : I → M) (g : J → N) (l : M →ₗ[R] P) (r : N →ₗ[R] P) (rev : I → J)
    (agree : ∀ i, l (f i) = r (g (rev i))) (z : I →₀ R) :
    l (freeLift R f z) = r (freeLift R g (Finsupp.mapDomain rev z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [Finsupp.mapDomain_add, hx, hy]
  | single i c => simp [Finsupp.mapDomain_single, agree]

variable {U : Type*} [Group U] {H G : Subgroup U} {a b : ConjEmbedding H G}

private theorem traceBasis_slide (d : Dot a b) (w : G) :
    Generator.traceBasis Complex b (d.element⁻¹ * w) =
      Generator.traceBasis Complex a (w * d.element⁻¹) := by
  have samePreimage (h : H) :
      a.toHom h = w * d.element⁻¹ ↔ b.toHom h = d.element⁻¹ * w := by
    have ha := d.intertwines h
    constructor
    · intro hw
      calc
        b.toHom h = d.element⁻¹ * (a.toHom h * d.element) := by rw [ha]; simp
        _ = d.element⁻¹ * w := by rw [hw]; simp [mul_assoc]
    · intro hw
      calc
        a.toHom h = (d.element * b.toHom h) * d.element⁻¹ := by rw [← ha]; simp
        _ = w * d.element⁻¹ := by rw [hw]; simp
  by_cases image : ∃ h : H, a.toHom h = w * d.element⁻¹
  · obtain ⟨h, hA⟩ := image
    have hB := (samePreimage h).mp hA
    rw [← hA, ← hB, Generator.traceBasis_image, Generator.traceBasis_image]
  · have outsideB : ¬ ∃ h : H, b.toHom h = d.element⁻¹ * w := by
      rintro ⟨h, hB⟩
      exact image ⟨h, (samePreimage h).mpr hB⟩
    rw [Generator.traceBasis_outside Complex b _ outsideB,
      Generator.traceBasis_outside Complex a _ image]

private theorem multiplicationCap_label_basis (z : DotLabel Complex a b) (x y : G) :
    let zDual : DotLabel Complex b a := Finsupp.mapDomain Dot.inverse z
    (multiplicationCap (R := Complex) b).eval.toLinearMap
        (Biset.pairLinear Complex (Biset.induction b) (Biset.restriction b)
          ((linearUpDot z).eval.toLinearMap (Finsupp.single x 1)) (Finsupp.single y 1)) =
      (multiplicationCap (R := Complex) a).eval.toLinearMap
        (Biset.pairLinear Complex (Biset.induction a) (Biset.restriction a)
          (Finsupp.single x 1) ((linearDownDot zDual).eval.toLinearMap (Finsupp.single y 1))) := by
  dsimp only
  rw [eval_linearUpDot_apply, eval_linearDownDot_apply]
  let l := ((multiplicationCap (R := Complex) b).eval.toLinearMap).comp
    ((Biset.pairLinear Complex (Biset.induction b) (Biset.restriction b)).flip (Finsupp.single y 1))
  let r := ((multiplicationCap (R := Complex) a).eval.toLinearMap).comp
    (Biset.pairLinear Complex (Biset.induction a) (Biset.restriction a) (Finsupp.single x 1))
  apply compareLabelLifts _ _ l r Dot.inverse _ z
  intro d
  simp only [l, r, LinearMap.comp_apply, LinearMap.flip_apply]
  rw [eval_upDot_single (R := Complex) d x 1,
    eval_downDot_single (R := Complex) d.inverse y 1,
    Biset.pairLinear_single, Biset.pairLinear_single, one_mul,
    eval_multiplicationCap_single, eval_multiplicationCap_single]
  simp only [Dot.inverse, inv_inv, mul_assoc]

private theorem traceCap_label_basis (z : DotLabel Complex a b) (x y : G) :
    let zDual : DotLabel Complex b a := Finsupp.mapDomain Dot.inverse z
    (traceCap (R := Complex) b).eval.toLinearMap
        (Biset.pairLinear Complex (Biset.restriction b) (Biset.induction b)
          ((linearDownDot z).eval.toLinearMap (Finsupp.single x 1)) (Finsupp.single y 1)) =
      (traceCap (R := Complex) a).eval.toLinearMap
        (Biset.pairLinear Complex (Biset.restriction a) (Biset.induction a)
          (Finsupp.single x 1) ((linearUpDot zDual).eval.toLinearMap (Finsupp.single y 1))) := by
  dsimp only
  rw [eval_linearDownDot_apply, eval_linearUpDot_apply]
  let l := ((traceCap (R := Complex) b).eval.toLinearMap).comp
    ((Biset.pairLinear Complex (Biset.restriction b) (Biset.induction b)).flip (Finsupp.single y 1))
  let r := ((traceCap (R := Complex) a).eval.toLinearMap).comp
    (Biset.pairLinear Complex (Biset.restriction a) (Biset.induction a) (Finsupp.single x 1))
  apply compareLabelLifts _ _ l r Dot.inverse _ z
  intro d
  simp only [l, r, LinearMap.comp_apply, LinearMap.flip_apply]
  rw [eval_downDot_single (R := Complex) d x 1,
    eval_upDot_single (R := Complex) d.inverse y 1,
    Biset.pairLinear_single, Biset.pairLinear_single, one_mul,
    eval_traceCap_single, eval_traceCap_single]
  simp only [Dot.inverse, one_smul]
  rw [mul_assoc, ← mul_assoc x y]
  exact traceBasis_slide d (x * y)

set_option maxHeartbeats 800000 in
theorem multiplicationCap_dotSlide (z : DotLabel Complex a b) :
    let zDual : DotLabel Complex b a := Finsupp.mapDomain Dot.inverse z
    ((z.upDrawing.horizontal (.ordinary (Diagram.id (.down b)))).vertical
      (.ordinary (multiplicationCap b))).interpret.eval =
    (((LabelledDrawing.ordinary (Diagram.id (.up a))).horizontal zDual.downDrawing).vertical
      (.ordinary (multiplicationCap a))).interpret.eval := by
  intro zDual
  change (((linearUpDot z).eval.horizontal (Diagram.id (.down b)).eval).vertical
      (multiplicationCap b).eval) =
    (((Diagram.id (.up a)).eval.horizontal (linearDownDot zDual).eval).vertical
      (multiplicationCap a).eval)
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro q c
  refine Quotient.inductionOn q (fun ⟨x, y⟩ => ?_)
  change (multiplicationCap b).eval.toLinearMap
      (((linearUpDot z).eval.horizontal (Diagram.id (.down b)).eval).toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Biset.restriction b) x y) c)) =
    (multiplicationCap a).eval.toLinearMap
      (((Diagram.id (.up a)).eval.horizontal (linearDownDot zDual).eval).toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Biset.restriction b) x y) c))
  rw [Biset.Hom.horizontal_single, Biset.Hom.horizontal_single, map_smul, map_smul,
    eval_id_apply, eval_id_apply]
  exact congrArg (c • ·) (multiplicationCap_label_basis z x y)

set_option maxHeartbeats 800000 in
theorem traceCap_dotSlide (z : DotLabel Complex a b) :
    let zDual : DotLabel Complex b a := Finsupp.mapDomain Dot.inverse z
    ((z.downDrawing.horizontal (.ordinary (Diagram.id (.up b)))).vertical
      (.ordinary (traceCap b))).interpret.eval =
    (((LabelledDrawing.ordinary (Diagram.id (.down a))).horizontal zDual.upDrawing).vertical
      (.ordinary (traceCap a))).interpret.eval := by
  intro zDual
  change (((linearDownDot z).eval.horizontal (Diagram.id (.up b)).eval).vertical
      (traceCap b).eval) =
    (((Diagram.id (.down a)).eval.horizontal (linearUpDot zDual).eval).vertical
      (traceCap a).eval)
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro q c
  refine Quotient.inductionOn q (fun ⟨x, y⟩ => ?_)
  change (traceCap b).eval.toLinearMap
      (((linearDownDot z).eval.horizontal (Diagram.id (.up b)).eval).toLinearMap
        (Finsupp.single ((Biset.restriction a).pair (Biset.induction b) x y) c)) =
    (traceCap a).eval.toLinearMap
      (((Diagram.id (.down a)).eval.horizontal (linearUpDot zDual).eval).toLinearMap
        (Finsupp.single ((Biset.restriction a).pair (Biset.induction b) x y) c))
  rw [Biset.Hom.horizontal_single, Biset.Hom.horizontal_single, map_smul, map_smul,
    eval_id_apply, eval_id_apply]
  exact congrArg (c • ·) (traceCap_label_basis z x y)

end MackeyDiagrams
