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

universe u

private theorem compareCaps {R : Type*} {K L J : Type u} [CommSemiring R]
    [Group K] [Group L] [Group J]
    {X X₁ X₂ : Biset K L} {Y Y₁ Y₂ : Biset L J} {P : Biset K J}
    (f₁ : Biset.Hom R X X₁) (g₁ : Biset.Hom R Y Y₁) (cap₁ : Biset.Hom R (X₁.tensor Y₁) P)
    (f₂ : Biset.Hom R X X₂) (g₂ : Biset.Hom R Y Y₂) (cap₂ : Biset.Hom R (X₂.tensor Y₂) P)
    (agree : ∀ x y, cap₁.toLinearMap
        (Biset.pairLinear R X₁ Y₁
          (f₁.toLinearMap (Finsupp.single x 1)) (g₁.toLinearMap (Finsupp.single y 1))) =
      cap₂.toLinearMap
        (Biset.pairLinear R X₂ Y₂
          (f₂.toLinearMap (Finsupp.single x 1)) (g₂.toLinearMap (Finsupp.single y 1)))) :
    (f₁.horizontal g₁).vertical cap₁ = (f₂.horizontal g₂).vertical cap₂ := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro q c
  refine Quotient.inductionOn q (fun ⟨x, y⟩ => ?_)
  change cap₁.toLinearMap ((f₁.horizontal g₁).toLinearMap (Finsupp.single (X.pair Y x y) c)) =
    cap₂.toLinearMap ((f₂.horizontal g₂).toLinearMap (Finsupp.single (X.pair Y x y) c))
  rw [Biset.Hom.horizontal_single, Biset.Hom.horizontal_single, map_smul, map_smul]
  exact congrArg (c • ·) (agree x y)

private theorem drawingVertical_eval {R : Type*} [CommSemiring R]
    {A B : Subgroup U} {p q t : Word A B}
    (f : LabelledDrawing R p q) (g : LabelledDrawing R q t) :
    (f.vertical g).interpret.eval = f.interpret.eval.vertical g.interpret.eval := rfl

private theorem drawingHorizontal_eval {R : Type*} [CommSemiring R]
    {A B C : Subgroup U} {p p' : Word A B} {q q' : Word B C}
    (f : LabelledDrawing R p p') (g : LabelledDrawing R q q') :
    (f.horizontal g).interpret.eval = f.interpret.eval.horizontal g.interpret.eval := rfl

private theorem drawingOrdinary_eval {R : Type*} [CommSemiring R]
    {A B : Subgroup U} {p q : Word A B} (f : Diagram R p q) :
    (LabelledDrawing.ordinary f).interpret.eval = f.eval := rfl

theorem multiplicationCap_dotSlide (z : DotLabel Complex a b) :
    let zDual : DotLabel Complex b a := Finsupp.mapDomain Dot.inverse z
    ((z.upDrawing.horizontal (.ordinary (Diagram.id (.down b)))).vertical
      (.ordinary (multiplicationCap b))).interpret.eval =
    (((LabelledDrawing.ordinary (Diagram.id (.up a))).horizontal zDual.downDrawing).vertical
      (.ordinary (multiplicationCap a))).interpret.eval := by
  intro zDual
  simp only [drawingVertical_eval, drawingHorizontal_eval, drawingOrdinary_eval,
    DotLabel.eval_upDrawing, DotLabel.eval_downDrawing]
  apply compareCaps
  intro x y
  exact multiplicationCap_label_basis z x y

theorem traceCap_dotSlide (z : DotLabel Complex a b) :
    let zDual : DotLabel Complex b a := Finsupp.mapDomain Dot.inverse z
    ((z.downDrawing.horizontal (.ordinary (Diagram.id (.up b)))).vertical
      (.ordinary (traceCap b))).interpret.eval =
    (((LabelledDrawing.ordinary (Diagram.id (.down a))).horizontal zDual.upDrawing).vertical
      (.ordinary (traceCap a))).interpret.eval := by
  intro zDual
  simp only [drawingVertical_eval, drawingHorizontal_eval, drawingOrdinary_eval,
    DotLabel.eval_upDrawing, DotLabel.eval_downDrawing]
  apply compareCaps
  intro x y
  exact traceCap_label_basis z x y

set_option maxHeartbeats 800000 in
example : ∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  ∀ z : MackeyDiagrams.DotLabel Complex a b,
    let zDual : MackeyDiagrams.DotLabel Complex b a :=
      Finsupp.mapDomain MackeyDiagrams.Dot.inverse z
    let rightZ := MackeyDiagrams.DotLabel.upDrawing z
    let leftZ := MackeyDiagrams.DotLabel.downDrawing zDual
    let rightDual := MackeyDiagrams.DotLabel.upDrawing zDual
    let leftDual := MackeyDiagrams.DotLabel.downDrawing z
    let idUpA := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
    let idUpB := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up b))
    let idDownA := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down a))
    let idDownB := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down b))
    let multiplicationLeft := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal rightZ idDownB)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.multiplicationCap b))
    let multiplicationRight := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal idUpA leftZ)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.multiplicationCap a))
    let traceLeft := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal leftDual idUpB)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.traceCap b))
    let traceRight := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal idDownA rightDual)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.traceCap a))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret multiplicationLeft) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret multiplicationRight) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret traceLeft) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret traceRight) := by
  intro U _ H G α β hα hβ a b z
  exact ⟨multiplicationCap_dotSlide z, traceCap_dotSlide z⟩

#print axioms multiplicationCap_dotSlide
#print axioms traceCap_dotSlide

end MackeyDiagrams
