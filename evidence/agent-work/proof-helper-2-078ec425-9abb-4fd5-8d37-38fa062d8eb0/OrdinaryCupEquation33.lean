import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.DotLabels
import MackeyDiagrams.OrdinaryCupTrace

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {H G : Subgroup U}
variable {R : Type v} [CommSemiring R]
variable {a b : ConjEmbedding H G}

private theorem ordinaryCup_pair (d : Dot a b) (h : H) :
    (Biset.restriction b).pair (Biset.induction a) (d.element⁻¹ * a.toHom h) 1 =
      (Biset.restriction b).pair (Biset.induction a) (b.toHom h) d.element⁻¹ := by
  have intertwines : b.toHom h * d.element⁻¹ = d.element⁻¹ * a.toHom h :=
    d.inverse.intertwines h
  rw [← intertwines]
  let k : G := d.element⁻¹
  have balance := Biset.pair_balance (Biset.restriction b) (Biset.induction a) k (b.toHom h) 1
  change (Biset.restriction b).pair (Biset.induction a)
      (b.toHom 1 * b.toHom h * ((k⁻¹)⁻¹)) (1 : G) =
    (Biset.restriction b).pair (Biset.induction a)
      (b.toHom h) (k * (1 : G) * (a.toHom 1)⁻¹) at balance
  simpa only [map_one, inv_inv, one_mul, mul_one, inv_one, k] using balance

private theorem ordinaryCup_labelBasis (z : DotLabel R a b) (h : H) :
    Biset.pairLinear R (Biset.restriction b) (Biset.induction a)
        ((Diagram.linearDownDot z).eval.toLinearMap (Finsupp.single (a.toHom h) 1))
        (Finsupp.single 1 1) =
      Biset.pairLinear R (Biset.restriction b) (Biset.induction a)
        (Finsupp.single (b.toHom h) 1)
        ((Diagram.linearUpDot (Finsupp.mapDomain Dot.inverse z)).eval.toLinearMap
          (Finsupp.single 1 1)) := by
  rw [Diagram.eval_linearDownDot_apply, Diagram.eval_linearUpDot_apply]
  let pair := Biset.pairLinear R (Biset.restriction b) (Biset.induction a)
  let left := (pair.flip (Finsupp.single 1 1)).comp
    (freeLift R fun d : Dot a b =>
      (Diagram.downDot (R := R) d).eval.toLinearMap (Finsupp.single (a.toHom h) 1))
  let right := (pair (Finsupp.single (b.toHom h) 1)).comp
    ((freeLift R fun e : Dot b a =>
      (Diagram.upDot (R := R) e).eval.toLinearMap (Finsupp.single 1 1)).comp
      (Finsupp.lmapDomain R R (Dot.inverse : Dot a b → Dot b a)))
  change left z = right z
  apply LinearMap.congr_fun
  apply Finsupp.lhom_ext
  intro d c
  change pair (freeLift R _ (Finsupp.single d c)) (Finsupp.single 1 1) =
    pair (Finsupp.single (b.toHom h) 1)
      (freeLift R _ (Finsupp.mapDomain Dot.inverse (Finsupp.single d c)))
  rw [Finsupp.mapDomain_single, freeLift_single, freeLift_single,
    Diagram.eval_downDot_single, Diagram.eval_upDot_single]
  change (pair.flip (Finsupp.single 1 1)) (c • Finsupp.single (d.element⁻¹ * a.toHom h) 1) =
    pair (Finsupp.single (b.toHom h) 1) (c • Finsupp.single (1 * d.element⁻¹) 1)
  rw [map_smul, map_smul, one_mul]
  change c • Biset.pairLinear R (Biset.restriction b) (Biset.induction a)
      (Finsupp.single (d.element⁻¹ * a.toHom h) 1) (Finsupp.single 1 1) =
    c • Biset.pairLinear R (Biset.restriction b) (Biset.induction a)
      (Finsupp.single (b.toHom h) 1) (Finsupp.single d.element⁻¹ 1)
  rw [Biset.pairLinear_single, Biset.pairLinear_single, ordinaryCup_pair d h]

theorem ordinaryCupEquation33 (z : DotLabel R a b) :
    ((LabelledDrawing.ordinary (Diagram.ordinaryCup a)).vertical
      (z.downDrawing.horizontal (LabelledDrawing.ordinary (Diagram.id (Word.up a))))).interpret.eval =
    ((LabelledDrawing.ordinary (Diagram.ordinaryCup b)).vertical
      ((LabelledDrawing.ordinary (Diagram.id (Word.down b))).horizontal
        (DotLabel.upDrawing (Finsupp.mapDomain Dot.inverse z)))).interpret.eval := by
  change (Diagram.ordinaryCup a).eval.vertical
    (z.downDrawing.interpret.eval.horizontal (Diagram.id (Word.up a)).eval) =
    (Diagram.ordinaryCup b).eval.vertical
      ((Diagram.id (Word.down b)).eval.horizontal
        (DotLabel.upDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval)
  rw [DotLabel.eval_downDrawing, DotLabel.eval_upDrawing]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro h r
  change H at h
  change ((Diagram.linearDownDot z).eval.horizontal (Diagram.id (Word.up a)).eval).toLinearMap
      ((Diagram.ordinaryCup a).eval.toLinearMap (Finsupp.single h r)) =
    ((Diagram.id (Word.down b)).eval.horizontal
      (Diagram.linearUpDot (Finsupp.mapDomain Dot.inverse z)).eval).toLinearMap
      ((Diagram.ordinaryCup b).eval.toLinearMap (Finsupp.single h r))
  rw [Diagram.eval_ordinaryCup_single, Diagram.eval_ordinaryCup_single,
    Biset.Hom.horizontal_single, Biset.Hom.horizontal_single,
    Diagram.eval_id_apply, Diagram.eval_id_apply, ordinaryCup_labelBasis]

#print axioms ordinaryCupEquation33

end MackeyDiagrams

example :
  ∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
      (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
      (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
    ∀ z : MackeyDiagrams.DotLabel Complex a b,
      let zDual : MackeyDiagrams.DotLabel Complex b a :=
        Finsupp.mapDomain MackeyDiagrams.Dot.inverse z
      let rightDual := MackeyDiagrams.DotLabel.upDrawing zDual
      let leftDual := MackeyDiagrams.DotLabel.downDrawing z
      let idUpA := MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
      let idDownB := MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down b))
      let ordinaryLeft := MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.ordinaryCup a))
        (MackeyDiagrams.LabelledDrawing.horizontal leftDual idUpA)
      let ordinaryRight := MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.ordinaryCup b))
        (MackeyDiagrams.LabelledDrawing.horizontal idDownB rightDual)
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret ordinaryLeft) =
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret ordinaryRight) := by
  intro U _ H G α β hα hβ a b z
  exact MackeyDiagrams.ordinaryCupEquation33 z
