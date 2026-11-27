import MackeyDiagrams
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem LeanWorkflowCheckedConnection : (∀ {U : Type*} [Group U] (L H G : Subgroup U) (α β : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hβ : ∀ l : L, β * (l : U) * β⁻¹ ∈ H),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let ab := MackeyDiagrams.ConjEmbedding.comp a b
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
  let upA := MackeyDiagrams.Word.up a
  let upB := MackeyDiagrams.Word.up b
  let downA := MackeyDiagrams.Word.down a
  let downB := MackeyDiagrams.Word.down b
  let upPair := MackeyDiagrams.Biset.pairLinear Complex upA.basis upB.basis
  let downPair := MackeyDiagrams.Biset.pairLinear Complex downB.basis downA.basis
  let upMerge := MackeyDiagrams.Diagram.mergeUp (R := Complex) a b
  let upSplit := MackeyDiagrams.Diagram.splitUp (R := Complex) a b
  let downMerge := MackeyDiagrams.Diagram.mergeDown (R := Complex) a b
  let downSplit := MackeyDiagrams.Diagram.splitDown (R := Complex) a b
  (∀ l : L, (ab.toHom l : U) = (α * β) * (l : U) * (α * β)⁻¹) ∧
  (∀ (x : MonoidAlgebra Complex G) (y : MonoidAlgebra Complex H),
    (MackeyDiagrams.Diagram.eval upMerge).toLinearMap
      (upPair (MonoidAlgebra.coeff x) (MonoidAlgebra.coeff y)) =
      MonoidAlgebra.coeff (x * φ y) ∧
    (MackeyDiagrams.Diagram.eval downMerge).toLinearMap
      (downPair (MonoidAlgebra.coeff y) (MonoidAlgebra.coeff x)) =
      MonoidAlgebra.coeff (φ y * x)) ∧
  (∀ z : MonoidAlgebra Complex G,
    (MackeyDiagrams.Diagram.eval upSplit).toLinearMap (MonoidAlgebra.coeff z) =
      upPair (MonoidAlgebra.coeff z) (MonoidAlgebra.coeff (1 : MonoidAlgebra Complex H)) ∧
    (MackeyDiagrams.Diagram.eval downSplit).toLinearMap (MonoidAlgebra.coeff z) =
      downPair (MonoidAlgebra.coeff (1 : MonoidAlgebra Complex H)) (MonoidAlgebra.coeff z)) ∧
  MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical upMerge upSplit) =
    MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.tensor upA upB)) ∧
  MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical upSplit upMerge) =
    MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up ab)) ∧
  MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical downMerge downSplit) =
    MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.tensor downB downA)) ∧
  MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical downSplit downMerge) =
    MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down ab))) :=
(by
  intro U inst L H G α β hα hβ a b ab φ upA upB downA downB upPair downPair upMerge upSplit downMerge downSplit
  refine ⟨?_, ?_, ?_, MackeyDiagrams.Diagram.mergeUp_splitUp a b,
    MackeyDiagrams.Diagram.splitUp_mergeUp a b,
    MackeyDiagrams.Diagram.mergeDown_splitDown a b,
    MackeyDiagrams.Diagram.splitDown_mergeDown a b⟩
  · intro l
    simp only [ab, a, b, MackeyDiagrams.ConjEmbedding.comp_apply,
      MackeyDiagrams.ConjEmbedding.ofConjugator_apply]
    group
  · intro x y
    induction x using MonoidAlgebra.induction_linear generalizing y with
    | zero => simp
    | add x₁ x₂ ih₁ ih₂ =>
      rcases ih₁ y with ⟨up₁,down₁⟩
      rcases ih₂ y with ⟨up₂,down₂⟩
      exact ⟨by simp [add_mul, up₁, up₂], by simp [mul_add, down₁, down₂]⟩
    | single g r =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y₁ y₂ ih₁ ih₂ =>
        rcases ih₁ with ⟨up₁,down₁⟩
        rcases ih₂ with ⟨up₂,down₂⟩
        simp only [MonoidAlgebra.coeff_single] at up₁ up₂ down₁ down₂
        exact ⟨by simp [mul_add, up₁, up₂], by simp [add_mul, down₁, down₂]⟩
      | single h t =>
        change
          upMerge.eval.toLinearMap (MackeyDiagrams.Biset.pairLinear Complex upA.basis upB.basis
            (Finsupp.single g r) (Finsupp.single h t)) = _ ∧
          downMerge.eval.toLinearMap (MackeyDiagrams.Biset.pairLinear Complex downB.basis downA.basis
            (Finsupp.single h t) (Finsupp.single g r)) = _
        simp only [MackeyDiagrams.Biset.pairLinear_single]
        change (MackeyDiagrams.Diagram.mergeUp (R := Complex) a b).eval.toLinearMap
            (Finsupp.single ((MackeyDiagrams.Biset.induction a).pair (MackeyDiagrams.Biset.induction b) g h) (r*t)) = _ ∧
          (MackeyDiagrams.Diagram.mergeDown (R := Complex) a b).eval.toLinearMap
            (Finsupp.single ((MackeyDiagrams.Biset.restriction b).pair (MackeyDiagrams.Biset.restriction a) h g) (t*r)) = _
        rw [MackeyDiagrams.Diagram.eval_mergeUp_single, MackeyDiagrams.Diagram.eval_mergeDown_single]
        have hp : φ (MonoidAlgebra.single h t) = MonoidAlgebra.single (a.toHom h) t := by
          change MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single h t) = _
          rw [MonoidAlgebra.mapDomain_single]
        rw [hp]
        change
          Finsupp.single (g * a.toHom h) (r * t) =
            (MonoidAlgebra.single g r * MonoidAlgebra.single (a.toHom h) t).coeff ∧
          Finsupp.single (a.toHom h * g) (t * r) =
            (MonoidAlgebra.single (a.toHom h) t * MonoidAlgebra.single g r).coeff
        simp only [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, and_self]
  · intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add z₁ z₂ ih₁ ih₂ =>
      exact ⟨by simp [ih₁.1, ih₂.1], by simp [ih₁.2, ih₂.2]⟩
    | single g r =>
      change upSplit.eval.toLinearMap (Finsupp.single g r) =
        MackeyDiagrams.Biset.pairLinear Complex upA.basis upB.basis (Finsupp.single g r)
          (Finsupp.single 1 1) ∧
        downSplit.eval.toLinearMap (Finsupp.single g r) =
        MackeyDiagrams.Biset.pairLinear Complex downB.basis downA.basis (Finsupp.single 1 1)
          (Finsupp.single g r)
      simp only [MackeyDiagrams.Biset.pairLinear_single, mul_one, one_mul]
      exact ⟨MackeyDiagrams.Diagram.eval_splitUp_single a b g r,
        MackeyDiagrams.Diagram.eval_splitDown_single a b g r⟩)
