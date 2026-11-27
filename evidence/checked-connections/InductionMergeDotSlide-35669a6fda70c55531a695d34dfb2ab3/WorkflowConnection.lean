import MackeyDiagrams
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem LeanWorkflowCheckedConnection : (∀ {U : Type*} [Group U] (K H G : Subgroup U) (γ α β : U)
    (hγ : ∀ h : H, γ * (h : U) * γ⁻¹ ∈ G)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ H)
    (hβ : ∀ k : K, β * (k : U) * β⁻¹ ∈ H)
    (he : α * β⁻¹ ∈ H),
  let g := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let e : MackeyDiagrams.Dot a b :=
    MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl) he
  let rightDot := MackeyDiagrams.Diagram.upDot (R := Complex) e
  let merge := MackeyDiagrams.Diagram.mergeUp (R := Complex) g a
  (∀ (γ' : U)
      (hγ' : ∀ h : H, γ' * (h : U) * (γ')⁻¹ ∈ G)
      (hd : γ * (γ')⁻¹ ∈ G),
    let g' := MackeyDiagrams.ConjEmbedding.ofConjugator γ' hγ'
    let d : MackeyDiagrams.Dot g g' :=
      MackeyDiagrams.Dot.ofRepresentatives γ γ' (fun _ => rfl) (fun _ => rfl) hd
    let lifted : MackeyDiagrams.Dot
        (MackeyDiagrams.ConjEmbedding.comp g a)
        (MackeyDiagrams.ConjEmbedding.comp g' a) :=
      ⟨MackeyDiagrams.Dot.element d,
        fun k => MackeyDiagrams.Dot.intertwines d
          (MackeyDiagrams.ConjEmbedding.toHom a k)⟩
    let merged := MackeyDiagrams.Dot.vertical lifted (MackeyDiagrams.Dot.whisker g' e)
    let left := MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.upDot d) rightDot)
      (MackeyDiagrams.Diagram.mergeUp g' b)
    let right := MackeyDiagrams.Diagram.vertical merge (MackeyDiagrams.Diagram.upDot merged)
    MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right) ∧
  (let left := MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal
        (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up g)) rightDot)
      (MackeyDiagrams.Diagram.mergeUp g b)
    let right := MackeyDiagrams.Diagram.vertical merge
      (MackeyDiagrams.Diagram.upDot (MackeyDiagrams.Dot.whisker g e))
    MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right)) :=
(by
  intro U group K H G γ α β hγ hα hβ he g a b e rightDot merge
  constructor
  · intro γ' hγ' hd g' d lifted merged left right
    apply MackeyDiagrams.Diagram.eval_ext
    intro z r
    refine Quotient.inductionOn z (fun xy => ?_)
    rcases xy with ⟨x, y⟩
    change G at x
    change H at y
    change left.eval.toLinearMap
        (Finsupp.single ((MackeyDiagrams.Word.up g).basis.pair
          (MackeyDiagrams.Word.up a).basis x y) r) =
      right.eval.toLinearMap
        (Finsupp.single ((MackeyDiagrams.Word.up g).basis.pair
          (MackeyDiagrams.Word.up a).basis x y) r)
    dsimp only [left, right, merge, rightDot]
    rw [MackeyDiagrams.Diagram.eval_vertical_apply,
      MackeyDiagrams.Diagram.eval_vertical_apply,
      MackeyDiagrams.Diagram.eval_horizontal_single,
      MackeyDiagrams.Diagram.eval_upDot_single,
      MackeyDiagrams.Diagram.eval_upDot_single,
      MackeyDiagrams.Biset.pairLinear_single, one_mul]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [MackeyDiagrams.Diagram.eval_mergeUp_single,
      MackeyDiagrams.Diagram.eval_mergeUp_single,
      MackeyDiagrams.Diagram.eval_upDot_single]
    congr 1
    change (x * d.element) * g'.toHom (y * e.element) =
      (x * g.toHom y) * (d.element * g'.toHom e.element)
    rw [map_mul, ← mul_assoc (x * d.element), mul_assoc x d.element,
      ← d.intertwines y]
    simp only [mul_assoc]
  · exact MackeyDiagrams.Diagram.mergeUp_slide_right _ _
)
