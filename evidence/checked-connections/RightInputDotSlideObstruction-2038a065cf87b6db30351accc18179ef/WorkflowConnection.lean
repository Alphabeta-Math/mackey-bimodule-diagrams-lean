import MackeyDiagrams
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem LeanWorkflowCheckedConnection : (let U := Equiv.Perm (Fin 4)
let G : Subgroup U := ⊤
let H := MulAction.stabilizer U (3 : Fin 4)
let K := H ⊓ MulAction.stabilizer U (2 : Fin 4)
let inG : ∀ x : U, x ∈ G := fun _ => Subgroup.mem_top _
let α : MackeyDiagrams.ConjEmbedding K H :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (by
    intro k
    simpa only [one_mul, inv_one, mul_one] using (inf_le_left : K ≤ H) k.property)
let γ : MackeyDiagrams.ConjEmbedding H G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (fun _ => inG _)
let target := MackeyDiagrams.ConjEmbedding.comp γ α
let g : G := ⟨Equiv.swap (2 : Fin 4) 3, inG _⟩
let gLabel : MackeyDiagrams.ConjEmbedding K G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator (g : U) (fun _ => inG _)
let input := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up γ)
  (MackeyDiagrams.Word.up α)
let output := MackeyDiagrams.Word.up target
let unitTensor := Finsupp.single
  (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction γ)
    (MackeyDiagrams.Biset.induction α) 1 1) (1 : Complex)
(g : U) ∈ Subgroup.centralizer (K : Set U) ∧ gLabel = target ∧ (g : U) ∉ H ∧
  ∃ d : MackeyDiagrams.Dot target target, MackeyDiagrams.Dot.element d = g ∧
    let B : MackeyDiagrams.Diagram Complex input output :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.mergeUp γ α) (MackeyDiagrams.Diagram.upDot d)
    let evalB := MackeyDiagrams.Diagram.eval B
    MackeyDiagrams.Biset.Hom.toLinearMap evalB unitTensor = Finsupp.single g 1 ∧
      ∀ (β : MackeyDiagrams.ConjEmbedding K H) (e : MackeyDiagrams.Dot α β)
        (h : MackeyDiagrams.ConjEmbedding.comp γ β = target),
        let A : MackeyDiagrams.Diagram Complex input
            (MackeyDiagrams.Word.up (MackeyDiagrams.ConjEmbedding.comp γ β)) :=
          MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal
              (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up γ))
              (MackeyDiagrams.Diagram.upDot e))
            (MackeyDiagrams.Diagram.mergeUp γ β)
        let evalA := MackeyDiagrams.Diagram.eval
          (Eq.ndrec (motive := fun out =>
            MackeyDiagrams.Diagram Complex input (MackeyDiagrams.Word.up out)) A h)
        MackeyDiagrams.Biset.Hom.toLinearMap evalA unitTensor =
          Finsupp.single
            (MackeyDiagrams.ConjEmbedding.toHom γ (MackeyDiagrams.Dot.element e)) 1 ∧
        evalA ≠ evalB) :=
(by
  dsimp only
  let s := Equiv.swap (2 : Fin 4) 3
  have hcomm (k : Equiv.Perm (Fin 4))
      (hk : k ∈ MulAction.stabilizer (Equiv.Perm (Fin 4)) (3 : Fin 4) ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 4)) (2 : Fin 4)) : k * s = s * k := by
    have h3 : k (3 : Fin 4) = 3 := MulAction.mem_stabilizer_iff.mp hk.1
    have h2 : k (2 : Fin 4) = 2 := MulAction.mem_stabilizer_iff.mp hk.2
    change k * Equiv.swap 2 3 = Equiv.swap 2 3 * k
    rw [Equiv.mul_swap_eq_swap_mul, h2, h3]
  have hcentr : s ∈ Subgroup.centralizer
      (↑(MulAction.stabilizer (Equiv.Perm (Fin 4)) (3 : Fin 4) ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 4)) (2 : Fin 4)) : Set (Equiv.Perm (Fin 4))) :=
    Subgroup.mem_centralizer_iff.mpr hcomm
  have hs : s ∉ MulAction.stabilizer (Equiv.Perm (Fin 4)) (3 : Fin 4) := by
    intro h
    have ht : s (3 : Fin 4) = 3 := MulAction.mem_stabilizer_iff.mp h
    change Equiv.swap (2 : Fin 4) 3 3 = 3 at ht
    rw [Equiv.swap_apply_right] at ht
    exact (by decide : (2 : Fin 4) ≠ 3) ht
  refine ⟨hcentr, ?_, hs, ?_⟩
  · apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro k
    apply Subtype.ext
    simp only [MackeyDiagrams.ConjEmbedding.comp_apply, MackeyDiagrams.ConjEmbedding.ofConjugator_apply, one_mul, inv_one, mul_one]
    change s * (k : Equiv.Perm (Fin 4)) * s⁻¹ = _
    rw [← hcomm k k.property, mul_assoc, mul_inv_cancel, mul_one]
  · refine ⟨⟨⟨s, Subgroup.mem_top s⟩, ?_⟩, rfl, ?_⟩
    · intro k
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MackeyDiagrams.ConjEmbedding.comp_apply, MackeyDiagrams.ConjEmbedding.ofConjugator_apply,
        one_mul, inv_one, mul_one]
      exact hcomm k k.property
    · constructor
      · rw [MackeyDiagrams.Diagram.eval_vertical_apply, MackeyDiagrams.Diagram.eval_mergeUp_single, map_one, one_mul,
          MackeyDiagrams.Diagram.eval_upDot_single, one_mul]
      · intro β e h
        have heq := MackeyDiagrams.Diagram.mergeUp_rightEmbedding_eq _ h
        subst β
        constructor
        · rw [MackeyDiagrams.Diagram.eval_vertical_apply, MackeyDiagrams.Diagram.eval_horizontal_single, MackeyDiagrams.Diagram.eval_id_apply,
            MackeyDiagrams.Diagram.eval_upDot_single, one_mul, MackeyDiagrams.Biset.pairLinear_single, mul_one, one_smul,
            MackeyDiagrams.Diagram.eval_mergeUp_single, one_mul]
        · apply MackeyDiagrams.Diagram.mergeUp_rightInput_ne_trunk
          rintro ⟨x, hx⟩
          apply hs
          have hxval := congrArg Subtype.val hx
          simp only [MackeyDiagrams.ConjEmbedding.ofConjugator_apply, one_mul, inv_one, mul_one] at hxval
          exact hxval ▸ x.property
)
