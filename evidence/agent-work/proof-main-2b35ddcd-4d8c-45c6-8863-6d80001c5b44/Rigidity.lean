import MackeyDiagrams

namespace CaseOneExample
open MackeyDiagrams

private def ThreeWireCode (code : PlanarCode.Code) : Prop :=
  ∀ event ∈ code,
    event.position ≤ 1 ∧ event.inputs.length = 2 ∧ event.outputs.length = 2 ∧
      ∃ k, event = .vertex event.position k

private theorem ThreeWireCode.middle {pre post code : PlanarCode.Code}
    (h : ThreeWireCode (pre ++ code ++ post)) : ThreeWireCode code := by
  intro event he
  exact h event (List.mem_append_left _ (List.mem_append_right _ he))

private theorem position_place (e : PlanarEvent) (i : Nat) :
    (e.place i).position = i := by cases e <;> rfl

private theorem inputs_place (e : PlanarEvent) (i : Nat) :
    (e.place i).inputs = e.inputs := by cases e <;> rfl

private theorem outputs_place (e : PlanarEvent) (i : Nat) :
    (e.place i).outputs = e.outputs := by cases e <;> rfl

private theorem equivalent_eq_of_three_wires {a b : PlanarCode.Code}
    (h : PlanarCode.Equivalent a b) :
    (ThreeWireCode a → a = b) ∧ (ThreeWireCode b → a = b) := by
  induction h with
  | refl a => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact ⟨fun h => (ih.2 h).symm, fun h => (ih.1 h).symm⟩
  | trans _ _ ih₁ ih₂ =>
    constructor
    · intro ha
      have hab := ih₁.1 ha
      exact hab.trans (ih₂.1 (hab ▸ ha))
    · intro hc
      have hbc := ih₂.2 hc
      exact (ih₁.2 (hbc.symm ▸ hc)).trans hbc
  | context pre post _ ih =>
    constructor
    · intro ha
      rw [ih.1 ha.middle]
    · intro hb
      rw [ih.2 hb.middle]
  | exchange pre post i gap left right =>
    constructor
    · intro ha
      have hleft := ha.middle (left.place i) (by simp)
      have hright := ha.middle (right.place (i + left.outputs.length + gap)) (by simp)
      have hw : left.outputs.length = 2 := by simpa only [outputs_place] using hleft.2.2.1
      have hi : i + left.outputs.length + gap ≤ 1 := by simpa only [position_place] using hright.1
      omega
    · intro hb
      have hleft := hb.middle (left.place i) (by simp)
      have hright := hb.middle (right.place (i + left.inputs.length + gap)) (by simp)
      have hw : left.inputs.length = 2 := by simpa only [inputs_place] using hleft.2.1
      have hi : i + left.inputs.length + gap ≤ 1 := by simpa only [position_place] using hright.1
      omega
  | @scale i below above a b _ _ =>
    constructor <;> intro h
    · obtain ⟨k, hk⟩ := (h (.scale i below above a) (by simp)).2.2.2
      cases hk
    · obtain ⟨k, hk⟩ := (h (.scale i below above b) (by simp)).2.2.2
      cases hk
  | @add i below above a b c d _ _ _ _ =>
    constructor <;> intro h
    · obtain ⟨k, hk⟩ := (h (.add i below above a c) (by simp)).2.2.2
      cases hk
    · obtain ⟨k, hk⟩ := (h (.add i below above b d) (by simp)).2.2.2
      cases hk

theorem right_code_eq {code : PlanarCode.Code}
    (h : Quotient.mk PlanarCode.setoid code =
      Quotient.mk PlanarCode.setoid [.vertex 1 .parallelUp, .vertex 0 .mixedProjection,
        .vertex 1 .mixedProjection]) :
    code = [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection] := by
  apply (equivalent_eq_of_three_wires (Quotient.exact h)).2
  intro event he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl <;> exact ⟨by decide, rfl, rfl, ⟨_, rfl⟩⟩

end CaseOneExample
