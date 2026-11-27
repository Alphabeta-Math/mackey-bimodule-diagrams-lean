import Core

namespace CaseTwoAudit
open MackeyDiagrams
open PlanarCode

private def leftCode : Code :=
  [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp]

private def RigidAt (p : Code) : Prop :=
  (∀ event ∈ p, event = .vertex 0 .mixedProjection ∨ event = .vertex 1 .mixedProjection ∨
    event = .vertex 0 .parallelUp) ∧
  (∀ before after x y, p = before ++ [x, y] ++ after →
    x.outputs.length = 2 ∧ x.inputs.length = 2 ∧ y.outputs.length = 2 ∧ y.inputs.length = 2 ∧
    x.position ≤ 1 ∧ y.position ≤ 1)

private theorem leftCode_rigid : RigidAt leftCode := by
  refine ⟨?_, ?_⟩
  · simp [leftCode]
  intro before after x y h
  rcases before with _ | ⟨a, ⟨_ | ⟨b, more⟩⟩⟩
  · simp [leftCode] at h
    obtain ⟨rfl, rfl, _⟩ := h
    decide
  · simp [leftCode] at h
    obtain ⟨_, rfl, rfl, _⟩ := h
    decide
  · have hlen := congrArg List.length h
    simp [leftCode] at hlen
    omega

-- Any sublist with surrounding context still occupies the same three-wire code.
-- Both adjacent pairs overlap, so no exchange can have either orientation here.
private theorem code_eq_of_equivalent_rigid {x y : Code} (h : Equivalent x y) :
    (∀ lead trail, RigidAt (lead ++ x ++ trail) → x = y) ∧
    (∀ lead trail, RigidAt (lead ++ y ++ trail) → x = y) := by
  induction h with
  | refl => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | symm _ ih => exact ⟨fun p q h => (ih.2 p q h).symm, fun p q h => (ih.1 p q h).symm⟩
  | trans _ _ ih₁ ih₂ =>
      constructor
      · intro p q h
        have h₁ := ih₁.1 p q h
        exact h₁.trans (ih₂.1 p q (h₁ ▸ h))
      · intro p q h
        have h₂ := ih₂.2 p q h
        exact (ih₁.2 p q (h₂.symm ▸ h)).trans h₂
  | context before after _ ih =>
      constructor
      · intro p q h
        have he := ih.1 (p ++ before) (after ++ q) (by simpa only [List.append_assoc] using h)
        rw [he]
      · intro p q h
        have he := ih.2 (p ++ before) (after ++ q) (by simpa only [List.append_assoc] using h)
        rw [he]
  | exchange before after i gap l r =>
      constructor
      · intro p q h
        have hh := h.2 (p ++ before) (after ++ q) (l.place i)
          (r.place (i + l.outputs.length + gap)) (by simp only [List.append_assoc])
        obtain ⟨hsize, _, _, _, _, hpos⟩ := hh
        have sz : (l.place i).outputs.length = l.outputs.length := by cases l <;> rfl
        have hr : (r.place (i + l.outputs.length + gap)).position = i + l.outputs.length + gap := by
          cases r <;> rfl
        omega
      · intro p q h
        have hh := h.2 (p ++ before) (after ++ q) (r.place (i + l.inputs.length + gap))
          (l.place i) (by simp only [List.append_assoc])
        obtain ⟨_, _, _, hsize, hpos, _⟩ := hh
        have sz : (l.place i).inputs.length = l.inputs.length := by cases l <;> rfl
        have hr : (r.place (i + l.inputs.length + gap)).position = i + l.inputs.length + gap := by
          cases r <;> rfl
        omega
  | @scale i b t x y _ _ =>
      constructor
      · intro p q h
        have bad := h.1 (.scale i b t x) (by simp)
        rcases bad with bad | bad | bad <;> cases bad
      · intro p q h
        have bad := h.1 (.scale i b t y) (by simp)
        rcases bad with bad | bad | bad <;> cases bad
  | @add i b t x y z w _ _ _ _ =>
      constructor
      · intro p q h
        have bad := h.1 (.add i b t x z) (by simp)
        rcases bad with bad | bad | bad <;> cases bad
      · intro p q h
        have bad := h.1 (.add i b t y w) (by simp)
        rcases bad with bad | bad | bad <;> cases bad

theorem checked_leftCode {p q : Word G F} (drawing : LabelledDrawing Complex p q)
    (h : drawing.planarShape = leftShape) : encode drawing.erase.geometry = leftCode := by
  have he := congrArg PlanarShape.wiring h
  change Quotient.mk PlanarCode.setoid (encode drawing.erase.geometry) =
    Quotient.mk PlanarCode.setoid leftCode at he
  have hr := Quotient.exact he
  exact (code_eq_of_equivalent_rigid hr).2 [] [] (by simpa using leftCode_rigid)

end CaseTwoAudit
