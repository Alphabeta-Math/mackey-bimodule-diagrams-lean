#check Exists.elim
#print axioms Classical.choose

universe u v

theorem pointwiseOfLiftFamily {I : Type u} {K : I → Type v}
    {P : ∀ i, K i → Prop}
    (h : ∃ lift : ∀ i, K i, ∀ i, P i (lift i) ∧ ∀ k, P i k → k = lift i) :
    (∀ i, ∃ k, P i k ∧ ∀ l, P i l → l = k) ∧ Nonempty (∀ i, K i) := by
  obtain ⟨lift, laws⟩ := h
  exact ⟨fun i => ⟨lift i, laws i⟩, ⟨lift⟩⟩

#print axioms pointwiseOfLiftFamily
