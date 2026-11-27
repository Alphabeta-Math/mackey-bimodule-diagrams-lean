universe u v

theorem pointwiseFactors {I : Type u} {L : I → Type v} [∀ i, Subsingleton (L i)]
    (h : ∀ i, Nonempty (L i)) : Nonempty (∀ i, L i) := by
  refine ⟨fun i => ?_⟩
  obtain ⟨f⟩ := h i
  exact f
