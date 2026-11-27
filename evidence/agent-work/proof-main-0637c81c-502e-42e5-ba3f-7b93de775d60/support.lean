private theorem finiteParabolicIntersection_preserves_and_fixes {ι : Type*} (X : Finset Nat)
    (D : ι → Finset Nat) (disjoint : Pairwise (fun i j => Disjoint (D i) (D j)))
    (cover : ∀ x, x ∈ X ↔ ∃ i, x ∈ D i) (σ : Equiv.Perm Nat)
    (hσ : σ ∈ iSup (fun i =>
      MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ D i)))) :
    (∀ i x, x ∈ D i → σ x ∈ D i) ∧ (∀ x, x ∉ X → σ x = x) := by
  classical
  refine Subgroup.iSup_induction _ (C := fun f : Equiv.Perm Nat =>
    (∀ i x, x ∈ D i → f x ∈ D i) ∧ (∀ x, x ∉ X → f x = x)) hσ ?_ ?_ ?_
  · intro j f hf
    obtain ⟨g, rfl⟩ := hf
    constructor
    · intro i x hx
      by_cases hij : i = j
      · subst j
        exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem g x).mpr hx
      · have hxj : x ∉ D j := fun h => Finset.disjoint_left.mp (disjoint hij) hx h
        rwa [Equiv.Perm.ofSubtype_apply_of_not_mem g hxj]
    · intro x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem g
        (fun h => hx ((cover x).mpr ⟨j, h⟩))
  · exact ⟨fun _ _ hx => hx, fun _ _ => rfl⟩
  · intro f g hf hg
    refine ⟨fun i x hx => hf.1 i (g x) (hg.1 i x hx), ?_⟩
    intro x hx
    change f (g x) = x
    rw [hg.2 x hx, hf.2 x hx]
