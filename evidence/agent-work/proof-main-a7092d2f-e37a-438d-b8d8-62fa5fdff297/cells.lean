
private theorem threeCosets_points (x : ↥threeCosetsInterval) :
    x = threeCosetsPoint 9 ∨ x = threeCosetsPoint 10 ∨
      x = threeCosetsPoint 11 ∨ x = threeCosetsPoint 12 := by
  obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp x.property
  have h : x.val = 9 ∨ x.val = 10 ∨ x.val = 11 ∨ x.val = 12 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

private theorem threeCosets_middle_test (x : ↥threeCosetsInterval) :
    (threeCosetsMiddle x).val ≤ 10 ↔ x.val = 9 ∨ x.val = 11 := by
  rcases threeCosets_points x with rfl | rfl | rfl | rfl <;> decide

private theorem threeCosets_last_test (x : ↥threeCosetsInterval) :
    (threeCosetsLast x).val ≤ 10 ↔ ¬(x.val ≤ 10) := by
  rcases threeCosets_points x with rfl | rfl | rfl | rfl <;> decide

private theorem threeCosets_conj_split_mem (X : Finset Nat) (m : Nat)
    (s f : Equiv.Perm ↥X) :
    f ∈ (threeCosetsSplit X m).map (MulAut.conj s).toMonoidHom ↔
      ∀ x : ↥X, (s.symm (f x)).val ≤ m ↔ (s.symm x).val ≤ m := by
  rw [Subgroup.mem_map_equiv, threeCosetsSplit_mem]
  change (∀ x : ↥X, (s.symm (f (s x))).val ≤ m ↔ x.val ≤ m) ↔ _
  constructor
  · intro h x
    simpa only [s.apply_symm_apply] using h (s.symm x)
  · intro h x
    simpa only [s.symm_apply_apply] using h (s x)

-- The two membership tests specify the ordered intersection cells of
-- Proposition 7.3, steps 1–2. Here only their pointwise separation is needed:
-- each point of the third ambient block has a distinct pair of memberships.
private theorem threeCosets_middle_inf :
    threeCosetsSplit threeCosetsInterval 10 ⊓
      (threeCosetsSplit threeCosetsInterval 10).map (MulAut.conj threeCosetsMiddle).toMonoidHom =
        ⊥ := by
  ext f
  rw [Subgroup.mem_inf, threeCosetsSplit_mem, threeCosets_conj_split_mem, Subgroup.mem_bot]
  constructor
  · rintro ⟨hlo, hmid⟩
    apply Equiv.ext
    intro x
    change f x = x
    specialize hlo x
    have he := hmid x
    change (threeCosetsMiddle (f x)).val ≤ 10 ↔ (threeCosetsMiddle x).val ≤ 10 at he
    rw [threeCosets_middle_test, threeCosets_middle_test] at he
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp x.property
    obtain ⟨h₃, h₄⟩ := Finset.mem_Icc.mp (f x).property
    apply Subtype.ext
    omega
  · rintro rfl
    exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

private theorem threeCosets_conj_half_swap :
    (threeCosetsHalf threeCosetsInterval 10 false).map (MulAut.conj threeCosetsLast).toMonoidHom =
      threeCosetsHalf threeCosetsInterval 10 true ∧
    (threeCosetsHalf threeCosetsInterval 10 true).map (MulAut.conj threeCosetsLast).toMonoidHom =
      threeCosetsHalf threeCosetsInterval 10 false := by
  let s := threeCosetsLast
  have hp (x : ↥threeCosetsInterval) : 10 < (s x).val ↔ x.val ≤ 10 := by
    rw [← Nat.not_le, threeCosets_last_test, not_not]
  have hq (x : ↥threeCosetsInterval) : (s x).val ≤ 10 ↔ 10 < x.val :=
    (threeCosets_last_test x).trans Nat.not_le
  have hTransport (p q : ↥threeCosetsInterval → Prop) (h : ∀ x, q (s x) ↔ p x)
      (f : Equiv.Perm ↥threeCosetsInterval) :
      (∀ x, p x → (MulAut.conj s).symm f x = x) ↔ (∀ x, q x → f x = x) := by
    constructor
    · intro hf y hy
      obtain ⟨x, rfl⟩ := s.surjective y
      have he := hf x ((h x).mp hy)
      change s.symm (f (s x)) = x at he
      rwa [Equiv.symm_apply_eq] at he
    · intro hf x hx
      change s.symm (f (s x)) = x
      rw [hf (s x) ((h x).mpr hx), s.symm_apply_apply]
  constructor <;> ext f <;> rw [Subgroup.mem_map_equiv]
  · rw [(threeCosetsHalf_mem _ _ _).1, (threeCosetsHalf_mem _ _ f).2]
    exact hTransport _ _ hq f
  · rw [(threeCosetsHalf_mem _ _ _).2, (threeCosetsHalf_mem _ _ f).1]
    exact hTransport _ _ hp f
