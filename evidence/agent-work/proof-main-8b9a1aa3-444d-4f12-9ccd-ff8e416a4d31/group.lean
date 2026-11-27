-- A permutation in both cyclic subgroups fixes every point other than 2.
-- Injectivity forces it to fix 2 as well. The join supplier concerns the
-- identification of a generated subgroup. Here the endpoint already
-- constructs the full three-point symmetric group by extension, so the
-- column calculation only needs the two inclusions and this intersection.
private theorem closure_swap_fixes {S : Subgroup (Equiv.Perm Nat)} {t x : S}
    {i j n : Nat} (ht : (t : Equiv.Perm Nat) = Equiv.swap i j)
    (hx : x ∈ Subgroup.closure {t}) (hni : n ≠ i) (hnj : n ≠ j) :
    (x : Equiv.Perm Nat) n = n := by
  let stab := (MulAction.stabilizer (Equiv.Perm Nat) n).comap (Subgroup.subtype S)
  have hle : Subgroup.closure {t} ≤ stab := (Subgroup.closure_le stab).mpr (by
    apply Set.singleton_subset_iff.mpr
    change (t : Equiv.Perm Nat) n = n
    rw [ht]
    exact Equiv.swap_apply_of_ne_of_ne hni hnj)
  exact hle hx

private theorem overlapping_swaps {S : Subgroup (Equiv.Perm Nat)} {t u x : S}
    (ht : (t : Equiv.Perm Nat) = Equiv.swap 1 2)
    (hu : (u : Equiv.Perm Nat) = Equiv.swap 2 3)
    (hx : x ∈ Subgroup.closure {t}) (hy : x ∈ Subgroup.closure {u}) : x = 1 := by
  have hfix (n : Nat) (hn : n ≠ 2) : (x : Equiv.Perm Nat) n = n := by
    by_cases h : n = 1
    · exact closure_swap_fixes hu hy hn (by omega)
    · exact closure_swap_fixes ht hx h hn
  apply Subtype.ext
  apply Equiv.ext
  intro n
  change (x : Equiv.Perm Nat) n = n
  by_cases hn : n = 2
  · subst n
    by_contra h
    have he := hfix ((x : Equiv.Perm Nat) 2) h
    exact h ((x : Equiv.Perm Nat).injective he)
  · exact hfix n hn
