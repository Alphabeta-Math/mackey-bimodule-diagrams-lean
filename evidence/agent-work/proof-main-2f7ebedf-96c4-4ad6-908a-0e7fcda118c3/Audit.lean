import TwoBlockDoubleCosetMatrices

#print axioms TwoBlockDoubleCosetMatrices

#check Fin.sum_univ_two

example (X : Finset Nat) (A B : Fin 2 → Finset ↥X)
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ j, (B j).Nonempty)
    (hdA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcA : ∀ x : ↥X, ∃ i, x ∈ A i) (hcB : ∀ x : ↥X, ∃ j, x ∈ B j)
    (a : Int) :
    let n : Int := X.card
    let c : Int := (A 0).card
    let d : Int := (B 0).card
    (a = max 0 (c + d - n) ∨ a = min c d) →
    ∃ σ : Equiv.Perm ↥X, ∀ i j : Fin 2,
      (![![a, c - a], ![d - a, n - c - d + a]] : Fin 2 → Fin 2 → Int) i j =
        Int.ofNat (A i ∩ Finset.map σ.toEmbedding (B j)).card := by
  intro n c d edge
  have hcn : c ≤ n := by
    change ((A 0).card : Int) ≤ (X.card : Int)
    have h := Finset.card_le_univ (A 0)
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  have hdn : d ≤ n := by
    change ((B 0).card : Int) ≤ (X.card : Int)
    have h := Finset.card_le_univ (B 0)
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  have hc : 0 ≤ c := Int.natCast_nonneg _
  have hd : 0 ≤ d := Int.natCast_nonneg _
  have interval : max 0 (c + d - n) ≤ min c d :=
    max_le (le_min hc hd) (le_min (by omega) (by omega))
  have lower : max 0 (c + d - n) ≤ a := by
    rcases edge with e | e
    · exact e.symm.le
    · rw [e]
      exact interval
  have upper : a ≤ min c d := by
    rcases edge with e | e
    · rw [e]
      exact interval
    · exact e.le
  let R : Fin 2 → Fin 2 → Int := ![![a, c - a], ![d - a, n - c - d + a]]
  apply (TwoBlockDoubleCosetMatrices X A B hA hB hdA hdB hcA hcB R).mpr
  exact ⟨a, ⟨lower, upper, rfl, rfl, rfl, rfl⟩, fun b hb => hb.2.2.1.symm⟩
