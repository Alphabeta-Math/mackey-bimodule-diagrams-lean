import MackeyDiagrams
import Proofs.ParabolicDoubleCosetRepresentatives

set_option maxHeartbeats 2000000

theorem TwoBlockDoubleCosetMatrices : (∀ (X : Finset Nat) (A B : Fin 2 → Finset ↥X),
  (∀ i, Finset.Nonempty (A i)) →
  (∀ j, Finset.Nonempty (B j)) →
  Pairwise (fun i i' => Disjoint (A i) (A i')) →
  Pairwise (fun j j' => Disjoint (B j) (B j')) →
  (∀ x : ↥X, ∃ i, x ∈ A i) →
  (∀ x : ↥X, ∃ j, x ∈ B j) →
  let n : Int := Int.ofNat (Finset.card X)
  let c : Int := Int.ofNat (Finset.card (A 0))
  let d : Int := Int.ofNat (Finset.card (B 0))
  ∀ R : Fin 2 → Fin 2 → Int,
    (∃ σ : Equiv.Perm ↥X, ∀ i j, R i j =
      Int.ofNat (Finset.card (A i ∩ Finset.map (Equiv.toEmbedding σ) (B j)))) ↔
    ∃! a : Int, max 0 (c + d - n) ≤ a ∧ a ≤ min c d ∧
      R 0 0 = a ∧ R 0 1 = c - a ∧ R 1 0 = d - a ∧ R 1 1 = n - c - d + a) :=
(by
  intro X A B hA hB hdA hdB hcA hcB n c d R
  -- Xiao, §7.3 (project PDF p. 30, published PDF p. 32), gives the same
  -- classification as the article portal. The portal has no separate numbered
  -- proof here. Its two numbered tableau steps in §7.2 are already proved in
  -- ParabolicDoubleCosetRepresentatives: split each row into consecutive
  -- pieces (step 1), then split each column and match the pieces (step 2).
  obtain ⟨classify, count, chooseRepresentative⟩ :=
    ParabolicDoubleCosetRepresentatives X 2 2 A B hA hB hdA hdB hcA hcB
  -- Sum the two disjoint blocks of either covering partition.
  have total (D : Fin 2 → Finset ↥X)
      (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
      (hc : ∀ x : ↥X, ∃ i, x ∈ D i) :
      ((D 0).card : Int) + ((D 1).card : Int) = n := by
    have cover : D 0 ∪ D 1 = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      obtain ⟨i, hi⟩ := hc x
      fin_cases i
      · exact Finset.mem_union_left _ hi
      · exact Finset.mem_union_right _ hi
    have h := Finset.card_union_of_disjoint (hd (by decide : (0 : Fin 2) ≠ 1))
    rw [cover, Finset.card_univ, Fintype.card_coe] at h
    change ((D 0).card : Int) + ((D 1).card : Int) = (X.card : Int)
    exact_mod_cast h.symm
  have secondRow : ((A 1).card : Int) = n - c := by
    have h : c + ((A 1).card : Int) = n := total A hdA hcA
    omega
  have secondCol : ((B 1).card : Int) = n - d := by
    have h : d + ((B 1).card : Int) = n := total B hdB hcB
    omega
  constructor
  · rintro ⟨σ, hσ⟩
    -- Proposition 7.3 gives Nat margins. Expand the two-term sums and do
    -- the parameter calculation in Int, where the article's differences live.
    let M := classify (DoubleCoset.mk _ _ σ)
    have entry (i j : Fin 2) : R i j = (M.val i j : Int) := by
      rw [hσ i j]
      exact congrArg Int.ofNat (count σ i j).symm
    have row (i : Fin 2) : R i 0 + R i 1 = ((A i).card : Int) := by
      have h := M.property.1 i
      rw [Fin.sum_univ_two] at h
      rw [entry i 0, entry i 1]
      exact_mod_cast h
    have col (j : Fin 2) : R 0 j + R 1 j = ((B j).card : Int) := by
      have h := M.property.2 j
      rw [Fin.sum_univ_two] at h
      rw [entry 0 j, entry 1 j]
      exact_mod_cast h
    have nonneg (i j : Fin 2) : 0 ≤ R i j := by
      rw [entry i j]
      exact Int.natCast_nonneg _
    have r₀ : R 0 0 + R 0 1 = c := row 0
    have r₁ : R 1 0 + R 1 1 = n - c := (row 1).trans secondRow
    have c₀ : R 0 0 + R 1 0 = d := col 0
    refine ⟨R 0 0, ⟨?_, ?_, rfl, by omega, by omega, by omega⟩, ?_⟩
    · exact max_le (nonneg 0 0) (by have h := nonneg 1 1; omega)
    · exact le_min (by have h := nonneg 0 1; omega) (by have h := nonneg 1 0; omega)
    · intro a ha
      exact ha.2.2.1.symm
  · rintro ⟨a, ⟨lower, upper, h00, h01, h10, h11⟩, _⟩
    have ha₀ := (le_max_left 0 (c + d - n)).trans lower
    have ha₁ := (le_max_right 0 (c + d - n)).trans lower
    have hac := upper.trans (min_le_left c d)
    have had := upper.trans (min_le_right c d)
    -- The weak bounds allow zero cells. Show nonnegativity before converting
    -- to the Nat matrix of Proposition 7.3, so Int.toNat preserves every entry.
    have nonneg : ∀ i j : Fin 2, 0 ≤ R i j := by
      simp only [Fin.forall_fin_two]
      exact ⟨⟨h00.symm ▸ ha₀, by omega⟩, ⟨by omega, by omega⟩⟩
    let M : Fin 2 → Fin 2 → Nat := fun i j => (R i j).toNat
    have entry (i j : Fin 2) : (M i j : Int) = R i j :=
      Int.toNat_of_nonneg (nonneg i j)
    have rows (i : Fin 2) : Finset.sum Finset.univ (M i) = (A i).card := by
      rw [Fin.sum_univ_two]
      have h : R i 0 + R i 1 = ((A i).card : Int) := by
        fin_cases i
        · change R 0 0 + R 0 1 = c
          omega
        · change R 1 0 + R 1 1 = ((A 1).card : Int)
          omega
      have h₀ := entry i 0
      have h₁ := entry i 1
      omega
    have cols (j : Fin 2) :
        Finset.sum Finset.univ (fun i => M i j) = (B j).card := by
      rw [Fin.sum_univ_two]
      have h : R 0 j + R 1 j = ((B j).card : Int) := by
        fin_cases j
        · change R 0 0 + R 1 0 = d
          omega
        · change R 0 1 + R 1 1 = ((B 1).card : Int)
          omega
      have h₀ := entry 0 j
      have h₁ := entry 1 j
      omega
    obtain ⟨σ, hσ, _⟩ := chooseRepresentative ⟨M, rows, cols⟩
    refine ⟨σ, fun i j => ?_⟩
    have h := count σ i j
    rw [hσ, Equiv.apply_symm_apply] at h
    exact (entry i j).symm.trans (congrArg Int.ofNat h))
