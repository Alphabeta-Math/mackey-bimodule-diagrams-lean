by
  intro X G block A B blockSym K H R rank five six
  -- Xiao's Example 7.2 (archived PDF p. 30, published 28 November
  -- revision p. 32) uses the numbered steps after Proposition 7.3 in
  -- §7.2 of the Alphabeta Math presentation.
  -- Step 1: check the partitions and the matrix margins for the row slices.
  have nonemptyA : ∀ i, (A i).Nonempty := by decide
  have nonemptyB : ∀ j, (B j).Nonempty := by decide
  have disjointA : Pairwise (fun i i' => Disjoint (A i) (A i')) := by
    intro i i' h
    fin_cases i <;> fin_cases i' <;> first | contradiction | decide
  have disjointB : Pairwise (fun j j' => Disjoint (B j) (B j')) := by
    intro j j' h
    fin_cases j <;> fin_cases j' <;> first | contradiction | decide
  have coverA : ∀ x : ↥X, ∃ i, x ∈ A i := by decide
  have coverB : ∀ x : ↥X, ∃ j, x ∈ B j := by decide
  have rowMargins : ∀ i, Finset.sum Finset.univ (R i) = (A i).card := by
    decide
  have colMargins : ∀ j, Finset.sum Finset.univ (fun i => R i j) = (B j).card := by
    decide
  obtain ⟨classify, hcard, hrepresentative⟩ :=
    ParabolicDoubleCosetRepresentatives X 2 2 A B
      nonemptyA nonemptyB disjointA disjointB coverA coverB
  obtain ⟨σ, hcoset, hmatch⟩ := hrepresentative ⟨R, rowMargins, colMargins⟩
  have cells_card : ∀ i j, (A i ∩ (B j).map σ.toEmbedding).card = R i j := by
    intro i j
    rw [← hcard σ i j, hcoset, Equiv.apply_symm_apply]
  -- Step 2: the representative supplier constructs the ordered matching.
  -- Compute the ranks from explicit sorted lists and compare the matching
  -- with the transposition on every point covered by the partitions.
  let point (n : Fin 6) : ↥X :=
    ⟨n.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  let row (i : Fin 2) : List ↥X :=
    if i = 0 then [point 0, point 1, point 3, point 4] else [point 2, point 5]
  let col (j : Fin 2) : List ↥X :=
    if j = 0 then [point 0, point 2, point 4] else [point 1, point 3, point 5]
  have sort_eq (S : Finset ↥X) (l : List ↥X) (hS : l.toFinset = S)
      (hn : l.Nodup) (hs : l.Pairwise (· ≤ ·)) : S.sort = l := by
    rw [← hS]
    exact (List.toFinset_sort (· ≤ ·) hn).mpr hs
  have sortedA (i : Fin 2) : (A i).sort = row i := by
    apply sort_eq <;> fin_cases i <;> decide
  have sortedB (j : Fin 2) : (B j).sort = col j := by
    apply sort_eq <;> fin_cases j <;> decide
  have swap_match : ∀ (i j : Fin 2) (x : ↥(A i)) (y : ↥(B j)),
      (Equiv.swap five six) y.val = x.val ↔
        ∃ k : Fin (R i j),
          rank (A i) x = (Finset.Iio j).sum (fun j' => R i j') + k.val ∧
          rank (B j) y = (Finset.Iio i).sum (fun i' => R i' j) + k.val := by
    simp only [rank, Finset.orderIsoOfFin_symm_apply, sortedA, sortedB, Equiv.swap_apply_def]
    decide
  have swap_eq : σ = Equiv.swap five six := by
    apply Equiv.ext
    intro y
    obtain ⟨j, hj⟩ := coverB y
    obtain ⟨i, hi⟩ := coverA (σ y)
    exact ((swap_match i j ⟨σ y, hi⟩ ⟨y, hj⟩).mpr
      ((hmatch i j ⟨σ y, hi⟩ ⟨y, hj⟩).mp rfl)).symm
  let τ := Equiv.swap five six
  have cell00 : A 0 ∩ (B 0).map τ.toEmbedding = block {1} := by decide
  have cell01 : A 0 ∩ (B 1).map τ.toEmbedding = block {2, 4, 5} := by decide
  have cell10 : A 1 ∩ (B 0).map τ.toEmbedding = block {3, 6} := by decide
  have cell11 : A 1 ∩ (B 1).map τ.toEmbedding = ∅ := by decide
  refine ⟨σ, cells_card, ?_, ?_, hmatch, swap_eq, ?_⟩
  · rw [swap_eq]
    exact cell00
  · rw [swap_eq]
    exact cell10
  -- Apply the block-intersection formula following Step 2 in §7.2.
  -- The singleton and empty cells each contribute the trivial subgroup.
  rw [swap_eq]
  change K ⊓ H.map (MulAut.conj τ).toMonoidHom = _
  rw [ParabolicMackeyIntersectionBlocks X 2 2 A B
    nonemptyA nonemptyB disjointA disjointB coverA coverB τ]
  change (⨆ i, ⨆ j, blockSym (A i ∩ (B j).map τ.toEmbedding)) = _
  have supTwo (f : Fin 2 → Subgroup G) : (⨆ i, f i) = f 0 ⊔ f 1 := by
    apply eq_of_forall_ge_iff
    intro P
    simp only [iSup_le_iff, sup_le_iff, Fin.forall_fin_two]
  simp only [supTwo]
  rw [cell00, cell01, cell10, cell11]
  have trivial (S : Finset ↥X) (hS : Subsingleton ↥S) : blockSym S = ⊥ := by
    apply le_antisymm _ bot_le
    rintro g ⟨p, rfl⟩
    have hp : p = 1 := by
      apply Equiv.ext
      intro x
      exact hS.elim _ _
    simp [hp]
  have singleton_cell : Subsingleton ↥(block {1}) := by
    constructor
    decide
  have empty_cell : Subsingleton ↥(∅ : Finset ↥X) := by
    constructor
    decide
  rw [trivial _ singleton_cell, trivial _ empty_cell, bot_sup_eq, sup_bot_eq]
