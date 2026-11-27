by
  intro ι κ _ _ X A B _ _ disjointA disjointB coverA coverB blockSym
  -- Steps 1–3 expand the Intersection argument in Xiao, Proposition 7.1.
  -- The context supplies no separate numbered Alphabeta Math proof for this endpoint.
  apply le_antisymm
  · intro σ hσ
    -- Step 1. Disjointness makes each factor preserve every block of its own partition.
    -- The ambient carrier is Nat, so also track the points outside the common finite set.
    obtain ⟨preserveA, fixOutside⟩ :=
      finiteParabolicIntersection_preserves_and_fixes X A disjointA coverA σ hσ.1
    obtain ⟨preserveB, _⟩ :=
      finiteParabolicIntersection_preserves_and_fixes X B disjointB coverB σ hσ.2
    -- Step 2. To pass from preservation to membership in the subgroup supremum,
    -- use Mathlib’s swap-closure criterion. The moved points lie in X, and a swap
    -- within the common refinement puts each moved x and σ x in the same orbit.
    let swaps : Set (Equiv.Perm Nat) := {s | ∃ i j, ∃ x y : Nat,
      x ∈ A i ∩ B j ∧ y ∈ A i ∩ B j ∧ x ≠ y ∧ s = Equiv.swap x y}
    have genuine : ∀ s ∈ swaps, Equiv.Perm.IsSwap s := by
      rintro s ⟨i, j, x, y, _, _, hxy, rfl⟩
      exact ⟨x, y, hxy, rfl⟩
    have swaps_le : Subgroup.closure swaps ≤
        iSup (fun i => iSup (fun j => blockSym (A i ∩ B j))) := by
      apply (Subgroup.closure_le _).mpr
      rintro s ⟨i, j, x, y, hx, hy, _, rfl⟩
      apply Subgroup.mem_iSup_of_mem i
      apply Subgroup.mem_iSup_of_mem j
      exact ⟨Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
    apply swaps_le
    apply (mem_closure_isSwap genuine).mpr
    constructor
    · refine X.finite_toSet.subset ?_
      intro x hx
      by_contra hxX
      exact hx (fixOutside x hxX)
    · intro x
      apply MulAction.mem_orbit_iff.mpr
      by_cases h : σ x = x
      · exact ⟨1, h.symm⟩
      · have hx : x ∈ X := by
          by_contra hxX
          exact h (fixOutside x hxX)
        obtain ⟨i, hi⟩ := (coverA x).mp hx
        obtain ⟨j, hj⟩ := (coverB x).mp hx
        have hswap : Equiv.swap x (σ x) ∈ Subgroup.closure swaps :=
          Subgroup.subset_closure ⟨i, j, x, σ x, Finset.mem_inter.mpr ⟨hi, hj⟩,
            Finset.mem_inter.mpr ⟨preserveA i x hi, preserveB j x hj⟩, Ne.symm h, rfl⟩
        exact ⟨⟨Equiv.swap x (σ x), hswap⟩, Equiv.swap_apply_left _ _⟩
  · -- Step 3. A factor of the refinement embeds into each parent factor.
    -- This restriction argument also applies to the empty block, whose extension is trivial.
    have block_mono {S T : Finset Nat} (hST : S ⊆ T) : blockSym S ≤ blockSym T := by
      rintro f ⟨g, rfl⟩
      have fix (x : Nat) (hx : x ∉ T) : Equiv.Perm.ofSubtype g x = x :=
        Equiv.Perm.ofSubtype_apply_of_not_mem g (fun hxS => hx (hST hxS))
      have preserve (x : Nat) : Equiv.Perm.ofSubtype g x ∈ T ↔ x ∈ T := by
        by_cases hx : x ∈ S
        · rw [Equiv.Perm.ofSubtype_apply_of_mem g hx]
          exact iff_of_true (hST (g ⟨x, hx⟩).property) (hST hx)
        · rw [Equiv.Perm.ofSubtype_apply_of_not_mem g hx]
      exact ⟨(Equiv.Perm.ofSubtype g).subtypePerm preserve,
        Equiv.Perm.ofSubtype_subtypePerm preserve (fun x hm => by
          by_contra hx
          exact hm (fix x hx))⟩
    refine iSup_le fun i => iSup_le fun j => le_inf ?_ ?_
    · exact (block_mono Finset.inter_subset_left).trans (le_iSup (fun k => blockSym (A k)) i)
    · exact (block_mono Finset.inter_subset_right).trans (le_iSup (fun k => blockSym (B k)) j)
