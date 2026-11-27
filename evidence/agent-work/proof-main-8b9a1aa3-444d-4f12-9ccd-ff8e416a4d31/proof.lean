by
  intro P finitary U T swap swap12 swap23 D E points extend B includeConj a b e u v w
    up down tensor comp vertical horizontal ordinary straight bottom top atLeft dot lowerLeft
    upperLeft middleRight finiteFibers basisVector r s lowerRight upperRight middleLeft
  have hDB : D ≤ B := by
    apply (Subgroup.closure_le B).mpr
    apply Set.singleton_subset_iff.mpr
    change ∃ p, extend p = Equiv.swap 1 2
    exact ⟨Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  have hEB : E ≤ B := by
    apply (Subgroup.closure_le B).mpr
    apply Set.singleton_subset_iff.mpr
    change ∃ p, extend p = Equiv.swap 2 3
    exact ⟨Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  have hdis : ∀ z : U, z ∈ D → z ∈ E → z = 1 :=
    fun _ hzD hzE => OverlapReplacementAux.overlapping_swaps rfl rfl hzD hzE
  refine ⟨(OverlapReplacementAux.rightLower r).2, (OverlapReplacementAux.leftUpper hEB).2, ?_⟩
  change (OverlapReplacementAux.left hDB hEB r s).interpret.eval =
    (OverlapReplacementAux.right r s).interpret.eval ∧ _
  exact ⟨OverlapReplacementAux.diagrams_eq hDB hEB hdis r s,
    fun x => OverlapReplacementAux.right_column r x s⟩
