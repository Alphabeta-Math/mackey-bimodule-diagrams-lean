by
  -- Example 8.4, archived PDF p. 39 and 28 November revision p. 41.
  -- Theorem 6.4(1) and Proposition 8.6 prescribe the join containment bounds.
  -- The registered extremality theorem is over finitary permutations of ℕ.
  -- Here the same bounds are checked directly in Perm Point using swaps.
  -- The registered Case 2 endpoint concerns its left projections. We reuse
  -- its single-crossing calculation (Lemma 6.3 and (6.1)), where the choice
  -- of ambient group is unrestricted, for the middle projection of Case 1.
  intro Point point1 point2 point3 point4 U A G C D F E P incl a b c d e f comp ad bc p
    middleFiberSize hCP conjugatedF
  have hconj : conjugatedF = D := by
    have hp : p.element = 1 := rfl
    change D.map (MulAut.conj (p.element : U)).toMonoidHom = D
    rw [hp]
    exact conj_one D
  rw [hconj]
  have hCG : C ≤ G := by
    change SmallerParabolicProjectionAux.C ≤ SmallerParabolicProjectionAux.G
    rw [← SmallerParabolicProjectionAux.intersection]
    exact inf_le_left
  refine ⟨SmallerParabolicProjectionAux.leastRegion, SmallerParabolicProjectionAux.intersection, ?_, ?_⟩
  · have hi : C.relIndex (G ⊓ P) = 1 := by
      rw [SmallerParabolicProjectionAux.intersection, Subgroup.relIndex_self]
    rw [← hi]
    exact SmallerParabolicProjectionAux.inclusionFiber le_top le_top hCG hCP _ rfl
  · have hi : C.relIndex (G ⊓ A) = 3 := by
      change C.relIndex (G ⊓ ⊤) = 3
      rw [inf_top_eq]
      exact SmallerParabolicProjectionAux.ambientIndex
    rw [← hi]
    exact SmallerParabolicProjectionAux.inclusionFiber le_top le_top hCG le_top _ rfl
