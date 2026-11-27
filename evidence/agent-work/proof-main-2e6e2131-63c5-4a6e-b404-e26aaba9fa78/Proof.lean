by
  classical
  intro U inst K H G L α β a b hα hβ ha hb hs eα eβ ea eb d s A B J σ hσ
    j orbit Ls Limage finiteIndex n X Y qBasis q fiber ι finiteFibers traceArg survives
    rightTransversal
  -- Article §5.1, Proposition 5.1 proof. The shared balanced basis and typed
  -- generators supply the balancing, intertwining, multiplication and trace
  -- rules. The functor-level strand and adjunction comparisons are unnecessary
  -- for these basis columns.
  have hLimage : MixedCrossingFiberMapsAux.diagonal eα ea = Limage :=
    MixedCrossingFiberMapsAux.diagonal_range α a hα ha
  have hLs : MixedCrossingFiberMapsAux.intersection eα eβ s = Ls := by
    change (MixedCrossingFiberMapsAux.leftHom eα).range ⊓
      (MixedCrossingFiberMapsAux.rightHom eβ s).range = _
    rw [MixedCrossingFiberMapsAux.leftHom_range α hα,
      MixedCrossingFiberMapsAux.rightHom_range β hβ s]
  have hLe := MixedCrossingFiberMapsAux.diagonal_le eα eβ ea eb d
  change MixedCrossingFiberMapsAux.diagonal eα ea ≤
    MixedCrossingFiberMapsAux.intersection eα eβ s at hLe
  rw [hLimage, hLs] at hLe
  have hsOrbit : s ∈ orbit := by
    change s ∈ DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
    exact DoubleCoset.mem_doubleCoset.2 (DoubleCoset.eq.1 (hσ j))
  have hRange : Set.range q = orbit :=
    (MixedCrossingFiberMapsAux.range_q eα eβ ea eb d).trans
      (DoubleCoset.doubleCoset_eq_of_mem hsOrbit)
  have hcard (g : G) (hg : g ∈ orbit) : Nat.card (fiber g) = n := by
    have hc := MixedCrossingFiberMapsAux.fiber_card eα eβ ea eb d g (hRange.symm ▸ hg)
    change Nat.card (fiber g) =
      (MixedCrossingFiberMapsAux.diagonal eα ea).relIndex
        (MixedCrossingFiberMapsAux.intersection eα eβ s) at hc
    rw [hLimage, hLs] at hc
    exact hc
  have hfinite : finiteFibers ↔ finiteIndex := by
    have hf := MixedCrossingFiberMapsAux.all_finite_iff eα eβ ea eb d
    change finiteFibers ↔ (MixedCrossingFiberMapsAux.diagonal eα ea).IsFiniteRelIndex
      (MixedCrossingFiberMapsAux.intersection eα eβ s) at hf
    rw [hLimage, hLs] at hf
    exact hf
  have hinfinite (g : G) (hg : g ∈ orbit) (hi : ¬ finiteIndex) : Set.Infinite (fiber g) := by
    have hf := MixedCrossingFiberMapsAux.fiber_finite eα eβ ea eb d g (hRange.symm ▸ hg)
    change (fiber g).Finite ↔ (MixedCrossingFiberMapsAux.diagonal eα ea).IsFiniteRelIndex
      (MixedCrossingFiberMapsAux.intersection eα eβ s) at hf
    rw [hLimage, hLs] at hf
    exact fun h => hi (hf.1 h)
  refine ⟨hLe, MixedCrossingFiberMapsAux.q_pair eα eβ ea eb d,
    MixedCrossingFiberMapsAux.multiplication_eval eα eβ ea eb d, hRange,
    fun g hg _ => hcard g hg, hfinite, hinfinite, MixedCrossingFiberMapsAux.cap_finite_iff eb,
    fun T hT g hg hi => MixedCrossingFiberMapsAux.survivors_infinite eα eβ ea eb d T hT g
      (hinfinite g hg hi), ?_⟩
  intro hf
  exact ⟨MixedCrossingFiberMapsAux.projection_eval eα eβ ea eb d hf,
    MixedCrossingFiberMapsAux.projection_transversal eα eβ ea eb d hf⟩
