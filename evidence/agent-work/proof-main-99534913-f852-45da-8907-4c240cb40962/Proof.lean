by
  classical
  intro U inst K H G L α β a b hα hβ ha hb hs eα eβ ea eb d s A B J σ hσ
    conjSubgroup Lj leftJ rightJ Mj M ML Ls Limage n qBasis q hIndex
  -- This item has no matching Alphabeta Math portal entry in the reviewed plan.
  -- Steps 1–3 of the argument in Xiao, §5.1, Proposition 5.1: the typed
  -- generators encode the balanced push and the reverse-cup/trace fiber sum.
  -- MixedCrossingFiberMaps supplies the image and stabilizer index at s,
  -- with finite relative index hIndex. This computes the cardinal directly
  -- at the original label, so Lemma 5.2's transport is unnecessary.
  obtain ⟨_, _, _, range_q, card_q, finite_q, _⟩ :=
    MixedCrossingFiberMaps K H G L α β a b hα hβ ha hb hs σ hσ
  have hf : ∀ z : M.basis.carrier, Set.Finite {w | qBasis w = z} := finite_q.mpr hIndex
  refine ⟨hf, ?_⟩
  intro ι p pThenIota iotaThenP straight evaluate orbit P finiteQ j hj
  -- Mathlib's DoubleCoset.eq converts s ∈ orbit j into the equality of classes
  -- using hσ. This connects the supplier's chosen class to the requested P j.
  have hj_eq : DoubleCoset.mk A B s = j := by
    rw [← hσ j]
    exact (DoubleCoset.eq.mpr (DoubleCoset.mem_doubleCoset.mp hj)).symm
  have hRange : Set.range q = orbit j := by
    rw [← hj_eq]
    exact range_q
  have hCard (g : G) (hg : g ∈ orbit j) : Nat.card {w | q w = g} = n := by
    rw [← hj_eq] at hg
    exact card_q g hg hIndex
  have hp : evaluate p = (MackeyDiagrams.Diagram.mixedProjection (R := Complex) eα eβ ea eb d hf).eval :=
    MixedCrossingCompositesAux.projection_eval eα eβ ea eb d hf
  have hι : evaluate ι = (MackeyDiagrams.Diagram.mixedMultiplication (R := Complex) eα eβ ea eb d).eval :=
    MixedCrossingCompositesAux.multiplication_eval eα eβ ea eb d
  let outer := MackeyDiagrams.Generator.mixedEquiv eα eβ
  have memOuter (z : M.basis.carrier) (w : ML.basis.carrier) :
      w ∈ (hf z).toFinset ↔ q w = outer z := by
    rw [(hf z).mem_toFinset]
    change qBasis w = z ↔ outer (qBasis w) = outer z
    exact outer.injective.eq_iff.symm
  have outerCard (z : M.basis.carrier) (hz : outer z ∈ orbit j) :
      (hf z).toFinset.card = n := by
    have hFinite : Set.Finite {w | q w = outer z} :=
      (hf z).subset fun _ hw => outer.injective hw
    exact (MixedCrossingCompositesAux.fiberCard q (outer z) hFinite _ (memOuter z)).symm.trans
      (hCard (outer z) hz)
  have innerFinset (z : ML.basis.carrier) :
      (hf (qBasis z)).toFinset = (finiteQ z).toFinset :=
    Finset.ext fun w => (memOuter (qBasis z) w).trans (finiteQ z).mem_toFinset.symm
  have innerCard (z : ML.basis.carrier) : (finiteQ z).toFinset.card = n := by
    rw [← innerFinset]
    exact outerCard (qBasis z) (hRange ▸ ⟨z, rfl⟩)
  -- Step 4: compose transfer and push in both orders. The compact
  -- projection needs only finite surviving fibers, as in the paragraph
  -- following the proof. The singleton evaluation adapters preserve
  -- the two labelled drawing stacks in the statement.
  have hInner (z : ML.basis.carrier) :
      (evaluate iotaThenP).toLinearMap (Finsupp.single z 1) =
        (finiteQ z).toFinset.sum (fun w => Finsupp.single w (1 : Complex)) := by
    change ((evaluate ι).vertical (evaluate p)).toLinearMap _ = _
    rw [hp, hι, ← innerFinset]
    exact MackeyDiagrams.Diagram.inclusion_then_projection_single Complex eα eβ ea eb d hf z
  have hOuter (z : M.basis.carrier) :
      (evaluate pThenIota).toLinearMap (Finsupp.single z 1) =
        Finsupp.single z ((hf z).toFinset.card : Complex) := by
    change ((evaluate p).vertical (evaluate ι)).toLinearMap _ = _
    rw [hp, hι]
    exact MackeyDiagrams.Diagram.projection_then_inclusion_single Complex eα eβ ea eb d hf z
  -- Step 5: an identity column has its own
  -- coefficient one and every other coefficient zero. The scaled
  -- column therefore imposes incompatible equations when n > 1.
  let z₀ : ML.basis.carrier := MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction ea) (MackeyDiagrams.Biset.restriction eb) 1 1
  have self_mem (z : ML.basis.carrier) : z ∈ (finiteQ z).toFinset :=
    (finiteQ z).mem_toFinset.mpr rfl
  have strict_fiber (hn : 1 < n) :
      ∃ w ∈ (finiteQ z₀).toFinset, w ≠ z₀ := by
    by_contra! h
    have hle := Finset.card_le_one.mpr
      (fun w hw v hv => (h w hw).trans (h v hv).symm)
    exact (not_le_of_gt hn) ((innerCard z₀) ▸ hle)
  have straight_column (z : ML.basis.carrier) :
      (evaluate straight).toLinearMap (Finsupp.single z 1) = Finsupp.single z 1 := rfl
  refine ⟨?_, hInner, ?_, ?_⟩
  · apply Finsupp.lhom_ext'
    intro z
    apply LinearMap.ext_ring
    change (evaluate pThenIota).toLinearMap (Finsupp.single z 1) =
      ((n : Complex) • P j) (Finsupp.single z 1)
    rw [hOuter]
    have hP : (P j) (Finsupp.single z 1) =
        if outer z ∈ orbit j then Finsupp.single z (1 : Complex) else 0 := by
      dsimp only [P]
      rw [Finsupp.lsum_single]
      change (if outer z ∈ orbit j then Finsupp.lsingle z else 0) (1 : Complex) = _
      by_cases hz : outer z ∈ orbit j <;> simp [hz]
    rw [LinearMap.smul_apply, hP]
    by_cases hz : outer z ∈ orbit j
    · rw [ite_eq_left hz, outerCard z hz, Finsupp.smul_single, smul_eq_mul, mul_one]
    · have hEmpty : (hf z).toFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact hz (hRange ▸ ⟨w, (memOuter z w).mp hw⟩)
      simp [hz, hEmpty]
  · constructor
    · intro hEq
      have hle : n ≤ 1 := by
        by_contra! hn
        obtain ⟨w, hw, hne⟩ := strict_fiber hn
        have h := hInner z₀
        rw [hEq, straight_column] at h
        have hwEq := congrArg (fun v : ML.basis.carrier →₀ Complex => v w) h
        change Finsupp.single z₀ (1 : Complex) w = _ at hwEq
        rw [MixedCrossingCompositesAux.sum_single_apply, ite_eq_left hw, Finsupp.single_eq_of_ne hne] at hwEq
        exact zero_ne_one hwEq
      rw [← innerCard z₀]
      exact Nat.le_antisymm ((innerCard z₀).symm ▸ hle)
        (Finset.card_pos.mpr ⟨z₀, self_mem z₀⟩)
    · intro hn
      apply MackeyDiagrams.Biset.Hom.ext
      apply Finsupp.lhom_ext'
      intro z
      apply LinearMap.ext_ring
      change (evaluate iotaThenP).toLinearMap (Finsupp.single z 1) =
        (evaluate straight).toLinearMap (Finsupp.single z 1)
      rw [hInner, straight_column]
      have hOne : (finiteQ z).toFinset = {z} :=
        Finset.card_eq_one.mp ((innerCard z).trans hn) |>.elim fun w hw => by
          have hz := self_mem z
          rw [hw, Finset.mem_singleton] at hz
          simpa [hz] using hw
      rw [hOne, Finset.sum_singleton]
  · intro hn c hEq
    obtain ⟨w, hw, hne⟩ := strict_fiber hn
    have hScaled : c • (evaluate iotaThenP).toLinearMap (Finsupp.single z₀ 1) =
        (evaluate straight).toLinearMap (Finsupp.single z₀ 1) :=
      congrArg (fun f => f.toLinearMap (Finsupp.single z₀ 1)) hEq
    rw [hInner, straight_column] at hScaled
    have hzEq := congrArg (fun v : ML.basis.carrier →₀ Complex => v z₀) hScaled
    have hwEq := congrArg (fun v : ML.basis.carrier →₀ Complex => v w) hScaled
    change (_ • _ : ML.basis.carrier →₀ Complex) z₀ = _ at hzEq
    change (_ • _ : ML.basis.carrier →₀ Complex) w = _ at hwEq
    rw [Finsupp.smul_apply, MixedCrossingCompositesAux.sum_single_apply,
      ite_eq_left (self_mem z₀), Finsupp.single_eq_same, smul_eq_mul, mul_one] at hzEq
    rw [Finsupp.smul_apply, MixedCrossingCompositesAux.sum_single_apply,
      ite_eq_left hw, Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_one] at hwEq
    exact one_ne_zero (hzEq.symm.trans hwEq)
