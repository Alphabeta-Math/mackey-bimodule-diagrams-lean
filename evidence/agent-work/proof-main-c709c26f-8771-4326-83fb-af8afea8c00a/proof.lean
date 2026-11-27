by
  classical
  -- Xiao, Example 8.1 [ex:curl-join-s3], archived PDF p. 34 and published
  -- 28 November revision p. 36. The revised diagram convention compares
  -- evaluated maps. Both ordered stacks are preserved in each orientation.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  intro _finitary _U _blockSym _S _H _swap _hSwap _p _q _r _hpq _hqr
    _A _B hA hB I J _inclusion _parabolic
  have hI : I = ⊥ := UnequalParabolicCurlProof.concrete_intersection
  have hJ : J = _H := UnequalParabolicCurlProof.concrete_join hA hB
  refine ⟨hI, hJ, ?_⟩
  intro G α hα hG a up down straightUp straightDown finiteIndex curls dA dB dI dJ AB ratio
  have hcH : Nat.card ↥_H = 6 := by
    rw [UnequalParabolicCurlProof.card_block UnequalParabolicCurlProof.S]
    decide
  have hcA : Nat.card ↥_A = 2 := UnequalParabolicCurlProof.card_A
  have hcB : Nat.card ↥_B = 2 := UnequalParabolicCurlProof.card_B
  have hcI : Nat.card ↥I = 1 := by rw [hI, Subgroup.card_bot]
  have hcJ : Nat.card ↥J = 6 := hJ.symm ▸ hcH
  let _ : Finite ↥_H := Finite.of_equiv _
    (UnequalParabolicCurlProof.blockEquiv UnequalParabolicCurlProof.S)
  have fA : finiteIndex dA := inferInstanceAs (Subgroup.FiniteIndex dA.toHom.range)
  have fB : finiteIndex dB := inferInstanceAs (Subgroup.FiniteIndex dB.toHom.range)
  have fI : finiteIndex dI := inferInstanceAs (Subgroup.FiniteIndex dI.toHom.range)
  have fJ : finiteIndex dJ := inferInstanceAs (Subgroup.FiniteIndex dJ.toHom.range)
  refine ⟨fA, fB, fI, fJ, ?_⟩
  intro cA cB cI cJ joinIntersectionUp joinIntersectionDown originalUp originalDown evalUp evalDown
  -- The two inputs come from different partitions of the same three-point
  -- carrier. Include the fixed points as singleton blocks to meet the
  -- common-carrier hypothesis of ParabolicCurlJoinIntersection.
  have hscaled := by
    have hG' : UnequalParabolicCurlProof.parabolic G := by
      obtain ⟨T, P, hnonempty, hdisjoint, hcover, hgroup⟩ := hG
      exact ⟨T, P, ⟨hnonempty, hdisjoint, hcover⟩, hgroup⟩
    obtain ⟨hP, eP⟩ := UnequalParabolicCurlProof.pair_partition 1 2 3 (by decide) (by decide)
    obtain ⟨hQ, eQ⟩ := UnequalParabolicCurlProof.pair_partition 2 3 1 (by decide) (by decide)
    rw [show ({2, 3, 1} : Finset Nat) = UnequalParabolicCurlProof.S by decide] at hQ
    obtain ⟨hS, eS⟩ := UnequalParabolicCurlProof.singleton_partition UnequalParabolicCurlProof.S ⟨1, by decide⟩
    exact UnequalParabolicCurlProof.compare_stacks α hα ⟨UnequalParabolicCurlProof.S, {UnequalParabolicCurlProof.S}, hS, eS⟩ hG'
      UnequalParabolicCurlProof.S _ _ hP hQ
      (UnequalParabolicCurlProof.block_A.symm.trans eP)
      (UnequalParabolicCurlProof.block_B.symm.trans eQ) hA hB fA fB fI fJ
  have hratio : ratio = (2 / 3 : Complex) := by
    change (Nat.card ↥AB : Complex) / (Nat.card ↥J : Complex) = _
    have hAB : Nat.card ↥AB = 4 := by
      change Nat.card ↥(Set.image2 (fun x y => x * y) (_A : Set _U) (_B : Set _U)) = 4
      rw [UnequalParabolicCurlProof.card_product_of_inf_eq_bot _A _B hI, hcA, hcB]
    rw [hAB, hcJ]
    norm_num
  have indexA : dA.toHom.range.index = 3 := by
    have e := UnequalParabolicCurlProof.inclusion_index hA
    change dA.toHom.range.index * Nat.card ↥_A = Nat.card ↥_H at e
    rw [hcA, hcH] at e
    omega
  have indexB : dB.toHom.range.index = 3 := by
    have e := UnequalParabolicCurlProof.inclusion_index hB
    change dB.toHom.range.index * Nat.card ↥_B = Nat.card ↥_H at e
    rw [hcB, hcH] at e
    omega
  have indexI : dI.toHom.range.index = 6 := by
    have e := UnequalParabolicCurlProof.inclusion_index (le_trans inf_le_left hA : I ≤ _H)
    change dI.toHom.range.index * Nat.card ↥I = Nat.card ↥_H at e
    rw [hcI, hcH] at e
    omega
  have indexJ : dJ.toHom.range.index = 1 := by
    have e := UnequalParabolicCurlProof.inclusion_index (sup_le hA hB : J ≤ _H)
    change dJ.toHom.range.index * Nat.card ↥J = Nat.card ↥_H at e
    rw [hcJ, hcH] at e
    omega
  have eA := UnequalParabolicCurlProof.eval_curls α hα hA fA
  have eB := UnequalParabolicCurlProof.eval_curls α hα hB fB
  have eI := UnequalParabolicCurlProof.eval_curls α hα (le_trans inf_le_left hA : I ≤ _H) fI
  have eJ := UnequalParabolicCurlProof.eval_curls α hα (sup_le hA hB : J ≤ _H) fJ
  change evalUp joinIntersectionUp = evalUp (.scale ratio originalUp) ∧
    evalDown joinIntersectionDown = evalDown (.scale ratio originalDown) at hscaled
  rw [hratio] at hscaled ⊢
  refine ⟨hscaled.1, hscaled.2, ?_, ?_, ?_, ?_⟩
  -- Each curl evaluates at its finite index. Vertical composition multiplies
  -- the scalars at the same boundary and keeps the lower and upper curls ordered.
  · have e := UnequalParabolicCurlProof.eval_stack cJ.1 cI.1 _ _ eJ.1 eI.1
    change evalUp joinIntersectionUp =
      evalUp (.scale ((dJ.toHom.range.index : Complex) * (dI.toHom.range.index : Complex)) straightUp) at e
    norm_num [indexJ, indexI] at e
    exact e
  · have e := UnequalParabolicCurlProof.eval_stack cB.1 cA.1 _ _ eB.1 eA.1
    change evalUp originalUp =
      evalUp (.scale ((dB.toHom.range.index : Complex) * (dA.toHom.range.index : Complex)) straightUp) at e
    norm_num [indexB, indexA] at e
    exact e
  · have e := UnequalParabolicCurlProof.eval_stack cJ.2 cI.2 _ _ eJ.2 eI.2
    change evalDown joinIntersectionDown =
      evalDown (.scale ((dJ.toHom.range.index : Complex) * (dI.toHom.range.index : Complex)) straightDown) at e
    norm_num [indexJ, indexI] at e
    exact e
  · have e := UnequalParabolicCurlProof.eval_stack cB.2 cA.2 _ _ eB.2 eA.2
    change evalDown originalDown =
      evalDown (.scale ((dB.toHom.range.index : Complex) * (dA.toHom.range.index : Complex)) straightDown) at e
    norm_num [indexB, indexA] at e
    exact e
