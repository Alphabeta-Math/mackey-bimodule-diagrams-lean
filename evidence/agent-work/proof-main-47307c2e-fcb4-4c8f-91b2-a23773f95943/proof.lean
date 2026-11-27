by
  classical
  intro U inst K H G α β conjugate hα hβ a b A B J σ hσ Lj left right dot
    kg gk gh M inner finiteFibers inclusion projection outer full cupProjection
  have hK (k : K) : α * (k : U) * α⁻¹ ∈ G := (a.toHom k).property
  have hH (h : H) : β * (h : U) * β⁻¹ ∈ G := (b.toHom h).property
  let f (j : J) (S : Subgroup U) (hS : S ≤ Lj j) :=
    Generator.mixedMultiplicationBasis a b (left j S hS) (right j S hS) (dot j S hS)
  let orbit (j : J) := DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
  -- Xiao, §5.1, “Smaller internal groups and intersections” (archived
  -- p. 17, revised published p. 19), invokes Proposition 5.1. The reviewed
  -- plan has no numbered Alphabeta Math proof for this endpoint.
  -- Steps 1–4 of the registered MixedCrossingComposites proof identify the
  -- multiplication and finite transfer on basis vectors. The registered
  -- smaller-group supplier gives their composite after fixing this exact
  -- representative, including the image and the relative fiber cardinality.
  have data (j : J) (S : Subgroup U) (hS : S ≤ Lj j) (h : S.IsFiniteRelIndex (Lj j)) :
      (∃ (hf : finiteFibers j S hS) (hfJ : finiteFibers j (Lj j) (full j)),
        (outer j S hS hf).eval =
          (Diagram.scale (S.relIndex (Lj j) : Complex) (outer j (Lj j) (full j) hfJ)).eval) ∧
      Set.range (fun w => Generator.mixedProduct a b (f j S hS w)) = orbit j ∧
      (∀ g ∈ orbit j, Nat.card {w | Generator.mixedProduct a b (f j S hS w) = g}
        = S.relIndex (Lj j)) := by
    obtain ⟨hf, hfJ, houter, hRange, _, _, hCard, _, _⟩ :=
      MixedCrossingsThroughSmallerGroup K H G α β hK hH σ hσ j S hS h
    exact ⟨⟨hf, hfJ, houter⟩, hRange, fun g hg => (hCard g hg).1⟩
  refine ⟨fun j S hS h => (data j S hS h).1, ?_⟩
  intro J₀ _ I L hL
  refine ⟨?_, ?_⟩
  · intro i j
    have hInv : (β⁻¹ * (σ i.val : U)⁻¹)⁻¹ * (β⁻¹ * (σ j.val : U)⁻¹) =
        (σ i.val : U) * (σ j.val : U)⁻¹ := by group
    exact (ConjEmbedding.ofConjugator_eq_iff _ _ _ _).trans (by rw [hInv])
  intro hIndex
  choose hfL hfJ hOuter using fun j : I => (data j.val L (hL j) (hIndex j)).1
  refine ⟨hfL, hfJ, ?_⟩
  intro n restricted usual normalized V term
  have hNorm (j : I) : (normalized j).eval = (usual j).eval := by
    have : L.IsFiniteRelIndex (Lj j.val) := hIndex j
    have hn : n j ≠ 0 := by
      change (L.relIndex (Lj j.val) : Complex) ≠ 0
      exact_mod_cast (Subgroup.index_ne_zero (H := L.subgroupOf (Lj j.val)) :
        L.relIndex (Lj j.val) ≠ 0)
    apply Biset.Hom.ext
    apply LinearMap.ext
    intro x
    change (n j)⁻¹ • ((restricted j).eval.toLinearMap x) = (usual j).eval.toLinearMap x
    rw [hOuter j]
    change (n j)⁻¹ • (n j • (usual j).eval.toLinearMap x) = _
    rw [← mul_smul, inv_mul_cancel₀ hn, one_smul]
  have orbit_iff (j : J) (g : G) : g ∈ orbit j ↔ DoubleCoset.mk A B g = j := by
    calc
      g ∈ orbit j ↔ DoubleCoset.mk A B g = DoubleCoset.mk A B (σ j) := by
        constructor
        · intro hg
          exact (DoubleCoset.eq.mpr (DoubleCoset.mem_doubleCoset.mp hg)).symm
        · intro hg
          exact DoubleCoset.mem_doubleCoset.mpr (DoubleCoset.eq.mp hg.symm)
      _ ↔ DoubleCoset.mk A B g = j := by rw [hσ j]
  have range_iff (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
      (hi : S.IsFiniteRelIndex (Lj j)) (z : M.basis.carrier) :
      z ∈ Set.range (f j S hS) ↔ DoubleCoset.mk A B (Generator.mixedProduct a b z) = j := by
    let e := Generator.mixedEquiv a b
    change z ∈ Set.range (f j S hS) ↔ DoubleCoset.mk A B (e z) = j
    rw [← orbit_iff, ← (data j S hS hi).2.1]
    exact ⟨fun ⟨w, hw⟩ => ⟨w, congrArg e hw⟩,
      fun ⟨w, hw⟩ => ⟨w, e.injective hw⟩⟩
  have hOrth (i j : I) (hij : i ≠ j) :
      (Diagram.vertical (inclusion i.val L (hL i)) (projection j.val L (hL j) (hfL j))).eval =
        (Diagram.zero (inner i.val L (hL i)) (inner j.val L (hL j))).eval := by
    apply Biset.Hom.projection_between_disjoint (f j.val L (hL j))
      (Generator.mixedMultiplication_equivariant a b _ _ _) (hfL j)
      (f i.val L (hL i)) (Generator.mixedMultiplication_equivariant a b _ _ _)
    apply Set.disjoint_left.mpr
    intro z hzj hzi
    exact hij (Subtype.ext (((range_iff i.val L (hL i) (hIndex i) z).mp hzi).symm.trans
      ((range_iff j.val L (hL j) (hIndex j) z).mp hzj)))
  have hSelf (j : J) : (Lj j).IsFiniteRelIndex (Lj j) :=
    inferInstance
  have hColumn (z : M.basis.carrier) (j : I) :
      term usual (Finsupp.single z 1) j =
        if j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)
        then Finsupp.single z 1 else 0 := by
    rw [show term usual (Finsupp.single z 1) j =
        Finsupp.single z ((hfJ j z).toFinset.card : Complex) from
      Diagram.projection_then_inclusion_single Complex a b _ _ _ (hfJ j) z]
    by_cases h : j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)
    · rw [ite_eq_left h]
      have hs : {w | f j.val (Lj j.val) (full j.val) w = z} =
          {w | Generator.mixedProduct a b (f j.val (Lj j.val) (full j.val) w) =
            Generator.mixedProduct a b z} :=
        Set.ext fun w => (Generator.mixedEquiv a b).injective.eq_iff.symm
      have hc : (hfJ j z).toFinset.card = 1 := by
        calc
          _ = Nat.card {w | f j.val (Lj j.val) (full j.val) w = z} :=
            CommonMackeyIntersectionSumAux.cardFiber _ (hfJ j z)
          _ = 1 := by
            rw [hs, (data j.val (Lj j.val) (full j.val) (hSelf j.val)).2.2 _
              ((orbit_iff j.val _).mpr h.symm), Subgroup.relIndex_self]
      rw [hc, Nat.cast_one]
    · rw [ite_eq_right h]
      have hempty : (hfJ j z).toFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact h (((range_iff j.val (Lj j.val) (full j.val) (hSelf j.val) z).mp
          ⟨w, (hfJ j z).mem_toFinset.mp hw⟩).symm)
      rw [hempty, Finset.card_empty, Nat.cast_zero, Finsupp.single_zero]
  have hTerm (x : V) : term normalized x = term usual x :=
    funext fun j => congrArg (fun m => m.toLinearMap x) (hNorm j)
  have hBasis (z : M.basis.carrier) :
      Function.support (term usual (Finsupp.single z 1)) =
        {j : I | j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)} := by
    ext j
    change (term usual (Finsupp.single z 1) j ≠ 0) ↔ _
    rw [hColumn]
    by_cases h : j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)
    · simp [h]
    · simp [h]
  -- MackeyIdentityDiagram sums a complete partition and uses comap
  -- subgroups to index its quotient. The selected family need not cover
  -- the basis. Use its basis-support argument on the selected subtype.
  -- Active indices inject into the finite image of the support of x.
  let coset := fun z : M.basis.carrier => DoubleCoset.mk A B (Generator.mixedProduct a b z)
  have finiteJ (x : V) : Set.Finite (Function.support (term usual x)) := by
    have hb : Set.Finite {j : I | j.val ∈ x.support.image coset} :=
      (x.support.image coset).finite_toSet.preimage Subtype.val_injective.injOn
    apply hb.subset
    intro j hj
    by_contra h
    apply hj
    have hs : (∑ z ∈ x.support, Finsupp.single z (x z)) = x := Finsupp.sum_single x
    change (usual j).eval.toLinearMap x = 0
    rw [← hs, map_sum]
    apply Finset.sum_eq_zero
    intro z hz
    have hne : j.val ≠ coset z := fun he => h (Finset.mem_image.mpr ⟨z, hz, he.symm⟩)
    have hp : Finsupp.single z (x z) = (x z) • Finsupp.single z (1 : Complex) := by
      simp [Finsupp.smul_single, smul_eq_mul]
    rw [hp, map_smul]
    change (x z) • term usual (Finsupp.single z 1) j = 0
    rw [hColumn, ite_eq_right hne, smul_zero]
  have finiteL (x : V) : Set.Finite (Function.support (term normalized x)) :=
    hTerm x ▸ finiteJ x
  refine ⟨hNorm, hOrth, ?_, ⟨finiteL, finiteJ, ?_⟩, ?_⟩
  · intro z
    exact ⟨(congrArg Function.support (hTerm _)).trans (hBasis z), hBasis z⟩
  · intro x
    have hFinset : (finiteL x).toFinset = (finiteJ x).toFinset := by
      ext j
      simp only [Set.Finite.mem_toFinset, hTerm x]
    rw [hFinset, hTerm x]
  · intro hJ₀ cupsL cupsJ indices withCupL withCupJ sumDiagrams
    have hCups (j : I) :
        (withCupL j).eval = (normalized j).eval ∧ (withCupJ j).eval = (usual j).eval := by
      exact ⟨CommonMackeyIntersectionSumAux.scaledCupOuter_eval a b
        (left j.val L (hL j)) (right j.val L (hL j)) (dot j.val L (hL j))
        (cupsL j) (hfL j) (n j)⁻¹,
        CommonMackeyIntersectionSumAux.cupOuter_eval a b
          (left j.val (Lj j.val) (full j.val)) (right j.val (Lj j.val) (full j.val))
          (dot j.val (Lj j.val) (full j.val)) (cupsJ j) (hfJ j)⟩
    exact ⟨CommonMackeyIntersectionSumAux.sumDiagram_eval_eq withCupL withCupJ
      (fun j => (hCups j).1.trans ((hNorm j).trans (hCups j).2.symm)) indices, hCups⟩
