by
  open MackeyDiagrams MackeyDiagrams.Diagram ReverseCupBendSupport in
  intro U _ K H G a b
  dsimp only
  intro finite
  -- Xiao, §3.5, Proposition 3.4, reverse-cup row. The archived original
  -- PDF has the diagrams on p. 12 and the computation on p. 13
  -- (SHA256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2).
  -- The revised published PDF has them on pp. 14 and 15 respectively
  -- (SHA256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  --
  -- Alphabeta Math's module tensor universal property, Steps 3.1 and 4.1,
  -- descends along the balance relations. The shared biset tensor already
  -- performs that descent, and pair_balance applies it to the two basis
  -- representatives of the right unital insertion. As in Step 5.1, equality
  -- follows on generators, here the group elements with coefficient one.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  --
  -- FiniteIndexReverseAdjunction supplies the right transversal and the
  -- cup formula on group elements after transport to a conjugating
  -- representative. The shared merge/split basis rules underlying
  -- InductionRestrictionMergesAndSplits apply directly to a and b.
  -- The associate and trace basis rules apply to the resulting pairs.
  -- Its cup formula uses rightCosetEquivCapFiber and computes transfer
  -- coefficients with transferBasis_apply. The public projection of
  -- that formula already gives the required sum over representatives.
  have finiteAlpha : a.toHom.range.FiniteIndex := by
    let := finite
    have h : ((b.comp a).toHom.range.comap b.toHom).FiniteIndex := inferInstance
    change ((b.toHom.comp a.toHom).range.comap b.toHom).FiniteIndex at h
    rw [MonoidHom.range_comp, Subgroup.comap_map_eq_self_of_injective b.injective] at h
    exact h
  change ((BentVertex.reverseCup b a finiteAlpha).expand (R := Complex)).eval =
    (rightBend a b finite).eval
  classical
  obtain ⟨⟨S, hS⟩, cupLarge⟩ := cupTransversal (b.comp a) finite
  have cupSmall := (cupTransversal a finiteAlpha).2
  -- The article chooses a product transversal and isolates the slice
  -- indexed by the identity coset. For an arbitrary large transversal,
  -- pull back that slice along b.toHom. This gives the same surviving
  -- terms without requiring a separate choice of outer representatives.
  let T := S.preimage b.toHom b.injective.injOn
  have memT (t : H) : t ∈ T ↔ b.toHom t ∈ S := Finset.mem_preimage
  have cosetTest (x y : H) :
      b.toHom x * (b.toHom y)⁻¹ ∈ (b.comp a).toHom.range ↔
        x * y⁻¹ ∈ a.toHom.range := by
    rw [← map_inv, ← map_mul]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, b.injective hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg b.toHom hk⟩
  have hT : RightTransversal a T := by
    intro h
    obtain ⟨s, hs, unique⟩ := hS (b.toHom h)
    have hsImage : s.val ∈ b.toHom.range := by
      obtain ⟨k, hk⟩ := hs
      refine ⟨(a.toHom k)⁻¹ * h, ?_⟩
      rw [map_mul, map_inv, ← ConjEmbedding.comp_apply, hk]
      group
    obtain ⟨t, ht⟩ := hsImage
    have htT : t ∈ T := (memT t).2 (ht.symm ▸ s.property)
    refine ⟨⟨t, htT⟩, (cosetTest h t).1 ?_, ?_⟩
    · rwa [ht]
    · intro u hu
      apply Subtype.ext
      apply b.injective
      have he := unique ⟨b.toHom u.val, (memT u.val).1 u.property⟩ ((cosetTest h u.val).2 hu)
      exact (congrArg Subtype.val he).trans ht.symm
  have smallAtOne := cupSmall T hT (1 : H)
  simp only [one_mul] at smallAtOne
  apply eval_ext_on_generators
  intro g
  change G at g
  rw [leftSum a b finiteAlpha g T smallAtOne, rightSum a b finite g S (cupLarge S hS g)]
  calc
    _ = ∑ s ∈ S.filter (fun s => s ∈ b.toHom.range), rightTerm a b g s := by
      refine Finset.sum_bij (fun t _ => b.toHom t) ?_ ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_filter.mpr ⟨(memT t).1 ht, ⟨t, rfl⟩⟩
      · intro t _ u _ he
        exact b.injective he
      · intro s hs
        obtain ⟨hsS, t, ht⟩ := Finset.mem_filter.mp hs
        exact ⟨t, (memT t).2 (ht.symm ▸ hsS), ht⟩
      · intro t _
        simp only [rightTerm, Generator.traceBasis_image, outputSingle]
        rw [Biset.pairLinear_single, one_mul]
    _ = _ := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro s hs hsFiltered
      have hsOutside : ¬ ∃ t : H, b.toHom t = s := by
        intro himage
        exact hsFiltered (Finset.mem_filter.mpr ⟨hs, himage⟩)
      simp only [rightTerm, Generator.traceBasis_outside Complex b s hsOutside, map_zero]
