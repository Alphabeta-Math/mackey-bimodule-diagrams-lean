by
  open MackeyDiagrams MackeyDiagrams.Diagram TraceCapBendSupport in
  intro U _ K H G a b finite
  -- Xiao, §3.5, Proposition 3.4, trace-cap row. Archived PDF pp. 12–13
  -- (bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and revised published PDF pp. 14–15
  -- (6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e)
  -- give the same ordered boundary K–G–H to K–H and the same trace calculation.
  -- Step 3.1 of Alphabeta Math's module tensor universal property factors
  -- through the balance relations. The shared evaluator handles that descent.
  -- Step 4.1 compares maps on elementary tensors. Here Quotient.inductionOn
  -- gives representatives of balanced pairs and eval_ext_on_generators
  -- extends the comparison linearly. Step 5.1 needs no choice for descent.
  -- The finite transversal below comes from the reverse-cup formula.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  change ((BentVertex.traceCap b a).expand (R := Complex)).eval =
    (vertical (horizontal (id (.down (b.comp a))) ((BentVertex.reverseCup b a finite).expand))
      (tail a b)).eval
  classical
  -- Use the registered reverse-adjunction theorem only for its cup formula
  -- and unique right transversal, instantiated at the inner finite-index image.
  -- The companion merges/splits theorem builds from the same shared basis rules.
  -- Those rules apply here directly to a and b, without choosing conjugators
  -- for the merge or split. The trace tests use the coordinator's basis rules.
  obtain ⟨T, hT, hcup⟩ := cup_transversal a finite
  apply eval_ext_on_generators
  intro z
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change G at x y
  let input := Finsupp.single ((Word.down (b.comp a)).basis.pair (Word.up b).basis x y) (1 : Complex)
  change ((BentVertex.traceCap b a).expand (R := Complex)).eval.toLinearMap input =
    (vertical (horizontal (id (.down (b.comp a))) ((BentVertex.reverseCup b a finite).expand))
      (tail a b)).eval.toLinearMap input
  dsimp only [input]
  rw [left_single a b x y, right_sum a b finite x y T hcup]
  let term (t : H) : H →₀ Complex :=
    (leftUnit (R := Complex) (.down a)).eval.toLinearMap
      (Biset.pairLinear Complex (Word.empty K).basis (Word.down a).basis
        (Generator.traceBasis Complex (b.comp a) (x * (y * b.toHom t⁻¹))) (Finsupp.single t 1))
  change Generator.traceBasis Complex b (x * y) = ∑ t ∈ T, term t
  -- Multiplying by the image of t⁻¹ reduces the large trace to a
  -- test on the corresponding right coset in H when x * y is in the image.
  have product (t : H) :
      x * (y * b.toHom t⁻¹) = (x * y) * (b.toHom t)⁻¹ := by
    rw [map_inv, mul_assoc]
  have zeroTerm (t : H) (hout : ¬ ∃ k : K, (b.comp a).toHom k = x * (y * b.toHom t⁻¹)) :
      term t = 0 := by
    dsimp only [term]
    rw [Generator.traceBasis_outside Complex (b.comp a) _ hout, map_zero, LinearMap.zero_apply, map_zero]
  by_cases hin : ∃ h : H, b.toHom h = x * y
  · obtain ⟨h, hh⟩ := hin
    rw [← hh, Generator.traceBasis_image]
    -- Exactly one representative survives the large trace.
    obtain ⟨t, ht, unique⟩ := hT h
    obtain ⟨k, hk⟩ := ht
    have htProduct : x * (y * b.toHom (t.val)⁻¹) = (b.comp a).toHom k := by
      rw [product, ← hh, ← map_inv, ← map_mul, ← hk, ConjEmbedding.comp_apply]
    have hterm : term t.val = Finsupp.single h 1 := by
      dsimp only [term]
      rw [htProduct, Generator.traceBasis_image, Biset.pairLinear_single, one_mul,
        eval_leftUnit_single]
      change Finsupp.single (a.toHom k * t.val * (1 : H)⁻¹) 1 = _
      rw [hk, inv_one, mul_one, mul_assoc, inv_mul_cancel, mul_one]
    rw [Finset.sum_eq_single t.val, hterm]
    · intro s hs hst
      apply zeroTerm
      rintro ⟨l, hl⟩
      rw [product, ← hh, ← map_inv, ← map_mul, ConjEmbedding.comp_apply] at hl
      have hm : h * s⁻¹ ∈ a.toHom.range := ⟨l, b.injective hl⟩
      exact hst (congrArg Subtype.val (unique ⟨s, hs⟩ hm))
    · exact fun hmissing => (hmissing t.property).elim
  · -- The composite image is contained in the outer image, which is
    -- invariant under multiplication by b.toHom t.
    rw [Generator.traceBasis_outside Complex b _ hin]
    symm
    apply Finset.sum_eq_zero
    intro t _
    apply zeroTerm
    rintro ⟨k, hk⟩
    rw [product, ConjEmbedding.comp_apply] at hk
    apply hin
    refine ⟨a.toHom k * t, ?_⟩
    rw [map_mul, hk, mul_assoc, inv_mul_cancel, mul_one]
