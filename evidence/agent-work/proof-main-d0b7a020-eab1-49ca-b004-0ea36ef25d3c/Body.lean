by
  classical
  open MackeyDiagrams OutsideRegionsAux in
  intro P finitary U parabolic G A D F C E hG hA hD hF hC _hE a b c d e f
    comp bc ad de image conjugate p element lower maximum minimum index
    up down tensor basisMap finiteFibers
  let _ : Finite G := parabolic_finite hG
  let _ : Finite A := parabolic_finite hA
  let _ : Finite D := parabolic_finite hD
  let _ : Finite F := parabolic_finite hF
  let hp : finiteFibers (basisMap a bc de f p) :=
    ((EvaluationForTwoProjections a b c d e f).1 p).2.1.mpr index
  refine ⟨hp, ?_⟩
  intro outside inside vertical horizontal identity parallel project multiply atRight Left Right
    transportLeft transportRight leftFinite rightFinite leftProject rightProject leftMultiply
    rightMultiply targetProject targetMultiply evalProject evalMultiply leftProjectRegions
    rightProjectRegions leftMultiplyRegions rightMultiplyRegions firstProjectionUnitFibers
  let parameter : ProjectionDot.Mixed a bc de f := ⟨p, hp⟩
  -- Xiao, Proposition 8.6, archived original p. 38 (bc57d13777e7df14…),
  -- revised published p. 40 (6d7e885955f23ae6…). The Alphabeta Math
  -- rendering gives the proof in prose and refers to the numbered Cases
  -- 1–4 of Theorems 6.4 and 6.5. These cases fix the two directions and
  -- the two crossing orientations. Compare regions after transport into A.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-three-outside
  -- The relative-index hypothesis supplies the target fiber witness by
  -- the registered Lemma 6.3. All witness diagrams retain their vertices.
  -- Prop. 7.1's meet and join suppliers use partitions of a common support,
  -- so the local adapter pads the two block families with singleton blocks.
  obtain ⟨minParabolic, maxParabolic⟩ :=
    parabolic_region_bounds a b c d element hG hD hF hC
  -- Case 1 and its Case 3 reversal. The registered Theorem 6.4(1)
  -- constructs the right shape at the join, with dots (p⁻¹, 1, 1).
  -- Its middle index is finite in a subgroup of the finite group A.
  obtain ⟨j, v, w, ell, m, n, hj, hright⟩ :=
    right_witness a b c d e f parameter
  let rmin : Right := ⟨⟨minimum.map A.subtype, minParabolic⟩, j, v, w, ell, m.dot, n.dot⟩
  have rminFinite : rightFinite rmin := ⟨m.finite, n.finite⟩
  have minP : minimum ∈ rightProjectRegions :=
    ⟨rmin, rminFinite, hj, (right_project_eval a b c d e f parameter ell m n).2 hright⟩
  have minM : minimum ∈ rightMultiplyRegions :=
    ⟨rmin, hj, (right_mul_eval a b c d e f parameter ell m.dot n.dot).2 hright⟩
  -- Case 2 and its Case 4 reversal. The full-intersection supplier
  -- gives the maximal Case 2 witness. Its restricted-embedding construction
  -- is carried out here for every intermediate parabolic H. Finite domains
  -- justify both transfer maps, and the same dots give the opposite map.
  have leftInterval : ∀ H : Subgroup A, parabolic (H.map A.subtype) →
      lower ≤ H → H ≤ maximum → H ∈ leftProjectRegions ∧ H ∈ leftMultiplyRegions := by
    intro H hH hlo hhi
    obtain ⟨r, s, t, x, y, z, htrans, hparam⟩ := left_witness a b c d e f p H hlo hhi
    let l : Left := ⟨⟨H.map A.subtype, hH⟩, r, s, t, x.dot, y.dot, z⟩
    have hfinite : leftFinite l := ⟨x.finite, y.finite⟩
    exact ⟨⟨l, hfinite, htrans, (left_project_eval a b c d e f parameter x y z).2 hparam⟩,
      ⟨l, htrans, (left_mul_eval a b c d e f parameter x.dot y.dot z).2 hparam⟩⟩
  obtain ⟨maxP, maxM⟩ := leftInterval maximum maxParabolic (lower_le_max a b c d e f p) le_rfl
  -- Lemma 6.3 and Theorem 6.5 identify the effective group element by the
  -- unit balanced pair. The coefficient and column checks are local since
  -- the replacement suppliers package existence and equality classes.
  -- In particular no inference about internal groups is made from a mere
  -- existence of a replacement at an unrelated region.
  refine ⟨⟨minP, ?_⟩, ⟨minM, ?_⟩, ⟨maxP, ?_⟩, ⟨maxM, ?_⟩, leftInterval, ?_⟩
  · rintro H ⟨⟨⟨B, hB⟩, j, v, w, ell, m, n⟩, hm, rfl, he⟩
    have h := (right_project_eval a b c d e f parameter ell ⟨m, hm.1⟩ ⟨n, hm.2⟩).1 he
    change rightBound a b c d p.element ≤ conj m.element j.toHom.range
    rw [← h]
    exact bound_right a b c d e f ell m n
  · rintro H ⟨⟨⟨B, hB⟩, j, v, w, ell, m, n⟩, rfl, he⟩
    have h := (right_mul_eval a b c d e f parameter ell m n).1 he
    change rightBound a b c d p.element ≤ conj m.element j.toHom.range
    rw [← h]
    exact bound_right a b c d e f ell m n
  · rintro H ⟨⟨⟨B, hB⟩, r, s, t, x, y, z⟩, hx, rfl, he⟩
    have h := (left_project_eval a b c d e f parameter ⟨x, hx.1⟩ ⟨y, hx.2⟩ z).1 he
    change conj (a.toHom z.element⁻¹) (a.comp r).toHom.range ≤ leftBound a b p.element
    rw [← h]
    exact bound_left a b c d e f x y z
  · rintro H ⟨⟨⟨B, hB⟩, r, s, t, x, y, z⟩, rfl, he⟩
    have h := (left_mul_eval a b c d e f parameter x y z).1 he
    change conj (a.toHom z.element⁻¹) (a.comp r).toHom.range ≤ leftBound a b p.element
    rw [← h]
    exact bound_left a b c d e f x y z
  · rintro ⟨⟨B, hB⟩, r, s, t, x, y, z⟩ hx he hmax
    have h := (left_project_eval a b c d e f parameter ⟨x, hx.1⟩ ⟨y, hx.2⟩ z).1 he
    change conj (a.toHom z.element⁻¹) (a.comp r).toHom.range = leftBound a b p.element at hmax
    rw [← h] at hmax
    -- The first crossing's common images now come from the full
    -- intersection. The project's mixed-basis injectivity lemma applies.
    have hinj := first_injective a b c d e f x y z hmax
    change ∀ u ∈ Set.range (basisMap a b r s x), ∃! w, basisMap a b r s x w = u
    rintro _ ⟨w, rfl⟩
    exact ⟨w, rfl, fun w' hw' => hinj hw'⟩
