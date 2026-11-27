by
  classical
  intro U inst G A D F C E repGA repAD repDF repGC repCE repEF
    hGA hAD hDF hGC hCE hEF ga ad df gc ce ef bottomPair topPair
    word bottom top straight merge split splitBottom mergeTop mergedEvaluation multiplier
    crossing crossLeft crossRight LeftLabels RightLabels leftDiagram rightDiagram
    leftMultiplier rightMultiplier
  -- Lemma 6.1, archived PDF pp. 19–20 and revised published PDF pp. 21–22.
  -- The source locator uses the archived pagination. The published PDF has
  -- a different checksum. The online proof has named sections, with no
  -- numbered Alphabeta proof steps supplied for this endpoint.
  -- Multiplier and support calculation. The registered supplier
  -- gives the two ordered formulas, support in the centralizer condition, and
  -- the equivalence between that condition and the boundary intertwining law.
  obtain ⟨hBoundary, _, _, _, hCriterion, hLeft, hRight⟩ :=
    ThreeInductionCrossingMultipliers G A D F C E repGA repAD repDF repGC repCE repEF
      hGA hAD hDF hGC hCE hEF
  let bottomEmbedding := bottomPair.comp df
  let topEmbedding := topPair.comp ef
  let u := repGA * repAD * repDF
  let v := repGC * repCE * repEF
  let Eligible := fun m : MonoidAlgebra Complex G =>
    ∀ p ∈ m.coeff.support, ∀ f : F,
      bottomEmbedding.toHom f * p = p * topEmbedding.toHom f
  have eligibleOfSupport (m : MonoidAlgebra Complex G)
      (hm : ∀ p ∈ m.coeff.support, u⁻¹ * (p : U) * v ∈ Subgroup.centralizer (F : Set U)) :
      Eligible m := by
    intro p hp f
    have he := ((hCriterion p).2.mpr (hm p hp)) f
    apply Subtype.ext
    change (bottomEmbedding.toHom f : U) * (p : U) =
      (p : U) * (topEmbedding.toHom f : U)
    rw [(hBoundary f).1, (hBoundary f).2]
    exact he
  have eligibleLeft (d : LeftLabels) : Eligible (leftMultiplier d) := by
    rcases d with ⟨B, gb, bd, be, x₁, x₂, x₃⟩
    exact eligibleOfSupport _ (hLeft B gb bd be x₁ x₂ x₃).2
  have eligibleRight (d : RightLabels) : Eligible (rightMultiplier d) := by
    rcases d with ⟨B', ab', cb', b'f, y₁, y₂, y₃⟩
    exact eligibleOfSupport _ (hRight B' ab' cb' b'f y₁ y₂ y₃).2
  -- Construction of φ and construction of ψ in Lemma 6.1. The article
  -- chooses representatives pv and v for each p in the support. Use the
  -- equivalent intertwining equation to form Dot directly, then pull back
  -- the finite coefficients along its injective element projection.
  -- Equal outer embeddings and the two bracketings of the middle
  -- embeddings are definitionally equal by composition of their homomorphisms.
  let ab' := ad.comp df
  let cb' := ce.comp ef
  let b'f := ConjEmbedding.id F
  let gb := ConjEmbedding.id G
  let y₁ := DotLabel.identity (R := Complex) ab'
  let y₃ := DotLabel.identity (R := Complex) cb'
  let x₁ := DotLabel.identity (R := Complex) bottomPair
  let x₃ := DotLabel.identity (R := Complex) topPair
  let middle := fun m => liftMultiplier (a := bottomEmbedding) (b := topEmbedding) m
  let makeRight : MonoidAlgebra Complex G → RightLabels :=
    fun m => ⟨F, ab', cb', b'f, y₁, middle m, y₃⟩
  let makeLeft : MonoidAlgebra Complex G → LeftLabels :=
    fun m => ⟨G, gb, bottomPair, topPair, x₁, middle m, x₃⟩
  have rightValue (m : MonoidAlgebra Complex G) (hm : Eligible m) :
      rightMultiplier (makeRight m) = m := by
    calc
      _ = (MonoidAlgebra.mapDomainAlgHom Complex Complex ga.toHom) (dotValue y₁) *
          dotValue (middle m) *
          (MonoidAlgebra.mapDomainAlgHom Complex Complex gc.toHom) (dotValue y₃) :=
        (hRight F ab' cb' b'f y₁ (middle m) y₃).1
      _ = m := by
        rw [dotValue_identity ab', dotValue_identity cb', map_one, map_one,
          one_mul, mul_one, liftMultiplier_value m hm]
  have leftValue (m : MonoidAlgebra Complex G) (hm : Eligible m) :
      leftMultiplier (makeLeft m) = m := by
    calc
      _ = dotValue x₁ *
          (MonoidAlgebra.mapDomainAlgHom Complex Complex gb.toHom) (dotValue (middle m)) *
          dotValue x₃ :=
        (hLeft G gb bottomPair topPair x₁ (middle m) x₃).1
      _ = m := by
        rw [dotValue_identity bottomPair, dotValue_identity topPair, one_mul, mul_one,
          liftMultiplier_value m hm]
        change MonoidAlgebra.mapDomainAlgHom Complex Complex (MonoidHom.id G) m = m
        simp only [MonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_apply]
  refine ⟨fun d => makeRight (leftMultiplier d), fun d => makeLeft (rightMultiplier d), ?_⟩
  have hφ (d : LeftLabels) := rightValue (leftMultiplier d) (eligibleLeft d)
  have hψ (d : RightLabels) := leftValue (rightMultiplier d) (eligibleRight d)
  -- Round-trip calculations in Lemma 6.1, by the two preservation equations.
  exact ⟨hφ, hψ, fun d => (hψ _).trans (hφ d), fun d => (hφ _).trans (hψ d)⟩
