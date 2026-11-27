by
  classical
  intro G inst K H I σ reps L incLK μ Mod Res Ind F S regular regularH regularG
    rightMulH tmul targetBasis summandTmul
  -- Xiao, Theorem 2.1, p. 5 of the archived original and p. 7 of the
  -- published 28 November revision.
  -- Specialize the checked coproduct construction of Theorem 2.2 to the
  -- two inclusions. Equations (2.1) and (2.2) give the coset partition and
  -- its stabilizers, which identify the balanced pairs used for (2.3).
  have balance (i : I) (t : L i) :
      (incLK i t : G) * σ i = σ i * (μ i t : G) := by
    change (t : G) * σ i = σ i * ((σ i)⁻¹ * (t : G) * ((σ i)⁻¹)⁻¹)
    group
  have intersection (i : I) (k : K) (h : H)
      (he : (k : G) = σ i * (h : G) * (σ i)⁻¹) : ∃ t : L i, incLK i t = k := by
    exact ⟨⟨k, k.property, ⟨h, h.property, he.symm⟩⟩, rfl⟩
  have bijective := OrdinaryMackeySupport.ordinaryBijective K H incLK μ σ balance reps intersection
  obtain ⟨e, he⟩ := OrdinaryMackeySupport.coproduct.{u,v} K.subtype H.subtype incLK μ σ
    balance bijective
  -- Mathlib induction indexes the first tensor factor by its inverse.
  -- For the regular module the checked comparison evaluates g ⊗ x as
  -- g times the image of x, and intertwines right multiplication.
  let c := OrdinaryMackeySupport.regularComparison.{u,v} K.subtype H.subtype
  refine ⟨e, c, ?_, OrdinaryMackeySupport.regularComparison_right K.subtype H.subtype, ?_⟩
  · intro g
    change c.hom (OrdinaryMackeySupport.tmul H.subtype regularH g (ULift.up 1)) = _
    rw [OrdinaryMackeySupport.regularComparison_apply_pure]
    change ULift.up (MonoidAlgebra.of Complex G g *
      MonoidAlgebra.mapDomainAlgHom Complex Complex H.subtype 1) = _
    rw [map_one, mul_one]
  · intro i k h
    change c.hom (e.inv.app regularH
      ((CategoryTheory.Limits.Sigma.ι S i).app regularH
        (OrdinaryMackeySupport.tmul (incLK i) ((Res (μ i)).obj regularH) k
          (ULift.up (MonoidAlgebra.of Complex H h))))) = _
    rw [he i regularH k, OrdinaryMackeySupport.regularComparison_apply_pure]
    change ULift.up (MonoidAlgebra.of Complex G ((k : G) * σ i) *
      MonoidAlgebra.mapDomainAlgHom Complex Complex H.subtype (MonoidAlgebra.of Complex H h)) = _
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
