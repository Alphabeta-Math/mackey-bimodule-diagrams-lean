by
  open MackeyDiagrams TransportToMackeyRepresentativeAux in
  intro U _ K H G L α β a b conjSubgroup Kα Hβ hK hH ha hb hs
    eα eβ ea eb d s A B J σ hσ j hj k h hsplit Lj Ls Limage Lprime leftJ rightJ
  -- Xiao, Lemma 5.2 (p. 16), and the portal reproduction give an
  -- unnumbered proof. It uses the factorization of s as a hypothesis. The
  -- double-coset memberships locate the representative. The supplied
  -- multipliers already give the equality needed below, so the route's
  -- DoubleCoset.eq and the transversal theorem are unnecessary. The
  -- embeddings are fixed by their conjugation formulas, so there is no
  -- need to compare their centralizer cosets. FLT transports double
  -- cosets. Here the index comparison uses ordinary left cosets.
  have hs_val : (s : U) = (α * a) * (β * b)⁻¹ := rfl
  have hsplit_val : (s : U) =
      (α * (k : U) * α⁻¹) * (σ j : U) * (β * (h : U) * β⁻¹) :=
    congrArg Subtype.val hsplit
  let c : U := α * (k : U)⁻¹ * α⁻¹
  let t : U := α * (k : U)⁻¹ * a
  have ht : t = (σ j : U) * β * (h : U) * b := by
    calc
      t = c * ((s : U) * (β * b)) := by
        rw [hs_val]
        dsimp only [c, t]
        group
      _ = _ := by
        rw [hsplit_val]
        dsimp only [c]
        group
  -- The two expressions for t give the two inclusions into the intersection.
  have hSub : Lprime ≤ Lj := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    change t * ℓ * t⁻¹ ∈ Kα ⊓ conjSubgroup ((σ j : U) * β) H
    constructor
    · have haℓ : a * ℓ * a⁻¹ ∈ K := ha ⟨ℓ, hℓ, rfl⟩
      refine ⟨(k : U)⁻¹ * (a * ℓ * a⁻¹) * (k : U),
        K.mul_mem (K.mul_mem (K.inv_mem k.property) haℓ) k.property, ?_⟩
      change α * ((k : U)⁻¹ * (a * ℓ * a⁻¹) * (k : U)) * α⁻¹ = t * ℓ * t⁻¹
      dsimp only [t]
      group
    · have hbℓ : b * ℓ * b⁻¹ ∈ H := hb ⟨ℓ, hℓ, rfl⟩
      refine ⟨(h : U) * (b * ℓ * b⁻¹) * (h : U)⁻¹,
        H.mul_mem (H.mul_mem h.property hbℓ) (H.inv_mem h.property), ?_⟩
      change ((σ j : U) * β) * ((h : U) * (b * ℓ * b⁻¹) * (h : U)⁻¹) *
        ((σ j : U) * β)⁻¹ = t * ℓ * t⁻¹
      rw [ht]
      group
  -- Conjugation by c carries both subgroup pairs to each other. Work
  -- with the actual left-coset quotient to include infinite indices.
  have hc : c ∈ Kα := ⟨(k : U)⁻¹, K.inv_mem k.property, rfl⟩
  have hleft : conjSubgroup c Kα = Kα :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Kα.le_normalizer hc)
  have hrightFixed : conjSubgroup (h : U) H = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer h.property)
  have hcRight : c * ((s : U) * β) = ((σ j : U) * β) * (h : U) := by
    rw [hsplit_val]
    dsimp only [c]
    group
  have hright : conjSubgroup c (conjSubgroup ((s : U) * β) H) =
      conjSubgroup ((σ j : U) * β) H := calc
    _ = conjSubgroup (c * ((s : U) * β)) H := conjugate_mul _ _ _
    _ = conjSubgroup (((σ j : U) * β) * (h : U)) H := by rw [hcRight]
    _ = conjSubgroup ((σ j : U) * β) (conjSubgroup (h : U) H) :=
      (conjugate_mul _ _ _).symm
    _ = _ := congrArg (conjSubgroup ((σ j : U) * β)) hrightFixed
  have hmapJ : conjSubgroup c Ls = Lj := by
    change (Kα ⊓ conjSubgroup ((s : U) * β) H).map (MulAut.conj c).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective]
    change conjSubgroup c Kα ⊓ conjSubgroup c (conjSubgroup ((s : U) * β) H) = Lj
    rw [hleft, hright]
  have hmapImage : conjSubgroup c Limage = Lprime := by
    calc
      _ = conjSubgroup (c * (α * a)) L := conjugate_mul _ _ _
      _ = conjSubgroup t L := by
        apply congrArg (fun z => conjSubgroup z L)
        dsimp only [c, t]
        group
      _ = _ := rfl
  have hindex :
      Cardinal.mk (Quotient (QuotientGroup.leftRel (Lprime.subgroupOf Lj))) =
        Cardinal.mk (Quotient (QuotientGroup.leftRel (Limage.subgroupOf Ls))) := by
    let cosetCard (S T : Subgroup U) :=
      Cardinal.mk (Quotient (QuotientGroup.leftRel (T.subgroupOf S)))
    change cosetCard Lj Lprime = cosetCard Ls Limage
    rw [← hmapJ, ← hmapImage]
    exact (coset_card_of_map (MulAut.conj c) Ls Limage).symm
  refine ⟨hSub, ?_⟩
  intro leftPrime rightPrime dprime X Y Xprime Yprime W Wprime q qprime ι ιprime
  -- Lemma 5.2 computes the restricted embeddings on t ℓ t⁻¹.
  -- These two formulas transport the generating balance relation both ways.
  let f : L ≃ Lprime := ((MulAut.conj t).subgroupMap L).toEquiv
  have hf_val (ℓ : L) : (f ℓ : U) = t * (ℓ : U) * t⁻¹ := rfl
  have hl (ℓ : L) : leftPrime.toHom (f ℓ) = k⁻¹ * ea.toHom ℓ * k := by
    apply Subtype.ext
    change α⁻¹ * (f ℓ : U) * (α⁻¹)⁻¹ =
      (k : U)⁻¹ * (a * (ℓ : U) * a⁻¹) * (k : U)
    rw [hf_val]
    dsimp only [t]
    group
  have hr (ℓ : L) : rightPrime.toHom (f ℓ) = h * eb.toHom ℓ * h⁻¹ := by
    apply Subtype.ext
    change (β⁻¹ * (σ j : U)⁻¹) * (f ℓ : U) * (β⁻¹ * (σ j : U)⁻¹)⁻¹ =
      (h : U) * (b * (ℓ : U) * b⁻¹) * (h : U)⁻¹
    rw [hf_val, ht]
    group
  let e : W.carrier ≃ Wprime.carrier := shiftBasis ea eb leftPrime rightPrime k h f hl hr
  have he : ∀ g w, e (W.act g w) = Wprime.act g (e w) :=
    shiftBasis_equivariant ea eb leftPrime rightPrime k h f hl hr
  have he_pair (x : K) (y : H) :
      e (X.pair Y x y) = Xprime.pair Yprime (x * k) (h * y) := rfl
  -- Crossing values agree on the balanced-pair representatives. The
  -- equality identifies the fibers, which suffices for finite transfers.
  have hcomm (w : W.carrier) : qprime (e w) = q w := by
    refine Quotient.inductionOn w (fun ⟨x, y⟩ => ?_)
    change qprime (e (X.pair Y x y)) = q (X.pair Y x y)
    rw [he_pair]
    change Generator.mixedPair eα eβ (eα.toHom (x * k) * σ j * eβ.toHom (h * y)) =
      Generator.mixedPair eα eβ (eα.toHom x * s * eβ.toHom y)
    apply congrArg (Generator.mixedPair eα eβ)
    rw [map_mul, map_mul, hsplit]
    group
  refine ⟨e, he, he_pair, ?_, ?_, hindex⟩
  · -- The reviewed syntax interprets a coefficient-one singleton drawing
    -- as the associated basis pushforward.
    rw [show ιprime.interpret.eval = _ from eval_multiplication_singleton
          eα eβ leftPrime rightPrime dprime,
      show ι.interpret.eval = _ from eval_multiplication_singleton eα eβ ea eb d]
    exact multiplication_commutes e he q qprime
      (Generator.mixedMultiplication_equivariant eα eβ ea eb d)
      (Generator.mixedMultiplication_equivariant eα eβ leftPrime rightPrime dprime) hcomm
  · -- The paper uses the inverse trace labels. The compact drawings
    -- implement those projections by transfer along the forward maps.
    intro hf hfprime p pprime
    rw [show p.interpret.eval = _ from eval_projection_singleton eα eβ ea eb d hf,
      show pprime.interpret.eval = _ from eval_projection_singleton
          eα eβ leftPrime rightPrime dprime hfprime]
    exact projection_commutes e he q qprime
      (Generator.mixedMultiplication_equivariant eα eβ ea eb d)
      (Generator.mixedMultiplication_equivariant eα eβ leftPrime rightPrime dprime)
      hcomm hf hfprime
