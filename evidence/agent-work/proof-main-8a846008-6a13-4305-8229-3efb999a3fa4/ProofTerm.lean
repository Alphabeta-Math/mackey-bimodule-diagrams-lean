by
  classical
  open ParabolicSharedRegionParallelInductionProof MackeyDiagrams in
  intro finitary U blockSym parabolic ι _ G K H B H' hG hK _ _ _
    α β γ δ α' β' hα hβ hγ hδ hα' hβ' v image P
  -- Xiao, Proposition 8.4, is on pp. 36–37 of the archived original
  -- source/mackey-bimodules.pdf
  -- (SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and pp. 38–39 of the revised published PDF at
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- (SHA-256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- These checksums correct the saved source note's byte-identity claim.
  -- Both rendered induction rows fix the outer words, change the middle
  -- labels from γᵢ, δᵢ to 1, vᵢ, and retain both marks.
  have image_le (i : ι) : image i ≤ P :=
    fun g hg => Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, hg⟩)
  have least (Q : Subgroup U) (hQ : ∀ i, image i ≤ Q) : P ≤ Q := by
    apply (Subgroup.closure_le Q).mpr
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact hQ i hi
  have inG (i : ι) (k : K) : v i * (k : U) * (v i)⁻¹ ∈ G := by
    have he : v i * (k : U) * (v i)⁻¹ =
        γ i * (δ i * (k : U) * (δ i)⁻¹) * (γ i)⁻¹ := by
      change (γ i * δ i) * (k : U) * (γ i * δ i)⁻¹ = _
      group
    rw [he]
    exact hγ i ⟨_, hδ i k⟩
  have hPG : P ≤ G := least G (fun i => by
    rintro _ ⟨k, hk, rfl⟩
    exact inG i ⟨k, hk⟩)
  let f := Subgroup.subtype finitary
  let L := P.map f
  have mapImage (i : ι) :
      (image i).map f = (K.map f).map (MulAut.conj (f (v i))).toMonoidHom := by
    change ((K.map (MulAut.conj (v i)).toMonoidHom).map f) = _
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have mapJoin : L = ⨆ i, (image i).map f := by
    change P.map f = _
    rw [show P = ⨆ i, image i from (Subgroup.iSup_eq_closure image).symm, Subgroup.map_iSup]
  have hParabolic : parabolic P := by
    change HasBlocks L
    let S := {σ : Equiv.Perm Nat | σ.IsSwap ∧ σ ∈ L}
    have swapGen : L = Subgroup.closure S := by
      have hSL : S ⊆ (L : Set (Equiv.Perm Nat)) := fun _ h => h.2
      apply le_antisymm _ ((Subgroup.closure_le L).mpr hSL)
      rw [mapJoin]
      refine iSup_le fun i => ?_
      have hle : (image i).map f ≤ L := Subgroup.map_mono (image_le i)
      rw [mapImage i] at hle ⊢
      exact conjugate_le_swapClosure hK _ hle
    obtain ⟨X, hX⟩ := fixesOutsideBlocks hG
    have fixes : ∀ σ ∈ L, ∀ x ∉ X, (σ : Equiv.Perm Nat) x = x :=
      fun σ hσ => hX σ ((Subgroup.map_mono hPG : L ≤ G.map f) hσ)
    rw [swapGen] at fixes ⊢
    exact blocksOfSwapClosure S (fun _ h => h.1) X fixes
  refine ⟨⟨⟨hPG, hParabolic, image_le⟩, fun Q hQ => least Q hQ.2.2⟩, hPG, ?_⟩
  intro inclusion throughP evalDrawing i a b c d a' b' bottom middle top newMiddle
  have same : middle = newMiddle :=
    sameComposites (hγ i) (hδ i) _ _
  refine ⟨same, ?_⟩
  intro x y newX newY original shared merge productDot split merged
  -- Use Theorem 5.4 via the finite-label clause of the registered induction
  -- result. That clause checks the middle merge/split inverse and applies
  -- DotLabel.upDrawing_compose within Biset.Hom.merge_dot_split_comp.
  -- Equality of the composite embeddings transports the complete
  -- labels. Equality induction preserves their ordered product, including
  -- zero labels, while both crossing drawings retain their own middle word.
  have oldFormula : evalDrawing original = evalDrawing merged :=
    ((ParallelReidemeisterTwoInduction G K (H i) (B i) (H' i)
      (α i) (β i) (γ i) (δ i) (α' i) (β' i)
      (hα i) (hβ i) (hγ i) (hδ i) (hα' i) (hβ' i)).2.1 x y).1
  have hIncl : ∀ p : P, (1 : U) * (p : U) * (1 : U)⁻¹ ∈ G := by
    intro p
    simpa only [one_mul, inv_one, mul_one] using hPG p.property
  have hThrough : ∀ k : K, v i * (k : U) * (v i)⁻¹ ∈ P := fun k =>
    image_le i ⟨(k : U), k.property, rfl⟩
  have newFormula :=
    ((ParallelReidemeisterTwoInduction G K (H i) P (H' i)
      (α i) (β i) 1 (v i) (α' i) (β' i)
      (hα i) (hβ i) hIncl hThrough (hα' i) (hβ' i)).2.1 newX newY).1
  change evalDrawing shared = evalDrawing (LabelledDrawing.vertical
    (LabelledDrawing.vertical merge (DotLabel.upDrawing (DotLabel.compose newX newY))) split)
    at newFormula
  have sameProduct : DotLabel.compose newX newY = DotLabel.compose x y :=
    composeTransport same x y
  rw [sameProduct] at newFormula
  exact ⟨oldFormula.trans newFormula.symm, newFormula⟩
