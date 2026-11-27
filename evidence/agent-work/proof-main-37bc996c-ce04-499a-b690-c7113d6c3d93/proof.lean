by
  classical
  intro finitary U blockSym parabolic ι finite G K H B H' hG hK hRegions
    α β γ δ α' β' hα hβ hγ hδ hα' hβ' v image P
  -- Xiao, Proposition 8.4 and the restriction row of its diagram
  -- (archived original pp. 36–37, published revision pp. 38–39).
  -- The two PDFs have distinct pagination and SHA-256 hashes.
  -- The restriction product formula is in §5.2, archived p. 18 and
  -- published p. 20. https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- Alphabeta Math's transposition proof, step 3.1, uses the universal
  -- property of the generated subgroup. Here its generators are the union
  -- of the middle conjugate subgroups, all contained in G.
  have hvG (i : ι) (k : K) : v i * (k : U) * (v i)⁻¹ ∈ G := by
    have h := hγ i ⟨δ i * (k : U) * (δ i)⁻¹, hδ i k⟩
    change γ i * (δ i * (k : U) * (δ i)⁻¹) * (γ i)⁻¹ ∈ G at h
    convert h using 1
    dsimp [v]
    group
  have member_le (i : ι) : image i ≤ P :=
    fun x hx => Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, hx⟩)
  have least (Q : Subgroup U) (hQ : ∀ i, image i ≤ Q) : P ≤ Q :=
    (Subgroup.closure_le _).mpr fun _ hx =>
      let ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      hQ i hi
  have hPG : P ≤ G := least G fun i => by
    rintro _ ⟨k, hk, rfl⟩
    exact hvG i ⟨k, hk⟩
  have hKP (i : ι) (k : K) : v i * (k : U) * (v i)⁻¹ ∈ P :=
    member_le i ⟨k, k.property, rfl⟩
  have hP : parabolic P := by
    let J := P.map (Subgroup.subtype finitary)
    let KG := K.map (Subgroup.subtype finitary)
    let ambientImage (i : ι) := KG.map (MulAut.conj ((v i : U) : Equiv.Perm Nat)).toMonoidHom
    have image_map (i : ι) : (image i).map (Subgroup.subtype finitary) = ambientImage i := by
      change (K.map (MulAut.conj (v i)).toMonoidHom).map (Subgroup.subtype finitary) = _
      unfold ambientImage KG
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    have ambient_closure : J = Subgroup.closure (Set.iUnion fun i => (ambientImage i : Set _)) := by
      change (Subgroup.closure _).map (Subgroup.subtype finitary) = _
      rw [MonoidHom.map_closure, Set.image_iUnion]
      congr 1
      ext σ
      refine Set.mem_iUnion.trans ?_
      rw [Set.mem_iUnion]
      exact exists_congr (fun i => show σ ∈ (image i).map (Subgroup.subtype finitary) ↔
        σ ∈ ambientImage i by rw [image_map])
    have ambient_le (i : ι) : ambientImage i ≤ J := by
      rw [← image_map i]
      exact Subgroup.map_mono (member_le i)
    have generated : Subgroup.closure {σ | σ ∈ J ∧ Equiv.Perm.IsSwap σ} = J := by
      apply le_antisymm
      · exact (Subgroup.closure_le _).mpr fun _ hs => hs.1
      refine le_trans (le_of_eq ambient_closure) ?_
      apply (Subgroup.closure_le _).mpr
      intro σ hσ
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hσ
      exact sharedRestriction_conj_le_generated hK _ (ambient_le i) hi
    obtain ⟨X, hX⟩ := sharedRestriction_fixes_outside hG
    exact sharedRestriction_parabolic_of_swaps X
      (fun x hx σ hσ => hX x hx σ (Subgroup.map_mono hPG hσ)) generated
  refine ⟨⟨⟨hP, hPG, member_le⟩, fun Q hQ => least Q hQ.2.2⟩, hPG, hKP, ?_⟩
  intro a b c f a' b' incl toP i u oldMiddle newMiddle w twoCrossings mergeDotSplit evalDrawing
  open MackeyDiagrams in
  have same : oldMiddle = newMiddle := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro k
    apply Subtype.ext
    simp only [oldMiddle, newMiddle, ConjEmbedding.comp_apply, c, f, incl, toP,
      ConjEmbedding.ofConjugator_apply, Subgroup.coe_inclusion, v]
    group
  refine ⟨same, ?_⟩
  -- The registered ParallelReidemeisterTwoRestriction applies to both chains
  -- using the six image-membership proofs. Its finite-label clause supplies the
  -- middle split–merge cancellation via Biset.Hom.merge_dot_split_comp and
  -- then uses DotLabel.downDrawing_compose. A product term acts by e⁻¹d⁻¹.
  -- Transporting the two labels along same leaves their product unchanged.
  -- The singleton case reduces that product on coefficient-one labels.
  open MackeyDiagrams in
  have agree (D : DotLabel Complex u oldMiddle) (E : DotLabel Complex oldMiddle w) :
      evalDrawing (twoCrossings (c i) (f i) D E) =
        evalDrawing (twoCrossings incl (toP i)
          (Eq.ndrec (motive := fun m => DotLabel Complex u m) D same)
          (Eq.ndrec (motive := fun m => DotLabel Complex m w) E same)) ∧
      evalDrawing (twoCrossings incl (toP i)
          (Eq.ndrec (motive := fun m => DotLabel Complex u m) D same)
          (Eq.ndrec (motive := fun m => DotLabel Complex m w) E same)) =
        evalDrawing (mergeDotSplit (DotLabel.compose D E)) := by
    have original : evalDrawing (twoCrossings (c i) (f i) D E) =
        evalDrawing (mergeDotSplit (DotLabel.compose D E)) :=
      (ParallelReidemeisterTwoRestriction K (H i) (B i) (H' i) G
        (α i) (β i) (γ i) (δ i) (α' i) (β' i)
        (hα i) (hβ i) (hγ i) (hδ i) (hα' i) (hβ' i)).2 D E
    let D' := Eq.ndrec (motive := fun m => DotLabel Complex u m) D same
    let E' := Eq.ndrec (motive := fun m => DotLabel Complex m w) E same
    have replacement : evalDrawing (twoCrossings incl (toP i) D' E') =
        evalDrawing (mergeDotSplit (DotLabel.compose D' E')) :=
      (ParallelReidemeisterTwoRestriction K (H i) P (H' i) G
        (α i) (β i) 1 (v i) (α' i) (β' i)
        (hα i) (hβ i) (fun p => by simpa only [one_mul, inv_one, mul_one] using hPG p.property)
        (hKP i) (hα' i) (hβ' i)).2 D' E'
    have product := sharedRestriction_compose_transport same D E
    change DotLabel.compose D' E' = DotLabel.compose D E at product
    rw [product] at replacement
    exact ⟨original.trans replacement.symm, replacement⟩
  refine ⟨?_, agree⟩
  intro d e
  simpa only [sharedRestriction_compose_single] using agree (Finsupp.single d 1) (Finsupp.single e 1)
