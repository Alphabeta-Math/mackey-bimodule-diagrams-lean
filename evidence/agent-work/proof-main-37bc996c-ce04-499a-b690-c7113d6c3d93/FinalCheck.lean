import MackeyDiagrams
import Proofs.ParallelReidemeisterTwoRestriction
import Proofs.FiniteParabolicJoinBlocks

set_option maxHeartbeats 2000000

private theorem sharedRestriction_compose_single {U : Type*} [Group U]
    {K G : Subgroup U} {u v w : MackeyDiagrams.ConjEmbedding K G}
    (d : MackeyDiagrams.Dot u v) (e : MackeyDiagrams.Dot v w) :
    MackeyDiagrams.DotLabel.compose (Finsupp.single d (1 : Complex))
      (Finsupp.single e 1) = Finsupp.single (d.vertical e) 1 := by
  change MackeyDiagrams.Dot.linearProduct (Finsupp.single d (1 : Complex))
    (Finsupp.single e 1) = Finsupp.single (d.vertical e) 1
  simp [MackeyDiagrams.Dot.linearProduct, Finsupp.sum_single_index]

private theorem sharedRestriction_compose_transport {U : Type*} [Group U]
    {K G : Subgroup U} {u v v' w : MackeyDiagrams.ConjEmbedding K G}
    (h : v = v') (D : MackeyDiagrams.DotLabel Complex u v)
    (E : MackeyDiagrams.DotLabel Complex v w) :
    MackeyDiagrams.DotLabel.compose
      (Eq.ndrec (motive := fun m => MackeyDiagrams.DotLabel Complex u m) D h)
      (Eq.ndrec (motive := fun m => MackeyDiagrams.DotLabel Complex m w) E h) =
    MackeyDiagrams.DotLabel.compose D E := by
  cases h
  rfl

private abbrev sharedRestriction_blockSym (S : Finset Nat) : Subgroup (Equiv.Perm Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S))

private abbrev sharedRestriction_Parabolic (J : Subgroup (Equiv.Perm Nat)) : Prop :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    J = ⨆ i, sharedRestriction_blockSym (blocks i)

private def sharedRestriction_swaps (S : Finset Nat) : Set (Equiv.Perm Nat) :=
  {σ | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ σ = Equiv.swap x y}

private theorem sharedRestriction_block_generated (S : Finset Nat) :
    sharedRestriction_blockSym S = Subgroup.closure (sharedRestriction_swaps S) := by
  let extend := Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S)
  -- Alphabeta Math, "Every finite permutation is a product of transpositions",
  -- steps 1.1, 2.1 and 3.1. Apply Mathlib's finite generation theorem on the
  -- block subtype, then identify the extended generators by their endpoints.
  -- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
  have generators : extend '' {σ | Equiv.Perm.IsSwap σ} = sharedRestriction_swaps S := by
    ext σ
    constructor
    · rintro ⟨_, ⟨x, y, hxy, rfl⟩, rfl⟩
      exact ⟨x, x.property, y, y.property, fun h => hxy (Subtype.ext h),
        Equiv.Perm.ofSubtype_swap_eq x y⟩
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      let x' : ↥S := ⟨x, hx⟩
      let y' : ↥S := ⟨y, hy⟩
      exact ⟨Equiv.swap x' y', ⟨x', y', fun h => hxy (congrArg Subtype.val h), rfl⟩,
        Equiv.Perm.ofSubtype_swap_eq x' y'⟩
  rw [← generators, ← MonoidHom.map_closure, Equiv.Perm.closure_isSwap, Subgroup.map_top]

private theorem sharedRestriction_fixes_outside {J : Subgroup (Equiv.Perm Nat)}
    (hJ : sharedRestriction_Parabolic J) :
    ∃ X : Finset Nat, ∀ (x : Nat), x ∉ X → ∀ σ ∈ J, σ x = x := by
  obtain ⟨n, blocks, _, _, rfl⟩ := hJ
  classical
  refine ⟨Finset.univ.biUnion blocks, fun x hx σ hσ => ?_⟩
  have hle : (⨆ i, sharedRestriction_blockSym (blocks i)) ≤
      MulAction.stabilizer (Equiv.Perm Nat) x := by
    apply iSup_le
    rintro i _ ⟨τ, rfl⟩
    exact Equiv.Perm.ofSubtype_apply_of_not_mem τ
      (fun hi => hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩))
  exact hle hσ

private theorem sharedRestriction_conj_le_generated
    {J K : Subgroup (Equiv.Perm Nat)} (hK : sharedRestriction_Parabolic K)
    (v : Equiv.Perm Nat)
    (h : K.map (MulAut.conj v).toMonoidHom ≤ J) :
    K.map (MulAut.conj v).toMonoidHom ≤
      Subgroup.closure {σ | σ ∈ J ∧ Equiv.Perm.IsSwap σ} := by
  obtain ⟨n, blocks, _, _, rfl⟩ := hK
  rw [Subgroup.map_iSup] at h ⊢
  apply iSup_le
  intro i
  have hi := (le_iSup (fun j => (sharedRestriction_blockSym (blocks j)).map
    (MulAut.conj v).toMonoidHom) i).trans h
  rw [sharedRestriction_block_generated, MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro σ ⟨τ, hτ, rfl⟩
  have inJ := hi ⟨τ, (sharedRestriction_block_generated (blocks i)).symm ▸
    Subgroup.subset_closure hτ, rfl⟩
  obtain ⟨x, _, y, _, hxy, rfl⟩ := hτ
  exact Subgroup.subset_closure
    ⟨inJ, v x, v y, fun he => hxy (v.injective he), (Equiv.swap_apply_apply v x y).symm⟩

private theorem sharedRestriction_parabolic_of_swaps {J : Subgroup (Equiv.Perm Nat)}
    (X : Finset Nat) (fixes : ∀ x, x ∉ X → ∀ σ ∈ J, σ x = x)
    (generated : Subgroup.closure {σ | σ ∈ J ∧ Equiv.Perm.IsSwap σ} = J) :
    sharedRestriction_Parabolic J := by
  classical
  -- The binary join supplier requires two partitions of a common carrier.
  -- For a whole family, use the orbits directly on the finite carrier of G.
  -- Alphabeta Math's adjacent-transposition proof, steps 1.1 and 2.1, uses
  -- endpoint swaps along consecutive letters. Here the swap-closure orbit
  -- criterion supplies endpoint swaps in the orbits of J.
  -- https://alphabetamath.cc/item/thm-adjacent-transpositions-generate-the-symmetric-group
  let rel : Setoid ↥X := (MulAction.orbitRel J Nat).comap Subtype.val
  let Class := Quotient rel
  let cls : ↥X → Class := Quotient.mk rel
  let block (c : Class) : Finset Nat :=
    X.filter (fun x => ∃ hx : x ∈ X, cls ⟨x, hx⟩ = c)
  have memBlock {x : Nat} {c : Class} :
      x ∈ block c ↔ ∃ hx : x ∈ X, cls ⟨x, hx⟩ = c := by
    change x ∈ X.filter (fun y => ∃ hy : y ∈ X, cls ⟨y, hy⟩ = c) ↔ _
    rw [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨h.choose, h⟩⟩
  have nonempty (c : Class) : (block c).Nonempty := by
    refine Quotient.inductionOn c fun x => ?_
    exact ⟨x, memBlock.mpr ⟨x.property, rfl⟩⟩
  have disjoint : Pairwise (fun c d => Disjoint (block c) (block d)) := by
    intro c d hcd
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨_, hc⟩ := memBlock.mp hx
    obtain ⟨_, hd⟩ := memBlock.mp hy
    exact hcd (hc.symm.trans hd)
  have swap_in (c : Class) {x y : Nat} (hx : x ∈ block c) (hy : y ∈ block c) :
      Equiv.swap x y ∈ J := by
    obtain ⟨hx, hxc⟩ := memBlock.mp hx
    obtain ⟨hy, hyc⟩ := memBlock.mp hy
    have hxy : rel ⟨x, hx⟩ ⟨y, hy⟩ := Quotient.exact (hxc.trans hyc.symm)
    change MulAction.orbitRel J Nat x y at hxy
    rw [MulAction.orbitRel_apply] at hxy
    have hs : ∀ σ ∈ {σ : Equiv.Perm Nat | σ ∈ J ∧ Equiv.Perm.IsSwap σ},
        Equiv.Perm.IsSwap σ := fun _ hσ => hσ.2
    rw [← generated] at hxy ⊢
    exact (swap_mem_closure_isSwap hs).mpr hxy
  have allBlocks : J = ⨆ c, sharedRestriction_blockSym (block c) := by
    apply le_antisymm
    · rw [← generated]
      apply (Subgroup.closure_le _).mpr
      rintro σ ⟨hσ, ⟨x, y, hxy, rfl⟩⟩
      have hx : x ∈ X := by
        by_contra hn
        exact hxy ((Equiv.swap_apply_left x y).symm.trans (fixes x hn _ hσ)).symm
      have hy : y ∈ X := by
        by_contra hn
        exact hxy ((Equiv.swap_apply_right x y).symm.trans (fixes y hn _ hσ))
      have eqClass : cls ⟨x, hx⟩ = cls ⟨y, hy⟩ := by
        apply Quotient.sound
        change MulAction.orbitRel J Nat x y
        exact MulAction.orbitRel_apply.mpr ⟨⟨Equiv.swap x y, hσ⟩, Equiv.swap_apply_right x y⟩
      let c := cls ⟨y, hy⟩
      have hxc : x ∈ block c := memBlock.mpr ⟨hx, eqClass⟩
      have hyc : y ∈ block c := memBlock.mpr ⟨hy, rfl⟩
      exact (le_iSup (fun d => sharedRestriction_blockSym (block d)) c)
        ⟨Equiv.swap ⟨x, hxc⟩ ⟨y, hyc⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
    · apply iSup_le
      intro c
      rw [sharedRestriction_block_generated]
      apply (Subgroup.closure_le _).mpr
      rintro σ ⟨x, hx, y, hy, _, rfl⟩
      exact swap_in c hx hy
  let _ : Fintype Class := Fintype.ofFinite Class
  let e := (Fintype.equivFin Class).symm
  refine ⟨Fintype.card Class, block ∘ e, fun i => nonempty (e i), ?_, ?_⟩
  · exact fun i j hij => disjoint (fun h => hij (e.injective h))
  · exact allBlocks.trans (e.iSup_comp (g := fun c => sharedRestriction_blockSym (block c))).symm

theorem ParabolicSharedRegionParallelRestriction : (let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun S => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S))
let parabolic : Subgroup U → Prop := fun L =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ j, Finset.Nonempty (blocks j)) ∧
    Pairwise (fun j k => Disjoint (blocks j) (blocks k)) ∧
    Subgroup.map (Subgroup.subtype finitary) L = iSup (fun j => blockSym (blocks j))
∀ {ι : Type*} [Finite ι] (G K : Subgroup U) (H B H' : ι → Subgroup U),
  parabolic G → parabolic K →
  (∀ i, parabolic (H i) ∧ parabolic (B i) ∧ parabolic (H' i)) →
  ∀ (α β γ δ α' β' : ι → U)
    (hα : ∀ i (h : H i), α i * (h : U) * (α i)⁻¹ ∈ G)
    (hβ : ∀ i (k : K), β i * (k : U) * (β i)⁻¹ ∈ H i)
    (hγ : ∀ i (b : B i), γ i * (b : U) * (γ i)⁻¹ ∈ G)
    (hδ : ∀ i (k : K), δ i * (k : U) * (δ i)⁻¹ ∈ B i)
    (hα' : ∀ i (h : H' i), α' i * (h : U) * (α' i)⁻¹ ∈ G)
    (hβ' : ∀ i (k : K), β' i * (k : U) * (β' i)⁻¹ ∈ H' i),
    let v := fun i => γ i * δ i
    let image := fun i => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (v i))) K
    let P := Subgroup.closure (Set.iUnion (fun i => (image i : Set U)))
    IsLeast {Q : Subgroup U | parabolic Q ∧ Q ≤ G ∧ ∀ i, image i ≤ Q} P ∧
    ∃ (hPG : P ≤ G) (hKP : ∀ i (k : K), v i * (k : U) * (v i)⁻¹ ∈ P),
      let a := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (α i) (hα i)
      let b := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (β i) (hβ i)
      let c := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (γ i) (hγ i)
      let f := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (δ i) (hδ i)
      let a' := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (α' i) (hα' i)
      let b' := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (β' i) (hβ' i)
      let incl : MackeyDiagrams.ConjEmbedding P G :=
        ⟨Subgroup.inclusion hPG, ⟨1, fun x => by
          simp only [Subgroup.coe_inclusion, one_mul, inv_one, mul_one]⟩⟩
      let toP := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (v i) (hKP i)
      ∀ i,
        let u := MackeyDiagrams.ConjEmbedding.comp (a i) (b i)
        let oldMiddle := MackeyDiagrams.ConjEmbedding.comp (c i) (f i)
        let newMiddle := MackeyDiagrams.ConjEmbedding.comp incl (toP i)
        let w := MackeyDiagrams.ConjEmbedding.comp (a' i) (b' i)
        let twoCrossings {M : Subgroup U}
            (g : MackeyDiagrams.ConjEmbedding M G)
            (q : MackeyDiagrams.ConjEmbedding K M)
            (D : MackeyDiagrams.DotLabel Complex u (MackeyDiagrams.ConjEmbedding.comp g q))
            (E : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp g q) w) :=
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.parallelDown (a i) (b i) g q
              (MackeyDiagrams.DotLabel.terms D))
            (MackeyDiagrams.LabelledDrawing.parallelDown g q (a' i) (b' i)
              (MackeyDiagrams.DotLabel.terms E))
        let mergeDotSplit (label : MackeyDiagrams.DotLabel Complex u w) :=
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
              (MackeyDiagrams.TrivalentVertex.mergeDown (a i) (b i)))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.DotLabel.downDrawing label)
              (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
                (MackeyDiagrams.TrivalentVertex.splitDown (a' i) (b' i))))
        let evalDrawing {p q : MackeyDiagrams.Word K G}
            (drawing : MackeyDiagrams.LabelledDrawing Complex p q) :=
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
        ∃ same : oldMiddle = newMiddle,
          let mapsAgree (D : MackeyDiagrams.DotLabel Complex u oldMiddle)
              (E : MackeyDiagrams.DotLabel Complex oldMiddle w)
              (product : MackeyDiagrams.DotLabel Complex u w) :=
            let D' := Eq.ndrec (motive := fun m => MackeyDiagrams.DotLabel Complex u m) D same
            let E' := Eq.ndrec (motive := fun m => MackeyDiagrams.DotLabel Complex m w) E same
            let original := twoCrossings (c i) (f i) D E
            let replacement := twoCrossings incl (toP i) D' E'
            let merged := mergeDotSplit product
            evalDrawing original = evalDrawing replacement ∧
            evalDrawing replacement = evalDrawing merged
          (∀ (d : MackeyDiagrams.Dot u oldMiddle) (e : MackeyDiagrams.Dot oldMiddle w),
            mapsAgree (Finsupp.single d 1) (Finsupp.single e 1)
              (Finsupp.single (MackeyDiagrams.Dot.vertical d e) 1)) ∧
          (∀ (D : MackeyDiagrams.DotLabel Complex u oldMiddle)
             (E : MackeyDiagrams.DotLabel Complex oldMiddle w),
            mapsAgree D E (MackeyDiagrams.DotLabel.compose D E))) :=
(by
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
  simpa only [sharedRestriction_compose_single] using agree (Finsupp.single d 1) (Finsupp.single e 1))

#print axioms ParabolicSharedRegionParallelRestriction
