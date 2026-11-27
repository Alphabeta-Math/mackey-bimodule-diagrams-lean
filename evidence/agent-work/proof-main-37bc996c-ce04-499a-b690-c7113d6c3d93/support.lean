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
