section
variable {α : Type*} [DecidableEq α] {ι κ : Type*}

private def tableauBlockGroup (D : ι → Finset α) : Subgroup (Equiv.Perm α) :=
  ⨆ i, MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x => x ∈ D i))

/- Proposition 7.3 uses the block products on the finite carrier X. The registered
   Proposition 7.1 supplier, FiniteParabolicIntersectionBlocks, gives an intersection
   equality on ambient Nat. It does not give the block-preserving membership criterion
   on X needed here. Use its disjoint-block and transposition argument on X directly. -/
private theorem tableauBlockGroup_mem [Finite α] (D : ι → Finset α)
    (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (hc : ∀ x, ∃ i, x ∈ D i)
    (p : Equiv.Perm α) :
    p ∈ tableauBlockGroup D ↔ ∀ i x, x ∈ D i → p x ∈ D i := by
  constructor
  · intro hp
    refine Subgroup.iSup_induction _ (C := fun f : Equiv.Perm α =>
      ∀ i x, x ∈ D i → f x ∈ D i) hp ?_ ?_ ?_
    · rintro j _ ⟨g, rfl⟩ i x hx
      by_cases hij : i = j
      · subst j
        exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem g x).mpr hx
      · have h : x ∉ D j := fun h => Finset.disjoint_left.mp (hd hij) hx h
        rwa [Equiv.Perm.ofSubtype_apply_of_not_mem g h]
    · exact fun _ _ hx => hx
    · exact fun f g hf hg i x hx => hf i (g x) (hg i x hx)
  · intro hp
    let swaps : Set (Equiv.Perm α) := {s | ∃ i x y,
      x ∈ D i ∧ y ∈ D i ∧ x ≠ y ∧ s = Equiv.swap x y}
    have hs : ∀ s ∈ swaps, Equiv.Perm.IsSwap s := by
      rintro s ⟨i, x, y, hx, hy, hxy, rfl⟩
      exact ⟨x, y, hxy, rfl⟩
    have hle : Subgroup.closure swaps ≤ tableauBlockGroup D := by
      apply (Subgroup.closure_le _).mpr
      rintro s ⟨i, x, y, hx, hy, hxy, rfl⟩
      apply Subgroup.mem_iSup_of_mem i
      exact ⟨Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
    apply hle
    refine (mem_closure_isSwap hs).mpr ⟨Set.toFinite _, fun x => ?_⟩
    apply MulAction.mem_orbit_iff.mpr
    by_cases h : p x = x
    · exact ⟨1, h.symm⟩
    · obtain ⟨i, hi⟩ := hc x
      have hswap : Equiv.swap x (p x) ∈ Subgroup.closure swaps :=
        Subgroup.subset_closure ⟨i, x, p x, hi, hp i x hi, Ne.symm h, rfl⟩
      exact ⟨⟨_, hswap⟩, Equiv.swap_apply_left _ _⟩

private theorem tableauBlockGroup_preserve [Finite α] (D : ι → Finset α)
    (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (hc : ∀ x, ∃ i, x ∈ D i)
    {p : Equiv.Perm α} (hp : p ∈ tableauBlockGroup D) (i : ι) (x : α) :
    p x ∈ D i ↔ x ∈ D i := by
  refine ⟨fun hx => ?_, (tableauBlockGroup_mem D hd hc p).mp hp i x⟩
  have h := (tableauBlockGroup_mem D hd hc p⁻¹).mp
    ((tableauBlockGroup D).inv_mem hp) i (p x) hx
  simpa [Equiv.Perm.inv_def] using h

omit [DecidableEq α] in
private theorem tableauIndex_unique (D : ι → Finset α)
    (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    {i j : ι} {x : α} (hi : x ∈ D i) (hj : x ∈ D j) : i = j := by
  by_contra h
  exact Finset.disjoint_left.mp (hd h) hi hj

private noncomputable def tableauPartition (D : ι → Finset α)
    (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (hc : ∀ x, ∃ i, x ∈ D i) :
    (Σ i, ↥(D i)) ≃ α :=
  Equiv.ofBijective (fun z => z.2.val) (by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
      change x.val = y.val at hxy
      have h : i = j := tableauIndex_unique D hd x.property (hxy.symm ▸ y.property)
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext hxy)
    · intro x
      obtain ⟨i, hx⟩ := hc x
      exact ⟨⟨i, ⟨x, hx⟩⟩, rfl⟩)

omit [DecidableEq α] in
private theorem tableauPartition_index (D : ι → Finset α)
    (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (hc : ∀ x, ∃ i, x ∈ D i)
    (x : α) (i : ι) : ((tableauPartition D hd hc).symm x).1 = i ↔ x ∈ D i := by
  let z := (tableauPartition D hd hc).symm x
  have hz : z.2.val = x := (tableauPartition D hd hc).apply_symm_apply x
  have hmem : x ∈ D z.1 := hz ▸ z.2.property
  exact ⟨fun h => h ▸ hmem, tableauIndex_unique D hd hmem⟩

private def tableauCell (A : ι → Finset α) (B : κ → Finset α) (p : Equiv.Perm α)
    (i : ι) (j : κ) : Finset α :=
  A i ∩ (B j).map p.toEmbedding

private theorem tableauCell_mem (A : ι → Finset α) (B : κ → Finset α)
    (p : Equiv.Perm α) (i : ι) (j : κ) (x : α) :
    x ∈ tableauCell A B p i j ↔ x ∈ A i ∧ p.symm x ∈ B j := by
  simp only [tableauCell, Finset.mem_inter, Finset.mem_map_equiv]

private theorem tableauCell_card [Fintype κ] [DecidableEq κ]
    (A : ι → Finset α) (B : κ → Finset α)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (hc : ∀ x, ∃ j, x ∈ B j)
    (p : Equiv.Perm α) (i : ι) :
    ∑ j, (tableauCell A B p i j).card = (A i).card := by
  let label := fun x => ((tableauPartition B hd hc).symm (p.symm x)).1
  rw [Finset.card_eq_sum_card_fiberwise (f := label) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext x
  simp only [tableauCell_mem, Finset.mem_filter]
  exact and_congr_right' (tableauPartition_index B hd hc (p.symm x) j).symm

private theorem tableauCell_transport (A : ι → Finset α) (B : κ → Finset α)
    (p q k : Equiv.Perm α)
    (hA : ∀ i x, k x ∈ A i ↔ x ∈ A i)
    (hB : ∀ j x, q.symm (k x) ∈ B j ↔ p.symm x ∈ B j) (i : ι) (j : κ) :
    (tableauCell A B p i j).card = (tableauCell A B q i j).card := by
  let e := k.subtypeEquiv (p := fun x => x ∈ tableauCell A B p i j)
    (q := fun x => x ∈ tableauCell A B q i j) (fun x => by
      simp only [tableauCell_mem, hA, hB])
  simpa only [Fintype.card_coe] using Fintype.card_congr e

private theorem tableauCell_card_symm (A : ι → Finset α) (B : κ → Finset α)
    (p : Equiv.Perm α) (i : ι) (j : κ) :
    (tableauCell A B p i j).card = (tableauCell B A p.symm j i).card := by
  let e := p.symm.subtypeEquiv (p := fun x => x ∈ tableauCell A B p i j)
    (q := fun x => x ∈ tableauCell B A p.symm j i) (fun x => by
      simp only [tableauCell_mem, Equiv.symm_symm, Equiv.apply_symm_apply, and_comm])
  simpa only [Fintype.card_coe] using Fintype.card_congr e

private theorem tableauCount_invariant [Finite α] (A : ι → Finset α) (B : κ → Finset α)
    (hdA : Pairwise (fun i j => Disjoint (A i) (A j))) (hcA : ∀ x, ∃ i, x ∈ A i)
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j))) (hcB : ∀ x, ∃ j, x ∈ B j)
    (p q : Equiv.Perm α)
    (hpq : DoubleCoset.mk (tableauBlockGroup A) (tableauBlockGroup B) p =
      DoubleCoset.mk (tableauBlockGroup A) (tableauBlockGroup B) q) (i : ι) (j : κ) :
    (tableauCell A B p i j).card = (tableauCell A B q i j).card := by
  obtain ⟨k, hk, h, hh, rfl⟩ := DoubleCoset.eq.mp hpq
  apply tableauCell_transport A B p (k * p * h) k (tableauBlockGroup_preserve A hdA hcA hk)
  intro j x
  have he : (k * p * h).symm (k x) = h.symm (p.symm x) := by
    apply (k * p * h).injective
    simp [Equiv.Perm.mul_apply]
  rw [he]
  exact tableauBlockGroup_preserve B hdB hcB ((tableauBlockGroup B).inv_mem hh) j (p.symm x)

private theorem tableauCells_disjoint (A : ι → Finset α) (B : κ → Finset α)
    (hdA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j))) (p : Equiv.Perm α) :
    Pairwise (fun u v : ι × κ =>
      Disjoint (tableauCell A B p u.1 u.2) (tableauCell A B p v.1 v.2)) := by
  intro u v huv
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hxi, hxj⟩ := (tableauCell_mem A B p u.1 u.2 x).mp hx
  obtain ⟨hyi, hyj⟩ := (tableauCell_mem A B p v.1 v.2 x).mp hy
  exact huv (Prod.ext (tableauIndex_unique A hdA hxi hyi) (tableauIndex_unique B hdB hxj hyj))

private theorem tableauCells_cover (A : ι → Finset α) (B : κ → Finset α)
    (hcA : ∀ x, ∃ i, x ∈ A i) (hcB : ∀ x, ∃ j, x ∈ B j)
    (p : Equiv.Perm α) (x : α) :
    ∃ u : ι × κ, x ∈ tableauCell A B p u.1 u.2 := by
  obtain ⟨i, hi⟩ := hcA x
  obtain ⟨j, hj⟩ := hcB (p.symm x)
  exact ⟨(i, j), (tableauCell_mem A B p i j x).mpr ⟨hi, hj⟩⟩

private theorem tableauCount_injective [Finite α] (A : ι → Finset α) (B : κ → Finset α)
    (hdA : Pairwise (fun i j => Disjoint (A i) (A j))) (hcA : ∀ x, ∃ i, x ∈ A i)
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j))) (hcB : ∀ x, ∃ j, x ∈ B j)
    (p q : Equiv.Perm α) (he : ∀ i j, (tableauCell A B p i j).card =
      (tableauCell A B q i j).card) :
    DoubleCoset.mk (tableauBlockGroup A) (tableauBlockGroup B) p =
      DoubleCoset.mk (tableauBlockGroup A) (tableauBlockGroup B) q := by
  -- Match the two tableaux cell by cell. The bijection of positions fixes row
  -- labels, and transporting it back through the two tableaux fixes column labels.
  let D := fun (f : Equiv.Perm α) (u : ι × κ) => tableauCell A B f u.1 u.2
  let split := fun f => tableauPartition (D f) (tableauCells_disjoint A B hdA hdB f)
    (tableauCells_cover A B hcA hcB f)
  let matchCells : (Σ u, ↥(D p u)) ≃ (Σ u, ↥(D q u)) :=
    Equiv.sigmaCongrRight fun u => Finset.equivOfCardEq (he u.1 u.2)
  let k : Equiv.Perm α := ((split p).symm.trans matchCells).trans (split q)
  have sameCell (u : ι × κ) (x : α) (hx : x ∈ D p u) : k x ∈ D q u := by
    have h := (matchCells ⟨u, ⟨x, hx⟩⟩).2.property
    have hx' : (split p).symm x = ⟨u, ⟨x, hx⟩⟩ :=
      (Equiv.symm_apply_eq (split p)).mpr rfl
    change (matchCells ⟨u, ⟨x, hx⟩⟩).2.val ∈ D q u at h
    change ((split q) (matchCells ((split p).symm x))) ∈ D q u
    rw [hx']
    exact h
  let l : Equiv.Perm α := q⁻¹ * k * p
  have hk : k ∈ tableauBlockGroup A := by
    apply (tableauBlockGroup_mem A hdA hcA k).mpr
    intro i x hx
    obtain ⟨j, hj⟩ := hcB (p.symm x)
    exact ((tableauCell_mem A B q i j _).mp
      (sameCell (i, j) x ((tableauCell_mem A B p i j x).mpr ⟨hx, hj⟩))).1
  have hl : l ∈ tableauBlockGroup B := by
    apply (tableauBlockGroup_mem B hdB hcB l).mpr
    intro j y hy
    obtain ⟨i, hi⟩ := hcA (p y)
    have hmem : p y ∈ D p (i, j) :=
      (tableauCell_mem A B p i j _).mpr ⟨hi, by simpa using hy⟩
    exact ((tableauCell_mem A B q i j _).mp (sameCell (i, j) _ hmem)).2
  exact DoubleCoset.eq.mpr
    ⟨k, hk, l⁻¹, (tableauBlockGroup B).inv_mem hl, by simp [l, mul_assoc]⟩
end
