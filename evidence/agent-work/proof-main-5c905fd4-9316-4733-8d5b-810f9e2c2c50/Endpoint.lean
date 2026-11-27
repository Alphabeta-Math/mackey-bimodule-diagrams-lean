import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Data.Finset.Sort
import MackeyDiagrams
import Proofs.FiniteParabolicIntersectionBlocks

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

section
variable {α : Type*} [LinearOrder α]

private noncomputable def tableauRank (S : Finset α) (x : ↥S) : Nat :=
  ((Finset.orderIsoOfFin S rfl).symm x).val

private noncomputable def tableauSlice {n : Nat} (S : Finset α)
    (sizes : Fin n → Nat) (hs : ∑ j, sizes j = S.card) :
    (Σ j, Fin (sizes j)) ≃ ↥S :=
  finSigmaFinEquiv.trans (Finset.orderIsoOfFin S hs.symm).toEquiv

private theorem tableauSlice_rank {n : Nat} (S : Finset α)
    (sizes : Fin n → Nat) (hs : ∑ j, sizes j = S.card) (j : Fin n) (k : Fin (sizes j)) :
    tableauRank S (tableauSlice S sizes hs ⟨j, k⟩) =
      (∑ t ∈ Finset.Iio j, sizes t) + k.val := by
  have hv : tableauRank S (tableauSlice S sizes hs ⟨j, k⟩) =
      (finSigmaFinEquiv (n := sizes) ⟨j, k⟩).val := by
    have hr {m : Nat} (h : S.card = m) (u : Fin m) :
        tableauRank S (Finset.orderIsoOfFin S h u) = u.val := by
      subst m
      exact congrArg Fin.val ((Finset.orderIsoOfFin S rfl).symm_apply_apply u)
    exact hr hs.symm _
  rw [hv, finSigmaFinEquiv_apply]
  congr 1
  have hIio : (Finset.univ : Finset (Fin j.val)).map (Fin.castLEEmb j.isLt.le) =
      Finset.Iio j := by
    ext t
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · rintro ⟨u, rfl⟩
      exact u.isLt
    · intro h
      exact ⟨⟨t.val, h⟩, Fin.ext rfl⟩
  rw [← hIio, Finset.sum_map]
  rfl
end

private def tableauFlip {r c : Nat} (R : Fin r → Fin c → Nat) :
    (Σ i, Σ j, Fin (R i j)) ≃ (Σ j, Σ i, Fin (R i j)) where
  toFun z := ⟨z.2.1, z.1, z.2.2⟩
  invFun z := ⟨z.2.1, z.1, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section
variable {α : Type*} [LinearOrder α] [DecidableEq α]

private theorem tableauOrdered {r c : Nat}
    (A : Fin r → Finset α) (B : Fin c → Finset α)
    (hdA : Pairwise (fun i j => Disjoint (A i) (A j))) (hcA : ∀ x, ∃ i, x ∈ A i)
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j))) (hcB : ∀ x, ∃ j, x ∈ B j)
    (R : Fin r → Fin c → Nat) (hr : ∀ i, ∑ j, R i j = (A i).card)
    (hc : ∀ j, ∑ i, R i j = (B j).card) :
    ∃ p : Equiv.Perm α, (∀ i j, (tableauCell A B p i j).card = R i j) ∧
      ∀ (i : Fin r) (j : Fin c) (x : ↥(A i)) (y : ↥(B j)),
        p y.val = x.val ↔ ∃ k : Fin (R i j),
          tableauRank (A i) x = (∑ t ∈ Finset.Iio j, R i t) + k.val ∧
          tableauRank (B j) y = (∑ t ∈ Finset.Iio i, R t j) + k.val := by
  -- Xiao §7.2, step 1: concatenate cells in each ordered row block.
  let rowSlice := fun i => tableauSlice (A i) (R i) (hr i)
  let rows := (Equiv.sigmaCongrRight rowSlice).trans (tableauPartition A hdA hcA)
  -- Step 2: concatenate in each ordered column block. Use the same cell offsets
  -- as for the rows, so matching on the shared coordinate type is order preserving.
  let colSlice := fun j => tableauSlice (B j) (fun i => R i j) (hc j)
  let cols := (tableauFlip R).trans
    ((Equiv.sigmaCongrRight colSlice).trans (tableauPartition B hdB hcB))
  let p : Equiv.Perm α := cols.symm.trans rows
  have forward (z : Σ i, Σ j, Fin (R i j)) : p (cols z) = rows z := by
    simp [p]
  have backward (z : Σ i, Σ j, Fin (R i j)) : p.symm (rows z) = cols z := by
    simp [p]
  have row_mem (z : Σ i, Σ j, Fin (R i j)) : rows z ∈ A z.1 :=
    (rowSlice z.1 z.2).property
  have col_mem (z : Σ i, Σ j, Fin (R i j)) : cols z ∈ B z.2.1 :=
    (colSlice z.2.1 ⟨z.1, z.2.2⟩).property
  have cell_mem (i : Fin r) (j : Fin c) (k : Fin (R i j)) :
      rows ⟨i, j, k⟩ ∈ tableauCell A B p i j := by
    apply (tableauCell_mem A B p i j _).mpr
    refine ⟨row_mem ⟨i, j, k⟩, ?_⟩
    rw [backward]
    exact col_mem ⟨i, j, k⟩
  have coordinates (i : Fin r) (j : Fin c) (x : α) (hx : x ∈ A i)
      (hy : p.symm x ∈ B j) :
      ∃ k : Fin (R i j), rows ⟨i, j, k⟩ = x := by
    obtain ⟨⟨a, b, k⟩, hz⟩ := rows.surjective x
    have ha : a = i := tableauIndex_unique A hdA (row_mem ⟨a, b, k⟩) (hz ▸ hx)
    have hb : b = j := by
      apply tableauIndex_unique B hdB (col_mem ⟨a, b, k⟩)
      rwa [← backward, hz]
    subst a
    subst b
    exact ⟨k, hz⟩
  have rank_injective (S : Finset α) : Function.Injective (tableauRank S) := by
    intro x y hxy
    apply (Finset.orderIsoOfFin S rfl).symm.injective
    exact Fin.ext hxy
  refine ⟨p, ?_, ?_⟩
  · intro i j
    -- Each matrix entry counts exactly the offsets in its cell.
    let f : Fin (R i j) → ↥(tableauCell A B p i j) :=
      fun k => ⟨rows ⟨i, j, k⟩, cell_mem i j k⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        have hrow : rows ⟨i, j, a⟩ = rows ⟨i, j, b⟩ :=
          congrArg (fun x : ↥(tableauCell A B p i j) => x.val) h
        exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj (rows.injective hrow)).2)).2
      · intro x
        obtain ⟨hi, hj⟩ := (tableauCell_mem A B p i j _).mp x.property
        obtain ⟨k, hk⟩ := coordinates i j x.val hi hj
        exact ⟨k, Subtype.ext hk⟩
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      (Fintype.card_congr (Equiv.ofBijective f hf)).symm
  · intro i j x y
    constructor
    · intro h
      have hxy : p.symm x.val = y.val := (Equiv.symm_apply_eq p).mpr h.symm
      obtain ⟨k, hk⟩ := coordinates i j x.val x.property (hxy ▸ y.property)
      have hk' : cols ⟨i, j, k⟩ = y.val := by rw [← backward, hk, hxy]
      have ex : rowSlice i ⟨j, k⟩ = x := Subtype.ext hk
      have ey : colSlice j ⟨i, k⟩ = y := Subtype.ext hk'
      exact ⟨k, ex ▸ tableauSlice_rank (A i) (R i) (hr i) j k,
        ey ▸ tableauSlice_rank (B j) (fun t => R t j) (hc j) i k⟩
    · rintro ⟨k, hx, hy⟩
      have ex : x = rowSlice i ⟨j, k⟩ := rank_injective _ (hx.trans
        (tableauSlice_rank (A i) (R i) (hr i) j k).symm)
      have ey : y = colSlice j ⟨i, k⟩ := rank_injective _ (hy.trans
        (tableauSlice_rank (B j) (fun t => R t j) (hc j) i k).symm)
      subst x
      subst y
      exact forward ⟨i, j, k⟩
end

theorem ParabolicDoubleCosetRepresentatives : (∀ (X : Finset Nat) (r c : Nat) (A : Fin r → Finset ↥X) (B : Fin c → Finset ↥X),
  (∀ i, Finset.Nonempty (A i)) →
  (∀ j, Finset.Nonempty (B j)) →
  Pairwise (fun i i' => Disjoint (A i) (A i')) →
  Pairwise (fun j j' => Disjoint (B j) (B j')) →
  (∀ x : ↥X, ∃ i, x ∈ A i) →
  (∀ x : ↥X, ∃ j, x ∈ B j) →
  let G := Equiv.Perm ↥X
  let blockSym := fun S : Finset ↥X =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ S))
  let K : Subgroup G := iSup (fun i => blockSym (A i))
  let H : Subgroup G := iSup (fun j => blockSym (B j))
  let Mat := {R : Fin r → Fin c → Nat //
    (∀ i, Finset.sum Finset.univ (R i) = Finset.card (A i)) ∧
    (∀ j, Finset.sum Finset.univ (fun i => R i j) = Finset.card (B j))}
  let rank := fun (S : Finset ↥X) (x : ↥S) =>
    ((Finset.orderIsoOfFin S rfl).symm x).val
  ∃ classify : DoubleCoset.Quotient (K : Set G) (H : Set G) ≃ Mat,
    (∀ (σ : G) i j, (classify (DoubleCoset.mk K H σ)).val i j =
      Finset.card (A i ∩ Finset.map (Equiv.toEmbedding σ) (B j))) ∧
    ∀ R : Mat, ∃ σ : G,
      DoubleCoset.mk K H σ = classify.symm R ∧
      ∀ (i : Fin r) (j : Fin c) (x : ↥(A i)) (y : ↥(B j)),
        σ y.val = x.val ↔
          ∃ k : Fin (R.val i j),
            rank (A i) x =
              Finset.sum (Finset.Iio j) (fun j' => R.val i j') + k.val ∧
            rank (B j) y =
              Finset.sum (Finset.Iio i) (fun i' => R.val i' j) + k.val) :=
(by
  intro X r c A B _ _ hdA hdB hcA hcB G blockSym K H Mat rank
  -- Xiao, Proposition 7.3 and the two numbered construction steps in §7.2.
  -- The project records no separate Alphabeta Math proof for this endpoint.
  let count : G → Mat := fun p => ⟨fun i j => (tableauCell A B p i j).card, by
    constructor
    · exact tableauCell_card A B hdB hcB p
    · intro j
      simp_rw [tableauCell_card_symm A B p]
      exact tableauCell_card B A hdA hcA p.symm j⟩
  -- Descend the count to the quotient using the left/right factors in DoubleCoset.eq.
  let onCosets : DoubleCoset.Quotient (K : Set G) (H : Set G) → Mat :=
    Quotient.lift count fun p q hpq =>
      Subtype.ext (funext fun i => funext fun j =>
        tableauCount_invariant A B hdA hcA hdB hcB p q (DoubleCoset.eq''.mpr hpq) i j)
  have chosen (R : Mat) : ∃ p : G, count p = R ∧
      ∀ (i : Fin r) (j : Fin c) (x : ↥(A i)) (y : ↥(B j)),
        p y.val = x.val ↔ ∃ k : Fin (R.val i j),
          rank (A i) x = (∑ t ∈ Finset.Iio j, R.val i t) + k.val ∧
          rank (B j) y = (∑ t ∈ Finset.Iio i, R.val t j) + k.val := by
    obtain ⟨p, hcount, hrank⟩ := tableauOrdered A B hdA hcA hdB hcB R.val R.property.1 R.property.2
    refine ⟨p, ?_, hrank⟩
    apply Subtype.ext
    funext i j
    change (tableauCell A B p i j).card = R.val i j
    exact hcount i j
  have bij : Function.Bijective onCosets := by
    constructor
    · intro a b
      refine Quotient.inductionOn' a (fun p => ?_)
      refine Quotient.inductionOn' b (fun q hpq => ?_)
      exact tableauCount_injective A B hdA hcA hdB hcB p q fun i j =>
        congrArg (fun R : Mat => R.val i j) hpq
    · intro R
      obtain ⟨p, hp, _⟩ := chosen R
      exact ⟨DoubleCoset.mk K H p, hp⟩
  let classify := Equiv.ofBijective onCosets bij
  refine ⟨classify, fun _ _ _ => rfl, fun R => ?_⟩
  obtain ⟨p, hp, hrank⟩ := chosen R
  exact ⟨p, (classify.eq_symm_apply).mpr hp, hrank⟩)

#print axioms ParabolicDoubleCosetRepresentatives
