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
        have hcoords := rows.injective hrow
        have hinner : (⟨j, a⟩ : Σ t, Fin (R i t)) = ⟨j, b⟩ :=
          eq_of_heq (Sigma.mk.inj hcoords).2
        exact eq_of_heq (Sigma.mk.inj hinner).2
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
