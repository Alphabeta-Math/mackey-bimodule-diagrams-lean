import MackeyDiagrams
import Proofs.MackeyDecompositionWithParabolicRepresentatives
import Proofs.ModuleTensorUniversalProperty

set_option maxHeartbeats 2000000

namespace FiniteParabolicCompositionSupport

private abbrev P  :=
  Equiv.Perm Nat

private abbrev Finitary  :=
  Subgroup.closure {s : P | Equiv.Perm.IsSwap s}

private abbrev blockSym (D : Finset Nat) : Subgroup P :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ D))

private abbrev blockProduct {m : Nat} (D : Fin m → Finset Nat) : Subgroup P :=
  iSup (fun i => blockSym (D i))

private abbrev Parabolic (S : Subgroup P) : Prop :=
  ∃ (m : Nat) (D : Fin m → Finset Nat),
    (∀ i, Finset.Nonempty (D i)) ∧ Pairwise (fun i j => Disjoint (D i) (D j)) ∧
    S = blockProduct D

private abbrev conjugate (s : P) (S : Subgroup P) : Subgroup P :=
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) S

private abbrev inside (H A : Subgroup P) := Subgroup.comap (Subgroup.subtype H) A

private abbrev Cosets (H A B : Subgroup P) : Type :=
  DoubleCoset.Quotient (inside H A : Set H) (inside H B : Set H)


private abbrev classOf (H A B : Subgroup P) (r : H) : Cosets H A B :=
  DoubleCoset.mk (inside H A) (inside H B) r

private abbrev OrderedSection (H A B : Subgroup P) (r : Cosets H A B → H) : Prop :=
  ∃ (X : Finset Nat) (m p q : Nat)
    (D : Fin m → Finset Nat) (U : Fin p → Finset Nat) (V : Fin q → Finset Nat),
    (∀ i, Finset.Nonempty (D i)) ∧
    (∀ a, Finset.Nonempty (U a)) ∧
    (∀ b, Finset.Nonempty (V b)) ∧
    Pairwise (fun i j => Disjoint (D i) (D j)) ∧
    Pairwise (fun a a' => Disjoint (U a) (U a')) ∧
    Pairwise (fun b b' => Disjoint (V b) (V b')) ∧
    (∀ n : Nat, n ∈ X ↔ ∃ i, n ∈ D i) ∧
    (∀ n : Nat, n ∈ X ↔ ∃ a, n ∈ U a) ∧
    (∀ n : Nat, n ∈ X ↔ ∃ b, n ∈ V b) ∧
    H = blockProduct D ∧ A = blockProduct U ∧ B = blockProduct V ∧
    (∀ a, ∃ i, U a ⊆ D i) ∧
    (∀ b, ∃ i, V b ⊆ D i) ∧
    let rows := fun i : Fin m => Finset.filter (fun a : Fin p => U a ⊆ D i) Finset.univ
    let cols := fun i : Fin m => Finset.filter (fun b : Fin q => V b ⊆ D i) Finset.univ
    let row := fun (i : Fin m) (a : Fin (Finset.card (rows i))) =>
      U (Finset.orderIsoOfFin (rows i) rfl a).val
    let col := fun (i : Fin m) (b : Fin (Finset.card (cols i))) =>
      V (Finset.orderIsoOfFin (cols i) rfl b).val
    let Mat := fun i : Fin m =>
      {R : Fin (Finset.card (rows i)) → Fin (Finset.card (cols i)) → Nat //
        (∀ a, Finset.sum Finset.univ (R a) = Finset.card (row i a)) ∧
        (∀ b, Finset.sum Finset.univ (fun a => R a b) = Finset.card (col i b))}
    let rank := fun (S : Finset Nat) (x : ↥S) =>
      ((Finset.orderIsoOfFin S rfl).symm x).val
    ∃ classify : Cosets H A B ≃ (∀ i : Fin m, Mat i),
      (∀ (s : H) (i : Fin m) a b,
        (classify (classOf H A B s) i).val a b =
          Finset.card (row i a ∩ Finset.map (Equiv.toEmbedding (s : P)) (col i b))) ∧
      (∀ j : Cosets H A B, classOf H A B (r j) = j) ∧
      ∀ (j : Cosets H A B) (i : Fin m) a b (x : ↥(row i a)) (y : ↥(col i b)),
        (r j : P) y.val = x.val ↔
          ∃ k : Fin ((classify j i).val a b),
            rank (row i a) x =
              Finset.sum (Finset.Iio b) (fun b' => (classify j i).val a b') + k.val ∧
            rank (col i b) y =
              Finset.sum (Finset.Iio a) (fun a' => (classify j i).val a' b) + k.val

private abbrev parabolicOn (X : Finset Nat) (H : Subgroup P) : Prop :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧
    H = iSup (fun i => blockSym (blocks i))


private theorem ofFamily {κ : Type} [Finite κ] (X : Finset Nat) (blocks : κ → Finset Nat)
    (hne : ∀ i, (blocks i).Nonempty)
    (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hc : ∀ x, x ∈ X ↔ ∃ i, x ∈ blocks i) :
    parabolicOn X (⨆ i, blockSym (blocks i)) := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, blocks ∘ e, fun i => hne (e i), ?_, ?_, ?_⟩
  · exact fun i j hij => hd (fun he => hij (e.injective he))
  · intro x
    rw [hc x]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa only [Function.comp_apply, e.apply_symm_apply] using hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, hi⟩
  · exact (e.iSup_comp (g := fun i => blockSym (blocks i))).symm
private theorem singletonSym (x : Nat) : blockSym {x} = ⊥ := by
  apply le_antisymm _ bot_le
  rintro σ ⟨τ, rfl⟩
  have hτ : τ = 1 := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    exact (Finset.mem_singleton.mp (τ y).property).trans
      (Finset.mem_singleton.mp y.property).symm
  rw [hτ, map_one]
  exact Subgroup.one_mem _
-- The binary formula takes two partitions of the same finite set.
-- Padding by singleton blocks adds only trivial symmetric factors.
private theorem pad {X Y : Finset Nat} {H : Subgroup (Equiv.Perm Nat)} (hXY : X ⊆ Y)
    (hH : parabolicOn X H) : parabolicOn Y H := by
  classical
  obtain ⟨n, B, hne, hd, hc, rfl⟩ := hH
  let blocks : Fin n ⊕ ↥(Y \ X) → Finset Nat := Sum.elim B (fun y => {y.val})
  have hsup : (⨆ i, blockSym (blocks i)) = ⨆ i, blockSym (B i) := by
    rw [iSup_sum]
    suffices h : (⨆ j : ↥(Y \ X), blockSym {j.val}) = ⊥ by
      change (⨆ i, blockSym (B i)) ⊔ (⨆ j : ↥(Y \ X), blockSym {j.val}) = _
      rw [h, sup_bot_eq]
    simp only [singletonSym, iSup_bot]
  rw [← hsup]
  refine ofFamily Y blocks ?_ ?_ ?_
  · rintro (i | y)
    · exact hne i
    · exact Finset.singleton_nonempty _
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    cases i with
    | inl i =>
        cases j with
        | inl j => exact Finset.disjoint_left.mp (hd (fun h => hij (congrArg Sum.inl h))) hx hy
        | inr y =>
            exact (Finset.mem_sdiff.mp y.property).2
              ((Finset.mem_singleton.mp hy) ▸ (hc x).mpr ⟨i, hx⟩)
    | inr y =>
        cases j with
        | inl j =>
            exact (Finset.mem_sdiff.mp y.property).2
              ((Finset.mem_singleton.mp hx) ▸ (hc x).mpr ⟨j, hy⟩)
        | inr z =>
            exact hij (congrArg Sum.inr (Subtype.ext
              ((Finset.mem_singleton.mp hx).symm.trans (Finset.mem_singleton.mp hy))))
  · intro x
    constructor
    · intro hx
      by_cases hxX : x ∈ X
      · obtain ⟨i, hi⟩ := (hc x).mp hxX
        exact ⟨Sum.inl i, hi⟩
      · exact ⟨Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxX⟩⟩, Finset.mem_singleton_self x⟩
    · rintro ⟨i | y, hx⟩
      · exact hXY ((hc x).mpr ⟨i, hx⟩)
      · exact (Finset.mem_singleton.mp hx).symm ▸ (Finset.mem_sdiff.mp y.property).1

private theorem blockSubset {X Y : Finset Nat} (h : X ⊆ Y) : blockSym X ≤ blockSym Y := by
  classical
  intro p hp
  obtain ⟨q, rfl⟩ := hp
  let p : P := Equiv.Perm.ofSubtype q
  have hmem (x : Nat) : p x ∈ Y ↔ x ∈ Y := by
    by_cases hx : x ∈ X
    · exact iff_of_true (h (by rw [show p x = (q ⟨x, hx⟩).val from
          Equiv.Perm.ofSubtype_apply_of_mem q hx]; exact (q ⟨x, hx⟩).property)) (h hx)
    · rw [show p x = x from Equiv.Perm.ofSubtype_apply_of_not_mem q hx]
  exact ⟨p.subtypePerm hmem, Equiv.Perm.ofSubtype_subtypePerm hmem
    (fun x hx => h (by
      by_contra hn
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem q hn)))⟩

private theorem blockSymFinite (X : Finset Nat) : Finite (blockSym X) := by
  apply Finite.of_surjective (MonoidHom.rangeRestrict (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X)))
  exact MonoidHom.rangeRestrict_surjective _

private theorem parabolicData {H : Subgroup P} (hH : Parabolic H) :
    H ≤ Finitary ∧ Finite H ∧ ∃ X, parabolicOn X H := by
  classical
  obtain ⟨m, D, hne, hd, rfl⟩ := hH
  let X := Finset.univ.biUnion D
  have hcover x : x ∈ X ↔ ∃ i, x ∈ D i := by simp [X]
  have hle : blockProduct D ≤ blockSym X :=
    iSup_le fun i => blockSubset (fun x hx => (hcover x).mpr ⟨i, hx⟩)
  have hfin : Finite (blockProduct D) :=
    haveI := blockSymFinite X
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  refine ⟨hle.trans ?_, hfin, X, m, D, hne, hd, hcover, rfl⟩
  rintro s ⟨q, rfl⟩
  exact mem_closure_isSwap'.mpr (X.finite_toSet.subset fun x hx => by
    by_contra hn
    exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem q hn))

private theorem parabolicOn_parabolic {X : Finset Nat} {H : Subgroup P} :
    parabolicOn X H → Parabolic H :=
  fun ⟨m, D, hne, hd, _, heq⟩ => ⟨m, D, hne, hd, heq⟩

private theorem conjParabolic {H : Subgroup P} (hH : Parabolic H) (s : ↥Finitary) :
    Parabolic (conjugate s.val H) := by
  classical
  obtain ⟨m, D, hne, hd, rfl⟩ := hH
  have heq := FiniteParabolicConjugateBlocks D hne hd s
  change conjugate s.val (blockProduct D) =
    blockProduct (fun i => (D i).image (s.val : Nat → Nat)) at heq
  rw [heq]
  refine ⟨m, fun i => (D i).image (s.val : Nat → Nat), fun i => (hne i).image _, ?_, rfl⟩
  intro i j hij
  exact Finset.disjoint_left.mpr fun x hx hy => by
    obtain ⟨y, hyi, hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hzj, hzx⟩ := Finset.mem_image.mp hy
    have heq := s.val.injective (hyx.trans hzx.symm)
    exact Finset.disjoint_left.mp (hd hij) hyi (heq ▸ hzj)

private theorem interParabolic {H K : Subgroup P} (hH : Parabolic H) (hK : Parabolic K) :
    Parabolic (H ⊓ K) := by
  classical
  obtain ⟨X, hX⟩ := (parabolicData hH).2.2
  obtain ⟨Y, hY⟩ := (parabolicData hK).2.2
  obtain ⟨n, A, hnA, hdA, hcA, rfl⟩ := pad (Y := X ∪ Y) Finset.subset_union_left hX
  obtain ⟨m, B, hnB, hdB, hcB, rfl⟩ := pad (Y := X ∪ Y) Finset.subset_union_right hY
  rw [FiniteParabolicIntersectionBlocks (X ∪ Y) A B hnA hnB hdA hdB hcA hcB]
  let Cell := {ij : Fin n × Fin m // (A ij.1 ∩ B ij.2).Nonempty}
  let C (ij : Cell) := A ij.val.1 ∩ B ij.val.2
  have hEmpty (Z : Finset Nat) (h : ¬ Z.Nonempty) : blockSym Z = ⊥ := by
    apply le_antisymm _ bot_le
    rintro p ⟨s, rfl⟩
    exact Subgroup.mem_bot.mpr (Equiv.ext fun x =>
      Equiv.Perm.ofSubtype_apply_of_not_mem s (fun hx => h ⟨x, hx⟩))
  have heq : (⨆ i, ⨆ j, blockSym (A i ∩ B j)) = ⨆ ij, blockSym (C ij) := by
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun j => ?_
      by_cases h : (A i ∩ B j).Nonempty
      · exact le_iSup (fun ij => blockSym (C ij)) (⟨(i, j), h⟩ : Cell)
      · exact le_of_eq_of_le (hEmpty _ h) bot_le
    · refine iSup_le fun ij => ?_
      exact (le_iSup (fun j => blockSym (A ij.val.1 ∩ B j)) ij.val.2).trans
        (le_iSup (fun i => ⨆ j, blockSym (A i ∩ B j)) ij.val.1)
  rw [heq]
  apply parabolicOn_parabolic (X := X ∪ Y)
  refine ofFamily _ C (fun ij => ij.property) ?_ ?_
  · intro ij kl h
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxk, hxl⟩ := Finset.mem_inter.mp hy
    have hai : ij.val.1 = kl.val.1 := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdA hne) hxi hxk
    have hbj : ij.val.2 = kl.val.2 := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdB hne) hxj hxl
    exact h (Subtype.ext (Prod.ext hai hbj))
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (hcA x).mp hx
      obtain ⟨j, hj⟩ := (hcB x).mp hx
      have h := Finset.mem_inter.mpr ⟨hi, hj⟩
      exact ⟨⟨(i, j), ⟨x, h⟩⟩, h⟩
    · rintro ⟨ij, hx⟩
      exact (hcA x).mpr ⟨ij.val.1, (Finset.mem_inter.mp hx).1⟩

private abbrev rows {m n : Nat} (D : Fin m → Finset Nat) (U : Fin n → Finset Nat)
    (i : Fin m) := Finset.univ.filter (fun a => U a ⊆ D i)

private abbrev row {m n : Nat} (D : Fin m → Finset Nat) (U : Fin n → Finset Nat)
    (i : Fin m) (a : Fin (rows D U i).card) :=
  U ((Finset.orderIsoOfFin (rows D U i) rfl a).val)

private theorem row_subset {m n : Nat} (D : Fin m → Finset Nat) (U : Fin n → Finset Nat)
    (i : Fin m) (a : Fin (rows D U i).card) : row D U i a ⊆ D i :=
  (Finset.mem_filter.mp (Finset.orderIsoOfFin (rows D U i) rfl a).property).2

private abbrev restricted (D S : Finset Nat) := S.subtype (· ∈ D)

private def restrictPoint {D S : Finset Nat} (h : S ⊆ D) (x : ↥S) : ↥(restricted D S) :=
  ⟨⟨x, h x.property⟩, Finset.mem_subtype.mpr x.property⟩

private theorem restricted_card {D S : Finset Nat} (h : S ⊆ D) :
    (restricted D S).card = S.card := by
  rw [← Finset.card_map (Function.Embedding.subtype (· ∈ D)), Finset.subtype_map_of_mem h]

private theorem restricted_rank {D S : Finset Nat} (h : S ⊆ D) (x : ↥S) :
    ((Finset.orderIsoOfFin (restricted D S) rfl).symm (restrictPoint h x)).val =
      ((Finset.orderIsoOfFin S rfl).symm x).val := by
  let points : ↥S ≃o ↥(restricted D S) :=
    { toFun := restrictPoint h
      invFun := fun y => ⟨y.val.val, Finset.mem_subtype.mp y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := by intro x y; rfl }
  have heq : points.trans (Finset.orderIsoOfFin (restricted D S) rfl).symm =
      (Finset.orderIsoOfFin S rfl).symm.trans (Fin.castOrderIso (restricted_card h).symm) := by
    apply Subsingleton.elim
  exact congrArg (fun f : ↥S ≃o Fin (restricted D S).card => (f x).val) heq

private theorem restricted_count {D S T : Finset Nat} (hs : S ⊆ D) (ht : T ⊆ D)
    (p : P) (q : Equiv.Perm ↥D) (hp : ∀ x : ↥D, (q x).val = p x.val) :
    (restricted D S ∩ (restricted D T).map q.toEmbedding).card =
      (S ∩ T.map p.toEmbedding).card := by
  let e := Function.Embedding.subtype (· ∈ D)
  have he : q.toEmbedding.trans e = e.trans p.toEmbedding :=
    Function.Embedding.ext fun x => hp x
  rw [← Finset.card_map e, Finset.map_inter, Finset.map_map, he, ← Finset.map_map,
    Finset.subtype_map_of_mem hs, Finset.subtype_map_of_mem ht]

private abbrev Matrix {m n k : Nat} (D : Fin m → Finset Nat)
    (A : Fin n → Finset Nat) (B : Fin k → Finset Nat) (i : Fin m) :=
  {R : Fin (rows D A i).card → Fin (rows D B i).card → Nat //
    (∀ a, Finset.sum Finset.univ (R a) = (row D A i a).card) ∧
    (∀ b, Finset.sum Finset.univ (fun a => R a b) = (row D B i b).card)}

private abbrev RestrictedMatrix {m n k : Nat} (D : Fin m → Finset Nat)
    (A : Fin n → Finset Nat) (B : Fin k → Finset Nat) (i : Fin m) :=
  {R : Fin (rows D A i).card → Fin (rows D B i).card → Nat //
    (∀ a, Finset.sum Finset.univ (R a) = (restricted (D i) (row D A i a)).card) ∧
    (∀ b, Finset.sum Finset.univ (fun a => R a b) = (restricted (D i) (row D B i b)).card)}

private def unrestrictedMatrix {m n k : Nat} (D : Fin m → Finset Nat)
    (A : Fin n → Finset Nat) (B : Fin k → Finset Nat) (i : Fin m) :
    RestrictedMatrix D A B i ≃ Matrix D A B i where
  toFun R := ⟨R.val,
    fun a => (R.property.1 a).trans (restricted_card (row_subset D A i a)),
    fun b => (R.property.2 b).trans (restricted_card (row_subset D B i b))⟩
  invFun R := ⟨R.val,
    fun a => (R.property.1 a).trans (restricted_card (row_subset D A i a)).symm,
    fun b => (R.property.2 b).trans (restricted_card (row_subset D B i b)).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def cosetsCongr (H : Subgroup P) {A B A' B' : Subgroup P}
    (hA : A = A') (hB : B = B') : Cosets H A B ≃ Cosets H A' B' := by
  subst A'
  subst B'
  exact Equiv.refl _

private theorem cosetsCongr_classOf (H : Subgroup P) {A B A' B' : Subgroup P}
    (hA : A = A') (hB : B = B') (s : H) :
    cosetsCongr H hA hB (classOf H A B s) = classOf H A' B' s := by
  subst A'
  subst B'
  rfl

private theorem orderedSection {H A B : Subgroup P}
    (hH : Parabolic H) (hA : Parabolic A) (hB : Parabolic B) (hAH : A ≤ H) (hBH : B ≤ H) :
    ∃ r : Cosets H A B → H, OrderedSection H A B r := by
  classical
  obtain ⟨X, hX⟩ := (parabolicData hH).2.2
  obtain ⟨Y, hY⟩ := (parabolicData hA).2.2
  obtain ⟨Z, hZ⟩ := (parabolicData hB).2.2
  let S := X ∪ Y ∪ Z
  obtain ⟨m, D, hnD, hdD, hcD, rfl⟩ :=
    pad (Y := S) (Finset.subset_union_left.trans Finset.subset_union_left) hX
  obtain ⟨n, U, hnU, hdU, hcU, rfl⟩ :=
    pad (Y := S) (Finset.subset_union_right.trans Finset.subset_union_left) hY
  obtain ⟨k, V, hnV, hdV, hcV, rfl⟩ :=
    pad (Y := S) Finset.subset_union_right hZ
  let H := blockProduct D
  let A := blockProduct U
  let B := blockProduct V
  obtain ⟨refU, refV, -⟩ :=
    ProductParabolicDoubleCosets S m n k D U V hnD hnU hnV hdD hdU hdV hcD hcU hcV hAH hBH
  have h1 (C : Subgroup P) :
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((1 : ↥Finitary) : P))) C = C := by
    have hm : (MulAut.conj (1 : P)).toMonoidHom = MonoidHom.id P := by
      ext p
      simp
    exact (congrArg (fun f : P →* P => C.map f) hm).trans (Subgroup.map_id C)
  have hA' : conjugate (1 : P) A = A := h1 A
  have hB' : conjugate (1 : P) B = B := h1 B
  have hAH' : conjugate (1 : P) A ≤ H := by rw [hA']; exact hAH
  have hBH' : conjugate (1 : P) B ≤ H := by rw [hB']; exact hBH
  -- The quantified section is in Theorem 7.4. The § 7.3 product section
  -- replaces tableau matching by the identity in one-coset blocks, and
  -- therefore only supplies the refinements here. Proposition 7.3 steps
  -- 1 and 2, matching consecutive pieces, are retained on every block.
  have data := MackeyDecompositionWithParabolicRepresentatives.{0} A B H
    (1 : ↥Finitary) (1 : ↥Finitary) S m n k D U V hnD hnU hnV hdD hdU hdV hcD hcU hcV
      rfl hA' hB' hAH' hBH'
  obtain ⟨split, classify, σ, hsplit, hcount, hσ, hrank, _⟩ := data
  let I (j : Cosets H A B) := cosetsCongr H hA'.symm hB'.symm j
  have hI (s : H) : I (classOf H A B s) = classOf H _ _ s :=
    cosetsCongr_classOf H hA'.symm hB'.symm s
  let convertMat := Equiv.piCongrRight (unrestrictedMatrix D U V)
  let r (j : Cosets H A B) := σ (classify (I j))
  let matrixClassify : Cosets H A B ≃ (∀ i, Matrix D U V i) :=
    (cosetsCongr H hA'.symm hB'.symm).trans (classify.trans convertMat)
  refine ⟨r, S, m, n, k, D, U, V, hnD, hnU, hnV, hdD, hdU, hdV, hcD, hcU, hcV,
    rfl, rfl, rfl, refU, refV, matrixClassify, ?_, ?_, ?_⟩
  · intro s i a b
    change (classify (I (classOf H A B s)) i).val a b = _
    rw [hI]
    exact (hcount s i a b).trans (restricted_count (row_subset D U i a)
      (row_subset D V i b) (s : P) (split s i) (hsplit s i))
  · intro j
    apply (cosetsCongr H hA'.symm hB'.symm).injective
    change I (classOf H A B (r j)) = I j
    rw [hI]
    exact (hσ (classify (I j))).trans (classify.symm_apply_apply (I j))
  · intro j i a b x y
    let x' := restrictPoint (row_subset D U i a) x
    let y' := restrictPoint (row_subset D V i b) y
    have hex : split (r j) i y'.val = x'.val ↔ (r j : P) y.val = x.val := by
      rw [← Subtype.coe_inj, hsplit]
      rfl
    have spec := hrank (classify (I j)) i a b x' y'
    change _ ↔ ∃ t : Fin ((classify (I j) i).val a b),
      ((Finset.orderIsoOfFin (restricted (D i) (row D U i a)) rfl).symm x').val = _ ∧
      ((Finset.orderIsoOfFin (restricted (D i) (row D V i b)) rfl).symm y').val = _ at spec
    rw [hex] at spec
    dsimp only [x', y'] at spec
    rw [ restricted_rank (row_subset D U i a) x, restricted_rank (row_subset D V i b) y] at spec
    exact spec

private theorem finiteCosets {H A B : Subgroup P} (hH : Parabolic H) :
    Finite (Cosets H A B) :=
  haveI := (parabolicData hH).2.1
  Finite.of_surjective (classOf H A B) (fun j => ⟨j.out, DoubleCoset.out_eq' j⟩)

private abbrev embed {S T : Subgroup P} (s : P) (h : conjugate s S ≤ T) : MackeyDiagrams.ConjEmbedding S T :=
  MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := T) s
    (fun x => h ⟨(x : P), x.property, rfl⟩)

private abbrev inverseEmbed {S T : Subgroup P} (s : P) (h : T ≤ conjugate s S) : MackeyDiagrams.ConjEmbedding T S :=
  MackeyDiagrams.ConjEmbedding.ofConjugator (H := T) (G := S) s⁻¹ (by
    intro x
    obtain ⟨y, hy, he⟩ := h x.property
    change s * y * s⁻¹ = (x : P) at he
    rw [← he]
    have cancel : s⁻¹ * (s * y * s⁻¹) * (s⁻¹)⁻¹ = y := by group
    rw [cancel]
    exact hy)

private abbrev Span (K H : Subgroup P) : Type :=
  Σ L : {S : Subgroup P // Parabolic S},
    {α : ↥Finitary // conjugate (α : P) L.val ≤ K} ×
    {β : ↥Finitary // conjugate (β : P) L.val ≤ H}

private abbrev pairWord {K H L : Subgroup P} (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H) : MackeyDiagrams.Word K H :=
  MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.down b)

private abbrev spanBasis {K H : Subgroup P} (S : Span K H) : MackeyDiagrams.Biset K H :=
  MackeyDiagrams.Word.basis
    (pairWord (embed (S.2.1.val : P) S.2.1.property) (embed (S.2.2.val : P) S.2.2.property))

private abbrev middleLeft {K H : Subgroup P} (S : Span K H) :=
  conjugate (S.2.2.val : P) S.1.val

private abbrev middleRight {H J : Subgroup P} (T : Span H J) :=
  conjugate (T.2.1.val : P) T.1.val

private abbrev intersectionGroup {K H J : Subgroup P} (S : Span K H) (T : Span H J) (r : H) :=
  middleLeft S ⊓ conjugate (r : P) (middleRight T)

private abbrev outerLeft {K H J : Subgroup P} (S : Span K H) (T : Span H J) (r : H) :=
  MackeyDiagrams.ConjEmbedding.comp
    (embed (S.2.1.val : P) S.2.1.property)
    (inverseEmbed (S.2.2.val : P) (show intersectionGroup S T r ≤ middleLeft S from inf_le_left))

private abbrev outerRight {K H J : Subgroup P} (S : Span K H) (T : Span H J) (r : H) :=
  MackeyDiagrams.ConjEmbedding.comp
    (embed (T.2.2.val : P) T.2.2.property)
    (MackeyDiagrams.ConjEmbedding.comp
      (inverseEmbed (T.2.1.val : P) (show middleRight T ≤ middleRight T from le_rfl))
      (inverseEmbed (r : P)
        (show intersectionGroup S T r ≤ conjugate (r : P) (middleRight T) from inf_le_right)))

private theorem intersectionParabolic {K H J : Subgroup P} (hH : Parabolic H)
    (S : Span K H) (T : Span H J) (r : H) :
    Parabolic (intersectionGroup S T r) :=
  interParabolic (conjParabolic S.1.property S.2.2.val)
    (conjParabolic (conjParabolic T.1.property T.2.1.val)
      ⟨r.val, (parabolicData hH).1 r.property⟩)

private noncomputable def composeSpan {K H J : Subgroup P} (hH : Parabolic H)
    (S : Span K H) (T : Span H J) (r : H) : Span K J := by
  let α := S.2.1.val * S.2.2.val⁻¹
  let β := T.2.2.val * T.2.1.val⁻¹ * (⟨r.val, (parabolicData hH).1 r.property⟩ : ↥Finitary)⁻¹
  refine ⟨⟨intersectionGroup S T r, intersectionParabolic hH S T r⟩,
    ⟨α, ?_⟩, ⟨β, ?_⟩⟩
  · rintro p ⟨x, hx, rfl⟩
    have hp := ((outerLeft S T r).toHom ⟨x, hx⟩).property
    change (S.2.1.val : P) * ((S.2.2.val : P)⁻¹ * x * ((S.2.2.val : P)⁻¹)⁻¹) *
      ((S.2.1.val : P)⁻¹) ∈ K at hp
    change (α : P) * x * (α : P)⁻¹ ∈ K
    unfold α
    push_cast
    convert hp using 1 <;> group
  · rintro p ⟨x, hx, rfl⟩
    have hp := ((outerRight S T r).toHom ⟨x, hx⟩).property
    change (T.2.2.val : P) * ((T.2.1.val : P)⁻¹ * ((r : P)⁻¹ * x * ((r : P)⁻¹)⁻¹) *
      ((T.2.1.val : P)⁻¹)⁻¹) * (T.2.2.val : P)⁻¹ ∈ J at hp
    change (β : P) * x * (β : P)⁻¹ ∈ J
    unfold β
    push_cast
    convert hp using 1 <;> group

private theorem composeSpan_basis {K H J : Subgroup P} (hH : Parabolic H)
    (S : Span K H) (T : Span H J) (r : H) :
    spanBasis (composeSpan hH S T r) = (pairWord (outerLeft S T r) (outerRight S T r)).basis := by
  have hl : embed ((composeSpan hH S T r).2.1.val : P) (composeSpan hH S T r).2.1.property =
      outerLeft S T r := by
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change ((S.2.1.val : P) * (S.2.2.val : P)⁻¹) * (x : P) *
      ((S.2.1.val : P) * (S.2.2.val : P)⁻¹)⁻¹ = _
    change _ = (S.2.1.val : P) * ((S.2.2.val : P)⁻¹ * (x : P) * ((S.2.2.val : P)⁻¹)⁻¹) *
      (S.2.1.val : P)⁻¹
    group
  have hr : embed ((composeSpan hH S T r).2.2.val : P) (composeSpan hH S T r).2.2.property =
      outerRight S T r := by
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change ((T.2.2.val : P) * (T.2.1.val : P)⁻¹ * (r : P)⁻¹) * (x : P) *
      ((T.2.2.val : P) * (T.2.1.val : P)⁻¹ * (r : P)⁻¹)⁻¹ = _
    change _ = (T.2.2.val : P) * ((T.2.1.val : P)⁻¹ * ((r : P)⁻¹ * (x : P) * ((r : P)⁻¹)⁻¹) *
      ((T.2.1.val : P)⁻¹)⁻¹) * (T.2.2.val : P)⁻¹
    group
  exact congrArg MackeyDiagrams.Word.basis (congrArg₂ pairWord hl hr)

private def regularSpan {H : Subgroup P} (hH : Parabolic H) : Span H H := by
  have h1 : conjugate 1 H ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    change (1 : P) * x * (1 : P)⁻¹ ∈ H
    simpa using hx
  exact ⟨⟨H, hH⟩, ⟨1, h1⟩, ⟨1, h1⟩⟩

private theorem regularSpan_basis {H : Subgroup P} (hH : Parabolic H) :
    spanBasis (regularSpan hH) = (pairWord (MackeyDiagrams.ConjEmbedding.id H)
      (MackeyDiagrams.ConjEmbedding.id H)).basis := by
  have heq (h : conjugate 1 H ≤ H) :
      embed 1 h = MackeyDiagrams.ConjEmbedding.id H := by
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (1 : P) * (x : P) * (1 : P)⁻¹ = (x : P)
    simp
  exact congrArg MackeyDiagrams.Word.basis (congrArg₂ pairWord (heq _) (heq _))
end FiniteParabolicCompositionSupport
