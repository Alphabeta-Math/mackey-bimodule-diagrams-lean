import MackeyDiagrams
import Proofs.ParabolicDoubleCosetRepresentatives

set_option maxHeartbeats 2000000

private abbrev parBlockExt {α : Type*} [DecidableEq α] (S : Finset α) :
    Equiv.Perm ↥S →* Equiv.Perm α :=
  Equiv.Perm.ofSubtype (p := fun x : α => x ∈ S)

private abbrev parBlockGroup {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) : Subgroup (Equiv.Perm α) :=
  ⨆ i, MonoidHom.range (parBlockExt (D i))

private def parBlockProduct {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (p : ∀ i, Equiv.Perm ↥(D i)) : Equiv.Perm α :=
  (List.ofFn (fun i => parBlockExt (D i) (p i))).prod

private theorem parBlockList_fixes {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (p : ∀ i, Equiv.Perm ↥(D i))
    (l : List (Fin n)) (x : α) (hx : ∀ i ∈ l, x ∉ D i) :
    (l.map (fun i => parBlockExt (D i) (p i))).prod x = x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change parBlockExt (D i) (p i) ((l.map (fun j => parBlockExt (D j) (p j))).prod x) = x
    rw [ih (fun j hj => hx j (List.mem_cons_of_mem _ hj))]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (hx i (List.mem_cons_self ..))

private theorem parBlockProduct_apply {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (p : ∀ i, Equiv.Perm ↥(D i)) (i : Fin n) (x : ↥(D i)) :
    parBlockProduct D p x.val = (p i x).val := by
  have hnot (j : Fin n) (hj : j ≠ i) (y : ↥(D i)) : y.val ∉ D j :=
    fun hy => Finset.disjoint_left.mp (hd hj) hy y.property
  suffices h : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      (l.map (fun j => parBlockExt (D j) (p j))).prod x.val = (p i x).val by
    simpa only [parBlockProduct, List.map_ofFn, Function.comp_id] using
      h (List.ofFn id) (List.nodup_ofFn.mpr fun _ _ e => e) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  intro l hn hi
  induction l with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons j l ih =>
    rw [List.nodup_cons] at hn
    change parBlockExt (D j) (p j) ((l.map (fun j => parBlockExt (D j) (p j))).prod x.val) = _
    by_cases e : j = i
    · subst j
      rw [parBlockList_fixes D p l x.val (fun k hk => hnot k (by
        rintro rfl
        exact hn.1 hk) x)]
      exact Equiv.Perm.ofSubtype_apply_coe _ x
    · rw [ih hn.2 ((List.mem_cons.mp hi).resolve_left (Ne.symm e))]
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (hnot j e (p i x))

private theorem parBlockProduct_fixes {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (p : ∀ i, Equiv.Perm ↥(D i)) (x : α)
    (hx : ∀ i, x ∉ D i) : parBlockProduct D p x = x := by
  simpa only [parBlockProduct, List.map_ofFn, Function.comp_id] using
    parBlockList_fixes D p (List.ofFn id) x (fun i _ => hx i)

private theorem parBlockProduct_mem {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (p : ∀ i, Equiv.Perm ↥(D i)) :
    parBlockProduct D p ∈ parBlockGroup D := by
  apply Subgroup.list_prod_mem
  intro σ hσ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hσ
  exact Subgroup.mem_iSup_of_mem i ⟨p i, rfl⟩

private theorem parBlockPreserve {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    {p : Equiv.Perm α} (hp : p ∈ parBlockGroup D) :
    (∀ i x, x ∈ D i → p x ∈ D i) ∧ (∀ x, (∀ i, x ∉ D i) → p x = x) := by
  refine Subgroup.iSup_induction _ (C := fun f : Equiv.Perm α =>
    (∀ i x, x ∈ D i → f x ∈ D i) ∧ (∀ x, (∀ i, x ∉ D i) → f x = x))
    hp ?_ ?_ ?_
  · rintro j _ ⟨g, rfl⟩
    refine ⟨?_, fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem g (hx j)⟩
    intro i x hx
    by_cases e : i = j
    · subst j
      exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem g x).mpr hx
    · have hj : x ∉ D j := fun h => Finset.disjoint_left.mp (hd e) hx h
      rwa [Equiv.Perm.ofSubtype_apply_of_not_mem g hj]
  · exact ⟨fun _ _ hx => hx, fun _ _ => rfl⟩
  · intro f g hf hg
    refine ⟨fun i x hx => hf.1 i (g x) (hg.1 i x hx), fun x hx => ?_⟩
    change f (g x) = x
    rw [hg.2 x hx, hf.2 x hx]

private theorem parBlockPreserve_iff {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    {p : Equiv.Perm α} (hp : p ∈ parBlockGroup D) (i : Fin n) (x : α) :
    p x ∈ D i ↔ x ∈ D i := by
  refine ⟨fun hx => ?_, (parBlockPreserve D hd hp).1 i x⟩
  simpa using (parBlockPreserve D hd ((parBlockGroup D).inv_mem hp)).1 i (p x) hx

private theorem parBlockProduct_restrict {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (p : Equiv.Perm α) (hp : ∀ i x, p x ∈ D i ↔ x ∈ D i)
    (hfix : ∀ x, (∀ i, x ∉ D i) → p x = x) :
    parBlockProduct D (fun i => p.subtypePerm (hp i)) = p := by
  ext x
  by_cases h : ∃ i, x ∈ D i
  · obtain ⟨i, hi⟩ := h
    exact parBlockProduct_apply D hd _ i ⟨x, hi⟩
  · have hx : ∀ i, x ∉ D i := fun i hi => h ⟨i, hi⟩
    rw [parBlockProduct_fixes D _ x hx, hfix x hx]

private noncomputable def parBlockSplit {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (hd : Pairwise (fun i j => Disjoint (D i) (D j))) :
    parBlockGroup D ≃* (∀ i, Equiv.Perm ↥(D i)) where
  toFun p i := p.val.subtypePerm (parBlockPreserve_iff D hd p.property i)
  invFun q := ⟨parBlockProduct D q, parBlockProduct_mem D q⟩
  left_inv p := Subtype.ext (parBlockProduct_restrict D hd p.val
    (parBlockPreserve_iff D hd p.property) (parBlockPreserve D hd p.property).2)
  right_inv q := funext fun i => Equiv.ext fun x =>
    Subtype.ext (parBlockProduct_apply D hd q i x)
  map_mul' _ _ := funext fun _ => Equiv.ext fun _ => Subtype.ext rfl

private theorem parBlockGroup_of_preserve {α : Type*} [DecidableEq α] {n : Nat}
    (D : Fin n → Finset α) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (p : Equiv.Perm α) (hp : ∀ i x, x ∈ D i → p x ∈ D i)
    (hfix : ∀ x, (∀ i, x ∉ D i) → p x = x) :
    p ∈ parBlockGroup D := by
  have hperm (i : Fin n) (x : α) : p x ∈ D i ↔ x ∈ D i := by
    refine ⟨fun h => ?_, hp i x⟩
    classical
    let f : ↥(D i) → ↥(D i) := fun y => ⟨p y.val, hp i y.val y.property⟩
    have hf : Function.Injective f := fun y z he => Subtype.ext (p.injective (congrArg Subtype.val he))
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) (⟨p x, h⟩ : ↥(D i))
    have e : y.val = x := p.injective (congrArg Subtype.val hy)
    exact e ▸ y.property
  rw [← parBlockProduct_restrict D hd p hperm hfix]
  exact parBlockProduct_mem D _

private theorem parBlockRefines {g r : Nat} (D : Fin g → Finset Nat) (A : Fin r → Finset Nat)
    (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (hna : ∀ a, (A a).Nonempty)
    (hcover : ∀ a x, x ∈ A a → ∃ i, x ∈ D i)
    (hle : parBlockGroup A ≤ parBlockGroup D) :
    ∀ a, ∃ i, A a ⊆ D i := by
  intro a
  obtain ⟨x, hx⟩ := hna a
  obtain ⟨i, hi⟩ := hcover a x hx
  refine ⟨i, fun y hy => ?_⟩
  have hswap : Equiv.swap x y ∈ parBlockGroup A :=
    Subgroup.mem_iSup_of_mem a
      ⟨Equiv.swap (⟨x, hx⟩ : ↥(A a)) ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  simpa using (parBlockPreserve D hd (hle hswap)).1 i x hi

private def parBlockIndices {g r : Nat} (D : Fin g → Finset Nat) (A : Fin r → Finset Nat)
    (i : Fin g) : Finset (Fin r) :=
  Finset.univ.filter (fun a => A a ⊆ D i)

private noncomputable def parBlockIndex {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (i : Fin g) :
    Fin (parBlockIndices D A i).card ≃o ↥(parBlockIndices D A i) :=
  Finset.orderIsoOfFin _ rfl

private noncomputable def parBlockPart {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (i : Fin g) (a : Fin (parBlockIndices D A i).card) :
    Finset ↥(D i) :=
  (A (parBlockIndex D A i a).val).subtype (fun x => x ∈ D i)

private theorem parBlockPart_subset {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (i : Fin g) (a : Fin (parBlockIndices D A i).card) :
    A (parBlockIndex D A i a).val ⊆ D i :=
  (Finset.mem_filter.mp (parBlockIndex D A i a).property).2

private theorem parBlockPart_of_subset {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (i : Fin g) (a : Fin r) (ha : A a ⊆ D i) :
    ∃ j, (parBlockIndex D A i j).val = a := by
  let j : ↥(parBlockIndices D A i) := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  exact ⟨(parBlockIndex D A i).symm j,
    congrArg Subtype.val ((parBlockIndex D A i).apply_symm_apply j)⟩

private theorem parBlockPart_partition {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hna : ∀ a, (A a).Nonempty) (hda : Pairwise (fun a b => Disjoint (A a) (A b)))
    (href : ∀ a, ∃ i, A a ⊆ D i)
    (hcover : ∀ i x, x ∈ D i → ∃ a, x ∈ A a) (i : Fin g) :
    (∀ a, (parBlockPart D A i a).Nonempty) ∧
    Pairwise (fun a b => Disjoint (parBlockPart D A i a) (parBlockPart D A i b)) ∧
    ∀ x : ↥(D i), ∃ a, x ∈ parBlockPart D A i a := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := hna (parBlockIndex D A i a).val
    exact ⟨⟨x, parBlockPart_subset D A i a hx⟩, Finset.mem_subtype.mpr hx⟩
  · intro a b hab
    have hne : (parBlockIndex D A i a).val ≠ (parBlockIndex D A i b).val :=
      fun h => hab ((parBlockIndex D A i).injective (Subtype.ext h))
    exact Finset.disjoint_left.mpr fun x hx hy =>
      Finset.disjoint_left.mp (hda hne) (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hy)
  · intro x
    obtain ⟨a, ha⟩ := hcover i x.val x.property
    obtain ⟨j, hj⟩ := href a
    have e : i = j := by
      by_contra h
      exact Finset.disjoint_left.mp (hd h) x.property (hj ha)
    subst j
    obtain ⟨b, hb⟩ := parBlockPart_of_subset D A i a hj
    exact ⟨b, Finset.mem_subtype.mpr (hb.symm ▸ ha)⟩

private theorem parBlockSplit_mem {g r : Nat} (D : Fin g → Finset Nat) (A : Fin r → Finset Nat)
    (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hda : Pairwise (fun a b => Disjoint (A a) (A b)))
    (href : ∀ a, ∃ i, A a ⊆ D i)
    (hcover : ∀ x, (∃ i, x ∈ D i) → ∃ a, x ∈ A a)
    (hlocal : ∀ i, Pairwise (fun a b => Disjoint (parBlockPart D A i a) (parBlockPart D A i b)) ∧
      ∀ x : ↥(D i), ∃ a, x ∈ parBlockPart D A i a)
    (p : parBlockGroup D) :
    p.val ∈ parBlockGroup A ↔
      ∀ i, parBlockSplit D hd p i ∈ parBlockGroup (parBlockPart D A i) := by
  constructor
  · intro hp i
    refine parBlockGroup_of_preserve _ (hlocal i).1 _ (fun a x hx => ?_) (fun x hx => ?_)
    · exact Finset.mem_subtype.mpr
        ((parBlockPreserve A hda hp).1 (parBlockIndex D A i a).val x.val
          (Finset.mem_subtype.mp hx))
    · obtain ⟨a, ha⟩ := (hlocal i).2 x
      exact False.elim (hx a ha)
  · intro hp
    refine parBlockGroup_of_preserve A hda p.val (fun a x hx => ?_) (fun x hx => ?_)
    · obtain ⟨i, hi⟩ := href a
      obtain ⟨b, hb⟩ := parBlockPart_of_subset D A i a hi
      let y : ↥(D i) := ⟨x, hi hx⟩
      have hy : y ∈ parBlockPart D A i b := Finset.mem_subtype.mpr (hb.symm ▸ hx)
      have hz : parBlockSplit D hd p i y ∈ parBlockPart D A i b :=
        (parBlockPreserve _ (hlocal i).1 (hp i)).1 b y hy
      have hz' := Finset.mem_subtype.mp hz
      change p.val x ∈ A (parBlockIndex D A i b).val at hz'
      rwa [hb] at hz'
    · apply (parBlockPreserve D hd p.property).2 x
      intro i hi
      obtain ⟨a, ha⟩ := hcover x ⟨i, hi⟩
      exact hx a ha

-- Section 7.3's componentwise equality follows by applying Mathlib's DoubleCoset.eq
-- in both directions. The reverse direction assembles the chosen left and right
-- factors via split.symm and uses the two subgroup membership equivalences.
private theorem parBlockCoset_eq {G ι : Type*} [Group G] {P : ι → Type*}
    [∀ i, Group (P i)] (split : G ≃* ∀ i, P i)
    (K H : Subgroup G) (Kᵢ Hᵢ : ∀ i, Subgroup (P i))
    (hK : ∀ x, x ∈ K ↔ ∀ i, split x i ∈ Kᵢ i)
    (hH : ∀ x, x ∈ H ↔ ∀ i, split x i ∈ Hᵢ i) (x y : G) :
    DoubleCoset.mk K H x = DoubleCoset.mk K H y ↔
      ∀ i, DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split x i) =
        DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split y i) := by
  constructor
  · intro h i
    obtain ⟨k, hk, l, hl, rfl⟩ := DoubleCoset.eq.mp h
    refine DoubleCoset.eq.mpr ⟨split k i, (hK k).mp hk i, split l i, (hH l).mp hl i, ?_⟩
    rw [map_mul, map_mul]
    rfl
  · intro h
    have f i := DoubleCoset.eq.mp (h i)
    choose k hk l hl e using f
    refine DoubleCoset.eq.mpr ⟨split.symm k, (hK _).mpr (fun i => ?_),
      split.symm l, (hH _).mpr (fun i => ?_), ?_⟩
    · rw [split.apply_symm_apply]
      exact hk i
    · rw [split.apply_symm_apply]
      exact hl i
    · apply split.injective
      simp only [map_mul, split.apply_symm_apply]
      exact funext e

private noncomputable def parBlockQuotientSplit {G ι : Type*} [Group G] {P : ι → Type*}
    [∀ i, Group (P i)] (split : G ≃* ∀ i, P i)
    (K H : Subgroup G) (Kᵢ Hᵢ : ∀ i, Subgroup (P i))
    (hK : ∀ x, x ∈ K ↔ ∀ i, split x i ∈ Kᵢ i)
    (hH : ∀ x, x ∈ H ↔ ∀ i, split x i ∈ Hᵢ i) :
    DoubleCoset.Quotient (K : Set G) H ≃
      (∀ i, DoubleCoset.Quotient (Kᵢ i : Set (P i)) (Hᵢ i)) := by
  let f : DoubleCoset.Quotient (K : Set G) H → ∀ i, DoubleCoset.Quotient (Kᵢ i : Set (P i)) (Hᵢ i) :=
    Quotient.lift (fun x i => DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split x i))
      (fun x y h => funext ((parBlockCoset_eq split K H Kᵢ Hᵢ hK hH x y).mp (Quotient.sound h)))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂ q q' (fun x y h => ?_)
    exact (parBlockCoset_eq split K H Kᵢ Hᵢ hK hH x y).mpr (congrFun h)
  · intro q
    refine ⟨DoubleCoset.mk K H (split.symm fun i => (q i).out), funext fun i => ?_⟩
    change DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split (split.symm fun i => (q i).out) i) = q i
    rw [split.apply_symm_apply]
    exact DoubleCoset.out_eq' (q i)

private theorem parBlockCoset_one {G : Type*} [Group G] (K H : Subgroup G)
    (h : K = ⊤ ∨ H = ⊤) (q : DoubleCoset.Quotient (K : Set G) H) :
    DoubleCoset.mk K H 1 = q := by
  rw [← DoubleCoset.out_eq' q]
  apply DoubleCoset.eq.mpr
  rcases h with hK | hH
  · exact ⟨q.out, (fun x : G => hK ▸ Subgroup.mem_top x) q.out, 1, H.one_mem, by simp⟩
  · exact ⟨1, K.one_mem, q.out, (fun x : G => hH ▸ Subgroup.mem_top x) q.out, by simp⟩

theorem ProductParabolicDoubleCosets : (∀ (X : Finset Nat) (g r c : Nat)
    (D : Fin g → Finset Nat) (A : Fin r → Finset Nat) (B : Fin c → Finset Nat),
  (∀ i, Finset.Nonempty (D i)) →
  (∀ a, Finset.Nonempty (A a)) →
  (∀ b, Finset.Nonempty (B b)) →
  Pairwise (fun i j => Disjoint (D i) (D j)) →
  Pairwise (fun a a' => Disjoint (A a) (A a')) →
  Pairwise (fun b b' => Disjoint (B b) (B b')) →
  (∀ n : Nat, n ∈ X ↔ ∃ i, n ∈ D i) →
  (∀ n : Nat, n ∈ X ↔ ∃ a, n ∈ A a) →
  (∀ n : Nat, n ∈ X ↔ ∃ b, n ∈ B b) →
  let blockSym := fun S : Finset Nat =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
  let G : Subgroup (Equiv.Perm Nat) := iSup (fun i => blockSym (D i))
  let K₀ : Subgroup (Equiv.Perm Nat) := iSup (fun a => blockSym (A a))
  let H₀ : Subgroup (Equiv.Perm Nat) := iSup (fun b => blockSym (B b))
  K₀ ≤ G → H₀ ≤ G →
  let K := Subgroup.comap (Subgroup.subtype G) K₀
  let H := Subgroup.comap (Subgroup.subtype G) H₀
  let Gᵢ := fun i : Fin g => Equiv.Perm ↥(D i)
  let rows := fun i : Fin g =>
    Finset.filter (fun a : Fin r => A a ⊆ D i) Finset.univ
  let cols := fun i : Fin g =>
    Finset.filter (fun b : Fin c => B b ⊆ D i) Finset.univ
  let row := fun (i : Fin g) (a : Fin (Finset.card (rows i))) =>
    Finset.subtype (fun n : Nat => n ∈ D i)
      (A ((Finset.orderIsoOfFin (rows i) rfl a).val))
  let col := fun (i : Fin g) (b : Fin (Finset.card (cols i))) =>
    Finset.subtype (fun n : Nat => n ∈ D i)
      (B ((Finset.orderIsoOfFin (cols i) rfl b).val))
  let localSym := fun (i : Fin g) (S : Finset ↥(D i)) =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : ↥(D i) => n ∈ S))
  let Kᵢ := fun i : Fin g => iSup (fun a => localSym i (row i a))
  let Hᵢ := fun i : Fin g => iSup (fun b => localSym i (col i b))
  let Mat := fun i : Fin g =>
    {R : Fin (Finset.card (rows i)) → Fin (Finset.card (cols i)) → Nat //
      (∀ a, Finset.sum Finset.univ (R a) = Finset.card (row i a)) ∧
      (∀ b, Finset.sum Finset.univ (fun a => R a b) = Finset.card (col i b))}
  let rank := fun (i : Fin g) (S : Finset ↥(D i)) (x : ↥S) =>
    ((Finset.orderIsoOfFin S rfl).symm x).val
  let Q := DoubleCoset.Quotient (K : Set G) (H : Set G)
  let Qᵢ := fun i : Fin g => DoubleCoset.Quotient (Kᵢ i : Set (Gᵢ i)) (Hᵢ i : Set (Gᵢ i))
  let extend := fun (i : Fin g) (σ : Gᵢ i) =>
    Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ D i) σ
  (∀ a, ∃ i, A a ⊆ D i) ∧
  (∀ b, ∃ i, B b ⊆ D i) ∧
  ∃ (split : G ≃* (∀ i, Gᵢ i)) (quotientSplit : Q ≃ (∀ i, Qᵢ i))
    (classify : ∀ i, Qᵢ i ≃ Mat i) (localRep : ∀ i, Mat i → Gᵢ i)
    (rep : (∀ i, Mat i) → G),
    (∀ (σ : G) (i : Fin g) (x : ↥(D i)),
      (split σ i x).val = (σ : Equiv.Perm Nat) x.val) ∧
    (∀ σ : G, (σ ∈ K ↔ ∀ i, split σ i ∈ Kᵢ i) ∧
      (σ ∈ H ↔ ∀ i, split σ i ∈ Hᵢ i)) ∧
    (∀ (σ : G) i,
      quotientSplit (DoubleCoset.mk K H σ) i = DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split σ i)) ∧
    (∀ (i : Fin g) (σ : Gᵢ i) a b,
      (classify i (DoubleCoset.mk (Kᵢ i) (Hᵢ i) σ)).val a b =
        Finset.card (row i a ∩ Finset.map (Equiv.toEmbedding σ) (col i b))) ∧
    (∀ (i : Fin g) (R : Mat i),
      DoubleCoset.mk (Kᵢ i) (Hᵢ i) (localRep i R) = (classify i).symm R) ∧
    (∀ (i : Fin g) (R : Mat i), Kᵢ i ≠ ⊤ → Hᵢ i ≠ ⊤ →
      ∀ a b (x : ↥(row i a)) (y : ↥(col i b)),
        localRep i R y.val = x.val ↔
          ∃ k : Fin (R.val a b),
            rank i (row i a) x = Finset.sum (Finset.Iio b) (fun b' => R.val a b') + k.val ∧
            rank i (col i b) y = Finset.sum (Finset.Iio a) (fun a' => R.val a' b) + k.val) ∧
    (∀ i, (Kᵢ i = ⊤ ∨ Hᵢ i = ⊤) → ∀ R : Mat i, localRep i R = 1) ∧
    (∀ R : ∀ i, Mat i,
      Pairwise (fun i j =>
        Disjoint {n : Nat | extend i (localRep i (R i)) n ≠ n}
          {n : Nat | extend j (localRep j (R j)) n ≠ n})) ∧
    (∀ R : ∀ i, Mat i,
      (rep R : Equiv.Perm Nat) = List.prod (List.ofFn (fun i => extend i (localRep i (R i))))) ∧
    Function.Bijective (fun R => DoubleCoset.mk K H (rep R))) :=
(by
  classical
  intro X g r c D A B _ hna hnb hd hda hdb coverD coverA coverB blockSym G K₀ H₀ hleK hleH K H
    Gᵢ rows cols row col localSym Kᵢ Hᵢ Mat rank Q Qᵢ extend
  -- Xiao, § 7.3: transpositions force refinement. Nonemptiness supplies a point in
  -- each row and column, and common coverage places it inside an ambient block.
  have hA : ∀ a, ∃ i, A a ⊆ D i :=
    parBlockRefines D A hd hna (fun a x hx => (coverD x).mp ((coverA x).mpr ⟨a, hx⟩)) hleK
  have hB : ∀ b, ∃ i, B b ⊆ D i :=
    parBlockRefines D B hd hnb (fun b x hx => (coverD x).mp ((coverB x).mpr ⟨b, hx⟩)) hleH
  have hcoverA (x : Nat) (hx : ∃ i, x ∈ D i) : ∃ a, x ∈ A a :=
    (coverA x).mp ((coverD x).mpr hx)
  have hcoverB (x : Nat) (hx : ∃ i, x ∈ D i) : ∃ b, x ∈ B b :=
    (coverB x).mp ((coverD x).mpr hx)
  have partA := parBlockPart_partition D A hd hna hda hA (fun i x hx => hcoverA x ⟨i, hx⟩)
  have partB := parBlockPart_partition D B hd hnb hdb hB (fun i x hx => hcoverB x ⟨i, hx⟩)

  -- Restriction gives the product isomorphism. The inverse uses the increasing
  -- Fin list order specified in Lean. At any point at most one factor can act.
  let split : G ≃* ∀ i, Gᵢ i := parBlockSplit D hd
  have hK (p : G) : p ∈ K ↔ ∀ i, split p i ∈ Kᵢ i :=
    parBlockSplit_mem D A hd hda hA hcoverA (fun i => (partA i).2) p
  have hH (p : G) : p ∈ H ↔ ∀ i, split p i ∈ Hᵢ i :=
    parBlockSplit_mem D B hd hdb hB hcoverB (fun i => (partB i).2) p
  let quotientSplit : Q ≃ ∀ i, Qᵢ i := parBlockQuotientSplit split K H Kᵢ Hᵢ hK hH
  have hquot (p : G) (i : Fin g) :
      quotientSplit (DoubleCoset.mk K H p) i = DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split p i) := rfl

  -- Proposition 7.3, steps 1 and 2 in the published HTML, split the ordered
  -- rows and columns and match the corresponding pieces in order. Apply the
  -- compiled supplier to each restricted partition after checking coverage,
  -- nonemptiness and disjointness. Its rank formula retains both step orders.
  have tableaux (i : Fin g) :=
    ParabolicDoubleCosetRepresentatives (D i) (rows i).card (cols i).card (row i) (col i)
      (partA i).1 (partB i).1 (partA i).2.1 (partB i).2.1 (partA i).2.2 (partB i).2.2
  choose classify hcount htable using tableaux
  choose tableau htableClass htableRank using htable
  -- Section 7.3 chooses 1 when either subgroup is the entire factor. In
  -- this branch both the tableau and 1 represent the unique double coset,
  -- so substitute 1 here and keep the ordered matching for the proper factors.
  let localRep (i : Fin g) (R : Mat i) : Gᵢ i :=
    if Kᵢ i = ⊤ ∨ Hᵢ i = ⊤ then 1 else tableau i R
  have hlocalClass (i : Fin g) (R : Mat i) :
      DoubleCoset.mk (Kᵢ i) (Hᵢ i) (localRep i R) = (classify i).symm R := by
    by_cases h : Kᵢ i = ⊤ ∨ Hᵢ i = ⊤
    · simpa only [localRep, ite_eq_left h] using parBlockCoset_one (Kᵢ i) (Hᵢ i) h ((classify i).symm R)
    · simpa only [localRep, ite_eq_right h] using htableClass i R
  let rep (R : ∀ i, Mat i) : G := split.symm (fun i => localRep i (R i))
  have hrep (R : ∀ i, Mat i) (i : Fin g) :
      quotientSplit (DoubleCoset.mk K H (rep R)) i = (classify i).symm (R i) := by
    rw [hquot]
    change DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split (split.symm _) i) = _
    rw [split.apply_symm_apply]
    exact hlocalClass i (R i)
  refine ⟨hA, hB, split, quotientSplit, classify, localRep, rep, ?_, ?_, hquot, hcount, hlocalClass,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro p i x
    rfl
  · exact fun p => ⟨hK p, hH p⟩
  · intro i R hk hh a b x y
    simpa only [localRep, ite_eq_right (not_or.mpr ⟨hk, hh⟩)] using htableRank i R a b x y
  · intro i h R
    simp only [localRep, ite_eq_left h]
  · intro R i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxi : x ∈ D i := by
      by_contra h
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem (localRep i (R i)) h)
    have hxj : x ∈ D j := by
      by_contra h
      exact hy (Equiv.Perm.ofSubtype_apply_of_not_mem (localRep j (R j)) h)
    exact Finset.disjoint_left.mp (hd hij) hxi hxj
  · intro R
    rfl
  · constructor
    · intro R S h
      change DoubleCoset.mk K H (rep R) = DoubleCoset.mk K H (rep S) at h
      funext i
      apply (classify i).symm.injective
      rw [← hrep R i, ← hrep S i, h]
    · intro q
      let R : ∀ i, Mat i := fun i => classify i (quotientSplit q i)
      refine ⟨R, quotientSplit.injective (funext fun i => ?_)⟩
      rw [hrep]
      exact (classify i).symm_apply_apply _)

#print axioms ProductParabolicDoubleCosets
