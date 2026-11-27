import MackeyDiagrams
import Proofs.ParabolicDoubleCosetRepresentatives

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
