import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.ExtremalParabolicsOfFiniteGroup

set_option maxHeartbeats 2000000

private abbrev bwFinitary : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}

private abbrev bwBlock (B : Set Nat) : Subgroup ↥bwFinitary :=
  fixingSubgroup (↥bwFinitary) Bᶜ

private abbrev bwGroup {ι : Type*} (B : ι → Set Nat) : Subgroup ↥bwFinitary :=
  ⨆ i, bwBlock (B i)

private theorem bwFixOutside {B : Set Nat} {p : ↥bwFinitary}
    (hp : p ∈ bwBlock B) {x : Nat} (hx : x ∉ B) : p.1 x = x :=
  (mem_fixingSubgroup_iff _).mp hp x hx

private theorem bwFactorMaps {B : Set Nat} {p : ↥bwFinitary}
    (hp : p ∈ bwBlock B) : Set.MapsTo p.1 B B := by
  intro x hx
  by_contra hy
  have he : p.1 x = x := p.1.injective (bwFixOutside hp hy)
  exact hy (he.symm ▸ hx)

private theorem bwPreserve {ι : Type*} (B : ι → Set Nat)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (j : ι)
    {p : ↥bwFinitary} (hp : p ∈ bwGroup B) :
    Set.MapsTo p.1 (B j) (B j) := by
  refine Subgroup.iSup_induction (fun i => bwBlock (B i))
    (C := fun q => Set.MapsTo q.1 (B j) (B j)) hp ?_ ?_ ?_
  · intro i q hq
    by_cases hij : i = j
    · subst i
      exact bwFactorMaps hq
    · intro x hx
      have hxi : x ∉ B i := fun hi => Set.disjoint_left.1 (hB hij) hi hx
      exact bwFixOutside hq hxi |>.symm ▸ hx
  · exact fun _ hx => hx
  · exact fun _ _ hq hr _ hx => hq (hr hx)

-- This also covers points lying in singleton factors.
private theorem bwFix {ι : Type*} (B : ι → Set Nat) {x : Nat}
    (hx : ∀ i, x ∈ B i → ∀ y ∈ B i, y = x)
    {p : ↥bwFinitary} (hp : p ∈ bwGroup B) : p.1 x = x := by
  classical
  refine Subgroup.iSup_induction (fun i => bwBlock (B i))
    (C := fun q => q.1 x = x) hp ?_ rfl ?_
  · intro i q hq
    by_cases hi : x ∈ B i
    · exact hx i hi _ (bwFactorMaps hq hi)
    · exact bwFixOutside hq hi
  · intro q r hq hr
    change q.1 (r.1 x) = x
    rw [hr, hq]

private theorem bwMovedInBlock {ι : Type*} (B : ι → Set Nat)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    {p : ↥bwFinitary} (hp : p ∈ bwGroup B) {x : Nat} (hx : p.1 x ≠ x) :
    ∃ j, x ∈ B j ∧ p.1 x ∈ B j := by
  classical
  have hex : ∃ j, x ∈ B j := by
    by_contra h
    exact hx (bwFix B (fun j hj => (h ⟨j, hj⟩).elim) hp)
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, hj, bwPreserve B hB j hp hj⟩

private def bwSwap (x y : Nat) : ↥bwFinitary :=
  ⟨Equiv.swap x y, by
    by_cases h : x = y
    · subst y
      rw [Equiv.swap_self]
      exact bwFinitary.one_mem
    · exact Subgroup.subset_closure ⟨x, y, h, rfl⟩⟩

private theorem bwSwapInBlock {B : Set Nat} {x y : Nat}
    (hx : x ∈ B) (hy : y ∈ B) : bwSwap x y ∈ bwBlock B := by
  apply (mem_fixingSubgroup_iff _).mpr
  intro z hz
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hz (h.symm ▸ hx))
    (fun h => hz (h.symm ▸ hy))

private theorem bwConjApply (p q : ↥bwFinitary) (x : Nat) :
    (p * q * p⁻¹).1 (p.1 x) = p.1 (q.1 x) := by
  change (p.1 * q.1 * p.1⁻¹) (p.1 x) = _
  simp [Equiv.Perm.mul_apply]

private theorem bwEmbedsBlock {ι κ : Type*} (X : ι → Set Nat) (Y : κ → Set Nat)
    (hY : Pairwise (fun j k => Disjoint (Y j) (Y k)))
    (p : ↥bwFinitary) (hp : ∀ h : bwGroup X, p * h.1 * p⁻¹ ∈ bwGroup Y)
    (i : ι) (hi : Set.Nontrivial (X i)) :
    ∃ j, Set.MapsTo p.1 (X i) (Y j) := by
  classical
  have pair {x y : Nat} (hx : x ∈ X i) (hy : y ∈ X i) (hne : x ≠ y) :
      ∃ j, p.1 x ∈ Y j ∧ p.1 y ∈ Y j := by
    let s := bwSwap x y
    have hmem : s ∈ bwGroup X := Subgroup.mem_iSup_of_mem i (bwSwapInBlock hx hy)
    have heq : (p * s * p⁻¹).1 (p.1 x) = p.1 y := by
      rw [bwConjApply]
      exact congrArg p.1 (Equiv.swap_apply_left x y)
    obtain ⟨j, hjx, hjy⟩ := bwMovedInBlock Y hY (hp ⟨s, hmem⟩)
      (fun he => hne (p.1.injective (he.symm.trans heq)))
    exact ⟨j, hjx, heq ▸ hjy⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hi
  obtain ⟨j, hj, _⟩ := pair hx hy hxy
  refine ⟨j, fun z hz => ?_⟩
  by_cases h : x = z
  · exact h ▸ hj
  · obtain ⟨k, hkx, hkz⟩ := pair hx hz h
    have hkj : k = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hY hne) hkx hj
    exact hkj ▸ hkz

private theorem bwConjSwap (p : ↥bwFinitary) (x y : Nat) :
    (p * bwSwap x y * p⁻¹).1 = Equiv.swap (p.1 x) (p.1 y) :=
  (Equiv.swap_apply_apply p.1 x y).symm

private theorem bwFiniteMoves (p : ↥bwFinitary) :
    {x : Nat | p.1 x ≠ x}.Finite :=
  mem_closure_isSwap'.mp p.2

-- Restrict the partial bijection to a finite slice before extending it.
private theorem bwExtendSlice (τ : ↥bwFinitary) (B D : Set Nat)
    (hB : Set.MapsTo τ.1 (D ∩ B) B) :
    ∃ q : ↥bwFinitary, q ∈ bwBlock B ∧ ∀ x ∈ D ∩ B, q.1 x = τ.1 x := by
  classical
  let S : Set Nat := {x : Nat | τ.1 x ≠ x} ∩ B
  let : Finite S := ((bwFiniteMoves τ).inter_of_left B).to_subtype
  let P : Set S := {x | x.1 ∈ D}
  let f : P → S := fun x =>
    ⟨τ.1 x.1.1, Equiv.Perm.set_support_apply_mem.mpr x.1.2.1, hB ⟨x.2, x.1.2.2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact τ.1.injective (congrArg Subtype.val h)
  let e := Equiv.ofInjective f hf
  let q : Equiv.Perm Nat := Equiv.Perm.ofSubtype (p := fun x => x ∈ S) e.extendSubtype
  have hfix {x : Nat} (hx : x ∉ S) : q x = x :=
    Equiv.Perm.ofSubtype_apply_of_not_mem _ hx
  have hq : q ∈ bwFinitary := by
    apply mem_closure_isSwap'.mpr
    apply ((bwFiniteMoves τ).inter_of_left B).subset
    intro x hx
    change q x ≠ x at hx
    by_contra h
    exact hx (hfix h)
  refine ⟨⟨q, hq⟩, (mem_fixingSubgroup_iff _).mpr (fun x hx => hfix (fun h => hx h.2)), ?_⟩
  intro x hx
  change q x = τ.1 x
  by_cases h : x ∈ S
  · rw [Equiv.Perm.ofSubtype_apply_of_mem e.extendSubtype h,
      Equiv.extendSubtype_apply_of_mem e ⟨x, h⟩ hx.1]
    rfl
  · rw [hfix h]
    by_contra hne
    exact h ⟨(fun he => hne he.symm), hx.2⟩

private theorem bwAssemble {κ : Type*} [DecidableEq κ] (Y : κ → Set Nat)
    (hY : Pairwise (fun j k => Disjoint (Y j) (Y k))) (J : Finset κ)
    (q : κ → ↥bwFinitary) (hq : ∀ j, q j ∈ bwBlock (Y j)) :
    ∃ p : ↥bwFinitary, p ∈ bwGroup Y ∧
      ∀ j, ∀ x ∈ Y j, p.1 x = if j ∈ J then (q j).1 x else x := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨1, (bwGroup Y).one_mem, ?_⟩
    intro j x _
    simp only [Finset.notMem_empty, ite_false]
    rfl
  | insert j J hj ih =>
    obtain ⟨p, hp, happ⟩ := ih
    refine ⟨p * q j, (bwGroup Y).mul_mem hp (Subgroup.mem_iSup_of_mem j (hq j)), ?_⟩
    intro k x hx
    change p.1 ((q j).1 x) = _
    by_cases hkj : k = j
    · subst k
      rw [happ j _ (bwFactorMaps (hq j) hx), ite_eq_right hj, ite_eq_left (Finset.mem_insert_self j J)]
    · rw [bwFixOutside (hq j) (fun h => Set.disjoint_left.1 (hY hkj) hx h),
        happ k x hx]
      simp only [Finset.mem_insert, hkj, false_or]

private theorem bwExtendOnBlocks {κ : Type*} (Y : κ → Set Nat)
    (hY : Pairwise (fun j k => Disjoint (Y j) (Y k))) (τ : ↥bwFinitary) (D : Set Nat)
    (hmaps : ∀ j, Set.MapsTo τ.1 (D ∩ Y j) (Y j))
    (hcover : ∀ x ∈ D, ∃ j, x ∈ Y j) :
    ∃ p : ↥bwFinitary, p ∈ bwGroup Y ∧ ∀ x ∈ D, p.1 x = τ.1 x := by
  classical
  choose q hq happ using fun j => bwExtendSlice τ (Y j) D (hmaps j)
  let J : Set κ := ⋃ (x : Nat) (_ : x ∈ {x : Nat | τ.1 x ≠ x}), {j | x ∈ Y j}
  have hJ : J.Finite := (bwFiniteMoves τ).biUnion fun x _ => Set.Subsingleton.finite (by
    intro j hj k hk
    by_contra h
    exact Set.disjoint_left.1 (hY h) hj hk)
  obtain ⟨p, hp, hpapp⟩ := bwAssemble Y hY hJ.toFinset q hq
  refine ⟨p, hp, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := hcover x hx
  rw [hpapp j x hj]
  by_cases h : j ∈ hJ.toFinset
  · rw [ite_eq_left h]
    exact happ j x ⟨hx, hj⟩
  · rw [ite_eq_right h]
    by_contra hne
    apply h
    exact hJ.mem_toFinset.mpr (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨(fun he => hne he.symm), hj⟩⟩)

theorem BlockwiseGroupElementDotCriterion : (
∀ {ι κ : Type*} (X : ι → Set Nat) (Y : κ → Set Nat),
  (∀ i, Set.Nonempty (X i)) → (∀ j, Set.Nonempty (Y j)) →
  Pairwise (fun i i' => Disjoint (X i) (X i')) →
  Pairwise (fun j j' => Disjoint (Y j) (Y j')) →
  let U := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
  let blockSym := fun B : Set Nat => _root_.fixingSubgroup (↥U) Bᶜ
  let H := iSup (fun i => blockSym (X i))
  let G := iSup (fun j => blockSym (Y j))
  ∀ (α β : ↥U)
      (hα : ∀ h : H, α * (h : ↥U) * α⁻¹ ∈ G)
      (hβ : ∀ h : H, β * (h : ↥U) * β⁻¹ ∈ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
    let inBlock := fun (σ : ↥U) (i : ι) (j : κ) =>
      Set.MapsTo (⇑(σ : Equiv.Perm Nat)) (X i) (Y j)
    (∀ i, Set.Nontrivial (X i) →
      (∃ j, inBlock α i j) ∧ (∃ j, inBlock β i j)) ∧
    (Nonempty (MackeyDiagrams.Dot a b) ↔
      ∀ i, Set.Nontrivial (X i) → ∃ j, inBlock α i j ∧ inBlock β i j)
) :=
(by
  classical
  intro ι κ X Y _ _ hX hY U blockSym H G α β hα hβ a b inBlock
  -- Xiao §3.4, “A criterion for group-element dots,” agrees in the archived
  -- source/mackey-bimodules.tex (line 1057) and the revised
  -- article-revision/mackey-bimodules.tex (line 1225). The archive and published
  -- PDFs have different SHA-256 digests. The reviewed Lean type is used as given.
  -- The plan supplies no numbered Alphabeta Math proof for this endpoint.
  -- The finite conjugate-block and extremal-parabolic theorems require finite
  -- input data. Here the block sets and the index types can be infinite.
  have aBlock := bwEmbedsBlock X Y hY α hα
  have bBlock := bwEmbedsBlock X Y hY β hβ
  refine ⟨fun i hi => ⟨aBlock i hi, bBlock i hi⟩, ?_⟩
  constructor
  · -- Necessity: test a genuine transposition in any nontrivial source block.
    rintro ⟨t⟩ i hi
    obtain ⟨j, hj⟩ := aBlock i hi
    obtain ⟨k, hk⟩ := bBlock i hi
    obtain ⟨x, hx, y, hy, hxy⟩ := hi
    let s : H := ⟨bwSwap x y, Subgroup.mem_iSup_of_mem i (bwSwapInBlock hx hy)⟩
    let d : ↥U := t.element.1
    have he := congrArg (fun g : G => g.1.1 (β.1 x)) (t.intertwines s)
    change (α * bwSwap x y * α⁻¹).1 (d.1 (β.1 x)) =
      d.1 ((β * bwSwap x y * β⁻¹).1 (β.1 x)) at he
    rw [bwConjSwap, bwConjSwap, Equiv.swap_apply_left] at he
    have moved : Equiv.swap (α.1 x) (α.1 y) (d.1 (β.1 x)) ≠ d.1 (β.1 x) :=
      fun h => hxy (β.1.injective (d.1.injective (h.symm.trans he)))
    have hin : d.1 (β.1 x) ∈ Y j := by
      by_cases h : d.1 (β.1 x) = α.1 x
      · exact h.symm ▸ hj hx
      · by_cases h' : d.1 (β.1 x) = α.1 y
        · exact h'.symm ▸ hj hy
        · exact (moved (Equiv.swap_apply_of_ne_of_ne h h')).elim
    have hkj : k = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hY hne) (bwPreserve Y hY k t.element.2 (hk hx)) hin
    exact ⟨j, hj, hkj ▸ hk⟩
  · -- Sufficiency: on active source blocks prescribe β x ↦ α x.
    -- Extend within each moved-support slice to keep the extension finitary,
    -- then multiply over the finitely many target blocks meeting that support.
    intro sameBlock
    let A : Set Nat := {x | ∃ i, Set.Nontrivial (X i) ∧ x ∈ X i}
    let D : Set Nat := (fun x => β.1 x) '' A
    let τ : ↥U := α * β⁻¹
    have hτ (x : Nat) : τ.1 (β.1 x) = α.1 x := by
      change (α.1 * β.1⁻¹) (β.1 x) = _
      simp [Equiv.Perm.mul_apply]
    have cover : ∀ z ∈ D, ∃ j, z ∈ Y j := by
      rintro _ ⟨x, ⟨i, hi, hx⟩, rfl⟩
      obtain ⟨j, _, hb⟩ := sameBlock i hi
      exact ⟨j, hb hx⟩
    have maps (j : κ) : Set.MapsTo τ.1 (D ∩ Y j) (Y j) := by
      rintro _ ⟨⟨x, ⟨i, hi, hx⟩, rfl⟩, hj⟩
      obtain ⟨k, ha, hb⟩ := sameBlock i hi
      have hkj : k = j := by
        by_contra hne
        exact Set.disjoint_left.1 (hY hne) (hb hx) hj
      rw [hτ]
      exact hkj ▸ ha hx
    obtain ⟨p, hp, hpD⟩ := bwExtendOnBlocks Y hY τ D maps cover
    have agree (x : Nat) (hx : x ∈ A) : p.1 (β.1 x) = α.1 x :=
      (hpD _ ⟨x, hx, rfl⟩).trans (hτ x)
    have preserves (h : H) {x : Nat} (hx : x ∈ A) : h.1.1 x ∈ A := by
      obtain ⟨i, hi, hx⟩ := hx
      exact ⟨i, hi, bwPreserve X hX i h.2 hx⟩
    have fixes (h : H) {x : Nat} (hx : x ∉ A) : h.1.1 x = x := by
      apply bwFix X _ h.2
      intro i hxi y hy
      by_contra hne
      exact hx ⟨i, ⟨y, hy, x, hxi, hne⟩, hxi⟩
    let d : G := ⟨p, hp⟩
    have intertwines (h : H) : a.toHom h * d = d * b.toHom h := by
      apply Subtype.ext
      apply Subtype.ext
      apply Equiv.ext
      intro z
      obtain ⟨y, rfl⟩ := β.1.surjective z
      change (α * h.1 * α⁻¹).1 (p.1 (β.1 y)) = p.1 ((β * h.1 * β⁻¹).1 (β.1 y))
      rw [bwConjApply]
      by_cases hy : y ∈ A
      · rw [agree y hy, bwConjApply, agree _ (preserves h hy)]
      · rw [fixes h hy]
        obtain ⟨w, hw⟩ := α.1.surjective (p.1 (β.1 y))
        have hwA : w ∉ A := by
          intro hwa
          exact hy ((β.1.injective (p.1.injective ((agree w hwa).trans hw))) ▸ hwa)
        rw [← hw, bwConjApply, fixes h hwA]
    -- The registered criterion applies to d in G at exactly these embeddings.
    obtain ⟨t, _⟩ := ((GroupElementDotCriterion H G α β hα hβ).2.1 d).2.2.2.mp intertwines
    exact ⟨t⟩)

#print axioms BlockwiseGroupElementDotCriterion
