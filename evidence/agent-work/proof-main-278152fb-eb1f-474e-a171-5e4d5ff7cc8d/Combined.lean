import Proofs.FiniteParabolicClosure
import Proofs.ReidemeisterOne

set_option maxHeartbeats 4000000

namespace BlockRefinementCurl

private abbrev finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev U := ↥finitary
private abbrev ambientBlock (S : Finset Nat) : Subgroup (Equiv.Perm Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S))
private abbrev blockSym (S : Finset Nat) : Subgroup U :=
  Subgroup.comap (Subgroup.subtype finitary) (ambientBlock S)
private abbrev blockGroup (P : Finset (Finset Nat)) : Subgroup U :=
  iSup (fun S : ↥P => blockSym (S : Finset Nat))
private abbrev partition (T : Finset Nat) (P : Finset (Finset Nat)) : Prop :=
  (∀ S ∈ P, Finset.Nonempty S) ∧
    (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
    (∀ x : Nat, x ∈ T ↔ ∃ S ∈ P, x ∈ S)
private abbrev merge (P : Finset (Finset Nat)) (A B : Finset Nat) :=
  insert (A ∪ B) (Finset.erase (Finset.erase P A) B)
private abbrev path (Y X : Finset (Finset Nat)) (n : Nat)
    (P : Nat → Finset (Finset Nat)) (A B : Nat → Finset Nat) : Prop :=
    P 0 = Y ∧ P n = X ∧ ∀ i, i < n →
      A i ∈ P i ∧ B i ∈ P i ∧ A i ≠ B i ∧ P (i + 1) = merge (P i) (A i) (B i)

private theorem swap_mem_ambientBlock {S : Finset Nat} {x y : Nat} (hx : x ∈ S)
    (hy : y ∈ S) : Equiv.swap x y ∈ ambientBlock S :=
  ⟨Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

-- Alphabeta Math, transpositions generate the symmetric group, Steps 1.1
-- and 2.1. Use the checked swap-closure criterion on Nat. Its two
-- hypotheses here are finite support in S and the internal swap of x
-- with its image whenever x moves.
-- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
private theorem ambientBlock_le_finitary (S : Finset Nat) : ambientBlock S ≤ finitary := by
  rintro σ ⟨τ, rfl⟩
  apply mem_closure_isSwap'.mpr
  exact S.finite_toSet.subset (fun x hx => by
    by_contra h
    exact hx ((MulAction.mem_fixedBy).2 (Equiv.Perm.ofSubtype_apply_of_not_mem τ h)))

private theorem map_blockGroup (P : Finset (Finset Nat)) :
    (blockGroup P).map finitary.subtype = ⨆ S : ↥P, ambientBlock (S : Finset Nat) := by
  rw [show blockGroup P = ⨆ S : ↥P, blockSym (S : Finset Nat) from rfl, Subgroup.map_iSup]
  congr 1
  funext S
  apply Subgroup.map_comap_eq_self
  rw [Subgroup.range_subtype]
  exact ambientBlock_le_finitary S

private theorem blockSym_mono {A B : Finset Nat} (h : A ⊆ B) :
    blockSym A ≤ blockSym B := by
  intro σ hσ
  change (σ : Equiv.Perm Nat) ∈ ambientBlock A at hσ
  change (σ : Equiv.Perm Nat) ∈ ambientBlock B
  obtain ⟨τ, hτ⟩ := hσ
  rw [← hτ]
  refine ⟨(Equiv.Perm.ofSubtype τ).subtypePerm (p := fun x : Nat => x ∈ B) ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ A
    · exact iff_of_true (h ((Equiv.Perm.ofSubtype_apply_mem_iff_mem τ x).2 hx)) (h hx)
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem τ hx]
  · exact Equiv.Perm.ofSubtype_subtypePerm _ (fun x hx => h (by
      by_contra hn
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem τ hn)))

private theorem block_unique {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    {x : Nat} {A B : Finset Nat} (hA : A ∈ P) (hB : B ∈ P)
    (hxA : x ∈ A) (hxB : x ∈ B) : A = B := by
  by_contra hn
  exact Finset.disjoint_left.mp (h.2.1 A hA B hB hn) hxA hxB

private theorem blockGroup_action {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    {σ : U} (hσ : σ ∈ blockGroup P) :
    (∀ S ∈ P, ∀ x ∈ S, (σ : Equiv.Perm Nat) x ∈ S) ∧
      (∀ x ∉ T, (σ : Equiv.Perm Nat) x = x) := by
  refine Subgroup.iSup_induction (fun S : ↥P => blockSym (S : Finset Nat))
    (C := fun f : U =>
      (∀ S ∈ P, ∀ x ∈ S, (f : Equiv.Perm Nat) x ∈ S) ∧
      (∀ x ∉ T, (f : Equiv.Perm Nat) x = x)) hσ ?_ ?_ ?_
  · intro S f hf
    obtain ⟨τ, hτ⟩ := (show (f : Equiv.Perm Nat) ∈ ambientBlock S from hf)
    rw [← hτ]
    constructor
    · intro V hV x hx
      by_cases he : V = S.val
      · subst V
        exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem τ x).2 hx
      · rwa [Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun hs =>
          he (block_unique h hV S.property hx hs))]
    · intro x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem τ
        (fun hs => hx ((h.2.2 x).2 ⟨S, S.property, hs⟩))
  · exact ⟨fun _ _ _ hx => hx, fun _ _ => rfl⟩
  · exact fun f g hf hg =>
      ⟨fun S hS x hx => hf.1 S hS _ (hg.1 S hS x hx),
        fun x hx => show (f : Equiv.Perm Nat) ((g : Equiv.Perm Nat) x) = x by
          rw [hg.2 x hx, hf.2 x hx]⟩

private theorem mem_map_blockGroup {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    {σ : Equiv.Perm Nat}
    (preserve : ∀ S ∈ P, ∀ x ∈ S, σ x ∈ S)
    (fixes : ∀ x ∉ T, σ x = x) : σ ∈ (blockGroup P).map finitary.subtype := by
  rw [map_blockGroup]
  let swaps : Set (Equiv.Perm Nat) :=
    {f | ∃ S ∈ P, ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f = Equiv.swap x y}
  have genuine : ∀ f ∈ swaps, Equiv.Perm.IsSwap f := by
    rintro f ⟨S, hS, x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, y, hxy, rfl⟩
  have hle : Subgroup.closure swaps ≤ ⨆ S : ↥P, ambientBlock (S : Finset Nat) := by
    apply (Subgroup.closure_le _).2
    rintro f ⟨S, hS, x, hx, y, hy, hxy, rfl⟩
    exact Subgroup.mem_iSup_of_mem (⟨S, hS⟩ : ↥P) (swap_mem_ambientBlock hx hy)
  apply hle
  refine (mem_closure_isSwap genuine).2 ⟨T.finite_toSet.subset ?_, ?_⟩
  · intro x hx
    by_contra ht
    exact hx ((MulAction.mem_fixedBy).2 (fixes x ht))
  · intro x
    by_cases hx : σ x = x
    · rw [hx]
      exact MulAction.mem_orbit_self x
    · have ht : x ∈ T := by
        by_contra hn
        exact hx (fixes x hn)
      obtain ⟨S, hS, hs⟩ := (h.2.2 x).1 ht
      have hswap : Equiv.swap x (σ x) ∈ Subgroup.closure swaps :=
        Subgroup.subset_closure ⟨S, hS, x, hs, σ x, preserve S hS x hs, Ne.symm hx, rfl⟩
      exact MulAction.mem_orbit_iff.mpr ⟨⟨_, hswap⟩, Equiv.swap_apply_left _ _⟩

private noncomputable def blockAct (P : Finset (Finset Nat))
    (f : ∀ S : ↥P, Equiv.Perm ↥(S : Finset Nat)) (x : Nat) : Nat := by
  classical
  exact if h : ∃ S : ↥P, x ∈ (S : Finset Nat) then
    (f h.choose ⟨x, h.choose_spec⟩).val else x

private theorem blockAct_apply {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    (f : ∀ S : ↥P, Equiv.Perm ↥(S : Finset Nat)) (S : ↥P) (x : ↥(S : Finset Nat)) :
    blockAct P f x = (f S x).val := by
  have hx : ∃ V : ↥P, x.val ∈ (V : Finset Nat) := ⟨S, x.property⟩
  rw [blockAct, dite_eq_left hx]
  have he : hx.choose = S := Subtype.ext
    (block_unique h hx.choose.property S.property hx.choose_spec x.property)
  have hw : (⟨hx.choose, hx.choose_spec⟩ : {V : ↥P // x.val ∈ (V : Finset Nat)}) =
      ⟨S, x.property⟩ := Subtype.ext he
  exact congrArg (fun w => (f w.val ⟨x.val, w.property⟩).val) hw

private theorem blockAct_fix {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    (f : ∀ S : ↥P, Equiv.Perm ↥(S : Finset Nat)) {x : Nat} (hx : x ∉ T) :
    blockAct P f x = x := by
  rw [blockAct, dite_eq_right (fun ⟨S, hs⟩ => hx ((h.2.2 x).2 ⟨S, S.property, hs⟩))]

private noncomputable def blockGlue {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    (f : ∀ S : ↥P, Equiv.Perm ↥(S : Finset Nat)) : Equiv.Perm Nat where
  toFun := blockAct P f
  invFun := blockAct P (fun S => (f S).symm)
  left_inv x := by
    by_cases hx : x ∈ T
    · obtain ⟨S, hS, hxS⟩ := (h.2.2 x).1 hx
      rw [blockAct_apply h f ⟨S, hS⟩ ⟨x, hxS⟩,
        blockAct_apply h (fun S => (f S).symm) ⟨S, hS⟩ (f ⟨S, hS⟩ ⟨x, hxS⟩)]
      exact congrArg Subtype.val ((f ⟨S, hS⟩).symm_apply_apply ⟨x, hxS⟩)
    · rw [blockAct_fix h f hx, blockAct_fix h _ hx]
  right_inv x := by
    by_cases hx : x ∈ T
    · obtain ⟨S, hS, hxS⟩ := (h.2.2 x).1 hx
      rw [blockAct_apply h (fun S => (f S).symm) ⟨S, hS⟩ ⟨x, hxS⟩,
        blockAct_apply h f ⟨S, hS⟩ ((f ⟨S, hS⟩).symm ⟨x, hxS⟩)]
      exact congrArg Subtype.val ((f ⟨S, hS⟩).apply_symm_apply ⟨x, hxS⟩)
    · rw [blockAct_fix h _ hx, blockAct_fix h f hx]

private noncomputable def blockRestrict {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    (σ : blockGroup P) (S : ↥P) : Equiv.Perm ↥(S : Finset Nat) :=
  (σ.val : Equiv.Perm Nat).subtypePerm (fun x => by
    refine ⟨fun hx => ?_, blockGroup_action h σ.property |>.1 S S.property x⟩
    have hi := (blockGroup_action h ((blockGroup P).inv_mem σ.property)).1
      S S.property ((σ.val : Equiv.Perm Nat) x) hx
    simpa [Equiv.Perm.inv_def] using hi)

private noncomputable def blockEquiv {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P) :
    ↥(blockGroup P) ≃ (∀ S : ↥P, Equiv.Perm ↥(S : Finset Nat)) :=
  Equiv.ofBijective (blockRestrict h) (by
    constructor
    · intro f g he
      apply Subtype.ext
      apply Subtype.ext
      apply Equiv.ext
      intro x
      by_cases hx : x ∈ T
      · obtain ⟨S, hS, hs⟩ := (h.2.2 x).1 hx
        exact congrArg (fun p : Equiv.Perm ↥S => (p ⟨x, hs⟩).val)
          (congrFun he (⟨S, hS⟩ : ↥P))
      · exact ((blockGroup_action h f.property).2 x hx).trans
          ((blockGroup_action h g.property).2 x hx).symm
    · intro f
      let σ := blockGlue h f
      have hm : σ ∈ (blockGroup P).map finitary.subtype := by
        apply mem_map_blockGroup h
        · intro S hS x hx
          change blockAct P f x ∈ S
          rw [blockAct_apply h f ⟨S, hS⟩ ⟨x, hx⟩]
          exact (f ⟨S, hS⟩ ⟨x, hx⟩).property
        · exact fun _ hx => blockAct_fix h f hx
      obtain ⟨u, hu, he⟩ := hm
      refine ⟨⟨u, hu⟩, ?_⟩
      funext S
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change (u : Equiv.Perm Nat) x = (f S x).val
      change (u : Equiv.Perm Nat) = σ at he
      rw [he]
      exact blockAct_apply h f S x)

private theorem blockCard {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P) :
    Nat.card ↥(blockGroup P) = ∏ S ∈ P, (S.card).factorial := by
  classical
  rw [Nat.card_congr (blockEquiv h), Nat.card_pi]
  calc
    _ = ∏ S : ↥P, ((S : Finset Nat).card).factorial := by
      apply Finset.prod_congr rfl
      intro S _
      simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]
    _ = _ := Finset.prod_coe_sort P (fun S => S.card.factorial)

private theorem blockFinite {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P) :
    Finite ↥(blockGroup P) :=
  Finite.of_injective _ (blockEquiv h).injective


private theorem mem_merge {P : Finset (Finset Nat)} {A B S : Finset Nat} :
    S ∈ merge P A B ↔ S = A ∪ B ∨ S ∈ P ∧ S ≠ A ∧ S ≠ B := by
  simp only [merge, Finset.mem_insert, Finset.mem_erase]
  tauto

private theorem merge_valid {T : Finset Nat} {P : Finset (Finset Nat)} {A B : Finset Nat}
    (h : partition T P) (ha : A ∈ P) (hb : B ∈ P) (_hab : A ≠ B) :
    partition T (merge P A B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S hs
    rcases mem_merge.mp hs with rfl | ⟨hs, _, _⟩
    · obtain ⟨x, hx⟩ := h.1 A ha
      exact ⟨x, Finset.mem_union_left B hx⟩
    · exact h.1 S hs
  · intro S hs V hv hne
    rcases mem_merge.mp hs with rfl | ⟨hs, hsa, hsb⟩
    · rcases mem_merge.mp hv with he | ⟨hv, hva, hvb⟩
      · exact (hne he.symm).elim
      · exact Finset.disjoint_union_left.mpr
          ⟨h.2.1 A ha V hv hva.symm, h.2.1 B hb V hv hvb.symm⟩
    · rcases mem_merge.mp hv with rfl | ⟨hv, _, _⟩
      · exact Finset.disjoint_union_right.mpr
          ⟨h.2.1 S hs A ha hsa, h.2.1 S hs B hb hsb⟩
      · exact h.2.1 S hs V hv hne
  · intro x
    rw [h.2.2]
    constructor
    · rintro ⟨S, hs, hx⟩
      by_cases hsa : S = A
      · subst S
        exact ⟨A ∪ B, mem_merge.mpr (Or.inl rfl), Finset.mem_union_left B hx⟩
      by_cases hsb : S = B
      · subst S
        exact ⟨A ∪ B, mem_merge.mpr (Or.inl rfl), Finset.mem_union_right A hx⟩
      exact ⟨S, mem_merge.mpr (Or.inr ⟨hs, hsa, hsb⟩), hx⟩
    · rintro ⟨S, hs, hx⟩
      rcases mem_merge.mp hs with rfl | ⟨hs, _, _⟩
      · exact (Finset.mem_union.mp hx).elim (fun hx => ⟨A, ha, hx⟩) (fun hx => ⟨B, hb, hx⟩)
      · exact ⟨S, hs, hx⟩

private theorem union_not_in {T : Finset Nat} {P : Finset (Finset Nat)} {A B : Finset Nat}
    (h : partition T P) (ha : A ∈ P) (hb : B ∈ P) (hne : A ≠ B) :
    A ∪ B ∉ P := by
  intro hab
  obtain ⟨x, hx⟩ := h.1 A ha
  obtain ⟨y, hy⟩ := h.1 B hb
  exact hne ((block_unique h ha hab hx (Finset.mem_union_left B hx)).trans
    (block_unique h hab hb (Finset.mem_union_right A hy) hy))

private theorem merge_le (P : Finset (Finset Nat)) (A B : Finset Nat) :
    blockGroup P ≤ blockGroup (merge P A B) := by
  refine iSup_le fun S => ?_
  have atUnion := le_iSup (fun V : ↥(merge P A B) => blockSym (V : Finset Nat))
    ⟨A ∪ B, mem_merge.mpr (Or.inl rfl)⟩
  rcases S with ⟨S, hs⟩
  by_cases ha : S = A
  · subst S
    exact (blockSym_mono Finset.subset_union_left).trans atUnion
  by_cases hb : S = B
  · subst S
    exact (blockSym_mono Finset.subset_union_right).trans atUnion
  exact le_iSup (fun V : ↥(merge P A B) => blockSym (V : Finset Nat))
    ⟨S, mem_merge.mpr (Or.inr ⟨hs, ha, hb⟩)⟩

private theorem relIndex_card {V : Type*} [Group V] {A B : Subgroup V} (h : A ≤ B) :
    A.relIndex B * Nat.card ↥A = Nat.card ↥B := by
  have he := Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  exact he ▸ Subgroup.index_mul_card (A.subgroupOf B)

private theorem merge_index {T : Finset Nat} {P : Finset (Finset Nat)} {A B : Finset Nat}
    (h : partition T P) (ha : A ∈ P) (hb : B ∈ P) (hab : A ≠ B) :
    (blockGroup P).relIndex (blockGroup (merge P A B)) =
      Nat.choose (A.card + B.card) A.card := by
  classical
  have eq := relIndex_card (merge_le P A B)
  let F : Finset Nat → Nat := fun S => S.card.factorial
  let Q := (P.erase A).erase B
  have hb' : B ∈ P.erase A := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have old : Nat.card ↥(blockGroup P) = F A * (F B * ∏ S ∈ Q, F S) := by
    rw [blockCard h, ← Finset.mul_prod_erase P F ha, ← Finset.mul_prod_erase (P.erase A) F hb']
  have new : Nat.card ↥(blockGroup (merge P A B)) = F (A ∪ B) * ∏ S ∈ Q, F S := by
    rw [blockCard (merge_valid h ha hb hab)]
    exact Finset.prod_insert (fun hu =>
      union_not_in h ha hb hab (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hu)))
  have hchoose : Nat.choose (A.card + B.card) A.card * F A * F B = F (A ∪ B) := by
    have hcard := Finset.card_union_of_disjoint (h.2.1 A ha B hb hab)
    simpa only [F, hcard, Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (n := A.card + B.card) (k := A.card)
        (Nat.le_add_right A.card B.card)
  rw [old, new, ← hchoose] at eq
  apply Nat.eq_of_mul_eq_mul_right
    (m := F A * (F B * ∏ S ∈ Q, F S))
  · exact Nat.mul_pos (Nat.factorial_pos _) (Nat.mul_pos (Nat.factorial_pos _)
      (Finset.prod_pos fun S _ => Nat.factorial_pos _))
  · simpa only [mul_assoc] using eq

private theorem finer_of_le {T : Finset Nat} {X Y : Finset (Finset Nat)}
    (hx : partition T X) (hy : partition T Y) (hle : blockGroup Y ≤ blockGroup X) :
    ∀ B ∈ Y, ∃ A ∈ X, B ⊆ A := by
  intro B hb
  obtain ⟨u, hu⟩ := hy.1 B hb
  obtain ⟨A, ha, hua⟩ := (hx.2.2 u).1 ((hy.2.2 u).2 ⟨B, hb, hu⟩)
  refine ⟨A, ha, ?_⟩
  intro v hv
  have hswap := swap_mem_ambientBlock hu hv
  let s : U := ⟨Equiv.swap u v, ambientBlock_le_finitary B hswap⟩
  have hs : s ∈ blockGroup Y := Subgroup.mem_iSup_of_mem (⟨B, hb⟩ : ↥Y)
    (show s ∈ blockSym B from hswap)
  have he := (blockGroup_action hx (hle hs)).1 A ha u hua
  change Equiv.swap u v u ∈ A at he
  rwa [Equiv.swap_apply_left] at he

private theorem factorial_fibers {T : Finset Nat} {X Y : Finset (Finset Nat)}
    (hx : partition T X) (hy : partition T Y)
    (rf : ∀ B ∈ Y, ∃ A ∈ X, B ⊆ A) :
    (∏ A ∈ X, ∏ B ∈ Y.filter (fun B => B ⊆ A), (B.card.factorial : Rat)) =
      ∏ B ∈ Y, (B.card.factorial : Rat) := by
  classical
  let dest : Finset Nat → Finset Nat := fun B =>
    if hb : B ∈ Y then (rf B hb).choose else ∅
  have hs (B : Finset Nat) (hb : B ∈ Y) := (rf B hb).choose_spec
  have dst (B : Finset Nat) (hb : B ∈ Y) :
      dest B ∈ X ∧ B ⊆ dest B := by
    simpa only [dest, dite_eq_left hb] using hs B hb
  have hf (A : Finset Nat) (ha : A ∈ X) :
      Y.filter (fun B => B ⊆ A) = Y.filter (fun B => dest B = A) := by
    ext B
    simp only [Finset.mem_filter]
    refine and_congr_right (fun hb => ⟨?_, fun he => he ▸ (dst B hb).2⟩)
    intro hba
    obtain ⟨x, hxb⟩ := hy.1 B hb
    exact block_unique hx (dst B hb).1 ha ((dst B hb).2 hxb) (hba hxb)
  calc
    _ = ∏ A ∈ X, ∏ B ∈ Y.filter (fun B => dest B = A), (B.card.factorial : Rat) :=
      Finset.prod_congr rfl fun A hA => by rw [hf A hA]
    _ = _ := Finset.prod_fiberwise_of_maps_to (fun B hB => (dst B hB).1) _

private theorem refinement_ratio {T : Finset Nat} {X Y : Finset (Finset Nat)}
    (hx : partition T X) (hy : partition T Y) (hle : blockGroup Y ≤ blockGroup X) :
    ((blockGroup Y).relIndex (blockGroup X) : Rat) =
      ∏ V ∈ X, (V.card.factorial : Rat) /
        (∏ W ∈ Y.filter (fun W => W ⊆ V), (W.card.factorial : Rat)) := by
  have hcard := relIndex_card hle
  rw [blockCard hx, blockCard hy] at hcard
  have rat : ((blockGroup Y).relIndex (blockGroup X) : Rat) *
      (∏ W ∈ Y, (W.card.factorial : Rat)) = ∏ V ∈ X, (V.card.factorial : Rat) := by
    exact_mod_cast hcard
  rw [Finset.prod_div_distrib, factorial_fibers hx hy (finer_of_le hx hy hle)]
  apply (eq_div_iff ?_).2 rat
  exact Finset.prod_ne_zero_iff.mpr fun W _ => by exact_mod_cast (Nat.factorial_ne_zero W.card)

private theorem merge_exists {T : Finset Nat} {X Y : Finset (Finset Nat)}
    (hx : partition T X) (hy : partition T Y)
    (rf : ∀ B ∈ Y, ∃ A ∈ X, B ⊆ A) (hne : Y ≠ X) :
    ∃ A ∈ Y, ∃ B ∈ Y, A ≠ B ∧ ∃ V ∈ X, A ⊆ V ∧ B ⊆ V := by
  by_contra! hn
  have coincide (V : Finset Nat) (hv : V ∈ X) : V ∈ Y := by
    obtain ⟨x, hxv⟩ := hx.1 V hv
    obtain ⟨A, ha, hxa⟩ := (hy.2.2 x).1 ((hx.2.2 x).2 ⟨V, hv, hxv⟩)
    obtain ⟨V', hv', hav'⟩ := rf A ha
    have hav : A ⊆ V := by
      rwa [block_unique hx hv' hv (hav' hxa) hxv] at hav'
    have hva : V ⊆ A := by
      intro y hyv
      obtain ⟨B, hb, hyb⟩ := (hy.2.2 y).1 ((hx.2.2 y).2 ⟨V, hv, hyv⟩)
      obtain ⟨W, hw, hbw⟩ := rf B hb
      have he : W = V := block_unique hx hw hv (hbw hyb) hyv
      subst W
      by_cases hab : A = B
      · rwa [hab]
      exact (hn A ha B hb hab V hv hav hbw).elim
    rwa [← Finset.Subset.antisymm hav hva]
  apply hne
  apply Finset.Subset.antisymm _ coincide
  intro A ha
  obtain ⟨V, hv, hav⟩ := rf A ha
  obtain ⟨x, hxA⟩ := hy.1 A ha
  have he := block_unique hy ha (coincide V hv) hxA (hav hxA)
  rwa [he]

private theorem path_exists {T : Finset Nat} {X Y : Finset (Finset Nat)}
    (hx : partition T X) (hy : partition T Y) (rf : ∀ B ∈ Y, ∃ A ∈ X, B ⊆ A) :
    ∃ n P A B, path Y X n P A B := by
  by_cases h : Y = X
  · exact ⟨0, fun _ => Y, fun _ => ∅, fun _ => ∅, rfl, h,
      fun i hi => (Nat.not_lt_zero _ hi).elim⟩
  obtain ⟨A, ha, B, hb, hab, V, hv, hav, hbv⟩ := merge_exists hx hy rf h
  let Z := merge Y A B
  have hz := merge_valid hy ha hb hab
  have rz : ∀ C ∈ Z, ∃ A ∈ X, C ⊆ A := by
    intro C hc
    rcases mem_merge.mp hc with rfl | ⟨hc, _, _⟩
    · exact ⟨V, hv, Finset.union_subset hav hbv⟩
    · exact rf C hc
  have dec : Z.card < Y.card := by
    have hb' : B ∈ Y.erase A := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have hu : A ∪ B ∉ (Y.erase A).erase B := fun hm =>
      union_not_in hy ha hb hab (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
    have h1 := Finset.card_erase_add_one ha
    have h2 := Finset.card_erase_add_one hb'
    change (insert (A ∪ B) ((Y.erase A).erase B)).card < Y.card
    rw [Finset.card_insert_of_notMem hu]
    omega
  obtain ⟨n, P, C, D, hzero, hend, hsteps⟩ := path_exists hx hz rz
  refine ⟨n + 1, (fun | 0 => Y | i + 1 => P i), (fun | 0 => A | i + 1 => C i),
    (fun | 0 => B | i + 1 => D i), rfl, hend, ?_⟩
  intro i hi
  cases i with
  | zero => exact ⟨ha, hb, hab, hzero⟩
  | succ i => exact hsteps i (Nat.lt_of_succ_lt_succ hi)
termination_by Y.card

open MackeyDiagrams

private noncomputable def inclusion : ∀ {A B : Subgroup U}, A ≤ B → MackeyDiagrams.ConjEmbedding A B :=
  fun h => ⟨Subgroup.inclusion h, ⟨1, fun x => by
    simp only [Subgroup.coe_inclusion, one_mul, inv_one, mul_one]⟩⟩
private noncomputable def curlPair : ∀ {A B : Subgroup U}, MackeyDiagrams.ConjEmbedding A B → Type :=
  fun a =>
    MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up a) ×
    MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.down a) (MackeyDiagrams.Word.down a)
private noncomputable def straightPair : ∀ {A B : Subgroup U} (a : MackeyDiagrams.ConjEmbedding A B), curlPair a :=
  fun a =>
    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up a)),
     MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down a)))
private noncomputable def indexedCurls :
    ∀ {A B C : Subgroup U} (a : MackeyDiagrams.ConjEmbedding B C)
      (d : MackeyDiagrams.ConjEmbedding A B),
      Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)) →
      Option (curlPair (MackeyDiagrams.ConjEmbedding.comp a d)) → curlPair a :=
  fun a d finite inner =>
    let openRight := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.upToUpDown a d finite)
    let closeRight := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.upDownToUp a d)
    let openLeft := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.downToUpDown a d finite)
    let closeLeft := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.upDownToDown a d)
    let rightUp := MackeyDiagrams.LabelledDrawing.vertical openRight
      (Option.elim inner closeRight (fun p =>
        MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal (Prod.fst p) (Prod.snd (straightPair d)))
          closeRight))
    let leftDown := MackeyDiagrams.LabelledDrawing.vertical openLeft
      (Option.elim inner closeLeft (fun p =>
        MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal (Prod.fst (straightPair d)) (Prod.snd p))
          closeLeft))
    (rightUp, leftDown)
private noncomputable def rightDownCurl :
    ∀ {A B C : Subgroup U} (a : MackeyDiagrams.ConjEmbedding B C)
      (d : MackeyDiagrams.ConjEmbedding A B),
      MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.down d) (MackeyDiagrams.Word.down d) :=
  fun a d =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.downToDownUp a d))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.downUpToDown a d))
private noncomputable def leftUpCurl :
    ∀ {A B C : Subgroup U} (a : MackeyDiagrams.ConjEmbedding B C)
      (d : MackeyDiagrams.ConjEmbedding A B),
      MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.up d) (MackeyDiagrams.Word.up d) :=
  fun a d =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.upToDownUp a d))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.downUpToUp a d))
private noncomputable def nestedCurls :
    ∀ (n : Nat) (L : Nat → Subgroup U)
      (h : ∀ i, i < n → L i ≤ L (i + 1)),
      (∀ i (hi : i < n), Subgroup.FiniteIndex
        (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (inclusion (h i hi))))) →
      ∀ t, t ≤ n → ∀ {D : Subgroup U} (a : MackeyDiagrams.ConjEmbedding (L t) D), curlPair a :=
  fun n L h finite =>
    Nat.rec
      (motive := fun t => t ≤ n → ∀ {D : Subgroup U}
        (a : MackeyDiagrams.ConjEmbedding (L t) D), curlPair a)
      (fun _ {_} a => straightPair a)
      (fun i prev hi {_} a =>
        let e := inclusion (h i hi)
        indexedCurls a e (finite i hi) (Option.some
          (prev (Nat.le_of_succ_le hi) (MackeyDiagrams.ConjEmbedding.comp a e))))
private noncomputable def atBoundary :
    ∀ {B H G : Subgroup U}, B = H → ∀ a : MackeyDiagrams.ConjEmbedding H G,
      (∀ b : MackeyDiagrams.ConjEmbedding B G, curlPair b) → curlPair a :=
  fun {B H G} h a f =>
    Eq.rec (motive := fun J _ => ∀ b : MackeyDiagrams.ConjEmbedding J G, curlPair b) f h a

private theorem range_inclusion {A B : Subgroup U} (h : A ≤ B) :
    (inclusion h).toHom.range = A.subgroupOf B := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hb
    exact ⟨⟨b.val, hb⟩, rfl⟩

private abbrev eval {K H : Subgroup U} {p q : Word K H}
    (d : LabelledDrawing Complex p q) :=
  d.interpret.eval

private abbrev curlEval {B G : Subgroup U} (a : ConjEmbedding B G)
    (p : curlPair a) (c : Complex) : Prop :=
  eval p.1 = (eval (straightPair a).1).scale c ∧
  eval p.2 = (eval (straightPair a).2).scale c

-- The checked Theorem 4.1 gives these four equalities for actual
-- conjugators. Representatives replace the symbolic embeddings by
-- equal underlying homomorphisms at the same boundaries.
private theorem direct_eval {K H G : Subgroup U} (a : ConjEmbedding H G)
    (d : ConjEmbedding K H) (f : Subgroup.FiniteIndex d.toHom.range) :
    curlEval a (indexedCurls a d f none) (d.toHom.range.index : Complex) ∧
    eval (rightDownCurl a d) = eval (straightPair d).2 ∧
    eval (leftUpCurl a d) = eval (straightPair d).1 := by
  obtain ⟨α, hα⟩ := a.hasRepresentative
  obtain ⟨δ, hδ⟩ := d.hasRepresentative
  let ha : ∀ x : H, α * (x : U) * α⁻¹ ∈ G := fun x => hα x ▸ (a.toHom x).property
  let hd : ∀ x : K, δ * (x : U) * δ⁻¹ ∈ H := fun x => hδ x ▸ (d.toHom x).property
  have ea : a = ConjEmbedding.ofConjugator α ha :=
    ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (hα x))
  have ed : d = ConjEmbedding.ofConjugator δ hd :=
    ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (hδ x))
  clear_value ha hd
  clear hα hδ
  rw [ea, ed] at *
  have r := ReidemeisterOne K H G δ α hd ha
  exact ⟨⟨r.1 f, r.2.2.2 f⟩, r.2.1, r.2.2.1⟩

private theorem straight_one {H G : Subgroup U} (a : ConjEmbedding H G) :
    curlEval a (straightPair a) 1 := by
  have scale_one {F B : Biset H G} (f : Biset.Hom Complex F B) : f.scale 1 = f := by
    apply Biset.Hom.ext
    apply LinearMap.ext
    intro x
    change (1 : Complex) • f.toLinearMap x = f.toLinearMap x
    exact one_smul _ _
  constructor
  · apply (scale_one _).symm
  · apply Biset.Hom.ext
    apply LinearMap.ext
    intro x
    symm
    exact one_smul _ _

private theorem hom_scale_mul {K H : Type*} [Group K] [Group H]
    {F B : Biset K H} (f : Biset.Hom Complex F B) (r s : Complex) :
    (f.scale r).scale s = f.scale (r * s) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change s • (r • f.toLinearMap x) = (r * s) • f.toLinearMap x
  rw [smul_smul, mul_comm s r]

-- The paper groups summands by two stages of coset representatives.
-- The checked direct curl and bilinearity on the balanced biset give
-- the same calculation at the two typed nested boundaries.
private theorem step_eval {K H G : Subgroup U} (a : ConjEmbedding H G)
    (d : ConjEmbedding K H) (f : Subgroup.FiniteIndex d.toHom.range)
    (p : curlPair (a.comp d)) (c : Complex) (hp : curlEval (a.comp d) p c) :
    curlEval a (indexedCurls a d f (some p)) (c * (d.toHom.range.index : Complex)) := by
  have dir := (direct_eval a d f).1
  obtain ⟨pu, pd⟩ := hp
  obtain ⟨du, dd⟩ := dir
  -- For the upward bend, the inner up map is the left tensor factor.
  -- For the downward bend, the inner down map is the right factor.
  constructor
  · simp only [indexedCurls, Option.elim, eval, LabelledDrawing.interpret, ScopedDiagram.eval,
      Prod.fst] at du ⊢
    rw [pu, Biset.Hom.horizontal_scale_left, Biset.Hom.vertical_scale_right,
      Biset.Hom.vertical_scale_left]
    simp only [eval, straightPair, LabelledDrawing.interpret, ScopedDiagram.eval, Diagram.eval,
      Word.basis, Biset.Hom.horizontal_id, Biset.Hom.id_vertical, du]
    rw [hom_scale_mul, mul_comm (d.toHom.range.index : Complex) c]
  · simp only [indexedCurls, Option.elim, eval, LabelledDrawing.interpret, ScopedDiagram.eval,
      Prod.snd] at dd ⊢
    rw [pd, Biset.Hom.horizontal_scale_right, Biset.Hom.vertical_scale_right,
      Biset.Hom.vertical_scale_left]
    simp only [eval, straightPair, LabelledDrawing.interpret, ScopedDiagram.eval, Diagram.eval,
      Word.basis, Biset.Hom.horizontal_id, Biset.Hom.id_vertical, dd]
    rw [hom_scale_mul, mul_comm (d.toHom.range.index : Complex) c]

private theorem nested_eval (n : Nat) (L : Nat → Subgroup U)
    (h : ∀ i, i < n → L i ≤ L (i + 1))
    (f : ∀ i (hi : i < n), Subgroup.FiniteIndex (inclusion (h i hi)).toHom.range) :
    ∀ t (ht : t ≤ n) {G : Subgroup U} (a : ConjEmbedding (L t) G),
      curlEval a (nestedCurls n L h f t ht a)
        ((∏ i ∈ Finset.range t, (L i).relIndex (L (i + 1)) : Nat) : Complex) := by
  intro t
  induction t with
  | zero =>
    intro ht G a
    simpa only [Finset.range_zero, Finset.prod_empty, Nat.cast_one] using straight_one a
  | succ t ih =>
    intro ht G a
    let e := inclusion (h t ht)
    have step := step_eval a e (f t ht) _ _
      (ih (Nat.le_of_succ_le ht) (a.comp e))
    change curlEval a (indexedCurls a e (f t ht) (some
      (nestedCurls n L h f t (Nat.le_of_succ_le ht) (a.comp e)))) _
    rwa [Finset.prod_range_succ, Nat.cast_mul, ← show e.toHom.range.index =
      (L t).relIndex (L (t + 1)) from congrArg Subgroup.index (range_inclusion (h t ht))]

private theorem boundary_eval {B H G : Subgroup U} (h : B = H) (a : ConjEmbedding H G)
    (p : ∀ b : ConjEmbedding B G, curlPair b) (c : Complex)
    (he : ∀ b, curlEval b (p b) c) : curlEval a (atBoundary h a p) c := by
  subst H
  exact he a

private theorem path_partition {T : Finset Nat} {X Y : Finset (Finset Nat)}
    {n : Nat} {P : Nat → Finset (Finset Nat)} {A B : Nat → Finset Nat}
    (hy : partition T Y) (hp : path Y X n P A B) :
    ∀ i, i ≤ n → partition T (P i) := by
  intro i
  induction i with
  | zero => simpa only [hp.1] using fun _ : 0 ≤ n => hy
  | succ i ih =>
    intro hi
    obtain ⟨ha, hb, hab, hm⟩ := hp.2.2 i hi
    rw [hm]
    exact merge_valid (ih (Nat.le_of_succ_le hi)) ha hb hab

private theorem path_index {T : Finset Nat} {X Y : Finset (Finset Nat)}
    {n : Nat} {P : Nat → Finset (Finset Nat)} {A B : Nat → Finset Nat}
    (hy : partition T Y) (hp : path Y X n P A B) :
    ∀ t, t ≤ n →
      (blockGroup Y).relIndex (blockGroup (P t)) =
        ∏ i ∈ Finset.range t, Nat.choose ((A i).card + (B i).card) (A i).card := by
  have incl : ∀ i, i < n → blockGroup (P i) ≤ blockGroup (P (i + 1)) := by
    intro i hi
    rw [(hp.2.2 i hi).2.2.2]
    exact merge_le _ _ _
  have start : ∀ i, i ≤ n → blockGroup Y ≤ blockGroup (P i) := by
    intro i
    induction i with
    | zero => simp only [hp.1, le_refl, implies_true]
    | succ i ih => exact fun hi => (ih (Nat.le_of_succ_le hi)).trans (incl i hi)
  intro t
  induction t with
  | zero => simp only [hp.1, Subgroup.relIndex_self, Finset.range_zero, Finset.prod_empty,
      implies_true]
  | succ t ih =>
    intro ht
    obtain ⟨ha, hb, hab, hm⟩ := hp.2.2 t ht
    have step : (blockGroup (P t)).relIndex (blockGroup (P (t + 1))) =
        Nat.choose ((A t).card + (B t).card) (A t).card := by
      rw [hm]
      exact merge_index (path_partition hy hp t (Nat.le_of_succ_le ht)) ha hb hab
    rw [Finset.prod_range_succ, ← step, ← ih (Nat.le_of_succ_le ht),
      Subgroup.relIndex_mul_relIndex (start t (Nat.le_of_succ_le ht)) (incl t ht)]

end BlockRefinementCurl
