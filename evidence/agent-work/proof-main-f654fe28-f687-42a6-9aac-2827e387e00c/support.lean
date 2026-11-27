private abbrev extremalBlockSym (S : Finset Nat) : Subgroup (Equiv.Perm Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ S))

private abbrev extremalParabolicOn (X : Finset Nat) (H : Subgroup (Equiv.Perm Nat)) : Prop :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧
    H = iSup (fun i => extremalBlockSym (blocks i))

private theorem extremalOfFamily (X : Finset Nat) {ι : Type} [Finite ι] (A : ι → Finset Nat)
    (nonempty : ∀ i, (A i).Nonempty)
    (disjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (cover : ∀ x, x ∈ X ↔ ∃ i, x ∈ A i) :
    extremalParabolicOn X (⨆ i, extremalBlockSym (A i)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, A ∘ e, fun i => nonempty (e i), ?_, ?_, ?_⟩
  · intro i j hij
    exact disjoint (fun h => hij (e.injective h))
  · intro x
    rw [cover x]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa only [Function.comp_apply, e.apply_symm_apply] using hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, hi⟩
  · exact (e.iSup_comp (g := fun i => extremalBlockSym (A i))).symm

private theorem extremalFixesOutside {S : Finset Nat} {f : Equiv.Perm Nat}
    (hf : f ∈ extremalBlockSym S) {x : Nat} (hx : x ∉ S) : f x = x := by
  classical
  obtain ⟨g, rfl⟩ := hf
  exact Equiv.Perm.ofSubtype_apply_of_not_mem g hx

private theorem extremalPreservesBlock {S : Finset Nat} {f : Equiv.Perm Nat}
    (hf : f ∈ extremalBlockSym S) {x : Nat} (hx : x ∈ S) : f x ∈ S := by
  classical
  obtain ⟨g, rfl⟩ := hf
  exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem g x).mpr hx

private theorem extremalBlockMono {S T : Finset Nat} (hST : S ⊆ T) : extremalBlockSym S ≤ extremalBlockSym T := by
  classical
  intro f hf
  have fixed (x : Nat) (hx : x ∉ T) : f x = x :=
    extremalFixesOutside hf (fun hs => hx (hST hs))
  have movedIn (x : Nat) (hx : f x ≠ x) : x ∈ T := by
    by_contra hout
    exact hx (fixed x hout)
  have invariant (x : Nat) : f x ∈ T ↔ x ∈ T := by
    by_cases h : f x = x
    · rw [h]
    · exact iff_of_true (by
        apply movedIn
        exact fun he => h (f.injective he)) (movedIn x h)
  exact ⟨f.subtypePerm invariant, Equiv.Perm.ofSubtype_subtypePerm invariant movedIn⟩

private theorem extremalSwapInBlock {S : Finset Nat} {a b : Nat} (ha : a ∈ S) (hb : b ∈ S) :
    Equiv.swap a b ∈ extremalBlockSym S := by
  classical
  exact ⟨Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩,
    Equiv.Perm.ofSubtype_swap_eq (⟨a, ha⟩ : {x // x ∈ S}) ⟨b, hb⟩⟩

-- Alphabeta Math, steps 1.1, 2.1 and 3.1, show that transpositions generate
-- a finite symmetric group by factoring cycles and concatenating the factors.
-- Here the ambient carrier is Nat. Use the checked finitary closure criterion
-- with finite support and a single internal swap witnessing each moved image.
-- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
private theorem extremalMemOfMoves {H : Subgroup (Equiv.Perm Nat)} {f : Equiv.Perm Nat}
    (hf : (MulAction.fixedBy Nat f)ᶜ.Finite)
    (hs : ∀ x, f x ≠ x → Equiv.swap x (f x) ∈ H) : f ∈ H := by
  classical
  let T : Set (Equiv.Perm Nat) := {g | g ∈ H ∧ g.IsSwap}
  have hT : ∀ g ∈ T, g.IsSwap := fun _ h => h.2
  have inClosure : f ∈ Subgroup.closure T := by
    apply (mem_closure_isSwap hT).mpr
    refine ⟨hf, fun x => ?_⟩
    by_cases h : f x = x
    · rw [h]
      exact MulAction.mem_orbit_self x
    · have hswap : Equiv.swap x (f x) ∈ T := ⟨hs x h, ⟨x, f x, Ne.symm h, rfl⟩⟩
      exact ⟨⟨Equiv.swap x (f x), Subgroup.subset_closure hswap⟩, Equiv.swap_apply_left _ _⟩
  exact ((Subgroup.closure_le H).mpr (show T ⊆ H from fun _ h => h.1)) inClosure

private theorem extremalBlockGenerated (S : Finset Nat) :
    extremalBlockSym S = Subgroup.closure {f : Equiv.Perm Nat |
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f = Equiv.swap a b} := by
  classical
  apply le_antisymm
  · intro f hf
    have supportIn : (MulAction.fixedBy Nat f)ᶜ ⊆ (S : Set Nat) := by
      intro x hx
      by_contra hout
      exact hx (extremalFixesOutside hf hout)
    apply extremalMemOfMoves ((S.finite_toSet).subset supportIn)
    intro x hx
    have hxs := supportIn (show x ∈ (MulAction.fixedBy Nat f)ᶜ from hx)
    exact Subgroup.subset_closure ⟨x, hxs, f x, extremalPreservesBlock hf hxs, hx.symm, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, ha, b, hb, _, rfl⟩
    exact extremalSwapInBlock ha hb

private theorem extremalSingleton (a : Nat) : extremalBlockSym {a} = ⊥ := by
  classical
  rw [extremalBlockGenerated, ← Subgroup.closure_empty]
  congr 1
  ext f
  simp

-- A transposition generates its two-point block group. Singleton padding
-- puts all these two-point groups on the common carrier required by Prop. 7.1.
private theorem extremalPairGenerated {a b : Nat} (hab : a ≠ b) :
    extremalBlockSym {a, b} = Subgroup.closure {Equiv.swap a b} := by
  classical
  rw [extremalBlockGenerated]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨u, hu, v, hv, huv, rfl⟩
    have hu' : u = a ∨ u = b := by simpa using hu
    have hv' : v = a ∨ v = b := by simpa using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact (huv rfl).elim
    · exact Subgroup.subset_closure (Set.mem_singleton _)
    · rw [Equiv.swap_comm]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    · exact (huv rfl).elim
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact Subgroup.subset_closure ⟨a, by simp, b, by simp, hab, rfl⟩

private theorem extremalTrivialOn (X : Finset Nat) : extremalParabolicOn X ⊥ := by
  classical
  let A : ↥X → Finset Nat := fun i => {i.val}
  have hSup : (⨆ i, extremalBlockSym (A i)) = ⊥ := by
    refine le_antisymm (iSup_le fun i => ?_) bot_le
    exact (extremalSingleton i.val).le
  rw [← hSup]
  refine extremalOfFamily X A (fun i => ⟨i.val, by simp [A]⟩) ?_ ?_
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' : x = i.val := Finset.mem_singleton.mp hx
    have hy' : x = j.val := Finset.mem_singleton.mp hy
    exact hij (Subtype.ext (hx'.symm.trans hy'))
  · intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, by simp [A]⟩
    · rintro ⟨i, hi⟩
      rw [Finset.mem_singleton.mp hi]
      exact i.property

private theorem extremalPaddedBlock (X : Finset Nat) {S : Finset Nat} (hS : S ⊆ X) (hne : S.Nonempty) :
    extremalParabolicOn X (extremalBlockSym S) := by
  classical
  let A : Option ↥(X \ S) → Finset Nat := fun i =>
    match i with
    | none => S
    | some x => {x.val}
  have hSup : (⨆ i, extremalBlockSym (A i)) = extremalBlockSym S := by
    apply le_antisymm
    · apply iSup_le
      intro i
      cases i with
      | none => exact le_rfl
      | some x => exact (extremalSingleton x.val).le.trans bot_le
    · exact le_iSup (fun i => extremalBlockSym (A i)) none
  rw [← hSup]
  refine extremalOfFamily X A ?_ ?_ ?_
  · intro i
    cases i with
    | none => exact hne
    | some x => exact ⟨x.val, by simp [A]⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    cases i <;> cases j
    next => exact hij rfl
    next v =>
      have hxv : x = v.val := Finset.mem_singleton.mp hy
      exact (Finset.mem_sdiff.mp v.property).2 (hxv ▸ hx)
    next u =>
      have hxu : x = u.val := Finset.mem_singleton.mp hx
      exact (Finset.mem_sdiff.mp u.property).2 (hxu ▸ hy)
    next u v =>
      have hxu : x = u.val := Finset.mem_singleton.mp hx
      have hxv : x = v.val := Finset.mem_singleton.mp hy
      exact hij (congrArg some (Subtype.ext (hxu.symm.trans hxv)))
  · intro x
    constructor
    · intro hx
      by_cases hs : x ∈ S
      · exact ⟨none, hs⟩
      · exact ⟨some ⟨x, Finset.mem_sdiff.mpr ⟨hx, hs⟩⟩, by simp [A]⟩
    · rintro ⟨i, hi⟩
      cases i with
      | none => exact hS hi
      | some v =>
        rw [Finset.mem_singleton.mp hi]
        exact (Finset.mem_sdiff.mp v.property).1

private theorem extremalBlockAction {ι : Type} {A : ι → Finset Nat}
    (disjoint : Pairwise (fun i j => Disjoint (A i) (A j))) {f : Equiv.Perm Nat} (hf : f ∈ ⨆ i, extremalBlockSym (A i)) :
    (∀ i x, x ∈ A i → f x ∈ A i) ∧
    (∀ x, (∀ i, x ∉ A i) → f x = x) := by
  classical
  refine Subgroup.iSup_induction (fun i => extremalBlockSym (A i)) hf
    (C := fun f => (∀ i x, x ∈ A i → f x ∈ A i) ∧
      (∀ x, (∀ i, x ∉ A i) → f x = x)) ?_ ?_ ?_
  · intro j f hj
    refine ⟨?_, fun x hx => extremalFixesOutside hj (hx j)⟩
    intro i x hx
    by_cases h : i = j
    · subst j
      exact extremalPreservesBlock hj hx
    · rw [extremalFixesOutside hj (fun hy => Finset.disjoint_left.mp (disjoint h) hx hy)]
      exact hx
  · exact ⟨fun _ _ hx => hx, fun _ _ => rfl⟩
  · intro f g hf hg
    exact ⟨fun i x hx => hf.1 i (g x) (hg.1 i x hx), fun x hx =>
      show f (g x) = x from (congrArg f (hg.2 x hx)).trans (hf.2 x hx)⟩
