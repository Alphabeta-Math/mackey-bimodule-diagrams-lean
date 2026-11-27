import MackeyDiagrams
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks

theorem FiniteParabolicClosure : (
  let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
    fun S => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ S))
  let parabolicOn : Finset Nat → Subgroup (Equiv.Perm Nat) → Prop :=
    fun X H =>
      ∃ (n : Nat) (blocks : Fin n → Finset Nat),
        (∀ i, Finset.Nonempty (blocks i)) ∧
        Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
        (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧
        H = iSup (fun i => blockSym (blocks i))
  let parabolic : Subgroup (Equiv.Perm Nat) → Prop :=
    fun H => ∃ X, parabolicOn X H
  (∀ (H : Subgroup (Equiv.Perm Nat)), parabolic H →
    ∀ α : ↥(Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}),
      parabolic (Subgroup.map
        (MulEquiv.toMonoidHom (MulAut.conj (α : Equiv.Perm Nat))) H)) ∧
  (∀ (X : Finset Nat) (H K : Subgroup (Equiv.Perm Nat)),
    parabolicOn X H → parabolicOn X K →
      parabolicOn X (H ⊓ K) ∧ parabolicOn X (H ⊔ K))
) :=
(by
  classical
  intro blockSym parabolicOn parabolic
  -- The three block identities are the registered suppliers for Xiao, Proposition 7.1.
  -- Reindexing by Fin supplies the index type required by parabolicOn, including
  -- Fin 0 for the empty partition.
  have ofBlocks {ι : Type} [Finite ι] (X : Finset Nat) (D : ι → Finset Nat)
      (nonempty : ∀ i, (D i).Nonempty)
      (disjoint : Pairwise (fun i j => Disjoint (D i) (D j)))
      (cover : ∀ x, x ∈ X ↔ ∃ i, x ∈ D i)
      (L : Subgroup (Equiv.Perm Nat)) (hL : L = ⨆ i, blockSym (D i)) :
      parabolicOn X L := by
    let _ := Fintype.ofFinite ι
    let e := (Fintype.equivFin ι).symm
    refine ⟨Fintype.card ι, fun i => D (e i), fun i => nonempty (e i), ?_, ?_, ?_⟩
    · intro i j hij
      exact disjoint (fun h => hij (e.injective h))
    · intro x
      rw [cover x]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨e i, hi⟩
    · exact hL.trans (e.iSup_comp (g := fun i => blockSym (D i))).symm
  constructor
  · intro H hH α
    obtain ⟨X, n, A, nonemptyA, disjointA, coverA, hA⟩ := hH
    let σ : Equiv.Perm Nat := α
    let D : Fin n → Finset Nat := fun i => (A i).image σ
    refine ⟨X.image σ, ofBlocks _ D ?_ ?_ ?_ _ ?_⟩
    · intro i
      obtain ⟨x, hx⟩ := nonemptyA i
      exact ⟨σ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro y hyi hyj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyi
      obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hyj
      exact Finset.disjoint_left.mp (disjointA hij) hx (σ.injective heq ▸ hz)
    · intro y
      constructor
      · rintro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨i, hi⟩ := (coverA x).mp hx
        exact ⟨i, Finset.mem_image.mpr ⟨x, hi, rfl⟩⟩
      · rintro ⟨i, hi⟩
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_image.mpr ⟨x, (coverA x).mpr ⟨i, hx⟩, rfl⟩
    · rw [hA]
      exact FiniteParabolicConjugateBlocks A nonemptyA disjointA α
  · intro X H K hH hK
    obtain ⟨n, A, nonemptyA, disjointA, coverA, hA⟩ := hH
    obtain ⟨m, B, nonemptyB, disjointB, coverB, hB⟩ := hK
    have intersection := FiniteParabolicIntersectionBlocks X A B
      nonemptyA nonemptyB disjointA disjointB coverA coverB
    have join := FiniteParabolicJoinBlocks X A B
      nonemptyA nonemptyB disjointA disjointB coverA coverB
    constructor
    · let cell : Fin n × Fin m → Finset Nat := fun p => A p.1 ∩ B p.2
      let D : {p // (cell p).Nonempty} → Finset Nat := fun p => cell p.val
      -- The intersection formula retains empty cells. The partition omits them
      -- because every permutation extended from an empty cell fixes all of Nat.
      refine ofBlocks X D (fun p => p.property) ?_ ?_ (H ⊓ K) ?_
      · intro p q hpq
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have hx' := Finset.mem_inter.mp (show x ∈ cell p.val from hx)
        have hy' := Finset.mem_inter.mp (show x ∈ cell q.val from hy)
        by_cases h : p.val.1 = q.val.1
        · have h' : p.val.2 ≠ q.val.2 :=
            fun h₂ => hpq (Subtype.ext (Prod.ext h h₂))
          exact Finset.disjoint_left.mp (disjointB h') hx'.2 hy'.2
        · exact Finset.disjoint_left.mp (disjointA h) hx'.1 hy'.1
      · intro x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := (coverA x).mp hx
          obtain ⟨j, hj⟩ := (coverB x).mp hx
          have hcell : x ∈ cell (i, j) := Finset.mem_inter.mpr ⟨hi, hj⟩
          exact ⟨⟨(i, j), ⟨x, hcell⟩⟩, hcell⟩
        · rintro ⟨p, hp⟩
          exact (coverA x).mpr ⟨p.val.1,
            (Finset.mem_inter.mp (show x ∈ cell p.val from hp)).1⟩
      · rw [hA, hB]
        change (⨆ i, blockSym (A i)) ⊓ (⨆ j, blockSym (B j)) =
          ⨆ p, blockSym (D p)
        refine intersection.trans ?_
        change (⨆ i, ⨆ j, blockSym (cell (i, j))) = ⨆ p, blockSym (D p)
        rw [← iSup_prod (f := fun p => blockSym (cell p))]
        apply le_antisymm
        · refine iSup_le fun p => ?_
          by_cases hp : (cell p).Nonempty
          · exact le_iSup (fun q => blockSym (D q)) ⟨p, hp⟩
          · rintro _ ⟨τ, rfl⟩
            have hτ : Equiv.Perm.ofSubtype τ = (1 : Equiv.Perm Nat) := by
              apply Equiv.ext
              intro x
              exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun hx => hp ⟨x, hx⟩)
            rw [hτ]
            exact Subgroup.one_mem _
        · exact iSup_comp_le (fun p => blockSym (cell p)) Subtype.val
    · let block : Sum (Fin n) (Fin m) → Finset Nat := Sum.elim A B
      let r : Sum (Fin n) (Fin m) → Sum (Fin n) (Fin m) → Prop := fun u v =>
        match u, v with
        | Sum.inl i, Sum.inr j => (A i ∩ B j).Nonempty
        | _, _ => False
      let graph := SimpleGraph.fromRel r
      let belongs (c : graph.ConnectedComponent) (x : Nat) : Prop :=
        ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v
      let D (c : graph.ConnectedComponent) : Finset Nat :=
        @Finset.filter Nat (belongs c) (Classical.decPred (belongs c)) X
      have mem_D (c : graph.ConnectedComponent) (x : Nat) :
          x ∈ D c ↔ x ∈ X ∧ belongs c x :=
        @Finset.mem_filter Nat (belongs c) (Classical.decPred (belongs c)) X x
      have block_mem_carrier (v : Sum (Fin n) (Fin m)) {x : Nat}
          (hx : x ∈ block v) : x ∈ X := by
        cases v with
        | inl i => exact (coverA x).mpr ⟨i, hx⟩
        | inr j => exact (coverB x).mpr ⟨j, hx⟩
      have component_eq_of_mem {u v : Sum (Fin n) (Fin m)} {x : Nat}
          (hu : x ∈ block u) (hv : x ∈ block v) :
          graph.connectedComponentMk u = graph.connectedComponentMk v := by
        cases u with
        | inl i =>
          cases v with
          | inl j =>
            have h : i = j := by
              by_contra h
              exact Finset.disjoint_left.mp (disjointA h) hu hv
            subst j
            rfl
          | inr j =>
            apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            exact (SimpleGraph.fromRel_adj r _ _).mpr
              ⟨by simp, Or.inl ⟨x, Finset.mem_inter.mpr ⟨hu, hv⟩⟩⟩
        | inr i =>
          cases v with
          | inl j =>
            apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            exact (SimpleGraph.fromRel_adj r _ _).mpr
              ⟨by simp, Or.inr ⟨x, Finset.mem_inter.mpr ⟨hv, hu⟩⟩⟩
          | inr j =>
            have h : i = j := by
              by_contra h
              exact Finset.disjoint_left.mp (disjointB h) hu hv
            subst j
            rfl
      -- Alphabeta Math, “Every finite permutation is a product of transpositions,”
      -- steps 1.1 and 2.1 factor cycles and assemble their transpositions. The
      -- registered join theorem supplies the resulting subgroup equality via
      -- swap closure on finite blocks of Nat. Here only the component partition
      -- remains to be proved, using disjointness and nonempty original blocks.
      refine ofBlocks X D ?_ ?_ ?_ (H ⊔ K) ?_
      · intro c
        induction c using SimpleGraph.ConnectedComponent.ind with
        | h v =>
          have hv : (block v).Nonempty := by
            cases v with
            | inl i => exact nonemptyA i
            | inr j => exact nonemptyB j
          obtain ⟨x, hx⟩ := hv
          exact ⟨x, (mem_D _ x).mpr ⟨block_mem_carrier v hx, v, rfl, hx⟩⟩
      · intro c d hcd
        apply Finset.disjoint_left.mpr
        intro x hxc hxd
        obtain ⟨_, u, hu, hxu⟩ := (mem_D c x).mp hxc
        obtain ⟨_, v, hv, hxv⟩ := (mem_D d x).mp hxd
        exact hcd (hu.symm.trans ((component_eq_of_mem hxu hxv).trans hv))
      · intro x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := (coverA x).mp hx
          exact ⟨graph.connectedComponentMk (Sum.inl i),
            (mem_D _ x).mpr ⟨hx, Sum.inl i, rfl, hi⟩⟩
        · rintro ⟨c, hc⟩
          exact ((mem_D c x).mp hc).1
      · rw [hA, hB]
        dsimp only at join
        set_option pp.all true in
          exact join)

