import MackeyDiagrams
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks

set_option maxHeartbeats 2000000

theorem FiniteParabolicClosure : ((
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
)) :=
(by
  classical
  intro blockSym parabolicOn parabolic
  -- Xiao, Proposition 7.1 (project PDF p. 28, published PDF p. 30).
  -- Reindex the finite block families by the Fin indices in the statement.
  -- This also works when the index type is empty.
  have ofFamily {ι : Type} [Finite ι] (X : Finset Nat)
      (blocks : ι → Finset Nat)
      (nonempty : ∀ i, (blocks i).Nonempty)
      (disjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
      (cover : ∀ x, x ∈ X ↔ ∃ i, x ∈ blocks i) :
      parabolicOn X (iSup (fun i => blockSym (blocks i))) := by
    let _ : Fintype ι := Fintype.ofFinite ι
    let e := (Fintype.equivFin ι).symm
    refine ⟨Fintype.card ι, blocks ∘ e, fun i => nonempty (e i), ?_, ?_, ?_⟩
    · intro i j hij
      exact disjoint (fun he => hij (e.injective he))
    · intro x
      rw [cover x]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨e.symm i, by simpa only [Function.comp_apply, e.apply_symm_apply] using hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨e i, hi⟩
    · exact (e.iSup_comp (g := fun i => blockSym (blocks i))).symm
  constructor
  · -- Proposition 7.1, conjugation. Use FiniteParabolicConjugateBlocks on
    -- the supplied finitary conjugator, and transport the common block witnesses.
    rintro H ⟨X, n, A, hA, dA, coverA, rfl⟩ α
    let σ : Equiv.Perm Nat := α
    rw [FiniteParabolicConjugateBlocks A hA dA α]
    refine ⟨X.image σ, n, fun i => (A i).image σ, ?_, ?_, ?_, rfl⟩
    · intro i
      obtain ⟨x, hx⟩ := hA i
      exact ⟨σ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hxi
      obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hxj
      have huv := σ.injective (hux.trans hvx.symm)
      exact Finset.disjoint_left.mp (dA hij) hu (huv ▸ hv)
    · intro x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨i, hi⟩ := (coverA y).mp hy
        exact ⟨i, Finset.mem_image.mpr ⟨y, hi, rfl⟩⟩
      · rintro ⟨i, hi⟩
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_image.mpr ⟨y, (coverA y).mpr ⟨i, hy⟩, rfl⟩
  · rintro X H K ⟨n, A, hA, dA, coverA, rfl⟩ ⟨m, B, hB, dB, coverB, rfl⟩
    have sameBlock {ι : Type} {blocks : ι → Finset Nat}
        (disjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
        {i j} {x : Nat} (hi : x ∈ blocks i) (hj : x ∈ blocks j) : i = j := by
      by_contra h
      exact Finset.disjoint_left.mp (disjoint h) hi hj
    constructor
    · -- Proposition 7.1, intersection. The registered formula includes all
      -- cells. The partition omits empty cells, whose extensions fix every point.
      rw [FiniteParabolicIntersectionBlocks X A B hA hB dA dB coverA coverB]
      let Cell := {ij : Fin n × Fin m // (A ij.1 ∩ B ij.2).Nonempty}
      let cell : Cell → Finset Nat := fun ij => A ij.val.1 ∩ B ij.val.2
      have omitEmpty :
          (⨆ i, ⨆ j, blockSym (A i ∩ B j)) = ⨆ ij, blockSym (cell ij) := by
        apply le_antisymm
        · refine iSup_le fun i => iSup_le fun j => ?_
          by_cases h : (A i ∩ B j).Nonempty
          · exact le_iSup (fun ij => blockSym (cell ij)) (⟨(i, j), h⟩ : Cell)
          · rintro f ⟨g, rfl⟩
            have eqOne : Equiv.Perm.ofSubtype g = (1 : Equiv.Perm Nat) := by
              apply Equiv.ext
              intro x
              exact Equiv.Perm.ofSubtype_apply_of_not_mem g (fun hx => h ⟨x, hx⟩)
            rw [eqOne]
            exact Subgroup.one_mem _
        · refine iSup_le fun ij => ?_
          exact (le_iSup (fun j => blockSym (A ij.val.1 ∩ B j)) ij.val.2).trans
            (le_iSup (fun i => ⨆ j, blockSym (A i ∩ B j)) ij.val.1)
      rw [omitEmpty]
      refine ofFamily X cell (fun ij => ij.property) ?_ ?_
      · intro ij kl h
        apply Finset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
        obtain ⟨hk, hl⟩ := Finset.mem_inter.mp hy
        exact h (Subtype.ext (Prod.ext (sameBlock dA hi hk) (sameBlock dB hj hl)))
      · intro x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := (coverA x).mp hx
          obtain ⟨j, hj⟩ := (coverB x).mp hx
          have hxCell := Finset.mem_inter.mpr ⟨hi, hj⟩
          exact ⟨⟨(i, j), ⟨x, hxCell⟩⟩, hxCell⟩
        · rintro ⟨ij, hx⟩
          exact (coverA x).mpr ⟨ij.val.1, (Finset.mem_inter.mp hx).1⟩
    · -- Proposition 7.1, generated subgroup. FiniteParabolicJoinBlocks uses
      -- walk induction to compose swaps along overlaps, as in steps 1.1 and 2.1 of
      -- https://alphabetamath.cc/item/thm-adjacent-transpositions-generate-the-symmetric-group
      -- It uses a finitary swap-closure criterion in place of the cycle factorization
      -- in steps 1.1 and 2.1 of
      -- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
      -- The disjoint nonempty covers supply the formula's partition hypotheses.
      -- Keep the index types abstract to match its overlap relation before
      -- specializing to Fin. Recover the partition using its exact filter on X.
      have onJoin {ι κ : Type} [Finite ι] [Finite κ] (A : ι → Finset Nat)
          (B : κ → Finset Nat) (hA : ∀ i, (A i).Nonempty) (hB : ∀ j, (B j).Nonempty)
          (dA : Pairwise (fun i j => Disjoint (A i) (A j)))
          (dB : Pairwise (fun i j => Disjoint (B i) (B j)))
          (coverA : ∀ x, x ∈ X ↔ ∃ i, x ∈ A i)
          (coverB : ∀ x, x ∈ X ↔ ∃ j, x ∈ B j) :
          parabolicOn X ((⨆ i, blockSym (A i)) ⊔ (⨆ j, blockSym (B j))) := by
        let block : ι ⊕ κ → Finset Nat := Sum.elim A B
        let overlap : (ι ⊕ κ) → (ι ⊕ κ) → Prop := fun u v =>
          match u, v with
          | Sum.inl i, Sum.inr j => (A i ∩ B j).Nonempty
          | _, _ => False
        let graph := SimpleGraph.fromRel overlap
        let componentBlock : graph.ConnectedComponent → Finset Nat := fun c =>
          let inComponent : Nat → Prop := fun x =>
            ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v
          @Finset.filter Nat inComponent (Classical.decPred inComponent) X
        have memComponent (c : graph.ConnectedComponent) (x : Nat) :
            x ∈ componentBlock c ↔ x ∈ X ∧
              ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v :=
          @Finset.mem_filter Nat _ (Classical.decPred _) _ _
        have blockNonempty (v : ι ⊕ κ) : (block v).Nonempty := by
          cases v with
          | inl i => exact hA i
          | inr j => exact hB j
        have blockSubset (v : ι ⊕ κ) : block v ⊆ X := by
          intro x hx
          cases v with
          | inl i => exact (coverA x).mpr ⟨i, hx⟩
          | inr j => exact (coverB x).mpr ⟨j, hx⟩
        have overlap_component {u v : ι ⊕ κ} {x : Nat}
            (hu : x ∈ block u) (hv : x ∈ block v) :
            graph.connectedComponentMk u = graph.connectedComponentMk v := by
          cases u with
          | inl i =>
            cases v with
            | inl j => rw [sameBlock dA hu hv]
            | inr j =>
              apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              apply (SimpleGraph.fromRel_adj overlap _ _).mpr
              exact ⟨Sum.inl_ne_inr, Or.inl ⟨x, Finset.mem_inter.mpr ⟨hu, hv⟩⟩⟩
          | inr j =>
            cases v with
            | inl i =>
              apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              apply (SimpleGraph.fromRel_adj overlap _ _).mpr
              exact ⟨Sum.inr_ne_inl, Or.inr ⟨x, Finset.mem_inter.mpr ⟨hv, hu⟩⟩⟩
            | inr k => rw [sameBlock dB hu hv]
        have joinFormula :
            ((⨆ i, blockSym (A i)) ⊔ (⨆ j, blockSym (B j))) =
              ⨆ c, blockSym (componentBlock c) :=
          FiniteParabolicJoinBlocks X A B hA hB dA dB coverA coverB
        rw [joinFormula]
        let _ : Finite (ι ⊕ κ) := by
          let _ : Fintype ι := Fintype.ofFinite ι
          let _ : Fintype κ := Fintype.ofFinite κ
          exact Finite.of_fintype _
        refine ofFamily X componentBlock ?_ ?_ ?_
        · intro c
          induction c using SimpleGraph.ConnectedComponent.ind with
          | h v =>
            obtain ⟨x, hx⟩ := blockNonempty v
            exact ⟨x, (memComponent _ x).mpr ⟨blockSubset v hx, v, rfl, hx⟩⟩
        · intro c d h
          apply Finset.disjoint_left.mpr
          intro x hx hy
          obtain ⟨_, u, huc, hu⟩ := (memComponent c x).mp hx
          obtain ⟨_, v, hvd, hv⟩ := (memComponent d x).mp hy
          exact h (huc.symm.trans ((overlap_component hu hv).trans hvd))
        · intro x
          constructor
          · intro hx
            obtain ⟨i, hi⟩ := (coverA x).mp hx
            exact ⟨graph.connectedComponentMk (Sum.inl i),
              (memComponent _ x).mpr ⟨hx, Sum.inl i, rfl, hi⟩⟩
          · rintro ⟨c, hx⟩
            exact ((memComponent c x).mp hx).1
      exact onJoin A B hA hB dA dB coverA coverB)
