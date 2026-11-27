import MackeyDiagrams
import Proofs.FiniteParabolicJoinBlocks

set_option maxHeartbeats 2000000

theorem FiniteParabolicJoinOfFamily : (
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
∀ {ι : Type*} [Finite ι] (A : ι → Subgroup (Equiv.Perm Nat)),
  (∀ i, parabolic (A i)) →
  let J := Subgroup.closure (Set.iUnion fun i => (A i : Set (Equiv.Perm Nat)))
  IsLeast {H : Subgroup (Equiv.Perm Nat) | parabolic H ∧ ∀ i, A i ≤ H} J ∧
    ∀ P : Subgroup (Equiv.Perm Nat), (∀ i, A i ≤ P) → J ≤ P
) :=
(by
  classical
  intro blockSym parabolicOn parabolic ι _ A hA J
  -- Xiao, § 7.5, applies Proposition 7.1 to a finite family.
  -- The endpoint is on p. 33 of the archived source/mackey-bimodules.pdf
  -- (SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and p. 35 of the revised published PDF, matching article-revision/mackey-bimodules.pdf
  -- (SHA-256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- The saved source note conflates the two copies. Both pages state this endpoint.
  -- Reindex any finite partition by Fin, including the empty partition.
  have ofFamily {κ : Type} [Finite κ] (X : Finset Nat) (blocks : κ → Finset Nat)
      (hne : ∀ i, (blocks i).Nonempty)
      (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
      (hc : ∀ x, x ∈ X ↔ ∃ i, x ∈ blocks i) :
      parabolicOn X (⨆ i, blockSym (blocks i)) := by
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
  have singletonSym (x : Nat) : blockSym {x} = ⊥ := by
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
  have pad {X Y : Finset Nat} {H : Subgroup (Equiv.Perm Nat)} (hXY : X ⊆ Y)
      (hH : parabolicOn X H) : parabolicOn Y H := by
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
  -- Proposition 7.1 uses swaps along overlapping blocks. The compiled supplier
  -- proves that step by walk induction, as in Alphabeta Math's adjacent
  -- transposition proof, steps 1.1 and 2.1, with overlaps in place of consecutive
  -- integers. It generates each component group by the finitary swap-closure
  -- criterion, in place of the cycle factorization in steps 1.1 and 2.1 of the
  -- general transposition proof. Here we verify the resulting partition.
  -- https://alphabetamath.cc/item/thm-adjacent-transpositions-generate-the-symmetric-group
  -- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
  have joinOn (X : Finset Nat) {κ ν : Type} [Fintype κ] [Fintype ν]
      (B : κ → Finset Nat) (C : ν → Finset Nat)
      (hneB : ∀ i, (B i).Nonempty) (hneC : ∀ j, (C j).Nonempty)
      (hdB : Pairwise (fun i j => Disjoint (B i) (B j)))
      (hdC : Pairwise (fun i j => Disjoint (C i) (C j)))
      (hcB : ∀ x, x ∈ X ↔ ∃ i, x ∈ B i)
      (hcC : ∀ x, x ∈ X ↔ ∃ j, x ∈ C j) :
      parabolicOn X ((⨆ i, blockSym (B i)) ⊔ (⨆ j, blockSym (C j))) := by
    let block : κ ⊕ ν → Finset Nat := Sum.elim B C
    let overlap : (κ ⊕ ν) → (κ ⊕ ν) → Prop := fun u v =>
      match u, v with
      | Sum.inl i, Sum.inr j => (B i ∩ C j).Nonempty
      | _, _ => False
    let graph := SimpleGraph.fromRel overlap
    let componentBlock (c : graph.ConnectedComponent) : Finset Nat :=
      let inComponent : Nat → Prop := fun x =>
        ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v
      @Finset.filter Nat inComponent (Classical.decPred inComponent) X
    have memComponent (c : graph.ConnectedComponent) (x : Nat) :
        x ∈ componentBlock c ↔ x ∈ X ∧ ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v :=
      @Finset.mem_filter Nat _ (Classical.decPred _) _ _
    have blockNonempty (v : κ ⊕ ν) : (block v).Nonempty := by
      cases v with
      | inl i => exact hneB i
      | inr j => exact hneC j
    have blockSubset (v : κ ⊕ ν) : block v ⊆ X := by
      intro x hx
      cases v with
      | inl i => exact (hcB x).mpr ⟨i, hx⟩
      | inr j => exact (hcC x).mpr ⟨j, hx⟩
    have sameBlock {μ : Type} {blocks : μ → Finset Nat}
        (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
        {i j : μ} {x : Nat} (hi : x ∈ blocks i) (hj : x ∈ blocks j) : i = j := by
      by_contra h
      exact Finset.disjoint_left.mp (hd h) hi hj
    have across {i j} {x : Nat} (hi : x ∈ B i) (hj : x ∈ C j) :
        graph.connectedComponentMk (Sum.inl i) = graph.connectedComponentMk (Sum.inr j) := by
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      exact (SimpleGraph.fromRel_adj overlap _ _).mpr
        ⟨Sum.inl_ne_inr, Or.inl ⟨x, Finset.mem_inter.mpr ⟨hi, hj⟩⟩⟩
    have sameComponent {u v : κ ⊕ ν} {x : Nat} (hu : x ∈ block u) (hv : x ∈ block v) :
        graph.connectedComponentMk u = graph.connectedComponentMk v := by
      cases u <;> cases v
      · rw [sameBlock hdB hu hv]
      · exact across hu hv
      · exact (across hv hu).symm
      · rw [sameBlock hdC hu hv]
    have joinFormula :
        ((⨆ i, blockSym (B i)) ⊔ (⨆ j, blockSym (C j))) = ⨆ c, blockSym (componentBlock c) :=
      FiniteParabolicJoinBlocks X B C hneB hneC hdB hdC hcB hcC
    rw [joinFormula]
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
      exact h (huc.symm.trans ((sameComponent hu hv).trans hvd))
    · intro x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := (hcB x).mp hx
        exact ⟨graph.connectedComponentMk (Sum.inl i), (memComponent _ x).mpr ⟨hx, Sum.inl i, rfl, hi⟩⟩
      · rintro ⟨c, hx⟩
        exact ((memComponent c x).mp hx).1
  have parabolicSup {H K : Subgroup (Equiv.Perm Nat)} (hH : parabolic H) (hK : parabolic K) :
      parabolic (H ⊔ K) := by
    obtain ⟨X, hX⟩ := hH
    obtain ⟨Y, hY⟩ := hK
    obtain ⟨n, B, hneB, hdB, hcB, rfl⟩ := pad (Y := X ∪ Y) Finset.subset_union_left hX
    obtain ⟨m, C, hneC, hdC, hcC, rfl⟩ := pad (Y := X ∪ Y) Finset.subset_union_right hY
    exact ⟨X ∪ Y, joinOn _ B C hneB hneC hdB hdC hcB hcC⟩
  have parabolicBot : parabolic ⊥ := by
    let blocks : Fin 0 → Finset Nat := Fin.elim0
    have h := ofFamily ∅ blocks (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (by simp)
    exact ⟨∅, by simpa only [iSup_of_empty] using h⟩
  -- Iterate the binary formula starting at the trivial subgroup.
  have parabolicFinset (s : Finset ι) : parabolic (s.sup A) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using parabolicBot
    | insert i s _ ih =>
      rw [Finset.sup_insert]
      exact parabolicSup (hA i) ih
  let _ : Fintype ι := Fintype.ofFinite ι
  -- The generated-subgroup minimality used in Alphabeta Math's transposition
  -- proof, step 3.1, applies to this union as a subset of the ambient permutation
  -- group. Union membership supplies the generators and checks their containment.
  have member_le (i : ι) : A i ≤ J := fun g hg =>
    Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, hg⟩)
  have least (P : Subgroup (Equiv.Perm Nat)) (hP : ∀ i, A i ≤ P) : J ≤ P := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact hP i hi
  have closure_eq : J = ⨆ i, A i :=
    le_antisymm (least _ (le_iSup A)) (iSup_le member_le)
  have sup_univ : (Finset.univ : Finset ι).sup A = ⨆ i, A i :=
    le_antisymm (Finset.sup_le_iff.mpr (fun i _ => le_iSup A i))
      (iSup_le fun i => Finset.le_sup (f := A) (Finset.mem_univ i))
  have parabolicJ : parabolic J := by
    rw [closure_eq, ← sup_univ]
    exact parabolicFinset _
  exact ⟨⟨⟨parabolicJ, member_le⟩, fun P hP => least P hP.2⟩, least⟩)
