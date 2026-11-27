import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Perm.ClosureSwap
import MackeyDiagrams

set_option maxHeartbeats 2000000

theorem FiniteParabolicJoinBlocks : (∀ {ι : Type*} {κ : Type*} [Finite ι] [Finite κ] (X : Finset Nat)
    (A : ι → Finset Nat) (B : κ → Finset Nat),
  (∀ i, Finset.Nonempty (A i)) →
  (∀ j, Finset.Nonempty (B j)) →
  Pairwise (fun i i' => Disjoint (A i) (A i')) →
  Pairwise (fun j j' => Disjoint (B j) (B j')) →
  (∀ n : Nat, n ∈ X ↔ ∃ i, n ∈ A i) →
  (∀ n : Nat, n ∈ X ↔ ∃ j, n ∈ B j) →
  let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
    fun S => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
  let block : Sum ι κ → Finset Nat := Sum.elim A B
  let graph : SimpleGraph (Sum ι κ) := SimpleGraph.fromRel fun u v =>
    match u, v with
    | Sum.inl i, Sum.inr j => Finset.Nonempty (A i ∩ B j)
    | _, _ => False
  let componentBlock : SimpleGraph.ConnectedComponent graph → Finset Nat := fun c =>
    let inComponent : Nat → Prop := fun n =>
      ∃ v : Sum ι κ, SimpleGraph.connectedComponentMk graph v = c ∧ n ∈ block v
    @Finset.filter Nat inComponent (Classical.decPred inComponent) X
  ((iSup fun i => blockSym (A i)) ⊔ (iSup fun j => blockSym (B j))) =
    iSup fun c => blockSym (componentBlock c)) :=
(by
  intro ι κ _ _ X A B _ _ _ _ coversA coversB blockSym block graph componentBlock
  let swaps (S : Finset Nat) : Set (Equiv.Perm Nat) :=
    {σ | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ σ = Equiv.swap x y}
  have swap_mem_block (S : Finset Nat) {x y : Nat} (hx : x ∈ S) (hy : y ∈ S) :
      Equiv.swap x y ∈ blockSym S :=
    ⟨Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  -- Alphabeta Math, "Every finite permutation is a product of transpositions",
  -- steps 1.1 and 2.1 generate the finite symmetric group by factoring cycles.
  -- For a block embedded in Nat we use the finitary swap-closure criterion.
  -- Distinct endpoints give genuine swaps, the block bounds the support, and
  -- the swap of a moved point with its image witnesses the orbit condition.
  -- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
  have blockSym_eq_closure (S : Finset Nat) : blockSym S = Subgroup.closure (swaps S) := by
    apply le_antisymm
    · rintro σ ⟨τ, rfl⟩
      have genuine : ∀ f ∈ swaps S, Equiv.Perm.IsSwap f := by
        rintro f ⟨x, _, y, _, hxy, rfl⟩
        exact ⟨x, y, hxy, rfl⟩
      apply (mem_closure_isSwap genuine).2
      have fixesOutside (x : Nat) (hx : x ∉ S) : Equiv.Perm.ofSubtype τ x = x :=
        Equiv.Perm.ofSubtype_apply_of_not_mem τ hx
      refine ⟨S.finite_toSet.subset ?_, ?_⟩
      · intro x hx
        by_contra hxS
        exact hx ((MulAction.mem_fixedBy).2 (fixesOutside x hxS))
      · intro x
        by_cases heq : Equiv.Perm.ofSubtype τ x = x
        · rw [heq]
          exact MulAction.mem_orbit_self x
        · have hx : x ∈ S := by
            by_contra hx
            exact heq (fixesOutside x hx)
          have hy : Equiv.Perm.ofSubtype τ x ∈ S := by
            rw [Equiv.Perm.ofSubtype_apply_of_mem τ hx]
            exact (τ ⟨x, hx⟩).property
          have hs : Equiv.swap (Equiv.Perm.ofSubtype τ x) x ∈ Subgroup.closure (swaps S) :=
            Subgroup.subset_closure ⟨_, hy, _, hx, heq, rfl⟩
          exact MulAction.mem_orbit_iff.mpr ⟨⟨_, hs⟩, Equiv.swap_apply_right _ _⟩
    · apply (Subgroup.closure_le _).2
      rintro σ ⟨x, hx, y, hy, _, rfl⟩
      exact swap_mem_block S hx hy
  have mem_component (c : graph.ConnectedComponent) (x : Nat) :
      x ∈ componentBlock c ↔ x ∈ X ∧
        ∃ v : Sum ι κ, graph.connectedComponentMk v = c ∧ x ∈ block v :=
    @Finset.mem_filter Nat _ (Classical.decPred _) _ _
  -- In Proposition 7.1 each input block lies in the union indexed by the
  -- component of its vertex. Here coverage puts that block inside X.
  -- Every generating swap acts inside that component and fixes its complement,
  -- giving the containment of the input join by the closure description.
  have subset_component (v : Sum ι κ) : block v ⊆ componentBlock (graph.connectedComponentMk v) := by
    intro x hx
    apply (mem_component _ _).2
    refine ⟨?_, v, rfl, hx⟩
    cases v with
    | inl i => exact (coversA x).2 ⟨i, hx⟩
    | inr j => exact (coversB x).2 ⟨j, hx⟩
  have block_le_component (v : Sum ι κ) :
      blockSym (block v) ≤ iSup (fun c => blockSym (componentBlock c)) := by
    apply le_trans _ (le_iSup (fun c => blockSym (componentBlock c)) (graph.connectedComponentMk v))
    rw [blockSym_eq_closure (block v)]
    apply (Subgroup.closure_le _).2
    rintro σ ⟨x, hx, y, hy, _, rfl⟩
    exact swap_mem_block _ (subset_component v hx) (subset_component v hy)
  let joined := (iSup fun i => blockSym (A i)) ⊔ (iSup fun j => blockSym (B j))
  have block_le_join (v : Sum ι κ) : blockSym (block v) ≤ joined := by
    cases v with
    | inl i => exact le_trans (le_iSup (fun i => blockSym (A i)) i) le_sup_left
    | inr j => exact le_trans (le_iSup (fun j => blockSym (B j)) j) le_sup_right
  have edge_overlap {u v : Sum ι κ} (h : graph.Adj u v) :
      ∃ x : Nat, x ∈ block u ∧ x ∈ block v := by
    cases u <;> cases v
    · exact False.elim (h.2.elim id id)
    · obtain ⟨x, hx⟩ := h.2.resolve_right id
      exact ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
    · obtain ⟨x, hx⟩ := h.2.resolve_left id
      exact ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
    · exact False.elim (h.2.elim id id)
  -- Alphabeta Math, "Adjacent transpositions generate the symmetric group",
  -- step 1.1 combines swaps along an interval of letters. For the overlap
  -- chains of Proposition 7.1, walk induction picks one point per overlap.
  -- Mathlib's swap_mem_trans handles the conjugation and repeated points.
  -- https://alphabetamath.cc/item/thm-adjacent-transpositions-generate-the-symmetric-group
  have walk_swap {u v : Sum ι κ} (p : graph.Walk u v) :
      ∀ {x y : Nat}, x ∈ block u → y ∈ block v → Equiv.swap x y ∈ joined := by
    induction p with
    | nil =>
        intro x y hx hy
        exact block_le_join _ (swap_mem_block _ hx hy)
    | cons huv _ ih =>
        intro x y hx hy
        obtain ⟨z, hzu, hzv⟩ := edge_overlap huv
        exact SubmonoidClass.swap_mem_trans joined
          (block_le_join _ (swap_mem_block _ hx hzu)) (ih hzv hy)
  apply le_antisymm
  · exact sup_le (iSup_le fun i => block_le_component (Sum.inl i))
      (iSup_le fun j => block_le_component (Sum.inr j))
  -- As in step 2.1 of the adjacent-transposition proof, containing every
  -- endpoint swap gives the entire symmetric group, here in each component.
  · apply iSup_le
    intro c
    rw [blockSym_eq_closure (componentBlock c)]
    apply (Subgroup.closure_le _).2
    rintro σ ⟨x, hx, y, hy, _, rfl⟩
    obtain ⟨_, u, hu, hxu⟩ := (mem_component c x).1 hx
    obtain ⟨_, v, hv, hyv⟩ := (mem_component c y).1 hy
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)
    exact walk_swap p hxu hyv)
