import MackeyDiagrams
import Proofs.FiniteParabolicClosure
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks

set_option maxHeartbeats 2000000

private theorem parabolicExample_components
    {V : Type} (graph : SimpleGraph V) (X : Finset Nat)
    (block : V → Finset Nat) (part : Bool → Finset Nat)
    (tag : V → Bool) (rep : Bool → V)
    (blockSubset : ∀ v, block v ⊆ part (tag v))
    (partSubset : ∀ t, part t ⊆ X)
    (partDisjoint : ∀ {t u}, t ≠ u → Disjoint (part t) (part u))
    (cover : ∀ x ∈ X, ∃ v, x ∈ block v)
    (edgeOverlap : ∀ {v w}, graph.Adj v w → (block v ∩ block w).Nonempty)
    (repTag : ∀ t, tag (rep t) = t)
    (paths : ∀ v, graph.Reachable v (rep (tag v))) :
    let componentBlock : graph.ConnectedComponent → Finset Nat := fun c =>
      let inComponent : Nat → Prop := fun x =>
        ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v
      @Finset.filter Nat inComponent (Classical.decPred inComponent) X
    (∀ t, componentBlock (graph.connectedComponentMk (rep t)) = part t) ∧
      (∀ c, ∃ t, graph.connectedComponentMk (rep t) = c) := by
  intro componentBlock
  have walkTag {v w : V} (p : graph.Walk v w) : tag v = tag w := by
    induction p with
    | nil => rfl
    | cons h _ ih =>
      refine Eq.trans ?_ ih
      by_contra hne
      obtain ⟨x, hx⟩ := edgeOverlap h
      obtain ⟨hv, hw⟩ := Finset.mem_inter.mp hx
      exact Finset.disjoint_left.mp (partDisjoint hne) (blockSubset _ hv) (blockSubset _ hw)
  have memComponent (c : graph.ConnectedComponent) (x : Nat) :
      x ∈ componentBlock c ↔
        x ∈ X ∧ ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v :=
    @Finset.mem_filter Nat _ (Classical.decPred _) _ _
  constructor
  · intro t
    ext x
    rw [memComponent]
    constructor
    · rintro ⟨_, v, hv, hx⟩
      obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.eq.mp hv
      have htag := (walkTag p).trans (repTag t)
      exact htag ▸ blockSubset v hx
    · intro hx
      have hxX := partSubset t hx
      obtain ⟨v, hv⟩ := cover x hxX
      have htag : tag v = t := by
        by_contra hne
        exact Finset.disjoint_left.mp (partDisjoint hne) (blockSubset v hv) hx
      exact ⟨hxX, v, htag ▸ SimpleGraph.ConnectedComponent.eq.mpr (paths v), hv⟩
  · intro c
    refine c.ind fun v => ?_
    exact ⟨tag v, (SimpleGraph.ConnectedComponent.eq.mpr (paths v)).symm⟩

theorem ParabolicBlockOperationExample : (
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun S => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let blocksA : Finset (Finset Nat) := {{1, 2, 3}, {4, 5}, {6}, {7}}
let blocksB : Finset (Finset Nat) := {{2, 3, 4}, {6, 7}, {1}, {5}}
let A := iSup (fun S : ↥blocksA => blockSym (Subtype.val S))
let B := iSup (fun S : ↥blocksB => blockSym (Subtype.val S))
let α : Equiv.Perm Nat := Equiv.swap 1 4 * Equiv.swap 4 6
Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) A =
    (blockSym {2, 3, 4} ⊔ blockSym {5, 6}) ∧
  A ⊓ B = blockSym {2, 3} ∧
  A ⊔ B = (blockSym {1, 2, 3, 4, 5} ⊔ blockSym {6, 7}) ∧
  Equiv.swap (1 : Nat) 5 ∈ A ⊔ B
) :=
(by
  intro blockSym blocksA blocksB A B α
  -- Xiao, Example 7.1, after Proposition 7.1. Reindex the two specified
  -- families by Fin 4 so finite checks use the same singleton blocks as the paper.
  -- The project PDF (p. 29) and published PDF (p. 31) have different bytes
  -- but give the same example. The calculation uses the three explicit block
  -- formulas underlying FiniteParabolicClosure, which gives existential closure.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  let a : Fin 4 → Finset Nat := ![{1, 2, 3}, {4, 5}, {6}, {7}]
  let b : Fin 4 → Finset Nat := ![{2, 3, 4}, {6, 7}, {1}, {5}]
  let X : Finset Nat := Finset.Icc 1 7
  have familySup (f : Fin 4 → Finset Nat) (blocks : Finset (Finset Nat))
      (h : Finset.univ.image f = blocks) :
      (⨆ i : ↥blocks, blockSym i.val) = ⨆ i, blockSym (f i) := by
    subst blocks
    rw [iSup_subtype, Finset.iSup_finset_image]
    simp only [Finset.mem_univ, iSup_pos]
  have hA : A = ⨆ i, blockSym (a i) := familySup a blocksA (by decide)
  have hB : B = ⨆ i, blockSym (b i) := familySup b blocksB (by decide)
  have nonemptyA : ∀ i, (a i).Nonempty := by decide
  have nonemptyB : ∀ i, (b i).Nonempty := by decide
  have disjointA : Pairwise (fun i j => Disjoint (a i) (a j)) := by
    change ∀ i j, i ≠ j → Disjoint (a i) (a j)
    decide
  have disjointB : Pairwise (fun i j => Disjoint (b i) (b j)) := by
    change ∀ i j, i ≠ j → Disjoint (b i) (b j)
    decide
  have coverOfUnion (f : Fin 4 → Finset Nat) (h : Finset.univ.biUnion f = X)
      (x : Nat) : x ∈ X ↔ ∃ i, x ∈ f i := by
    rw [← h, Finset.mem_biUnion]
    simp only [Finset.mem_univ, true_and]
  have coverA := coverOfUnion a (by decide)
  have coverB := coverOfUnion b (by decide)
  have smallBlock (S : Finset Nat) (hS : S.card ≤ 1) : blockSym S = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨f, rfl⟩
    rw [Subgroup.mem_bot]
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ S
    · rw [Equiv.Perm.ofSubtype_apply_of_mem f hx]
      exact Finset.card_le_one_iff.mp hS (f ⟨x, hx⟩).property hx
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem f hx
  rw [hA, hB]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Conjugation. Alphabeta Math's transposition-generation steps 1.1 and
    -- 2.1 factor cycles and then concatenate the factors. The conjugator here
    -- is already given as two genuine swaps, so closure under multiplication
    -- supplies the finitary hypothesis directly.
    -- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
    have swapInClosure {x y : Nat} (hne : x ≠ y) :
        Equiv.swap x y ∈ Subgroup.closure {σ : Equiv.Perm Nat | σ.IsSwap} :=
      Subgroup.subset_closure ⟨x, y, hne, rfl⟩
    have hα : α ∈ Subgroup.closure {σ : Equiv.Perm Nat | σ.IsSwap} :=
      Subgroup.mul_mem _ (swapInClosure (by decide : (1 : Nat) ≠ 4))
        (swapInClosure (by decide : (4 : Nat) ≠ 6))
    rw [FiniteParabolicConjugateBlocks a nonemptyA disjointA ⟨α, hα⟩]
    let images : Fin 4 → Finset Nat := ![{2, 3, 4}, {5, 6}, {1}, {7}]
    -- The concrete image check evaluates the two swaps on each input block.
    have imageEq : ∀ i, (a i).image α = images i := by decide
    change (⨆ i, blockSym ((a i).image α)) = _
    simp only [imageEq]
    apply le_antisymm
    · apply iSup_le
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
      · rw [smallBlock (images _) (by decide)]
        exact bot_le
      · rw [smallBlock (images _) (by decide)]
        exact bot_le
    · exact sup_le (le_iSup (fun i => blockSym (images i)) 0)
        (le_iSup (fun i => blockSym (images i)) 1)
  · -- Intersection. The formula keeps every cell of the common refinement.
    -- Cells with at most one point contribute the trivial subgroup.
    rw [FiniteParabolicIntersectionBlocks X a b nonemptyA nonemptyB disjointA disjointB
      coverA coverB]
    change (⨆ i, ⨆ j, blockSym (a i ∩ b j)) = blockSym {2, 3}
    have cells : ∀ i j, a i ∩ b j = {2, 3} ∨ (a i ∩ b j).card ≤ 1 := by decide
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun j => ?_
      obtain h | h := cells i j
      · rw [h]
      · rw [smallBlock _ h]
        exact bot_le
    · have cell00 : a 0 ∩ b 0 = {2, 3} := by decide
      rw [← cell00]
      exact (le_iSup (fun j => blockSym (a 0 ∩ b j)) 0).trans
        (le_iSup (fun i => ⨆ j, blockSym (a i ∩ b j)) 0)
  · -- Generation. Keep the carrier filter in the registered join formula.
    -- Tag every input block by the proposed component. The six explicit
    -- overlap edges give paths to the two representatives, and every edge
    -- preserves the tag because the two output blocks are disjoint.
    have join := FiniteParabolicJoinBlocks X a b nonemptyA nonemptyB disjointA disjointB
      coverA coverB
    extract_lets block graph componentBlock at join
    let V := Sum (Fin 4) (Fin 4)
    let part : Bool → Finset Nat := fun t => if t then {6, 7} else {1, 2, 3, 4, 5}
    let tag : V → Bool := fun v => decide (block v ⊆ part true)
    let rep : Bool → V := fun t => .inr (if t then 1 else 0)
    have blockSubset : ∀ v, block v ⊆ part (tag v) := by decide
    have partSubset : ∀ t, part t ⊆ X := by decide
    have partDisjoint : ∀ t u, t ≠ u → Disjoint (part t) (part u) := by decide
    have cover (x : Nat) (hx : x ∈ X) : ∃ v, x ∈ block v := by
      obtain ⟨i, hi⟩ := (coverA x).mp hx
      exact ⟨.inl i, hi⟩
    have edgeOverlap {v w : V} (h : graph.Adj v w) :
        (block v ∩ block w).Nonempty := by
      cases v <;> cases w
      · exact False.elim (h.2.elim id id)
      · exact h.2.elim id False.elim
      · rw [Finset.inter_comm]
        exact h.2.elim False.elim id
      · exact False.elim (h.2.elim id id)
    have edge (i j : Fin 4) (h : (a i ∩ b j).Nonempty) :
        graph.Adj (.inl i) (.inr j) :=
      ⟨by simp, Or.inl h⟩
    have e00 := (edge 0 0 (by decide)).reachable
    have e10 := (edge 1 0 (by decide)).reachable
    have e02 := (edge 0 2 (by decide)).reachable
    have e13 := (edge 1 3 (by decide)).reachable
    have e21 := (edge 2 1 (by decide)).reachable
    have e31 := (edge 3 1 (by decide)).reachable
    have paths (v : V) : graph.Reachable v (rep (tag v)) := by
      cases v with
      | inl i =>
        fin_cases i
        · exact e00
        · exact e10
        · exact e21
        · exact e31
      | inr j =>
        fin_cases j
        · exact SimpleGraph.Reachable.rfl
        · exact SimpleGraph.Reachable.rfl
        · exact e02.symm.trans e00
        · exact e13.symm.trans e10
    have repTag : ∀ t, tag (rep t) = t := by decide
    obtain ⟨componentEq, componentCover⟩ := parabolicExample_components graph X block part tag
      rep blockSubset partSubset (fun h => partDisjoint _ _ h) cover edgeOverlap repTag paths
    have componentEq' (t : Bool) : componentBlock (graph.connectedComponentMk (rep t)) = part t :=
      componentEq t
    have result : (⨆ c, blockSym (componentBlock c)) =
        blockSym (part false) ⊔ blockSym (part true) := by
      apply le_antisymm
      · apply iSup_le
        intro c
        obtain ⟨t, rfl⟩ := componentCover c
        rw [componentEq']
        cases t
        · exact le_sup_left
        · exact le_sup_right
      · apply sup_le
        · rw [← componentEq' false]
          exact le_iSup (fun c => blockSym (componentBlock c)) (graph.connectedComponentMk (rep false))
        · rw [← componentEq' true]
          exact le_iSup (fun c => blockSym (componentBlock c)) (graph.connectedComponentMk (rep true))
    exact join.trans result
  · -- The endpoint transposition follows the paper's overlapping-block path
    -- using 1–2–4–5. Each edge is a swap of two points of a single input block.
    have swapInBlock (S : Finset Nat) {x y : Nat} (hx : x ∈ S) (hy : y ∈ S) :
        Equiv.swap x y ∈ blockSym S :=
      ⟨Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
    let L := (⨆ i, blockSym (a i)) ⊔ (⨆ j, blockSym (b j))
    have leftLe : (⨆ i, blockSym (a i)) ≤ L := le_sup_left
    have rightLe : (⨆ j, blockSym (b j)) ≤ L := le_sup_right
    have h12 : Equiv.swap (1 : Nat) 2 ∈ L :=
      leftLe (Subgroup.mem_iSup_of_mem 0 (swapInBlock (a 0) (by decide) (by decide)))
    have h24 : Equiv.swap (2 : Nat) 4 ∈ L :=
      rightLe (Subgroup.mem_iSup_of_mem 0 (swapInBlock (b 0) (by decide) (by decide)))
    have h45 : Equiv.swap (4 : Nat) 5 ∈ L :=
      leftLe (Subgroup.mem_iSup_of_mem 1 (swapInBlock (a 1) (by decide) (by decide)))
    exact SubmonoidClass.swap_mem_trans L (SubmonoidClass.swap_mem_trans L h12 h24) h45
)

#print axioms ParabolicBlockOperationExample
