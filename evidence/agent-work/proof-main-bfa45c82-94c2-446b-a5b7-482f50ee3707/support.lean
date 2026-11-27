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
