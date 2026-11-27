by
  intro S₂ S₄ G split P T K H
  -- Xiao, Example 7.6 (archived p. 31; published 28 November revision p. 33).
  -- Alphabeta Math's numbered construction in §7.2, steps 1–2, uses
  -- ordered cells to choose a tableau representative. In each coordinate
  -- one side is the whole block, so the cell pieces on that side are the
  -- two consecutive pairs on the other side. Matching in order gives 1.
  -- ProductParabolicDoubleCosets takes subgroups defined by partitions of
  -- a finite set in Perm Nat. For these explicit product subgroups, realize
  -- its componentwise argument by supplying the factors of every element.
  have class_one {L R : Subgroup S₄} (factor : ∀ g : S₄, ∃ l ∈ L, ∃ r ∈ R, g = l * r) :
      ∀ q : DoubleCoset.Quotient (L : Set S₄) (R : Set S₄),
        q = DoubleCoset.mk L R 1 := by
    intro q
    obtain ⟨l, hl, r, hr, h⟩ := factor q.out
    exact (DoubleCoset.out_eq' q).symm.trans
      ((DoubleCoset.eq.mpr ⟨l, hl, r, hr, by simpa only [mul_one] using h⟩).symm)
  have both (q : DoubleCoset.Quotient (K : Set G) (H : Set G)) :
      q = DoubleCoset.mk K H 1 := by
    let g : G := q.out
    refine (DoubleCoset.out_eq' q).symm.trans (Eq.symm (DoubleCoset.eq.mpr ?_))
    refine ⟨(1, g.2), ⟨P.one_mem, Subgroup.mem_top _⟩,
      (g.1, 1), ⟨Subgroup.mem_top _, P.one_mem⟩, ?_⟩
    change g = (1, g.2) * 1 * (g.1, 1)
    apply Prod.ext
    · change g.1 = 1 * 1 * g.1
      simp only [one_mul]
    · change g.2 = g.2 * 1 * 1
      simp only [mul_one]
  -- ParabolicMackeyIntersectionBlocks computes intersections in a single
  -- symmetric group from two covering partitions and a conjugator. Here
  -- the conjugator is 1 and membership in the product gives the intersection.
  have intersection : K ⊓ H = Subgroup.prod P P := by
    apply Subgroup.ext
    intro g
    change (g.1 ∈ P ∧ g.2 ∈ T) ∧ (g.1 ∈ T ∧ g.2 ∈ P) ↔ g.1 ∈ P ∧ g.2 ∈ P
    exact ⟨fun h => ⟨h.1.1, h.2.2⟩,
      fun h => ⟨⟨h.1, Subgroup.mem_top _⟩, ⟨Subgroup.mem_top _, h.2⟩⟩⟩
  refine ⟨class_one (fun g => ⟨1, P.one_mem, g, Subgroup.mem_top _, (one_mul g).symm⟩),
    class_one (fun g => ⟨g, Subgroup.mem_top _, 1, P.one_mem, (mul_one g).symm⟩),
    both, intersection, ?_⟩
  -- Each copy of P acts independently on its two disjoint Fin 2 blocks.
  have split_injective : Function.Injective split :=
    (Equiv.permCongrHom (finSumFinEquiv (m := 2) (n := 2))).injective.comp
      Equiv.Perm.sumCongrHom_injective
  let blockEquiv : (S₂ × S₂) ≃* P := MonoidHom.ofInjective split_injective
  exact ⟨(MulEquiv.subgroupCongr intersection).trans
    ((Subgroup.prodEquiv P P).trans (MulEquiv.prodCongr blockEquiv.symm blockEquiv.symm))⟩
