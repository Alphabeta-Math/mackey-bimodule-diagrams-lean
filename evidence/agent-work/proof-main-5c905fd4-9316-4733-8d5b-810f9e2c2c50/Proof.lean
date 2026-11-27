by
  intro X r c A B _ _ hdA hdB hcA hcB G blockSym K H Mat rank
  -- Xiao, Proposition 7.3 and the two numbered construction steps in §7.2.
  -- The project PDF has this passage on p. 30 and the live PDF on p. 31.
  -- Both give the same classification and ordered matching.
  -- The project records no separate Alphabeta Math proof for this endpoint.
  let count : G → Mat := fun p => ⟨fun i j => (tableauCell A B p i j).card, by
    constructor
    · exact tableauCell_card A B hdB hcB p
    · intro j
      simp_rw [tableauCell_card_symm A B p]
      exact tableauCell_card B A hdA hcA p.symm j⟩
  -- Descend the count to the quotient using the left/right factors in DoubleCoset.eq.
  let onCosets : DoubleCoset.Quotient (K : Set G) (H : Set G) → Mat :=
    Quotient.lift count fun p q hpq =>
      Subtype.ext (funext fun i => funext fun j =>
        tableauCount_invariant A B hdA hcA hdB hcB p q (DoubleCoset.eq''.mpr hpq) i j)
  have chosen (R : Mat) : ∃ p : G, count p = R ∧
      ∀ (i : Fin r) (j : Fin c) (x : ↥(A i)) (y : ↥(B j)),
        p y.val = x.val ↔ ∃ k : Fin (R.val i j),
          rank (A i) x = (∑ t ∈ Finset.Iio j, R.val i t) + k.val ∧
          rank (B j) y = (∑ t ∈ Finset.Iio i, R.val t j) + k.val := by
    obtain ⟨p, hcount, hrank⟩ := tableauOrdered A B hdA hcA hdB hcB R.val R.property.1 R.property.2
    refine ⟨p, ?_, hrank⟩
    apply Subtype.ext
    funext i j
    change (tableauCell A B p i j).card = R.val i j
    exact hcount i j
  have bij : Function.Bijective onCosets := by
    constructor
    · intro a b
      refine Quotient.inductionOn' a (fun p => ?_)
      refine Quotient.inductionOn' b (fun q hpq => ?_)
      exact tableauCount_injective A B hdA hcA hdB hcB p q fun i j =>
        congrArg (fun R : Mat => R.val i j) hpq
    · intro R
      obtain ⟨p, hp, _⟩ := chosen R
      exact ⟨DoubleCoset.mk K H p, hp⟩
  let classify := Equiv.ofBijective onCosets bij
  refine ⟨classify, fun _ _ _ => rfl, fun R => ?_⟩
  obtain ⟨p, hp, hrank⟩ := chosen R
  exact ⟨p, (classify.eq_symm_apply).mpr hp, hrank⟩
