by
  -- Xiao §6.1 (archived p. 19, published 28 November revision p. 21)
  -- cites Khovanov, Proposition 7, equation (36), top-right identity
  -- (arXiv:1009.3295, p. 31). This endpoint has no matching numbered
  -- Alphabeta proof in the route. The adjacent-transposition argument
  -- applies over Complex and includes n = 0.
  intro n X U S G H J F nested inclusion a b c p q r word i j k leftSwap rightSwap ab bc
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change n = n + 1 at hv
    omega
  have hik : i ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    change n = n + 2 at hv
    omega
  have hjk : j ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    change n + 1 = n + 2 at hv
    omega
  -- Each swap has to be in its own target region and fix the source action
  -- by conjugation. The right swap fixes the last point of Fin (n+3).
  have rightMem : rightSwap ∈ H := by
    change Equiv.swap i j ∈ fixingSubgroup U {t : X | n + 2 ≤ t.val}
    apply (mem_fixingSubgroup_iff U).2
    intro t ht
    change n + 2 ≤ t.val at ht
    have hti : t ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      change t.val = n at hv
      omega
    have htj : t ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      change t.val = n + 1 at hv
      omega
    exact Equiv.swap_apply_of_ne_of_ne hti htj
  have fixes {m : Nat} (u : S m) (t : X) (ht : m ≤ t.val) : (u : U) t = t :=
    (mem_fixingSubgroup_iff U).mp u.property t ht
  -- Diagram.upDot uses the coefficient-one singleton case of the shared
  -- dot language. The two eligibility proofs use the endpoints fixed by
  -- each source subgroup and Mathlib's permutation transport of a swap.
  let d : MackeyDiagrams.Dot ab ab :=
    ⟨⟨leftSwap, Subgroup.mem_top _⟩, fun u => by
      apply Subtype.ext
      change (u : U) * Equiv.swap j k = Equiv.swap j k * (u : U)
      rw [Equiv.mul_swap_eq_swap_mul, fixes u j (by change n + 1 ≤ n + 1; omega),
        fixes u k (by change n + 1 ≤ n + 2; omega)]⟩
  let e : MackeyDiagrams.Dot bc bc :=
    ⟨⟨rightSwap, rightMem⟩, fun u => by
      apply Subtype.ext
      change (u : U) * Equiv.swap i j = Equiv.swap i j * (u : U)
      rw [Equiv.mul_swap_eq_swap_mul, fixes u i (by change n ≤ n; omega),
        fixes u j (by change n ≤ n + 1; omega)]⟩
  refine ⟨d, e, rfl, rfl, ?_⟩
  apply StandardSymmetricBraidProof.braid a b c d e
  apply Subtype.ext
  change Equiv.swap i j * Equiv.swap j k * Equiv.swap i j =
    Equiv.swap j k * Equiv.swap i j * Equiv.swap j k
  calc
    Equiv.swap i j * Equiv.swap j k * Equiv.swap i j =
        Equiv.swap j i * Equiv.swap k j * Equiv.swap j i := by
      rw [Equiv.swap_comm j i, Equiv.swap_comm k j]
    _ = Equiv.swap i k := Equiv.swap_mul_swap_mul_swap hjk.symm hik.symm
    _ = Equiv.swap k i := Equiv.swap_comm _ _
    _ = Equiv.swap j k * Equiv.swap i j * Equiv.swap j k :=
      (Equiv.swap_mul_swap_mul_swap hij hik).symm
