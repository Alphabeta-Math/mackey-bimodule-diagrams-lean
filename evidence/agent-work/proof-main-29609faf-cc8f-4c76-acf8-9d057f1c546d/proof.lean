by
  intro n m hm hmn X G interval block blockSym K
  have hn : 1 ≤ n := hm.trans hmn
  have hcut : n < n + m := by omega
  -- Xiao, §7.3 and Example 7.4 (archived pp. 30–31, revised published
  -- pp. 32–33). Alphabeta Math's §7.2 steps 1–2 split the ordered
  -- row blocks and match the ordered column pieces at the matrix sizes.
  -- The registered standard-representative theorem uses the matrix
  -- classification to certify §7.3's reverse-pairing recursion.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-double-cosets
  -- Here both cuts are n. Positivity of m gives nonempty parent blocks,
  -- and m ≤ n identifies the supplier's swap bound with m.
  have standard := StandardTwoBlockRepresentatives (n + m) n n hn hcut hn hcut
  dsimp only at standard
  generalize hbound : Nat.min (Nat.min n n) (n + m - Nat.max n n) = bound at standard
  have hbound' : bound = m := hbound.symm.trans (by
    simp only [Nat.min_self, Nat.max_self, Nat.add_sub_cancel_left, Nat.min_eq_right hmn])
  clear hbound
  subst bound
  simp only [Nat.min_self, Nat.max_self] at standard
  obtain ⟨left, right, σ, hlabels, hzero, hsucc, _, hbij, _, hcells⟩ := standard
  refine ⟨left, right, σ, hlabels, hzero, hsucc, hbij, ?_⟩
  -- Each specified swap removes n-j from the first-block image and adds
  -- n+j+1. Keep the finite carrier and interval filters symbolic.
  have himage (i : Fin (m + 1)) (x : ↥X) :
      ((σ i).symm x).val ≤ n ↔ x.val ≤ n - i.val ∨ (n < x.val ∧ x.val ≤ n + i.val) := by
    induction i using Fin.induction generalizing x with
    | zero =>
        rw [hzero]
        change x.val ≤ n ↔ x.val ≤ n - 0 ∨ (n < x.val ∧ x.val ≤ n + 0)
        omega
    | succ j ih =>
        rw [hsucc]
        have hj := j.isLt
        exact equalTwoBlockSwapStep (by omega) (left j) (right j)
          (hlabels j).1 (hlabels j).2 (σ j.castSucc) ih x
  intro i k L
  let C (r c : Fin 2) := block r ∩ (block c).map (σ i).toEmbedding
  have hk : k ≤ m := Nat.le_of_lt_succ i.isLt
  have hkₙ : k ≤ n := hk.trans hmn
  have hparent : Disjoint (block 0) (block 1) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    change x ∈ equalTwoBlockInterval (n + m) 1 n at hx
    change x ∈ equalTwoBlockInterval (n + m) (n + 1) (n + m) at hy
    have h₁ := (equalTwoBlockMemInterval.mp hx).2
    have h₂ := (equalTwoBlockMemInterval.mp hy).1
    omega
  have hdisj := equalTwoBlockCellsDisjoint block hparent (σ i)
  obtain ⟨h00, h01, h10, h11⟩ := equalTwoBlockCellIntervals hkₙ (σ i) (himage i)
  have h00' : C 0 0 = interval 1 (n - k) := h00
  have h01' : C 0 1 = interval (n - k + 1) n := h01
  have h10' : C 1 0 = interval (n + 1) (n + k) := h10
  have h11' : C 1 1 = interval (n + k + 1) (n + m) := h11
  obtain ⟨hs00, hs01, hs10, hs11, _, hL⟩ := hcells i
  have hs00' : (C 0 0).card = n - k := by
    change ((C 0 0).card : Int) = (n : Int) - (k : Int) at hs00
    omega
  have hs01' : (C 0 1).card = k := by
    change ((C 0 1).card : Int) = (n : Int) - ((n : Int) - (k : Int)) at hs01
    omega
  have hs10' : (C 1 0).card = k := by
    change ((C 1 0).card : Int) = (n : Int) - ((n : Int) - (k : Int)) at hs10
    omega
  have hs11' : (C 1 1).card = m - k := by
    change ((C 1 1).card : Int) =
      ((n + m : Nat) : Int) - (n : Int) - (n : Int) + ((n : Int) - (k : Int)) at hs11
    omega
  -- The supplier sums over nonempty cells. An empty cell's symmetric
  -- group extends to the identity, so adjoining it adds a trivial factor.
  have hAll : L = ⨆ p : Fin 2 × Fin 2, blockSym (C p.1 p.2) :=
    hL.trans (equalTwoBlockAllFactors fun p : Fin 2 × Fin 2 => C p.1 p.2)
  constructor
  · rw [hAll, iSup_prod]
    simp only [equalTwoBlockSupPair, h00', h01', h10', h11', sup_assoc]
  · -- Extend each cell permutation by the identity. Disjointness gives
    -- commuting, independent images. Inverting this injective extension
    -- onto its range recovers the separate cell permutations.
    -- The rank equivalences also apply to the empty cells.
    let rank {s : Nat} (A : Finset ↥X) (h : A.card = s) :
        Equiv.Perm ↥A ≃* Equiv.Perm (Fin s) :=
      (Finset.orderIsoOfFin A h).toEquiv.symm.permCongrHom
    exact ⟨(MulEquiv.subgroupCongr hAll).trans
      ((equalTwoBlockProduct (fun p : Fin 2 × Fin 2 => C p.1 p.2) hdisj).trans
        ((equalTwoBlockRowOrder fun r c => Equiv.Perm ↥(C r c)).trans
          ((rank _ hs00').prodCongr
            ((rank _ hs01').prodCongr ((rank _ hs10').prodCongr (rank _ hs11'))))))⟩
