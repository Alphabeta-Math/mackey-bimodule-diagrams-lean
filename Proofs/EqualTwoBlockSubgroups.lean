import Mathlib.GroupTheory.NoncommPiCoprod
import MackeyDiagrams
import Proofs.StandardTwoBlockRepresentatives

set_option maxHeartbeats 2000000

private abbrev equalTwoBlockFactor {α : Type*} [DecidableEq α] (A : Finset α) :
    Subgroup (Equiv.Perm α) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : α => x ∈ A))

private theorem equalTwoBlockAllFactors {α ι : Type*} [DecidableEq α] (A : ι → Finset α) :
    (⨆ p : {p : ι // (A p).Nonempty}, equalTwoBlockFactor (A p.val)) =
      ⨆ p, equalTwoBlockFactor (A p) := by
  apply le_antisymm
  · exact iSup_le fun p => le_iSup (fun i => equalTwoBlockFactor (A i)) p.val
  · apply iSup_le
    intro p
    by_cases hp : (A p).Nonempty
    · exact le_iSup (fun i : {i : ι // (A i).Nonempty} =>
        equalTwoBlockFactor (A i.val)) ⟨p, hp⟩
    · apply le_trans ?_ bot_le
      rintro g ⟨f, rfl⟩
      apply Subgroup.mem_bot.mpr (Equiv.ext fun x => ?_)
      exact Equiv.Perm.ofSubtype_apply_of_not_mem f (fun hx => hp ⟨x, hx⟩)

private noncomputable def equalTwoBlockProduct {α ι : Type*} [DecidableEq α] [Fintype ι]
    (A : ι → Finset α) (hA : Pairwise fun i j => Disjoint (A i) (A j)) :
    ↥(⨆ i, equalTwoBlockFactor (A i)) ≃* ((i : ι) → Equiv.Perm ↥(A i)) := by
  let extend (i : ι) : Equiv.Perm ↥(A i) →* Equiv.Perm α := Equiv.Perm.ofSubtype
  have fixOutside (i : ι) (f : Equiv.Perm ↥(A i)) (x : α) (hx : x ∉ A i) :
      extend i f x = x := Equiv.Perm.ofSubtype_apply_of_not_mem f hx
  have commute : Pairwise fun i j => ∀ f g, Commute (extend i f) (extend j g) := by
    intro i j hij f g
    apply Equiv.Perm.Disjoint.commute
    intro x
    by_cases hx : x ∈ A i
    · exact Or.inr (fixOutside j g x (Finset.disjoint_left.mp (hA hij) hx))
    · exact Or.inl (fixOutside i f x hx)
  have independent : iSupIndep fun i => (extend i).range := by
    intro i
    rw [disjoint_iff_inf_le]
    rintro g ⟨⟨f, rfl⟩, hg⟩
    apply Subgroup.mem_bot.mpr (Equiv.ext fun x => ?_)
    by_cases hx : x ∈ A i
    · have fixes : (⨆ j, ⨆ _ : j ≠ i, (extend j).range) ≤
          MulAction.stabilizer (Equiv.Perm α) x := by
        refine iSup_le fun j => iSup_le fun hji => ?_
        rintro _ ⟨u, rfl⟩
        exact MulAction.mem_stabilizer_iff.mpr
          (fixOutside j u x (Finset.disjoint_left.mp (hA hji.symm) hx))
      exact MulAction.mem_stabilizer_iff.mp (fixes hg)
    · exact fixOutside i f x hx
  let extendAll := MonoidHom.noncommPiCoprod extend commute
  have hRange : extendAll.range = ⨆ i, equalTwoBlockFactor (A i) :=
    MonoidHom.noncommPiCoprod_range extend
  have hInj : Function.Injective extendAll :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep extend independent
      (fun _ => Equiv.Perm.ofSubtype_injective)
  exact (MulEquiv.subgroupCongr hRange.symm).trans (MonoidHom.ofInjective hInj).symm

private theorem equalTwoBlockSupPair {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    (⨆ r, f r) = f 0 ⊔ f 1 := by
  refine le_antisymm (iSup_le ?_) (sup_le (le_iSup f 0) (le_iSup f 1))
  intro r
  fin_cases r
  · exact le_sup_left
  · exact le_sup_right

private def equalTwoBlockPair (P : Fin 2 → Type*) [∀ i, Mul (P i)] :
    ((i : Fin 2) → P i) ≃* P 0 × P 1 where
  toEquiv := piFinTwoEquiv P
  map_mul' _ _ := rfl

private def equalTwoBlockRowOrder (P : Fin 2 → Fin 2 → Type*)
    [∀ i j, MulOneClass (P i j)] :
    ((p : Fin 2 × Fin 2) → P p.1 p.2) ≃* P 0 0 × P 0 1 × P 1 0 × P 1 1 := by
  let curry : ((p : Fin 2 × Fin 2) → P p.1 p.2) ≃* ((i j : Fin 2) → P i j) :=
    { toFun := fun f i j => f (i, j)
      invFun := fun f p => f p.1 p.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact curry.trans ((equalTwoBlockPair _).trans
    (((equalTwoBlockPair _).prodCongr (equalTwoBlockPair _)).trans MulEquiv.prodAssoc))

private abbrev equalTwoBlockInterval (N l h : Nat) : Finset ↥(Finset.Icc 1 N) :=
  Finset.filter (fun x => l ≤ x.val ∧ x.val ≤ h) Finset.univ

private theorem equalTwoBlockMemInterval {N l h : Nat} {x : ↥(Finset.Icc 1 N)} :
    x ∈ equalTwoBlockInterval N l h ↔ l ≤ x.val ∧ x.val ≤ h := by
  simp [equalTwoBlockInterval]

private theorem equalTwoBlockSwapStep {N n j : Nat} (hj : j < n)
    (a b : ↥(Finset.Icc 1 N)) (ha : a.val = n - j) (hb : b.val = n + j + 1)
    (f : Equiv.Perm ↥(Finset.Icc 1 N))
    (hf : ∀ x : ↥(Finset.Icc 1 N), (f.symm x).val ≤ n ↔
      x.val ≤ n - j ∨ (n < x.val ∧ x.val ≤ n + j))
    (x : ↥(Finset.Icc 1 N)) :
    ((Equiv.swap a b * f).symm x).val ≤ n ↔
      x.val ≤ n - (j + 1) ∨ (n < x.val ∧ x.val ≤ n + (j + 1)) := by
  change (f.symm (Equiv.swap a b x)).val ≤ n ↔ _
  rw [hf, Equiv.swap_apply_def]
  split_ifs with hx hy
  · subst x
    omega
  · subst x
    omega
  · have hx' : x.val ≠ a.val := fun h => hx (Subtype.ext h)
    have hy' : x.val ≠ b.val := fun h => hy (Subtype.ext h)
    omega

private abbrev equalTwoBlockPartition (N n : Nat) (r : Fin 2) :
    Finset ↥(Finset.Icc 1 N) :=
  if r = 0 then equalTwoBlockInterval N 1 n else equalTwoBlockInterval N (n + 1) N

private theorem equalTwoBlockCellIntervals {N n k : Nat} (hk : k ≤ n)
    (σ : Equiv.Perm ↥(Finset.Icc 1 N))
    (hσ : ∀ x : ↥(Finset.Icc 1 N), (σ.symm x).val ≤ n ↔
      x.val ≤ n - k ∨ (n < x.val ∧ x.val ≤ n + k)) :
    let C := fun r c => equalTwoBlockPartition N n r ∩
      (equalTwoBlockPartition N n c).map σ.toEmbedding
    C 0 0 = equalTwoBlockInterval N 1 (n - k) ∧
    C 0 1 = equalTwoBlockInterval N (n - k + 1) n ∧
    C 1 0 = equalTwoBlockInterval N (n + 1) (n + k) ∧
    C 1 1 = equalTwoBlockInterval N (n + k + 1) N := by
  intro C
  have first : equalTwoBlockPartition N n 0 = equalTwoBlockInterval N 1 n := rfl
  have second : equalTwoBlockPartition N n 1 = equalTwoBlockInterval N (n + 1) N := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext x <;>
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_Icc.mp x.property <;>
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_Icc.mp (σ.symm x).property <;>
    have hcompl : n + 1 ≤ (σ.symm x).val ↔ ¬ (σ.symm x).val ≤ n := by omega
  all_goals
    simp only [C, Finset.mem_inter, Finset.mem_map_equiv, first, second,
      equalTwoBlockMemInterval, hcompl, hσ x]
    omega

private theorem equalTwoBlockCellsDisjoint {α : Type*} [DecidableEq α]
    (B : Fin 2 → Finset α) (hB : Disjoint (B 0) (B 1)) (σ : Equiv.Perm α) :
    Pairwise (fun p q : Fin 2 × Fin 2 =>
      Disjoint (B p.1 ∩ (B p.2).map σ.toEmbedding) (B q.1 ∩ (B q.2).map σ.toEmbedding)) := by
  have hd : Pairwise (fun r c => Disjoint (B r) (B c)) := by
    intro r c hrc
    fin_cases r <;> fin_cases c
    · exact (hrc rfl).elim
    · exact hB
    · exact hB.symm
    · exact (hrc rfl).elim
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
  obtain ⟨hy₁, hy₂⟩ := Finset.mem_inter.mp hy
  by_cases h : p.1 = q.1
  · have h' : p.2 ≠ q.2 := fun h₂ => hpq (Prod.ext h h₂)
    exact Finset.disjoint_left.mp (hd h') (Finset.mem_map_equiv.mp hx₂)
      (Finset.mem_map_equiv.mp hy₂)
  · exact Finset.disjoint_left.mp (hd h) hx₁ hy₁

theorem EqualTwoBlockSubgroups : (
∀ (n m : Nat), 1 ≤ m → m ≤ n →
  let X : Finset Nat := Finset.Icc 1 (n + m)
  let G := Equiv.Perm ↥X
  let interval := fun lo hi : Nat =>
    Finset.filter (fun x : ↥X => lo ≤ Subtype.val x ∧ Subtype.val x ≤ hi) Finset.univ
  let block : Fin 2 → Finset ↥X := fun r =>
    if r = 0 then interval 1 n else interval (n + 1) (n + m)
  let blockSym := fun S : Finset ↥X =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ S))
  let K : Subgroup G := iSup (fun r => blockSym (block r))
  ∃ (left right : Fin m → ↥X) (σ : Fin (m + 1) → G),
    (∀ j : Fin m,
      Subtype.val (left j) = n - Fin.val j ∧
      Subtype.val (right j) = n + Fin.val j + 1) ∧
    σ 0 = 1 ∧
    (∀ j : Fin m, σ (Fin.succ j) =
      Equiv.swap (left j) (right j) * σ (Fin.castSucc j)) ∧
    Function.Bijective (fun i => DoubleCoset.mk K K (σ i)) ∧
    ∀ i : Fin (m + 1),
      let k := Fin.val i
      let L : Subgroup G := K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (σ i))) K
      L = ((blockSym (interval 1 (n - k)) ⊔
            blockSym (interval (n - k + 1) n)) ⊔
            blockSym (interval (n + 1) (n + k))) ⊔
            blockSym (interval (n + k + 1) (n + m)) ∧
      Nonempty (MulEquiv ↥L
        (Equiv.Perm (Fin (n - k)) × Equiv.Perm (Fin k) ×
          Equiv.Perm (Fin k) × Equiv.Perm (Fin (m - k))))
) :=
(by
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
            ((rank _ hs01').prodCongr ((rank _ hs10').prodCongr (rank _ hs11'))))))⟩)
