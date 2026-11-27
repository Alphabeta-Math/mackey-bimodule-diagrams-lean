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
