namespace UnequalParabolicCurlProof

open MackeyDiagrams

private abbrev finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev U := ↥finitary
private abbrev block (S : Finset Nat) : Subgroup U :=
  Subgroup.comap finitary.subtype
    (MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S)))

private def extend (S : Finset Nat) : Equiv.Perm ↥S →* U :=
  (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S)).codRestrict finitary (fun σ => by
    refine mem_closure_isSwap'.mpr (S.finite_toSet.subset ?_)
    intro x hx
    by_contra hn
    exact hx ((MulAction.mem_fixedBy).2 (Equiv.Perm.ofSubtype_apply_of_not_mem σ hn)))

private theorem extend_range (S : Finset Nat) : (extend S).range = block S := by
  ext σ
  change (∃ τ, extend S τ = σ) ↔ ∃ τ, Equiv.Perm.ofSubtype τ = (σ : Equiv.Perm Nat)
  exact ⟨fun ⟨τ, h⟩ => ⟨τ, congrArg Subtype.val h⟩, fun ⟨τ, h⟩ => ⟨τ, Subtype.ext h⟩⟩

private noncomputable def blockEquiv (S : Finset Nat) : Equiv.Perm ↥S ≃ ↥(block S) :=
  (MulEquiv.ofInjective (f := extend S) (fun _ _ e =>
    Equiv.Perm.ofSubtype_injective (congrArg Subtype.val e))).toEquiv.trans
    (Equiv.Set.ofEq (congrArg SetLike.coe (extend_range S)))

private theorem card_block (S : Finset Nat) : Nat.card ↥(block S) = S.card.factorial := by
  rw [← Nat.card_congr (blockEquiv S), Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]

-- Alphabeta Math, transpositions generate the symmetric group, Steps 1.1,
-- 2.1 and 3.1. The factorization applies on the finite block subtype.
-- Swap induction packages the cycle factorization and extends each factor
-- by the identity to Nat. The generated subgroup is tested after extension.
-- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
private theorem block_le_of_swaps (S : Finset Nat) (K : Subgroup U)
    (hs : ∀ x y : ↥S, x ≠ y → extend S (Equiv.swap x y) ∈ K) : block S ≤ K := by
  rw [← extend_range]
  rintro _ ⟨σ, rfl⟩
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simpa only [map_one] using K.one_mem
  | swap_mul τ x y hxy ih =>
    rw [map_mul]
    exact K.mul_mem (hs x y hxy) ih

private abbrev transposition {S : Finset Nat} (x y : ↥S) (h : (x : Nat) ≠ (y : Nat)) : U :=
  ⟨Equiv.swap (x : Nat) (y : Nat), Subgroup.subset_closure ⟨(x : Nat), (y : Nat), h, rfl⟩⟩

private theorem extend_swap {S : Finset Nat} (x y : ↥S) (h : (x : Nat) ≠ (y : Nat)) :
    extend S (Equiv.swap x y) = transposition x y h :=
  Subtype.ext (Equiv.Perm.ofSubtype_swap_eq x y)

private theorem block_pair {S : Finset Nat} (x y : ↥S) (h : (x : Nat) ≠ (y : Nat)) :
    block {(x : Nat), (y : Nat)} = Subgroup.zpowers (transposition x y h) := by
  let T : Finset Nat := {(x : Nat), (y : Nat)}
  let p : ↥T := ⟨x, Finset.mem_insert_self _ _⟩
  let q : ↥T := ⟨y, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have e : extend T (Equiv.swap p q) = transposition x y h :=
    Subtype.ext (Equiv.Perm.ofSubtype_swap_eq p q)
  have mem : extend T (Equiv.swap p q) ∈ Subgroup.zpowers (transposition x y h) :=
    e.symm ▸ Subgroup.mem_zpowers _
  have casesT (i : ↥T) : i = p ∨ i = q := by
    have hi := i.property
    change (i : Nat) ∈ {(x : Nat), (y : Nat)} at hi
    simpa only [Finset.mem_insert, Finset.mem_singleton, ← Subtype.ext_iff] using hi
  apply le_antisymm
  · apply block_le_of_swaps
    intro i j hij
    rcases casesT i with rfl | rfl <;> rcases casesT j with rfl | rfl
    · exact (hij rfl).elim
    · exact mem
    · rwa [Equiv.swap_comm]
    · exact (hij rfl).elim
  · apply Subgroup.zpowers_le.mpr
    rw [← e, ← extend_range]
    exact ⟨_, rfl⟩

private theorem fixes_outside {S : Finset Nat} {σ : U} (hσ : σ ∈ block S)
    {x : Nat} (hx : x ∉ S) : (σ : Equiv.Perm Nat) x = x := by
  obtain ⟨τ, hτ⟩ := hσ
  rw [← hτ]
  exact Equiv.Perm.ofSubtype_apply_of_not_mem τ hx

private theorem preserves_block {S : Finset Nat} {σ : U} (hσ : σ ∈ block S)
    {x : Nat} (hx : x ∈ S) : (σ : Equiv.Perm Nat) x ∈ S := by
  obtain ⟨τ, hτ⟩ := hσ
  rw [← hτ]
  exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem τ x).2 hx

private abbrev S : Finset Nat := {1, 2, 3}
private abbrev p : ↥S := ⟨1, by decide⟩
private abbrev q : ↥S := ⟨2, by decide⟩
private abbrev r : ↥S := ⟨3, by decide⟩
private abbrev A := Subgroup.zpowers (transposition p q (by decide))
private abbrev B := Subgroup.zpowers (transposition q r (by decide))
private abbrev H := block S

private theorem concrete_intersection : A ⊓ B = ⊥ := by
  have eA : block {1, 2} = A := block_pair p q (by decide)
  have eB : block {2, 3} = B := block_pair q r (by decide)
  rw [← eA, ← eB]
  apply le_antisymm ?_ bot_le
  intro σ hσ
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (σ : Equiv.Perm Nat) x = x
  have h1 : (σ : Equiv.Perm Nat) 1 = 1 := fixes_outside hσ.2 (by decide)
  by_cases hx : x ∈ ({1, 2} : Finset Nat)
  · rcases (show x = 1 ∨ x = 2 by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx)
      with rfl | rfl
    · exact h1
    · have h2 := preserves_block hσ.1 hx
      rcases (show (σ : Equiv.Perm Nat) 2 = 1 ∨ (σ : Equiv.Perm Nat) 2 = 2 by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using h2) with e | e
      · exact (by decide : (2 : Nat) ≠ 1) ((σ : Equiv.Perm Nat).injective (e.trans h1.symm)) |>.elim
      · exact e
  · exact fixes_outside hσ.1 hx

private theorem concrete_join (hA : A ≤ H) (hB : B ≤ H) : A ⊔ B = H := by
  apply le_antisymm (sup_le hA hB)
  have hpq : extend S (Equiv.swap p q) ∈ A ⊔ B := by
    rw [extend_swap p q (by decide)]
    exact le_sup_left (Subgroup.mem_zpowers _)
  have hqr : extend S (Equiv.swap q r) ∈ A ⊔ B := by
    rw [extend_swap q r (by decide)]
    exact le_sup_right (Subgroup.mem_zpowers _)
  have hpr : extend S (Equiv.swap p r) ∈ A ⊔ B := by
    -- The missing swap (13) is the conjugate of (12) by (23).
    rw [Equiv.swap_comm p r,
      ← Equiv.swap_mul_swap_mul_swap (x := p) (y := q) (z := r) (by decide) (by decide),
      map_mul, map_mul]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem hqr hpq) hqr
  have casesS (i : ↥S) : i = p ∨ i = q ∨ i = r := by
    have hi := i.property
    change (i : Nat) ∈ {1, 2, 3} at hi
    simpa only [Finset.mem_insert, Finset.mem_singleton, ← Subtype.ext_iff] using hi
  apply block_le_of_swaps
  intro i j hij
  rcases casesS i with rfl | rfl | rfl <;> rcases casesS j with rfl | rfl | rfl
  all_goals first | exact (hij rfl).elim | exact hpq | exact hqr | exact hpr |
    (rw [Equiv.swap_comm]; first | exact hpq | exact hqr | exact hpr)

end UnequalParabolicCurlProof
