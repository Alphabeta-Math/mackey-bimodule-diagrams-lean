import MackeyDiagrams
import Proofs.ParabolicExtremalThreeInductionRegions

namespace ExtremalThreeInductionExample

private abbrev Perm := Equiv.Perm Nat
private abbrev finitary := Subgroup.closure {σ : Perm | Equiv.Perm.IsSwap σ}
private abbrev U := ↥finitary
private abbrev blockSym (S : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
private abbrev onBlock (S : Finset Nat) := (blockSym S).comap finitary.subtype
private abbrev transposition (i j : Nat) (h : i ≠ j) : U :=
  ⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, h, rfl⟩⟩

-- Factor permutations on the finite subtype before extending by the identity.
private theorem block_le_of_swaps (S : Finset Nat) (H : Subgroup Perm)
    (hs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Equiv.swap i j ∈ H) :
    blockSym S ≤ H := by
  rintro _ ⟨σ, rfl⟩
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [map_one]; exact H.one_mem
  | swap_mul f i j hij ih =>
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq]
    exact H.mul_mem (hs i i.property j j.property (fun h => hij (Subtype.ext h))) ih

private theorem onBlock_le_of_swaps (S : Finset Nat) (H : Subgroup U)
    (hs : ∀ i ∈ S, ∀ j ∈ S, ∀ h : i ≠ j, transposition i j h ∈ H) :
    onBlock S ≤ H := by
  have hle : blockSym S ≤ H.map finitary.subtype :=
    block_le_of_swaps S _ fun i hi j hj h => ⟨transposition i j h, hs i hi j hj h, rfl⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hle (show (x : Perm) ∈ blockSym S from hx)
  exact (finitary.subtype_injective hxy) ▸ hy

private theorem transposition_mem_block {S : Finset Nat} {i j : Nat} (h : i ≠ j)
    (hi : i ∈ S) (hj : j ∈ S) : transposition i j h ∈ onBlock S :=
  ⟨Equiv.swap (⟨i, hi⟩ : ↥S) ⟨j, hj⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

private theorem pair_block {i j : Nat} (h : i ≠ j) :
    Subgroup.closure ({transposition i j h} : Set U) = onBlock {i, j} := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
      (transposition_mem_block h (by simp) (by simp)))
  · apply onBlock_le_of_swaps
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact Subgroup.subset_closure (Set.mem_singleton _)
    · have hs : transposition j i hxy = transposition i j h := Subtype.ext (Equiv.swap_comm j i)
      rw [hs]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    · exact (hxy rfl).elim

private abbrev aSwap := transposition 1 2 (by decide)
private abbrev cSwap := transposition 2 3 (by decide)
private abbrev aGroup := Subgroup.closure ({aSwap} : Set U)
private abbrev cGroup := Subgroup.closure ({cSwap} : Set U)

private theorem join_blocks : aGroup ⊔ cGroup = onBlock (Finset.Icc 1 3) := by
  have h12 : aSwap ∈ aGroup ⊔ cGroup := le_sup_left (Subgroup.subset_closure (Set.mem_singleton _))
  have h23 : cSwap ∈ aGroup ⊔ cGroup := le_sup_right (Subgroup.subset_closure (Set.mem_singleton _))
  have h13eq : transposition 1 3 (by decide) = cSwap * aSwap * cSwap := by
    apply Subtype.ext
    change Equiv.swap 1 3 = Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 2 3
    rw [Equiv.swap_mul_swap_mul_swap (by decide : (1 : Nat) ≠ 2) (by decide : (1 : Nat) ≠ 3),
      Equiv.swap_comm]
  have h13 : transposition 1 3 (by decide) ∈ aGroup ⊔ cGroup :=
    h13eq ▸ (aGroup ⊔ cGroup).mul_mem ((aGroup ⊔ cGroup).mul_mem h23 h12) h23
  have increasing (i j : Nat) (hi : i ∈ Finset.Icc 1 3) (hj : j ∈ Finset.Icc 1 3)
      (hij : i < j) : transposition i j hij.ne ∈ aGroup ⊔ cGroup := by
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    have hcases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h12
    · exact h13
    · exact h23
  apply le_antisymm
  · exact sup_le
      ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
        (transposition_mem_block (by decide) (by decide) (by decide))))
      ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
        (transposition_mem_block (by decide) (by decide) (by decide))))
  · apply onBlock_le_of_swaps
    intro i hi j hj hij
    rcases hij.lt_or_gt with h | h
    · exact increasing i j hi hj h
    · have heq : transposition i j hij = transposition j i h.ne := Subtype.ext (Equiv.swap_comm i j)
      rw [heq]
      exact increasing j i hj hi h

private theorem block_fixes {S : Finset Nat} {x : U} (hx : x ∈ onBlock S)
    {n : Nat} (hn : n ∉ S) : (x : Perm) n = n := by
  obtain ⟨σ, hσ⟩ := (show (x : Perm) ∈ blockSym S from hx)
  rw [← hσ]
  exact Equiv.Perm.ofSubtype_apply_of_not_mem σ hn

private theorem meet_blocks : aGroup ⊓ cGroup = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hxA : x ∈ onBlock {1, 2} := pair_block (by decide : (1 : Nat) ≠ 2) ▸ hx.1
  have hxC : x ∈ onBlock {2, 3} := pair_block (by decide : (2 : Nat) ≠ 3) ▸ hx.2
  have fixed (n : Nat) (hn : n ≠ 2) : (x : Perm) n = n := by
    by_cases h : n = 1
    · exact block_fixes hxC (by simp [h])
    · exact block_fixes hxA (by simp [h, hn])
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro n
  change (x : Perm) n = n
  by_cases h : n = 2
  · subst n
    by_contra hn
    exact hn ((x : Perm).injective (fixed ((x : Perm) 2) hn))
  · exact fixed n h

private abbrev Parabolic (H : Subgroup U) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H.map finitary.subtype = ⨆ i, blockSym (blocks i)

private theorem block_parabolic (S : Finset Nat) (hs : S.Nonempty) : Parabolic (onBlock S) := by
  refine ⟨1, fun _ => S, fun _ => hs, fun i j hij => (hij (Subsingleton.elim i j)).elim, ?_⟩
  rw [iSup_unique]
  apply Subgroup.map_comap_eq_self
  rw [Subgroup.range_subtype]
  exact block_le_of_swaps S _ fun i _ j _ hij => Subgroup.subset_closure ⟨i, j, hij, rfl⟩

private theorem bot_parabolic : Parabolic (⊥ : Subgroup U) := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  simp only [Subgroup.map_bot, iSup_of_empty]

end ExtremalThreeInductionExample
