import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
import MackeyDiagrams
import Proofs.MovingMergeDotBackToBranch
import Proofs.BlockwiseGroupElementDotCriterion
open scoped Pointwise

namespace StrongerEmbeddingSlideProof

private abbrev Finitary : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}

private abbrev Block (X : Set Nat) : Subgroup ↥Finitary :=
  fixingSubgroup (↥Finitary) Xᶜ

private abbrev Blocks (i : Fin 4) : Set Nat :=
  Set.Icc (3 * (i : Nat) + 1) (3 * (i : Nat) + 3)

private abbrev Carrier : Set Nat := Set.Icc 1 12

private abbrev Conjugate (p : ↥Finitary) (L : Subgroup ↥Finitary) :=
  L.map (MulAut.conj p).toMonoidHom

private def swapInFinitary (i j : Nat) (hij : i ≠ j) : ↥Finitary :=
  ⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩

private def blockSwap : ↥Finitary :=
  swapInFinitary 4 7 (by decide) * swapInFinitary 5 8 (by decide) *
    swapInFinitary 6 9 (by decide)

private theorem fixOutside {X : Set Nat} {p : ↥Finitary}
    (hp : p ∈ Block X) {x : Nat} (hx : x ∉ X) : p.1 x = x :=
  (mem_fixingSubgroup_iff _).mp hp x hx

private theorem blockMono {X Y : Set Nat} (h : X ⊆ Y) : Block X ≤ Block Y :=
  fixingSubgroup_antitone (↥Finitary) (Set.compl_subset_compl.mpr h)

private theorem blocksDisjoint : Pairwise (fun i j => Disjoint (Blocks i) (Blocks j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro n hi hj
  change 3 * (i : Nat) + 1 ≤ n ∧ n ≤ 3 * (i : Nat) + 3 at hi
  change 3 * (j : Nat) + 1 ≤ n ∧ n ≤ 3 * (j : Nat) + 3 at hj
  exact hij (Fin.ext (by omega))

private theorem blocksNontrivial (i : Fin 4) : Set.Nontrivial (Blocks i) := by
  refine ⟨3 * (i : Nat) + 1, ?_, 3 * (i : Nat) + 2, ?_, by omega⟩
  · change 3 * (i : Nat) + 1 ≤ _ ∧ _ ≤ 3 * (i : Nat) + 3
    omega
  · change 3 * (i : Nat) + 1 ≤ _ ∧ _ ≤ 3 * (i : Nat) + 3
    omega

private theorem covered {n : Nat} (hn : n ∈ Carrier) : ∃ i, n ∈ Blocks i := by
  change 1 ≤ n ∧ n ≤ 12 at hn
  let i : Fin 4 := ⟨(n - 1) / 3, by omega⟩
  refine ⟨i, ?_⟩
  change 3 * ((n - 1) / 3) + 1 ≤ n ∧ n ≤ 3 * ((n - 1) / 3) + 3
  omega

private theorem preserveCarrier (p : ↥Finitary)
    (hp : Conjugate p (⨆ i, Block (Blocks i)) ≤ Block Carrier)
    (hKG : (⨆ i, Block (Blocks i)) ≤ Block Carrier) :
    Set.MapsTo p.1 Carrier Carrier := by
  have step := BlockwiseGroupElementDotCriterion Blocks (fun _ : Unit => Carrier)
    (fun i => (blocksNontrivial i).nonempty)
    (fun _ => ⟨1, by decide⟩) blocksDisjoint
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
  have hG : (⨆ _ : Unit, Block Carrier) = Block Carrier := iSup_const
  have hp' (k : ↥(⨆ i, Block (Blocks i))) :
      p * k.1 * p⁻¹ ∈ (⨆ _ : Unit, Block Carrier) := by
    rw [hG]
    exact hp (Subgroup.mem_map.mpr ⟨k.1, k.2, rfl⟩)
  have h1 (k : ↥(⨆ i, Block (Blocks i))) :
      1 * k.1 * (1 : ↥Finitary)⁻¹ ∈ (⨆ _ : Unit, Block Carrier) := by
    simpa only [hG, one_mul, inv_one, mul_one] using hKG k.2
  intro n hn
  obtain ⟨i, hi⟩ := covered hn
  obtain ⟨_, hblock⟩ := ((step p 1 hp' h1).1 i (blocksNontrivial i)).1
  exact hblock hi

private theorem conjugateInside {L : Subgroup ↥Finitary} (hL : L ≤ Block Carrier)
    {p : ↥Finitary} (hp : Set.MapsTo p.1 Carrier Carrier) :
    Conjugate p L ≤ Block Carrier := by
  rintro _ ⟨q, hq, rfl⟩
  apply (mem_fixingSubgroup_iff _).mpr
  intro z hz
  have hz' : p.1.symm z ∉ Carrier := fun h => hz (p.1.apply_symm_apply z ▸ hp h)
  change p.1 (q.1 (p.1.symm z)) = z
  rw [fixOutside (hL hq) hz', p.1.apply_symm_apply]

private theorem blockSwapFix {x : Nat}
    (hx : x < 4 ∨ 9 < x) : blockSwap.1 x = x := by
  change Equiv.swap 4 7 (Equiv.swap 5 8 (Equiv.swap 6 9 x)) = x
  rw [Equiv.swap_apply_of_ne_of_ne (by omega : x ≠ 6) (by omega : x ≠ 9),
    Equiv.swap_apply_of_ne_of_ne (by omega : x ≠ 5) (by omega : x ≠ 8),
    Equiv.swap_apply_of_ne_of_ne (by omega : x ≠ 4) (by omega : x ≠ 7)]

private theorem blockSwapInvolutive : blockSwap⁻¹ = blockSwap := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change blockSwap.1 (blockSwap.1 x) = x
  by_cases hx : 4 ≤ x ∧ x ≤ 9
  · obtain ⟨hlo, hhi⟩ := hx
    interval_cases x <;> decide
  · have hfix := blockSwapFix (x := x) (by omega)
    rw [hfix, hfix]

private theorem conjugateBlock (p : ↥Finitary) (X Y : Set Nat)
    (h : p • X = Y) : Conjugate p (Block X) = Block Y :=
  SubMulAction.fixingSubgroup_map_conj_eq (by rw [Set.smul_set_compl, h])

private theorem blockSwapBlocks (i : Fin 4) :
    blockSwap • Blocks i = Blocks (Equiv.swap 1 2 i) := by
  have h (j : Fin 4) {x : Nat} (hx : x ∈ Blocks j) :
      blockSwap.1 x ∈ Blocks (Equiv.swap 1 2 j) := by
    change 3 * (j : Nat) + 1 ≤ x ∧ x ≤ 3 * (j : Nat) + 3 at hx
    change 3 * ((Equiv.swap 1 2 j : Fin 4) : Nat) + 1 ≤ blockSwap.1 x ∧
      blockSwap.1 x ≤ 3 * ((Equiv.swap 1 2 j : Fin 4) : Nat) + 3
    obtain ⟨hlo, hhi⟩ := hx
    fin_cases j <;> norm_num at hlo hhi <;> interval_cases x <;> decide
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, blockSwapInvolutive]
  change blockSwap.1 x ∈ Blocks i ↔ x ∈ Blocks (Equiv.swap 1 2 i)
  constructor
  · intro hx
    have he : blockSwap.1 (blockSwap.1 x) = x := by
      have he' : blockSwap⁻¹.1 (blockSwap.1 x) = x := blockSwap.1.symm_apply_apply x
      rw [blockSwapInvolutive] at he'
      exact he'
    exact he ▸ h i hx
  · intro hx
    simpa only [Equiv.swap_apply_self] using h (Equiv.swap 1 2 i) hx

private theorem blockSwapNormalizes :
    Conjugate blockSwap (⨆ i, Block (Blocks i)) = ⨆ i, Block (Blocks i) := by
  unfold Conjugate
  rw [Subgroup.map_iSup]
  have he (i : Fin 4) :
      (Block (Blocks i)).map (MulAut.conj blockSwap).toMonoidHom =
        Block (Blocks (Equiv.swap 1 2 i)) :=
    conjugateBlock blockSwap _ _ (blockSwapBlocks i)
  simp only [he]
  apply le_antisymm
  · exact iSup_le fun i => le_iSup (fun j => Block (Blocks j)) (Equiv.swap 1 2 i)
  · refine iSup_le fun i => ?_
    obtain ⟨j, rfl⟩ := (Equiv.swap (1 : Fin 4) 2).surjective i
    exact le_iSup (fun j => Block (Blocks (Equiv.swap 1 2 j))) j

private theorem blockPreserves {X : Set Nat} {p : ↥Finitary} (hp : p ∈ Block X) :
    Set.MapsTo p.1 X X := by
  intro x hx
  by_contra h
  have he : x = p.1 x := p.1.injective (fixOutside hp h).symm
  exact h (he ▸ hx)

private theorem stabilizeFirst {p : ↥Finitary}
    (hp : p ∈ Block (Blocks 0 ∪ Blocks 1) ⊔ Block (Blocks 2 ∪ Blocks 3)) :
    Set.MapsTo p.1 (Blocks 0 ∪ Blocks 1) (Blocks 0 ∪ Blocks 1) := by
  let L := Blocks 0 ∪ Blocks 1
  let R := Blocks 2 ∪ Blocks 3
  have hd : Disjoint L R := by
    rw [Set.disjoint_left]
    rintro x (h0 | h1) (h2 | h3)
    · exact Set.disjoint_left.mp (blocksDisjoint (by decide : (0 : Fin 4) ≠ 2)) h0 h2
    · exact Set.disjoint_left.mp (blocksDisjoint (by decide : (0 : Fin 4) ≠ 3)) h0 h3
    · exact Set.disjoint_left.mp (blocksDisjoint (by decide : (1 : Fin 4) ≠ 2)) h1 h2
    · exact Set.disjoint_left.mp (blocksDisjoint (by decide : (1 : Fin 4) ≠ 3)) h1 h3
  let stabilizer := MulAction.stabilizer (↥Finitary) L
  have stabilizes (q : ↥Finitary) (hq : Set.MapsTo q.1 L L)
      (hqInv : Set.MapsTo (q⁻¹).1 L L) : q ∈ stabilizer := by
    apply MulAction.mem_stabilizer_iff.mpr
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change (q⁻¹).1 x ∈ L ↔ x ∈ L
    exact ⟨fun hx => q.1.apply_symm_apply x ▸ hq hx, fun hx => hqInv hx⟩
  have fixes (q : ↥Finitary) (hq : q ∈ Block R) : Set.MapsTo q.1 L L := by
    intro x hx
    rw [fixOutside hq (Set.disjoint_left.mp hd hx)]
    exact hx
  have hs : Block L ⊔ Block R ≤ stabilizer :=
    sup_le (fun q hq => stabilizes q (blockPreserves hq) (blockPreserves ((Block L).inv_mem hq)))
      (fun q hq => stabilizes q (fixes q hq) (fixes q⁻¹ ((Block R).inv_mem hq)))
  have hp' := MulAction.mem_stabilizer_iff.mp (hs hp)
  intro x hx
  change p • x ∈ L
  rw [← hp']
  exact Set.smul_mem_smul_set hx

end StrongerEmbeddingSlideProof
