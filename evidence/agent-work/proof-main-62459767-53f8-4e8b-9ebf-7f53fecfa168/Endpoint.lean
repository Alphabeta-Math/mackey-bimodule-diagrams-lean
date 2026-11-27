import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
import MackeyDiagrams
import Proofs.MovingMergeDotBackToBranch
import Proofs.BlockwiseGroupElementDotCriterion
import Proofs.FiniteParabolicConjugateBlocks

set_option maxHeartbeats 2000000

namespace StrongerEmbeddingSlideProof

open scoped Pointwise

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
  fixingSubgroup_antitone (↥Finitary) Nat (Set.compl_subset_compl.mpr h)

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

open MackeyDiagrams

section Evaluation

variable {U : Type*} [Group U] {K H G : Subgroup U}

-- The local unit-evaluation argument from RightInputDotSlideObstruction
-- works at a distinct target embedding too. Check it here with that boundary.
private theorem trunkUnit (γ : ConjEmbedding H G) (a : ConjEmbedding K H)
    {target : ConjEmbedding K G} (d : Dot (γ.comp a) target) :
    ((LabelledDrawing.trivalent (TrivalentVertex.mergeUp γ a)).vertical
      (DotLabel.upDrawing (Finsupp.single d (1 : Complex)))).interpret.eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction a) 1 1) 1) =
      Finsupp.single d.element 1 := by
  change (DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval.toLinearMap
    ((Diagram.mergeUp γ a).eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction a) 1 1) 1)) = _
  rw [Diagram.eval_mergeUp_single, map_one, one_mul, DotLabel.eval_upDrawing,
    Diagram.eval_linearUpDot_apply, freeLift_single, one_smul,
    Diagram.eval_upDot_single, one_mul]

-- The output of an up strand has carrier G for every target embedding.
-- Eliminate the output equality before evaluating the transported drawing.
private theorem rightBranchUnit (γ : ConjEmbedding H G) (a b : ConjEmbedding K H)
    (label : DotLabel Complex a b) (target : ConjEmbedding K G)
    (h : γ.comp b = target) :
    let A := ((LabelledDrawing.ordinary (Diagram.id (Word.up γ))).horizontal
      (DotLabel.upDrawing label)).vertical
      (LabelledDrawing.trivalent (TrivalentVertex.mergeUp γ b))
    (LabelledDrawing.interpret
      (Eq.ndrec (motive := fun out =>
        LabelledDrawing Complex ((Word.up γ).tensor (Word.up a)) (Word.up out))
        A h)).eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction a) 1 1) 1) =
      Finsupp.mapDomain (fun term => γ.toHom term.element) label := by
  subst target
  classical
  let outer := Biset.induction γ
  let inner := Biset.induction b
  let merge := (Diagram.mergeUp (R := Complex) γ b).eval.toLinearMap
  let dot := (DotLabel.upDrawing label).interpret.eval
  let straight := (Diagram.id (R := Complex) (Word.up γ)).eval
  let pairAtOne := Biset.pairLinear Complex outer inner (Finsupp.single 1 1)
  change merge ((straight.horizontal dot).toLinearMap
    (Finsupp.single (outer.pair (Biset.induction a) 1 1) 1)) = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change merge (pairAtOne (dot.toLinearMap (Finsupp.single 1 1))) = _
  rw [show dot.toLinearMap (Finsupp.single 1 1) =
      (label.support.toList.map (fun d => label d • Finsupp.single d.element 1)).sum by
    simpa only [dot, one_mul] using DotLabel.upDrawing_basis label (1 : H)]
  change (merge.comp pairAtOne)
      ((label.support.toList.map (fun d => label d • Finsupp.single d.element 1)).sum) = _
  rw [map_list_sum, List.map_map, ← List.sum_toFinset _ label.support.nodup_toList,
    Finset.toList_toFinset, Finsupp.mapDomain, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  change merge (pairAtOne (label d • Finsupp.single d.element 1)) = _
  rw [map_smul, map_smul]
  dsimp only [pairAtOne, merge, outer, inner]
  rw [Biset.pairLinear_single, mul_one, Diagram.eval_mergeUp_single, one_mul,
    Finsupp.smul_single, smul_eq_mul, mul_one]

end Evaluation

end StrongerEmbeddingSlideProof

open StrongerEmbeddingSlideProof

theorem StrongerEmbeddingConditionSlideObstruction : (
let Sfin : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥Sfin
let B : Fin 4 → Set Nat := fun i =>
  Set.Icc (3 * (i : Nat) + 1) (3 * (i : Nat) + 3)
let blockSym : Set Nat → Subgroup U := fun X => _root_.fixingSubgroup U Xᶜ
let K : Subgroup U := iSup (fun i => blockSym (B i))
let H : Subgroup U :=
  blockSym (B 0 ∪ B 1) ⊔ blockSym (B 2 ∪ B 3)
let G : Subgroup U := blockSym (Set.Icc 1 12)
let β : U := 1
let swapInU : (i j : Nat) → i ≠ j → U := fun i j hij =>
  ⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩
let α : U :=
  swapInU 4 7 (by decide) * swapInU 5 8 (by decide) * swapInU 6 9 (by decide)
let conj : U → Subgroup U → Subgroup U := fun σ L =>
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj σ)) L
(∀ σ : U, conj σ K ≤ G → conj (σ * β⁻¹) H ≤ G) ∧
  conj α K = K ∧ α ∉ H ∧
  ∃ (hKH : K ≤ H) (hHG : H ≤ G) (hα : α ∈ G),
    let ιKH : MackeyDiagrams.ConjEmbedding K H :=
      MackeyDiagrams.ConjEmbedding.ofConjugator β (fun k => by
        change (1 : U) * (k : U) * (1 : U)⁻¹ ∈ H
        simpa only [one_mul, inv_one, mul_one] using hKH k.property)
    let ιHG : MackeyDiagrams.ConjEmbedding H G :=
      MackeyDiagrams.ConjEmbedding.ofConjugator 1 (fun h => by
        simpa only [one_mul, inv_one, mul_one] using hHG h.property)
    let incl := MackeyDiagrams.ConjEmbedding.comp ιHG ιKH
    let target : MackeyDiagrams.ConjEmbedding K G :=
      MackeyDiagrams.ConjEmbedding.ofConjugator α (fun k =>
        G.mul_mem (G.mul_mem hα (hHG (hKH k.property))) (G.inv_mem hα))
    let input := MackeyDiagrams.Word.tensor
      (MackeyDiagrams.Word.up ιHG) (MackeyDiagrams.Word.up ιKH)
    ∃ d : MackeyDiagrams.Dot incl target,
      MackeyDiagrams.Dot.element d = (⟨α, hα⟩ : G) ∧
      let onMerged : MackeyDiagrams.LabelledDrawing Complex input (MackeyDiagrams.Word.up target) :=
        MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.trivalent
            (MackeyDiagrams.TrivalentVertex.mergeUp ιHG ιKH))
          (MackeyDiagrams.DotLabel.upDrawing
            (Finsupp.single d (1 : Complex) : MackeyDiagrams.DotLabel Complex incl target))
      ¬ ∃ (b : MackeyDiagrams.ConjEmbedding K H)
          (label : MackeyDiagrams.DotLabel Complex ιKH b)
          (h : MackeyDiagrams.ConjEmbedding.comp ιHG b = target),
        let onRight : MackeyDiagrams.LabelledDrawing Complex input
            (MackeyDiagrams.Word.up (MackeyDiagrams.ConjEmbedding.comp ιHG b)) :=
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal
              (MackeyDiagrams.LabelledDrawing.ordinary
                (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up ιHG)))
              (MackeyDiagrams.DotLabel.upDrawing label))
            (MackeyDiagrams.LabelledDrawing.trivalent
              (MackeyDiagrams.TrivalentVertex.mergeUp ιHG b))
        MackeyDiagrams.ScopedDiagram.eval
            (MackeyDiagrams.LabelledDrawing.interpret
              (Eq.ndrec (motive := fun out =>
                MackeyDiagrams.LabelledDrawing Complex input (MackeyDiagrams.Word.up out))
                onRight h)) =
          MackeyDiagrams.ScopedDiagram.eval
            (MackeyDiagrams.LabelledDrawing.interpret onMerged)
) :=
(by
  classical
  intro Sfin U B blockSym K H G β swapInU α conj
  -- Xiao §3.4, Example 3.5 (ex:stronger-slide-obstruction), archived PDF
  -- p. 11 and published 28 November revision p. 13. The four blocks are
  -- from Example 3.3. The marked positions follow the §3.2 induction merge
  -- drawing (archive p. 9, revision p. 11), which depicts (3.1) with the
  -- outer strand unchanged. The plan supplies no numbered Alphabeta proof.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=13
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#ex:stronger-slide-obstruction
  have eachInside (i : Fin 4) : Blocks i ⊆ Carrier := by
    intro n hn
    change 3 * (i : Nat) + 1 ≤ n ∧ n ≤ 3 * (i : Nat) + 3 at hn
    change 1 ≤ n ∧ n ≤ 12
    have hi := i.isLt
    omega
  have hKH : K ≤ H := by
    change (⨆ i, Block (Blocks i)) ≤
      Block (Blocks 0 ∪ Blocks 1) ⊔ Block (Blocks 2 ∪ Blocks 3)
    refine iSup_le fun i => ?_
    fin_cases i
    · exact (blockMono (fun _ h => Or.inl h)).trans le_sup_left
    · exact (blockMono (fun _ h => Or.inr h)).trans le_sup_left
    · exact (blockMono (fun _ h => Or.inl h)).trans le_sup_right
    · exact (blockMono (fun _ h => Or.inr h)).trans le_sup_right
  have hHG : H ≤ G :=
    sup_le (blockMono (Set.union_subset (eachInside 0) (eachInside 1)))
      (blockMono (Set.union_subset (eachInside 2) (eachInside 3)))
  have hα : α ∈ G := by
    apply (mem_fixingSubgroup_iff _).mpr
    intro x hx
    change ¬ (1 ≤ x ∧ x ≤ 12) at hx
    exact blockSwapFix (by omega)
  have hOutside : α ∉ H := by
    intro h
    have h4 : 4 ∈ Blocks 0 ∪ Blocks 1 := Or.inr (by decide : 4 ∈ Blocks 1)
    have h7 := stabilizeFirst h h4
    have he : blockSwap.1 4 = 7 := by decide
    change blockSwap.1 4 ∈ Blocks 0 ∪ Blocks 1 at h7
    rw [he] at h7
    exact (by decide : 7 ∉ Blocks 0 ∪ Blocks 1) h7
  -- The support claim uses the first part of BlockwiseGroupElementDotCriterion
  -- with the single target block [1,12]. Every source block has three points.
  -- FiniteParabolicConjugateBlocks works in the full permutation group with
  -- ranges on Finset subtypes. The stabilizer conjugation lemma works directly
  -- for these fixing subgroups inside the finitary ambient group.
  refine ⟨?_, blockSwapNormalizes, hOutside, hKH, hHG, hα, ?_⟩
  · intro σ hσ
    have hp := preserveCarrier σ hσ (hKH.trans hHG)
    change Conjugate (σ * (1 : U)⁻¹) H ≤ G
    rw [inv_one, mul_one]
    exact conjugateInside hHG hp
  · intro ιKH ιHG incl target input
    have hOuter (x : H) : (ιHG.toHom x : U) = (x : U) := by
      dsimp only [ιHG]
      simp only [MackeyDiagrams.ConjEmbedding.ofConjugator_apply, one_mul, inv_one, mul_one]
    have hIncl (k : K) :
        (incl.toHom k : U) = (1 : U) * (k : U) * (1 : U)⁻¹ := by
      change (ιHG.toHom (ιKH.toHom k) : U) = _
      rw [hOuter]
      rfl
    -- The right-multiplication convention uses the relative element α⁻¹.
    -- Here the three disjoint transpositions make α⁻¹ equal to α.
    let d : MackeyDiagrams.Dot incl target :=
      MackeyDiagrams.Dot.ofRepresentatives 1 α hIncl (fun _ => rfl)
        (by
          change (1 : ↥Finitary) * blockSwap⁻¹ ∈ G
          rw [one_mul, blockSwapInvolutive]
          exact hα)
    have hd : d.element = (⟨α, hα⟩ : G) := by
      apply Subtype.ext
      change (1 : U) * α⁻¹ = α
      rw [one_mul]
      exact blockSwapInvolutive
    refine ⟨d, hd, ?_⟩
    intro onMerged
    rintro ⟨b, label, boundary, heval⟩
    -- MovingMergeDotBackToBranch gives the singleton slide criterion. The
    -- owner-clarified right mark has arbitrary finite coefficients. Evaluate
    -- both typed composites on the balanced unit tensor, using (3.1)'s
    -- multiplication and the finite-label basis formula.
    let units := Finsupp.single
      ((MackeyDiagrams.Biset.induction ιHG).pair (MackeyDiagrams.Biset.induction ιKH) 1 1)
      (1 : Complex)
    have ht := trunkUnit ιHG ιKH d
    have hr := rightBranchUnit ιHG ιKH b label target boundary
    have hAtUnits := congrArg (fun f => MackeyDiagrams.Biset.Hom.toLinearMap f units) heval
    change _ = MackeyDiagrams.Biset.Hom.toLinearMap onMerged.interpret.eval units at hAtUnits
    dsimp only [onMerged] at hAtUnits
    rw [hr, ht] at hAtUnits
    have hzero : Finsupp.mapDomain (fun term => ιHG.toHom term.element) label d.element = 0 := by
      by_contra hnonzero
      have hs := Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hnonzero)
      obtain ⟨term, _, hterm⟩ := Finset.mem_image.mp hs
      apply hOutside
      have hval := congrArg Subtype.val hterm
      rw [hOuter, hd] at hval
      change (term.element : U) = α at hval
      rw [← hval]
      exact term.element.property
    have hCoeff := DFunLike.congr_fun hAtUnits d.element
    change Finsupp.mapDomain (fun term => ιHG.toHom term.element) label d.element =
      Finsupp.single d.element (1 : Complex) d.element at hCoeff
    rw [hzero, Finsupp.single_eq_same] at hCoeff
    exact zero_ne_one hCoeff)

#print axioms StrongerEmbeddingConditionSlideObstruction
