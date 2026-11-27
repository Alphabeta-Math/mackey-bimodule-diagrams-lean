import MackeyDiagrams
import Proofs.ParallelReidemeisterTwoInduction
import Proofs.FiniteParabolicJoinBlocks

set_option maxHeartbeats 2000000

namespace ParabolicSharedRegionParallelInductionProof

open MackeyDiagrams

private abbrev blockSym (X : Finset Nat) : Subgroup (Equiv.Perm Nat) :=
  (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X)).range

private abbrev HasBlocks (L : Subgroup (Equiv.Perm Nat)) : Prop :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    L = ⨆ i, blockSym (blocks i)

private theorem fixesOutsideBlocks {L : Subgroup (Equiv.Perm Nat)} (hL : HasBlocks L) :
    ∃ X : Finset Nat, ∀ σ ∈ L, ∀ x ∉ X, (σ : Equiv.Perm Nat) x = x := by
  classical
  obtain ⟨n, blocks, _, _, rfl⟩ := hL
  let X := Finset.univ.biUnion blocks
  refine ⟨X, fun σ hσ x hx => ?_⟩
  refine Subgroup.iSup_induction (fun i => blockSym (blocks i))
    (C := fun f => f x = x) hσ ?_ rfl ?_
  · rintro i f ⟨f', rfl⟩
    exact Equiv.Perm.ofSubtype_apply_of_not_mem f' (fun hi =>
      hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩))
  · intro f g hf hg
    rw [Equiv.Perm.mul_apply, hg, hf]

-- Alphabeta Math, "Transpositions generate the symmetric group", steps 1.1,
-- 2.1 and 3.1. Use permutation induction on the finite subtype in place of
-- cycle factorization. Identity extension and conjugation carry each genuine
-- swap to a genuine swap of Nat, so generated-subgroup minimality applies.
-- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
private theorem conjugate_le_swapClosure
    {K L : Subgroup (Equiv.Perm Nat)} (hK : HasBlocks K) (g : Equiv.Perm Nat)
    (hle : K.map (MulAut.conj g).toMonoidHom ≤ L) :
    K.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure {σ : Equiv.Perm Nat | σ.IsSwap ∧ σ ∈ L} := by
  let S := {σ : Equiv.Perm Nat | σ.IsSwap ∧ σ ∈ L}
  obtain ⟨n, blocks, _, _, rfl⟩ := hK
  rw [Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  let extend := Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ blocks i)
  let f := (MulAut.conj g).toMonoidHom.comp extend
  rintro σ ⟨_, ⟨τ, rfl⟩, rfl⟩
  change f τ ∈ Subgroup.closure S
  refine τ.swap_induction_on (motive := fun π => f π ∈ Subgroup.closure S) ?_ ?_
  · rw [map_one]
    exact (Subgroup.closure S).one_mem
  · intro π x y hxy hπ
    rw [map_mul]
    refine (Subgroup.closure S).mul_mem (Subgroup.subset_closure (show f (Equiv.swap x y) ∈ S from ?_)) hπ
    refine ⟨?_, hle ⟨extend (Equiv.swap x y), le_iSup
      (fun i => blockSym (blocks i)) i ⟨Equiv.swap x y, rfl⟩, rfl⟩⟩
    refine ⟨g x, g y, fun he => hxy (Subtype.ext (g.injective he)), ?_⟩
    change MulAut.conj g (Equiv.Perm.ofSubtype (Equiv.swap x y)) = _
    rw [Equiv.Perm.ofSubtype_swap_eq]
    exact Equiv.symm_trans_swap_trans (x : Nat) (y : Nat) g

-- The binary block formula on the route takes two partitions of one carrier.
-- For the entire family, use the orbit blocks of the swap-generated join on
-- the finite carrier supplied by G. This includes the empty family and avoids
-- padding each pair of partitions with singleton blocks before a binary join.
private theorem blocksOfSwapClosure
    (S : Set (Equiv.Perm Nat)) (hS : ∀ σ ∈ S, σ.IsSwap) (X : Finset Nat)
    (hX : ∀ σ ∈ Subgroup.closure S, ∀ x ∉ X, (σ : Equiv.Perm Nat) x = x) :
    HasBlocks (Subgroup.closure S) := by
  classical
  let L := Subgroup.closure S
  let r := Setoid.comap (fun x : ↥X => (x : Nat)) (MulAction.orbitRel L Nat)
  let blocks (q : Quotient r) : Finset Nat :=
    (Finset.univ.filter (fun x : ↥X => Quotient.mk r x = q)).image Subtype.val
  have memBlock (q : Quotient r) (x : Nat) :
      x ∈ blocks q ↔ ∃ hx : x ∈ X, Quotient.mk r ⟨x, hx⟩ = q := by
    constructor
    · intro hx
      obtain ⟨⟨y, hy⟩, hq, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨hy, (Finset.mem_filter.mp hq).2⟩
    · rintro ⟨hx, hq⟩
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
  have orbit_of_same {q : Quotient r} {x y : Nat} (hx : x ∈ blocks q)
      (hy : y ∈ blocks q) : y ∈ MulAction.orbit L x := by
    obtain ⟨hx', hxq⟩ := (memBlock q x).mp hx
    obtain ⟨hy', hyq⟩ := (memBlock q y).mp hy
    have hrel : r ⟨y, hy'⟩ ⟨x, hx'⟩ := Quotient.exact (hyq.trans hxq.symm)
    exact MulAction.orbitRel_apply.mp (show MulAction.orbitRel L Nat y x from hrel)
  have blocks_le : (⨆ q, blockSym (blocks q)) ≤ L := by
    refine iSup_le fun q => ?_
    rintro σ ⟨τ, rfl⟩
    apply (mem_closure_isSwap hS).mpr
    have fixes (x : Nat) (hx : x ∉ blocks q) : Equiv.Perm.ofSubtype τ x = x :=
      Equiv.Perm.ofSubtype_apply_of_not_mem τ hx
    refine ⟨(blocks q).finite_toSet.subset (fun x hx => ?_), fun x => ?_⟩
    · by_contra hn
      exact hx (MulAction.mem_fixedBy.mpr (fixes x hn))
    · by_cases hx : x ∈ blocks q
      · exact orbit_of_same hx ((Equiv.Perm.ofSubtype_apply_mem_iff_mem τ x).mpr hx)
      · rw [fixes x hx]
        exact MulAction.mem_orbit_self x
  have le_blocks : L ≤ ⨆ q, blockSym (blocks q) := by
    let J := ⨆ q, blockSym (blocks q)
    let T := {σ : Equiv.Perm Nat | σ.IsSwap ∧ σ ∈ J}
    have hTJ : Subgroup.closure T ≤ J := (Subgroup.closure_le _).2 (fun _ ht => ht.2)
    intro σ hσ
    apply hTJ
    refine (mem_closure_isSwap (S := T) (fun _ ht => ht.1)).mpr
      ⟨((mem_closure_isSwap hS).mp hσ).1, fun x => ?_⟩
    by_cases he : σ x = x
    · rw [he]
      exact MulAction.mem_orbit_self x
    · have hx : x ∈ X := by
        by_contra hn
        exact he (hX σ hσ x hn)
      have hy : σ x ∈ X := by
        by_contra hn
        have hfix : σ (σ x) = σ x := hX σ hσ (σ x) hn
        exact he (σ.injective hfix)
      let q := Quotient.mk r ⟨x, hx⟩
      have hq : Quotient.mk r ⟨σ x, hy⟩ = q := by
        apply Quotient.sound
        exact MulAction.orbitRel_apply.mpr
          (MulAction.mem_orbit_iff.mpr ⟨⟨σ, hσ⟩, rfl⟩)
      have hxq := (memBlock q x).mpr ⟨hx, rfl⟩
      have hyq := (memBlock q (σ x)).mpr ⟨hy, hq⟩
      have hswap : Equiv.swap x (σ x) ∈ blockSym (blocks q) :=
        ⟨Equiv.swap ⟨x, hxq⟩ ⟨σ x, hyq⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
      exact MulAction.mem_orbit_iff.mpr
        ⟨⟨Equiv.swap x (σ x), Subgroup.subset_closure
          (show Equiv.swap x (σ x) ∈ T from
            ⟨⟨x, σ x, Ne.symm he, rfl⟩, le_iSup (fun q => blockSym (blocks q)) q hswap⟩)⟩,
          Equiv.swap_apply_left _ _⟩
  let _ : Fintype (Quotient r) := Fintype.ofFinite _
  let e := (Fintype.equivFin (Quotient r)).symm
  refine ⟨Fintype.card (Quotient r), blocks ∘ e, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨x, hx⟩ := Quotient.mk_surjective (e i)
    exact ⟨x, (memBlock (e i) x).2 ⟨x.property, hx⟩⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hx', hi⟩ := (memBlock (e i) x).mp hx
    obtain ⟨hy', hj⟩ := (memBlock (e j) x).mp hy
    exact hij (e.injective (hi.symm.trans hj))
  · exact (le_antisymm le_blocks blocks_le).trans
      (e.iSup_comp (g := fun q => blockSym (blocks q))).symm

private theorem sameComposites {U : Type*} [Group U] {G K B P : Subgroup U}
    {γ δ : U} (hγ : ∀ b : B, γ * (b : U) * γ⁻¹ ∈ G)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ B)
    (h1 : ∀ p : P, (1 : U) * (p : U) * (1 : U)⁻¹ ∈ G)
    (hγδ : ∀ k : K, (γ * δ) * (k : U) * (γ * δ)⁻¹ ∈ P) :
    (ConjEmbedding.ofConjugator γ hγ).comp (ConjEmbedding.ofConjugator δ hδ) =
      (ConjEmbedding.ofConjugator 1 h1).comp (ConjEmbedding.ofConjugator (γ * δ) hγδ) := by
  apply ConjEmbedding.ext
  apply MonoidHom.ext
  intro k
  apply Subtype.ext
  simp only [ConjEmbedding.comp_apply, ConjEmbedding.ofConjugator_apply, one_mul, inv_one, mul_one]
  group

private theorem composeTransport {U : Type*} [Group U] {G K : Subgroup U}
    {bottom middle newMiddle top : ConjEmbedding K G} (h : middle = newMiddle)
    (x : DotLabel Complex bottom middle) (y : DotLabel Complex middle top) :
    DotLabel.compose
      (Eq.ndrec (motive := fun m => DotLabel Complex bottom m) x h)
      (Eq.ndrec (motive := fun m => DotLabel Complex m top) y h) =
        DotLabel.compose x y := by
  cases h
  rfl

end ParabolicSharedRegionParallelInductionProof
