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
    apply (Subgroup.closure S).mul_mem _ hπ
    apply Subgroup.subset_closure
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
  -- Every nonfixed point of a join element and its image lie in one block.
  -- Their internal swap gives an orbit witness in the subgroup generated
  -- by genuine swaps from the block factors.
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

theorem ParabolicSharedRegionParallelInduction : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) := fun X =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))
let parabolic : Subgroup U → Prop := fun L =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) L = iSup (fun i => blockSym (blocks i))
∀ {ι : Type*} [Finite ι] (G K : Subgroup U) (H B H' : ι → Subgroup U),
  parabolic G → parabolic K →
  (∀ i, parabolic (H i)) → (∀ i, parabolic (B i)) → (∀ i, parabolic (H' i)) →
  ∀ (α β γ δ α' β' : ι → U)
    (hα : ∀ i (h : H i), α i * (h : U) * (α i)⁻¹ ∈ G)
    (hβ : ∀ i (k : K), β i * (k : U) * (β i)⁻¹ ∈ H i)
    (hγ : ∀ i (b : B i), γ i * (b : U) * (γ i)⁻¹ ∈ G)
    (hδ : ∀ i (k : K), δ i * (k : U) * (δ i)⁻¹ ∈ B i)
    (hα' : ∀ i (h : H' i), α' i * (h : U) * (α' i)⁻¹ ∈ G)
    (hβ' : ∀ i (k : K), β' i * (k : U) * (β' i)⁻¹ ∈ H' i),
  let v := fun i => γ i * δ i
  let image := fun i => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (v i))) K
  let P := Subgroup.closure (Set.iUnion fun i => (image i : Set U))
  IsLeast {Q : Subgroup U | Q ≤ G ∧ parabolic Q ∧ ∀ i, image i ≤ Q} P ∧
  ∃ hP : P ≤ G,
    let inclusion := MackeyDiagrams.ConjEmbedding.ofConjugator (H := P) (G := G)
      (1 : U) (fun p => by simpa only [one_mul, inv_one, mul_one] using hP p.property)
    let throughP := fun i =>
      MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := P) (v i) (fun k => by
        apply Subgroup.subset_closure
        exact Set.mem_iUnion.mpr ⟨i, (show (MulAut.conj (v i)) (k : U) ∈ image i from
          ⟨(k : U), k.property, rfl⟩)⟩)
    let evalDrawing {p q : MackeyDiagrams.Word G K}
        (drawing : MackeyDiagrams.LabelledDrawing Complex p q) :=
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
    ∀ i,
      let a := MackeyDiagrams.ConjEmbedding.ofConjugator (α i) (hα i)
      let b := MackeyDiagrams.ConjEmbedding.ofConjugator (β i) (hβ i)
      let c := MackeyDiagrams.ConjEmbedding.ofConjugator (γ i) (hγ i)
      let d := MackeyDiagrams.ConjEmbedding.ofConjugator (δ i) (hδ i)
      let a' := MackeyDiagrams.ConjEmbedding.ofConjugator (α' i) (hα' i)
      let b' := MackeyDiagrams.ConjEmbedding.ofConjugator (β' i) (hβ' i)
      let bottom := MackeyDiagrams.ConjEmbedding.comp a b
      let middle := MackeyDiagrams.ConjEmbedding.comp c d
      let top := MackeyDiagrams.ConjEmbedding.comp a' b'
      let newMiddle := MackeyDiagrams.ConjEmbedding.comp inclusion (throughP i)
      ∃ sameMiddle : middle = newMiddle,
        ∀ (x : MackeyDiagrams.DotLabel Complex bottom middle)
          (y : MackeyDiagrams.DotLabel Complex middle top),
          let newX := Eq.ndrec
            (motive := fun m => MackeyDiagrams.DotLabel Complex bottom m) x sameMiddle
          let newY := Eq.ndrec
            (motive := fun m => MackeyDiagrams.DotLabel Complex m top) y sameMiddle
          let original := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.parallelUp a b c d (MackeyDiagrams.DotLabel.terms x))
            (MackeyDiagrams.LabelledDrawing.parallelUp c d a' b' (MackeyDiagrams.DotLabel.terms y))
          let shared := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.parallelUp a b inclusion (throughP i)
              (MackeyDiagrams.DotLabel.terms newX))
            (MackeyDiagrams.LabelledDrawing.parallelUp inclusion (throughP i) a' b'
              (MackeyDiagrams.DotLabel.terms newY))
          let merge := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
            (MackeyDiagrams.TrivalentVertex.mergeUp a b)
          let productDot := MackeyDiagrams.DotLabel.upDrawing (MackeyDiagrams.DotLabel.compose x y)
          let split := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
            (MackeyDiagrams.TrivalentVertex.splitUp a' b')
          let merged := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.vertical merge productDot) split
          evalDrawing original = evalDrawing shared ∧
          evalDrawing shared = evalDrawing merged
) :=
(by
  classical
  open ParabolicSharedRegionParallelInductionProof MackeyDiagrams in
  intro finitary U blockSym parabolic ι _ G K H B H' hG hK _ _ _
    α β γ δ α' β' hα hβ hγ hδ hα' hβ' v image P
  -- Xiao, Proposition 8.4, is on pp. 36–37 of the archived original
  -- source/mackey-bimodules.pdf
  -- (SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and pp. 38–39 of the revised published PDF at
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- (SHA-256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- These checksums correct the saved source note's byte-identity claim.
  -- Both rendered induction rows fix the outer words, change the middle
  -- labels from γᵢ, δᵢ to 1, vᵢ, and retain both marks.
  have image_le (i : ι) : image i ≤ P :=
    fun g hg => Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, hg⟩)
  have least (Q : Subgroup U) (hQ : ∀ i, image i ≤ Q) : P ≤ Q := by
    apply (Subgroup.closure_le Q).mpr
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact hQ i hi
  have inG (i : ι) (k : K) : v i * (k : U) * (v i)⁻¹ ∈ G := by
    have he : v i * (k : U) * (v i)⁻¹ =
        γ i * (δ i * (k : U) * (δ i)⁻¹) * (γ i)⁻¹ := by
      change (γ i * δ i) * (k : U) * (γ i * δ i)⁻¹ = _
      group
    rw [he]
    exact hγ i ⟨_, hδ i k⟩
  have hPG : P ≤ G := least G (fun i => by
    rintro _ ⟨k, hk, rfl⟩
    exact inG i ⟨k, hk⟩)
  let f := Subgroup.subtype finitary
  let L := P.map f
  have mapImage (i : ι) :
      (image i).map f = (K.map f).map (MulAut.conj (f (v i))).toMonoidHom := by
    change ((K.map (MulAut.conj (v i)).toMonoidHom).map f) = _
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have mapJoin : L = ⨆ i, (image i).map f := by
    change P.map f = _
    rw [show P = ⨆ i, image i from (Subgroup.iSup_eq_closure image).symm, Subgroup.map_iSup]
  have hParabolic : parabolic P := by
    change HasBlocks L
    let S := {σ : Equiv.Perm Nat | σ.IsSwap ∧ σ ∈ L}
    have swapGen : L = Subgroup.closure S := by
      have hSL : S ⊆ (L : Set (Equiv.Perm Nat)) := fun _ h => h.2
      apply le_antisymm _ ((Subgroup.closure_le L).mpr hSL)
      rw [mapJoin]
      refine iSup_le fun i => ?_
      have hle : (image i).map f ≤ L := Subgroup.map_mono (image_le i)
      rw [mapImage i] at hle ⊢
      exact conjugate_le_swapClosure hK _ hle
    obtain ⟨X, hX⟩ := fixesOutsideBlocks hG
    have fixes : ∀ σ ∈ L, ∀ x ∉ X, (σ : Equiv.Perm Nat) x = x :=
      fun σ hσ => hX σ ((Subgroup.map_mono hPG : L ≤ G.map f) hσ)
    rw [swapGen] at fixes ⊢
    exact blocksOfSwapClosure S (fun _ h => h.1) X fixes
  refine ⟨⟨⟨hPG, hParabolic, image_le⟩, fun Q hQ => least Q hQ.2.2⟩, hPG, ?_⟩
  intro inclusion throughP evalDrawing i a b c d a' b' bottom middle top newMiddle
  have same : middle = newMiddle :=
    sameComposites (hγ i) (hδ i) _ _
  refine ⟨same, ?_⟩
  intro x y newX newY original shared merge productDot split merged
  -- Use Theorem 5.4 via the finite-label clause of the registered induction
  -- result. That clause checks the middle merge/split inverse and applies
  -- DotLabel.upDrawing_compose within Biset.Hom.merge_dot_split_comp.
  -- Equality of the composite embeddings transports the complete
  -- labels. Equality induction preserves their ordered product, including
  -- zero labels, while both crossing drawings retain their own middle word.
  have oldFormula : evalDrawing original = evalDrawing merged :=
    ((ParallelReidemeisterTwoInduction G K (H i) (B i) (H' i)
      (α i) (β i) (γ i) (δ i) (α' i) (β' i)
      (hα i) (hβ i) (hγ i) (hδ i) (hα' i) (hβ' i)).2.1 x y).1
  have hIncl : ∀ p : P, (1 : U) * (p : U) * (1 : U)⁻¹ ∈ G := by
    intro p
    simpa only [one_mul, inv_one, mul_one] using hPG p.property
  have hThrough : ∀ k : K, v i * (k : U) * (v i)⁻¹ ∈ P := fun k =>
    image_le i ⟨(k : U), k.property, rfl⟩
  have newFormula :=
    ((ParallelReidemeisterTwoInduction G K (H i) P (H' i)
      (α i) (β i) 1 (v i) (α' i) (β' i)
      (hα i) (hβ i) hIncl hThrough (hα' i) (hβ' i)).2.1 newX newY).1
  change evalDrawing shared = evalDrawing (LabelledDrawing.vertical
    (LabelledDrawing.vertical merge (DotLabel.upDrawing (DotLabel.compose newX newY))) split)
    at newFormula
  have sameProduct : DotLabel.compose newX newY = DotLabel.compose x y :=
    composeTransport same x y
  rw [sameProduct] at newFormula
  exact ⟨oldFormula.trans newFormula.symm, newFormula⟩)
