import MackeyDiagrams
import Proofs.ExtremalParabolicsOfFiniteGroup
import Proofs.MixedCrossingsThroughSmallerGroup
import Proofs.MackeyInclusionAndProjectionCrossings

set_option maxHeartbeats 2000000

namespace LargestCommonMixedCrossingParabolicProof

open MackeyDiagrams

private abbrev finitary := Subgroup.closure {g : Equiv.Perm Nat | g.IsSwap}
private abbrev blockSym (X : Finset Nat) : Subgroup (Equiv.Perm Nat) :=
  (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X)).range
private abbrev HasBlocks (H : Subgroup (Equiv.Perm Nat)) : Prop :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H = ⨆ i, blockSym (blocks i)

private theorem finiteOfBlocks {H : Subgroup (Equiv.Perm Nat)} (hH : HasBlocks H) :
    Finite H := by
  classical
  obtain ⟨n, blocks, _, _, rfl⟩ := hH
  let X := Finset.univ.biUnion blocks
  have fixes (g : ↥(⨆ i, blockSym (blocks i))) (x : Nat) (hx : x ∉ X) :
      (g : Equiv.Perm Nat) x = x := by
    refine Subgroup.iSup_induction (fun i => blockSym (blocks i))
      (C := fun f => f x = x) g.property ?_ rfl ?_
    · rintro i f ⟨f', rfl⟩
      exact Equiv.Perm.ofSubtype_apply_of_not_mem f' fun hi =>
        hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
    · intro f g hf hg
      rw [Equiv.Perm.mul_apply, hg, hf]
  have preserves (g : ↥(⨆ i, blockSym (blocks i))) (x : Nat) :
      (g : Equiv.Perm Nat) x ∈ X ↔ x ∈ X := by
    constructor
    · intro hgx
      by_contra hx
      exact hx (fixes g x hx ▸ hgx)
    · intro hx
      by_contra hgx
      exact hgx (show (g : Equiv.Perm Nat) x ∈ X from
        ((g : Equiv.Perm Nat).injective (fixes g _ hgx)).symm ▸ hx)
  refine Finite.of_injective
    (fun g : ↥(⨆ i, blockSym (blocks i)) => (g : Equiv.Perm Nat).subtypePerm (preserves g)) ?_
  intro g h heq
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ X
  · exact congrArg (fun p : Equiv.Perm ↥X => (p ⟨x, hx⟩).val) heq
  · rw [fixes g x hx, fixes h x hx]

private theorem greatestSwapClosure (P : Subgroup finitary) [Finite P] :
    IsGreatest {S : Subgroup finitary | HasBlocks (S.map finitary.subtype) ∧ S ≤ P}
      (Subgroup.closure {g : finitary | g ∈ P ∧ (g : Equiv.Perm Nat).IsSwap}) := by
  classical
  let f := finitary.subtype
  let T : Set finitary := {g | g ∈ P ∧ (g : Equiv.Perm Nat).IsSwap}
  let L := Subgroup.closure T
  let Q := P.map f
  let L' := Subgroup.closure {g : Equiv.Perm Nat | g ∈ Q ∧ g.IsSwap}
  have hQ : Q ≤ finitary := by
    rintro g ⟨x, _, rfl⟩
    exact x.property
  let : Finite Q := Finite.of_surjective (fun x : P => (⟨f x.val, ⟨x.val, x.property, rfl⟩⟩ : Q))
    (by rintro ⟨g, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  have hMap : L.map f = L' := by
    change (Subgroup.closure T).map f = _
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hs⟩
    · rintro ⟨⟨x, hx, rfl⟩, hs⟩
      exact ⟨x, ⟨hx, hs⟩, rfl⟩
  have equivalent (H : Subgroup (Equiv.Perm Nat)) :
      HasBlocks H ↔ ∃ X : Finset Nat, ∃ (n : Nat) (blocks : Fin n → Finset Nat),
        (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
        (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ H = ⨆ i, blockSym (blocks i) := by
    constructor
    · rintro ⟨n, blocks, hne, hd, heq⟩
      exact ⟨Finset.univ.biUnion blocks, n, blocks, hne, hd,
        fun m => by simp only [Finset.mem_biUnion, Finset.mem_univ, true_and], heq⟩
    · rintro ⟨_, n, blocks, hne, hd, _, heq⟩
      exact ⟨n, blocks, hne, hd, heq⟩
  have hExt := (ExtremalParabolicsOfFiniteGroup Q hQ).1
  refine ⟨⟨?_, (Subgroup.closure_le P).mpr fun _ hg => hg.1⟩, ?_⟩
  · exact hMap.symm ▸ (equivalent L').mpr hExt.1.1
  · rintro S ⟨hBlocks, hSP⟩
    have hImage : S.map f ≤ L' :=
      hExt.2 ⟨(equivalent (S.map f)).mp hBlocks, Subgroup.map_mono hSP⟩
    intro g hg
    have hg' : f g ∈ L.map f := hMap ▸ hImage ⟨g, hg, rfl⟩
    obtain ⟨x, hx, hxeq⟩ := hg'
    exact (show x = g from Subtype.val_injective hxeq) ▸ hx

private theorem compactOuterEval {U : Type*} [Group U] {K H G S : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding S K)
    (r : ConjEmbedding S H) (d : Dot (a.comp l) (b.comp r))
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (LabelledDrawing.vertical (LabelledDrawing.compactProjection a b l r [(1, ⟨d, hf⟩)])
      (LabelledDrawing.mixedMultiplication a b l r [(1, d)])).interpret.eval =
    (Diagram.vertical (Diagram.mixedProjection (R := Complex) a b l r d hf)
      (Diagram.mixedMultiplication a b l r d)).eval := by
  exact congrArg₂ (fun p i => p.vertical i)
    (MackeyCrossingProof.compact_projection a b l r d hf)
    (MackeyCrossingProof.compact_inclusion a b l r d)

end LargestCommonMixedCrossingParabolicProof

open MackeyDiagrams LargestCommonMixedCrossingParabolicProof

theorem LargestCommonMixedCrossingParabolic : (
let U := ↥(Subgroup.closure {g : Equiv.Perm Nat | Equiv.Perm.IsSwap g})
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun X => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X))
let parabolic : Subgroup U → Prop := fun S =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype _) S = iSup (fun i => blockSym (blocks i))
∀ (K H G : Subgroup U) (α β : U),
  parabolic K → parabolic H → parabolic G →
  let conjugate := fun (c : U) (S : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
  ∀ (hα : conjugate α K ≤ G) (hβ : conjugate β H ≤ G),
    let a : MackeyDiagrams.ConjEmbedding K G :=
      MackeyDiagrams.ConjEmbedding.ofConjugator α
        (fun k => hα ⟨(k : U), k.property, rfl⟩)
    let b : MackeyDiagrams.ConjEmbedding H G :=
      MackeyDiagrams.ConjEmbedding.ofConjugator β
        (fun h => hβ ⟨(h : U), h.property, rfl⟩)
    let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
    let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b)
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let Lj := fun j : J => conjugate α K ⊓ conjugate ((σ j : U) * β) H
      let left := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := K) α⁻¹ (by
          intro ℓ
          obtain ⟨k, hk, heq⟩ := (hS ℓ.property).1
          change α * k * α⁻¹ = (ℓ : U) at heq
          rw [← heq]
          change k ∈ K at hk
          convert hk using 1
          group)
      let right := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := H)
          (β⁻¹ * (σ j : U)⁻¹) (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := (hS ℓ.property).2
            change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
            rw [← heq]
            change h ∈ H at hh
            convert hh using 1
            group)
      let dot := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (left j S hS))
          (MackeyDiagrams.ConjEmbedding.comp b (right j S hS)) from
          ⟨σ j, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (σ j : U) =
              (σ j : U) * (β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
      let M := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.down a)
        (MackeyDiagrams.Word.up b)
      let finiteFibers := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        ∀ z : (MackeyDiagrams.Word.basis M).carrier,
          Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b
            (left j S hS) (right j S hS) (dot j S hS) w = z}
      let outer := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
          (hf : finiteFibers j S hS) =>
        show MackeyDiagrams.LabelledDrawing Complex M M from
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.compactProjection a b (left j S hS) (right j S hS)
              [(1, ⟨dot j S hS, hf⟩)])
            (MackeyDiagrams.LabelledDrawing.mixedMultiplication a b (left j S hS) (right j S hS)
              [(1, dot j S hS)])
      ∀ (J₀ : Set J),
        let I := {j : J // j ∈ J₀}
        ∀ (j₀ : I),
          let C := G ⊓ Subgroup.centralizer
            (Set.range (fun j : I => (σ j₀.val : U) * (σ j.val : U)⁻¹))
          let P := (iInf (fun j : I => Lj j.val)) ⊓ C
          let L := Subgroup.closure {g : U | g ∈ P ∧ Equiv.Perm.IsSwap (Subtype.val g)}
          let hL : ∀ j : I, L ≤ Lj j.val := fun j =>
            le_trans ((Subgroup.closure_le P).mpr (fun _ hg => hg.1))
              (le_trans inf_le_left (iInf_le (fun i : I => Lj i.val) j))
          let admissible := fun S : Subgroup U =>
            parabolic S ∧
              ∃ hS : ∀ j : I, S ≤ Lj j.val,
                ∀ i j : I,
                  left i.val S (hS i) = left j.val S (hS j) ∧
                  right i.val S (hS i) = right j.val S (hS j)
          IsGreatest {S : Subgroup U | admissible S} L ∧
          (∀ S : Subgroup U, admissible S → ∀ j : I,
            Subgroup.relIndex L (Lj j.val) ≤ Subgroup.relIndex S (Lj j.val)) ∧
          (∃ (finite : Fintype I)
              (hfL : ∀ j : I, finiteFibers j.val L (hL j))
              (hfJ : ∀ j : I, finiteFibers j.val (Lj j.val) (le_refl (Lj j.val))),
            let indices : Finset I := @Finset.univ I finite
            let restricted := fun j : I => MackeyDiagrams.LabelledDrawing.scale
              ((Subgroup.relIndex L (Lj j.val) : Complex)⁻¹) (outer j.val L (hL j) (hfL j))
            let usual := fun j : I => outer j.val (Lj j.val) (le_refl (Lj j.val)) (hfJ j)
            let restrictedSum : MackeyDiagrams.IndexedDrawing Complex M M I :=
              MackeyDiagrams.IndexedDrawing.mk indices restricted
            let usualSum : MackeyDiagrams.IndexedDrawing Complex M M I :=
              MackeyDiagrams.IndexedDrawing.mk indices usual
            MackeyDiagrams.IndexedDrawing.eval restrictedSum =
              MackeyDiagrams.IndexedDrawing.eval usualSum)
) :=
(by
  classical
  intro U blockSym parabolic K H G α β _ _ hG conjugate hα hβ a b A B J σ hσ
    Lj left right dot M finiteFibers outer J₀ I j₀ C P L hL admissible
  -- Xiao, Proposition 8.3, archived PDF p. 35 and 28 November revision p. 37.
  -- The reviewed plan records no numbered Alphabeta Math proof for this item.
  -- First reduce common labels to subgroup containment. The
  -- representative of the fixed left label is independent of the summand.
  have labelCriterion (S : Subgroup U) (hS : ∀ j : I, S ≤ Lj j.val) (j : I) :
      right j₀.val S (hS j₀) = right j.val S (hS j) ↔
        (σ j₀.val : U) * (σ j.val : U)⁻¹ ∈ Subgroup.centralizer (S : Set U) := by
    have hratio : (β⁻¹ * (σ j₀.val : U)⁻¹)⁻¹ * (β⁻¹ * (σ j.val : U)⁻¹) =
        (σ j₀.val : U) * (σ j.val : U)⁻¹ := by group
    exact (ConjEmbedding.ofConjugator_eq_iff _ _ _ _).trans (by rw [hratio])
  have each_le_G (j : J) : Lj j ≤ G := le_trans inf_le_left hα
  have admissible_iff (S : Subgroup U) : admissible S ↔ parabolic S ∧ S ≤ P := by
    constructor
    · rintro ⟨hs, hS, hLabels⟩
      refine ⟨hs, le_inf (le_iInf hS) (le_inf (le_trans (hS j₀) (each_le_G _)) ?_)⟩
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp ((labelCriterion S hS j).mp
        (hLabels j₀ j).2) x hx).symm
    · rintro ⟨hs, hSP⟩
      have hS (j : I) : S ≤ Lj j.val := le_trans hSP (le_trans inf_le_left (iInf_le _ j))
      have hl (j : I) : right j₀.val S (hS j₀) = right j.val S (hS j) := by
        apply (labelCriterion S hS j).mpr
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxc : x ∈ Subgroup.centralizer
            (Set.range (fun i : I => (σ j₀.val : U) * (σ i.val : U)⁻¹)) := (hSP hx).2.2
        exact (Subgroup.mem_centralizer_iff.mp hxc _ ⟨j, rfl⟩).symm
      exact ⟨hs, hS, fun i j => ⟨rfl, (hl i).symm.trans (hl j)⟩⟩

  -- The ambient finite-parabolic lemma applies to the image of P in Perm Nat.
  -- Its block predicate transfers along the finitary inclusion, using the
  -- union of the blocks as carrier. Intersections need no block formula here.
  let : Finite (G.map (Subgroup.subtype _)) := finiteOfBlocks hG
  let : Finite G := Finite.of_injective
    (fun g : G => (⟨(g.val : Equiv.Perm Nat), ⟨g.val, g.property, rfl⟩⟩ :
      G.map (Subgroup.subtype _)))
    (fun g h heq => Subtype.ext (Subtype.ext (congrArg (fun q : G.map (Subgroup.subtype _) => q.val) heq)))
  let : Finite P := Finite.of_injective
    (Subgroup.inclusion (show P ≤ G from le_trans inf_le_right inf_le_left)) (fun _ _ h => Subtype.ext (congrArg (fun g : G => g.val) h))
  have hHull := greatestSwapClosure P
  have hGreatest : IsGreatest {S : Subgroup U | admissible S} L := by
    refine ⟨(admissible_iff L).mpr hHull.1, ?_⟩
    intro S hS
    exact hHull.2 ((admissible_iff S).mp hS)

  have hIndex (S : Subgroup U) (j : I) : S.IsFiniteRelIndex (Lj j.val) := by
    let : Finite ↥(Lj j.val) := Finite.of_injective
      (Subgroup.inclusion (each_le_G j.val))
      (fun _ _ h => Subtype.ext (congrArg (fun g : G => g.val) h))
    exact Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  have hNonzero (S : Subgroup U) (j : I) : S.relIndex (Lj j.val) ≠ 0 := by
    let := hIndex S j
    exact Subgroup.index_ne_zero (H := S.subgroupOf (Lj j.val))
  refine ⟨hGreatest, fun S hS j =>
    Subgroup.relIndex_le_of_le_left (hGreatest.2 hS) (hNonzero S j), ?_⟩

  -- Steps 1–4 of the registered MixedCrossingComposites proof compute the
  -- multiplication and transfer on basis vectors. The smaller-group theorem
  -- packages their comparison for any finite-index subgroup of this Lj and
  -- the same representative. The summed clause of CommonMackeyIntersectionSum
  -- uses the full selected intersection, which can exceed the parabolic hull.
  -- Apply the per-representative theorem at L to obtain both fiber proofs.
  have ha (k : K) : α * (k : U) * α⁻¹ ∈ G := (a.toHom k).property
  have hb (h : H) : β * (h : U) * β⁻¹ ∈ G := (b.toHom h).property
  have termData (j : I) :
      ∃ (hfL : finiteFibers j.val L (hL j))
        (hfJ : finiteFibers j.val (Lj j.val) (le_refl (Lj j.val))),
      ∀ x : M.basis.carrier →₀ Complex,
        (L.relIndex (Lj j.val) : Complex)⁻¹ • (outer j.val L (hL j) hfL).interpret.eval.toLinearMap x =
          (outer j.val (Lj j.val) (le_refl (Lj j.val)) hfJ).interpret.eval.toLinearMap x := by
    obtain ⟨hfL, hfJ, hOuter, _⟩ :=
      MixedCrossingsThroughSmallerGroup K H G α β ha hb σ hσ j.val L (hL j) (hIndex L j)
    refine ⟨hfL, hfJ, fun x => ?_⟩
    have hEvalL := compactOuterEval a b (left j.val L (hL j)) (right j.val L (hL j))
      (dot j.val L (hL j)) hfL
    have hEvalJ := compactOuterEval a b (left j.val (Lj j.val) (le_refl _))
      (right j.val (Lj j.val) (le_refl _)) (dot j.val (Lj j.val) (le_refl _)) hfJ
    change (L.relIndex (Lj j.val) : Complex)⁻¹ •
      ((LabelledDrawing.vertical _ _).interpret.eval.toLinearMap x) =
        (LabelledDrawing.vertical _ _).interpret.eval.toLinearMap x
    rw [hEvalL, hEvalJ]
    let full : Diagram Complex M M := Diagram.vertical
      (Diagram.mixedProjection a b (left j.val (Lj j.val) (le_refl _))
        (right j.val (Lj j.val) (le_refl _)) (dot j.val (Lj j.val) (le_refl _)) hfJ)
      (Diagram.mixedMultiplication a b (left j.val (Lj j.val) (le_refl _))
        (right j.val (Lj j.val) (le_refl _)) (dot j.val (Lj j.val) (le_refl _)))
    change _ = (Diagram.scale (L.relIndex (Lj j.val) : Complex) full).eval at hOuter
    change _ = full.eval.toLinearMap x
    rw [hOuter]
    have hn : (L.relIndex (Lj j.val) : Complex) ≠ 0 := by exact_mod_cast hNonzero L j
    change (L.relIndex (Lj j.val) : Complex)⁻¹ •
      (((L.relIndex (Lj j.val) : Complex) • full.eval.toLinearMap) x) = _
    rw [LinearMap.smul_apply]
    rw [← mul_smul, inv_mul_cancel₀ hn, one_smul]

  choose hfL hfJ termEq using termData
  let : Finite J := Quotient.finite _
  refine ⟨Fintype.ofFinite I, hfL, hfJ, ?_⟩
  intro indices restricted usual restrictedSum usualSum
  -- Both original sum nodes keep the same index set and complete summands.
  -- Evaluation is pointwise, so the normalized comparison applies termwise.
  apply LinearMap.ext
  intro x
  rw [IndexedDrawing.eval_apply, IndexedDrawing.eval_apply]
  change (∑ j ∈ indices, (restricted j).interpret.eval.toLinearMap x) =
    ∑ j ∈ indices, (usual j).interpret.eval.toLinearMap x
  exact Finset.sum_congr rfl fun j _ => termEq j x
)
#print axioms LargestCommonMixedCrossingParabolic
