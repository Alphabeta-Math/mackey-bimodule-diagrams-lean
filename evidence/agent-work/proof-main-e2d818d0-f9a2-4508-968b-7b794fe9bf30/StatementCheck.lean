import MackeyDiagrams
import Proofs.CommonMackeyIntersectionSum
import Proofs.FiniteParabolicIntersectionBlocks

set_option maxHeartbeats 2000000

noncomputable def CheckedLargestCommonMixedCrossingParabolic : Prop := (
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
)

#print axioms CheckedLargestCommonMixedCrossingParabolic
#print axioms CommonMackeyIntersectionSum
#print axioms FiniteParabolicIntersectionBlocks
#check MackeyDiagrams.IndexedDrawing.eval_apply
#check Subgroup.relIndex_mul_relIndex
#check Subgroup.index_ne_zero
