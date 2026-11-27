import MackeyDiagrams
import Proofs.MackeyInclusionAndProjectionCrossings

universe u v

def CheckedMackeySummandProjection : Prop :=
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U),
  let Kα := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K
  let Hβ := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj β)) H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let L := fun j : J =>
        Kα ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H
      let C := fun j : J =>
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (β⁻¹ * (σ j : U)⁻¹))) (L j)
      ∀ (I : J → Type v) (hRep : ∀ j : J, I j → H)
        (_ : ∀ (j : J) (h : H), ∃! i : I j, (h : U) * (hRep j i : U)⁻¹ ∈ C j)
        (j : J),
        let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
          (fun k => hK ⟨(k : U), k.property, rfl⟩)
        let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
          (fun h => hH ⟨(h : U), h.property, rfl⟩)
        let s := σ j
        let l := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹
          (by
            intro ℓ
            obtain ⟨k, hk, heq⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at heq
            change k ∈ K at hk
            rw [← heq]
            convert hk using 1
            group)
        let r := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
          (β⁻¹ * (s : U)⁻¹)
          (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := ℓ.property.2
            change ((s : U) * β) * h * ((s : U) * β)⁻¹ = (ℓ : U) at heq
            change h ∈ H at hh
            rw [← heq]
            convert hh using 1
            group)
        let d : MackeyDiagrams.Dot
            (MackeyDiagrams.ConjEmbedding.comp a l) (MackeyDiagrams.ConjEmbedding.comp b r) :=
          ⟨s, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (s : U) =
              (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
        let M := MackeyDiagrams.Word.tensor
          (MackeyDiagrams.Word.down a) (MackeyDiagrams.Word.up b)
        let Mj := MackeyDiagrams.Word.tensor
          (MackeyDiagrams.Word.up l) (MackeyDiagrams.Word.down r)
        let surviving := fun (g : G) =>
          {i : I j | α⁻¹ * (g : U) * β * (hRep j i : U)⁻¹ * β⁻¹ * (s : U)⁻¹ * α ∈ K}
        ∃ (hf : ∀ z, Set.Finite
            {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b l r d w = z})
          (hs : ∀ g : G, Set.Finite (surviving g)),
          let projectionLabel : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b l r) :=
            [(1, ⟨d, hf⟩)]
          let inclusionLabel : List (Complex × MackeyDiagrams.Dot (a.comp l) (b.comp r)) :=
            [(1, d)]
          let p : MackeyDiagrams.LabelledDrawing Complex M Mj :=
            MackeyDiagrams.LabelledDrawing.compactProjection a b l r projectionLabel
          let ι : MackeyDiagrams.LabelledDrawing Complex Mj M :=
            MackeyDiagrams.LabelledDrawing.mixedMultiplication a b l r inclusionLabel
          let composite := MackeyDiagrams.LabelledDrawing.vertical p ι
          ∀ g : G,
            let z := MackeyDiagrams.Generator.mixedPair a b g
            let image := (MackeyDiagrams.LabelledDrawing.interpret composite).eval.toLinearMap
              (Finsupp.single z (1 : Complex))
            image = Finsupp.single z (Finset.card (Set.Finite.toFinset (hs g)) : Complex) ∧
              (DoubleCoset.mk A B g = j → image = Finsupp.single z (1 : Complex)) ∧
              (DoubleCoset.mk A B g ≠ j → image = 0)

#print axioms CheckedMackeySummandProjection

open MackeyDiagrams in
theorem checkedCompactComposite
    {U : Type u} [Group U] {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (d : Dot (a.comp l) (b.comp r))
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (LabelledDrawing.vertical
      (LabelledDrawing.compactProjection a b l r [(1, ⟨d, hf⟩)])
      (LabelledDrawing.mixedMultiplication (R := Complex) a b l r [(1, d)])).interpret.eval =
    (Diagram.vertical (Diagram.mixedProjection a b l r d hf)
      (Diagram.mixedMultiplication (R := Complex) a b l r d)).eval :=
  congrArg₂ Biset.Hom.vertical
    (MackeyCrossingProof.compact_projection a b l r d hf)
    (MackeyCrossingProof.compact_inclusion a b l r d)

#print axioms checkedCompactComposite
#check MackeyDiagrams.Diagram.projection_then_inclusion_single
#check MackeyDiagrams.Generator.mixedRange_eq_doubleCoset
#check MackeyDiagrams.Generator.injective_mixedMultiplicationBasis
#check SurvivingCosetRepresentative
