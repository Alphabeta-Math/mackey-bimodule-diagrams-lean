import MackeyDiagrams
import Proofs.MixedCrossingFiberMaps
import Proofs.TransportToMackeyRepresentative

universe u

def correctedMixedCrossingComposites : Prop :=
  ∀ {U : Type u} [Group U] (K H G L : Subgroup U) (α β a b : U)
      (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
      (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G)
      (ha : ∀ ℓ : L, a * (ℓ : U) * a⁻¹ ∈ K)
      (hb : ∀ ℓ : L, b * (ℓ : U) * b⁻¹ ∈ H)
      (hs : (α * a) * (β * b)⁻¹ ∈ G),
    let eα := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let eβ := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
    let ea := MackeyDiagrams.ConjEmbedding.ofConjugator a ha
    let eb := MackeyDiagrams.ConjEmbedding.ofConjugator b hb
    let d : MackeyDiagrams.Dot
        (MackeyDiagrams.ConjEmbedding.comp eα ea)
        (MackeyDiagrams.ConjEmbedding.comp eβ eb) :=
      MackeyDiagrams.Dot.ofRepresentatives (α * a) (β * b)
        (by
          intro ℓ
          change α * (a * (ℓ : U) * a⁻¹) * α⁻¹ = _
          simp only [mul_inv_rev, mul_assoc])
        (by
          intro ℓ
          change β * (b * (ℓ : U) * b⁻¹) * β⁻¹ = _
          simp only [mul_inv_rev, mul_assoc]) hs
    let s := MackeyDiagrams.Dot.element d
    let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eα)
    let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eβ)
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let conjSubgroup := fun (c : U) (S : Subgroup U) =>
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
      let Lj := fun j : J => conjSubgroup α K ⊓ conjSubgroup ((σ j : U) * β) H
      let leftJ := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := Lj j) (G := K) α⁻¹
          (by
            intro ℓ
            obtain ⟨k, hk, heq⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at heq
            rw [← heq]
            change k ∈ K at hk
            convert hk using 1
            group)
      let rightJ := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := Lj j) (G := H)
          (β⁻¹ * (σ j : U)⁻¹)
          (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := ℓ.property.2
            change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
            rw [← heq]
            change h ∈ H at hh
            convert hh using 1
            group)
      let _Mj := fun j : J =>
        MackeyDiagrams.Word.tensor
          (MackeyDiagrams.Word.up (leftJ j)) (MackeyDiagrams.Word.down (rightJ j))
      let M := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.down eα) (MackeyDiagrams.Word.up eβ)
      let ML := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.up ea) (MackeyDiagrams.Word.down eb)
      let Ls := conjSubgroup α K ⊓ conjSubgroup ((s : U) * β) H
      let Limage := conjSubgroup (α * a) L
      let n := Subgroup.relIndex Limage Ls
      let qBasis := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ ea eb d
      let q := fun w : (MackeyDiagrams.Word.basis ML).carrier =>
        MackeyDiagrams.Generator.mixedProduct eα eβ (qBasis w)
      Subgroup.IsFiniteRelIndex Limage Ls →
        ∃ hf : ∀ z : (MackeyDiagrams.Word.basis M).carrier,
            Set.Finite {w | qBasis w = z},
          let ι : MackeyDiagrams.LabelledDrawing Complex ML M :=
            MackeyDiagrams.LabelledDrawing.mixedMultiplication eα eβ ea eb [(1, d)]
          let p : MackeyDiagrams.LabelledDrawing Complex M ML :=
            MackeyDiagrams.LabelledDrawing.compactProjection eα eβ ea eb [(1, ⟨d, hf⟩)]
          let pThenIota := MackeyDiagrams.LabelledDrawing.vertical p ι
          let iotaThenP := MackeyDiagrams.LabelledDrawing.vertical ι p
          let straight : MackeyDiagrams.LabelledDrawing Complex ML ML :=
            MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id ML)
          let evaluate := fun {bottom top : MackeyDiagrams.Word K H}
              (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
            MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
          let orbit := fun j : J => DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
          let P := fun j : J =>
            show ((MackeyDiagrams.Word.basis M).carrier →₀ Complex) →ₗ[Complex]
                ((MackeyDiagrams.Word.basis M).carrier →₀ Complex) from by
              classical
              exact Finsupp.lsum Complex (fun z =>
                if MackeyDiagrams.Generator.mixedProduct eα eβ z ∈ orbit j
                then Finsupp.lsingle z else 0)
          let finiteQ := fun z : (MackeyDiagrams.Word.basis ML).carrier =>
            show Set.Finite {w | q w = q z} from
              Set.Finite.subset (hf (qBasis z)) (by
                intro w hw
                exact (MackeyDiagrams.Generator.mixedEquiv eα eβ).injective hw)
          ∀ j : J, s ∈ orbit j →
            MackeyDiagrams.Biset.Hom.toLinearMap (evaluate pThenIota) =
              (n : Complex) • P j ∧
            (∀ z : (MackeyDiagrams.Word.basis ML).carrier,
              MackeyDiagrams.Biset.Hom.toLinearMap (evaluate iotaThenP)
                  (Finsupp.single z (1 : Complex)) =
                Finset.sum (Set.Finite.toFinset (finiteQ z))
                  (fun w => Finsupp.single w (1 : Complex))) ∧
            (evaluate iotaThenP = evaluate straight ↔
              n = 1) ∧
            (1 < n → ∀ c : Complex,
              evaluate (MackeyDiagrams.LabelledDrawing.scale c iotaThenP) ≠
                evaluate straight)

#print axioms correctedMixedCrossingComposites
