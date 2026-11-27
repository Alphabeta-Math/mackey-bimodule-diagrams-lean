import MackeyDiagrams
import Proofs.MixedCrossingFiberMaps
import Proofs.TransportToMackeyRepresentative

open MackeyDiagrams
universe u

section Drawings

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))
variable (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z})

private theorem multiplication_eval :
    (LabelledDrawing.mixedMultiplication (R := Complex) a b l r [(1, d)]).interpret.eval =
      (Diagram.mixedMultiplication (R := Complex) a b l r d).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval]

private theorem projection_eval :
    (LabelledDrawing.compactProjection (R := Complex) a b l r [(1, ⟨d, hf⟩)]).interpret.eval =
      (Diagram.mixedProjection (R := Complex) a b l r d hf).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval]

example (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    let p := LabelledDrawing.compactProjection (R := Complex) a b l r [(1, ⟨d, hf⟩)]
    let i := LabelledDrawing.mixedMultiplication (R := Complex) a b l r [(1, d)]
    (p.vertical i).interpret.eval.toLinearMap (Finsupp.single z 1) =
      Finsupp.single z ((hf z).toFinset.card : Complex) := by
  change (Biset.Hom.vertical _ _).toLinearMap (Finsupp.single z 1) = _
  rw [projection_eval, multiplication_eval]
  exact Diagram.projection_then_inclusion_single Complex a b l r d hf z

example (z : ((Biset.induction l).tensor (Biset.restriction r)).carrier) :
    let p := LabelledDrawing.compactProjection (R := Complex) a b l r [(1, ⟨d, hf⟩)]
    let i := LabelledDrawing.mixedMultiplication (R := Complex) a b l r [(1, d)]
    (i.vertical p).interpret.eval.toLinearMap (Finsupp.single z 1) =
      Finset.sum (hf (Generator.mixedMultiplicationBasis a b l r d z)).toFinset
        (fun w => Finsupp.single w (1 : Complex)) := by
  change (Biset.Hom.vertical _ _).toLinearMap (Finsupp.single z 1) = _
  rw [projection_eval, multiplication_eval]
  exact Diagram.inclusion_then_projection_single Complex a b l r d hf z

example :
    let p := LabelledDrawing.compactProjection (R := Complex) a b l r [(1, ⟨d, hf⟩)]
    let i := LabelledDrawing.mixedMultiplication (R := Complex) a b l r [(1, d)]
    let p₀ := LabelledDrawing.ordinary (Diagram.mixedProjection (R := Complex) a b l r d hf)
    let i₀ := LabelledDrawing.ordinary (Diagram.mixedMultiplication (R := Complex) a b l r d)
    (p.vertical i).planarShape = (p₀.vertical i₀).planarShape ∧
    (i.vertical p).planarShape = (i₀.vertical p₀).planarShape :=
  ⟨rfl, rfl⟩

example (g : G) (hg : g ∈ DoubleCoset.doubleCoset d.element a.toHom.range b.toHom.range) :
    Generator.mixedPair a b g ∈ Set.range (Generator.mixedMultiplicationBasis a b l r d) := by
  obtain ⟨_, ⟨k, rfl⟩, _, ⟨h, rfl⟩, heq⟩ := DoubleCoset.mem_doubleCoset.mp hg
  exact (Generator.mixedRange_eq_doubleCoset a b l r d g).mpr ⟨k, h, heq⟩

end Drawings

section FiberSupplier

variable {U : Type u} [Group U] (K H G L : Subgroup U) (α β a b : U)
variable (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
variable (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G)
variable (ha : ∀ ℓ : L, a * (ℓ : U) * a⁻¹ ∈ K)
variable (hb : ∀ ℓ : L, b * (ℓ : U) * b⁻¹ ∈ H)
variable (hs : (α * a) * (β * b)⁻¹ ∈ G)

example :
    let eα := ConjEmbedding.ofConjugator α hα
    let eβ := ConjEmbedding.ofConjugator β hβ
    let ea := ConjEmbedding.ofConjugator a ha
    let eb := ConjEmbedding.ofConjugator b hb
    let d : Dot (eα.comp ea) (eβ.comp eb) :=
      Dot.ofRepresentatives (α * a) (β * b)
        (by
          intro ℓ
          change α * (a * (ℓ : U) * a⁻¹) * α⁻¹ = _
          simp only [mul_inv_rev, mul_assoc])
        (by
          intro ℓ
          change β * (b * (ℓ : U) * b⁻¹) * β⁻¹ = _
          simp only [mul_inv_rev, mul_assoc]) hs
    let A := eα.toHom.range
    let B := eβ.toHom.range
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (hσ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let Ls := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((d.element : U) * β))) H
      let Limage := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (α * a))) L
      let qBasis := Generator.mixedMultiplicationBasis eα eβ ea eb d
      let q := fun w => Generator.mixedProduct eα eβ (qBasis w)
      Subgroup.IsFiniteRelIndex Limage Ls →
      (∀ z, Set.Finite {w | qBasis w = z}) ∧
      ∀ (j : J), d.element ∈ DoubleCoset.doubleCoset (σ j) A B →
        Set.range q = DoubleCoset.doubleCoset (σ j) A B ∧
        ∀ g ∈ DoubleCoset.doubleCoset (σ j) A B,
          Nat.card {w | q w = g} = Limage.relIndex Ls := by
  intro eα eβ ea eb d A B J σ hσ Ls Limage qBasis q hIndex
  obtain ⟨_, _, _, range_q, card_q, finite_q, _⟩ :=
    MixedCrossingFiberMaps K H G L α β a b hα hβ ha hb hs σ hσ
  refine ⟨finite_q.mpr hIndex, ?_⟩
  intro j hj
  have hj_eq : DoubleCoset.mk A B d.element = j := by
    rw [← hσ j]
    exact (DoubleCoset.eq.mpr (DoubleCoset.mem_doubleCoset.mp hj)).symm
  rw [← hj_eq]
  exact ⟨range_q, fun g hg => card_q g hg hIndex⟩

end FiberSupplier

#print axioms multiplication_eval
#print axioms projection_eval
#print axioms MixedCrossingFiberMaps
#print axioms TransportToMackeyRepresentative

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
