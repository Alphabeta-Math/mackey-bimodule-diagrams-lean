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
