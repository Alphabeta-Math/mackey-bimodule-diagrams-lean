import MackeyDiagrams
import Proofs.MixedCrossingsThroughSmallerGroup
import Proofs.MackeyDecompositionWithParabolicRepresentatives

set_option maxHeartbeats 2000000

theorem ParabolicSmallerMackeyReverseComposite : (
let U := ↥(Subgroup.closure {s : Equiv.Perm Nat | Equiv.Perm.IsSwap s})
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) := fun X =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))
let parabolic : Subgroup U → Prop := fun S =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype _) S = iSup (fun i => blockSym (blocks i))
∀ (K H G : Subgroup U) (α β : U)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  parabolic K → parabolic H → parabolic G →
  let eα := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let eβ := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eα)
  let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eβ)
  let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
  ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j) (j : J),
    let s := σ j
    let orbit := DoubleCoset.doubleCoset s (A : Set G) (B : Set G)
    let a := α⁻¹
    let b := β⁻¹ * (s : U)⁻¹
    let Lj := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((s : U) * β))) H
    let left := fun (S : Subgroup U) (hS : S ≤ Lj) =>
      MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := K) a (by
        intro ℓ
        obtain ⟨k, hk, heq⟩ := (hS ℓ.property).1
        change α * k * α⁻¹ = (ℓ : U) at heq
        change α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹ ∈ K
        rw [← heq]
        change k ∈ K at hk
        convert hk using 1
        group)
    let right := fun (S : Subgroup U) (hS : S ≤ Lj) =>
      MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := H) b (by
        intro ℓ
        obtain ⟨h, hh, heq⟩ := (hS ℓ.property).2
        change (s : U) * β * h * ((s : U) * β)⁻¹ = (ℓ : U) at heq
        change (β⁻¹ * (s : U)⁻¹) * (ℓ : U) * (β⁻¹ * (s : U)⁻¹)⁻¹ ∈ H
        rw [← heq]
        change h ∈ H at hh
        convert hh using 1
        group)
    let dot := fun (S : Subgroup U) (hS : S ≤ Lj) =>
      show MackeyDiagrams.Dot
          (MackeyDiagrams.ConjEmbedding.comp eα (left S hS))
          (MackeyDiagrams.ConjEmbedding.comp eβ (right S hS)) from
        ⟨s, by
          intro ℓ
          apply Subtype.ext
          change (α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹) * (s : U) =
            (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
              (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
          group⟩
    ∀ (L : Subgroup U) (hL : L ≤ Lj),
      parabolic L → Subgroup.IsFiniteRelIndex L Lj →
      let leftL := left L hL
      let rightL := right L hL
      let leftJ := left Lj (le_refl Lj)
      let rightJ := right Lj (le_refl Lj)
      let dL := dot L hL
      let dJ := dot Lj (le_refl Lj)
      let M := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.down eα) (MackeyDiagrams.Word.up eβ)
      let ML := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.up leftL) (MackeyDiagrams.Word.down rightL)
      let MJ := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.up leftJ) (MackeyDiagrams.Word.down rightJ)
      let qBasis := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ leftL rightL dL
      let qBasisJ := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ leftJ rightJ dJ
      let q := fun z : (MackeyDiagrams.Word.basis ML).carrier =>
        MackeyDiagrams.Generator.mixedProduct eα eβ (qBasis z)
      let fiber := fun g : G => {w | q w = g}
      let n := Subgroup.relIndex L Lj
      ∃ (hLFinite : ∀ z : (MackeyDiagrams.Word.basis M).carrier,
          Set.Finite {w | qBasis w = z})
        (hJFinite : ∀ z : (MackeyDiagrams.Word.basis M).carrier,
          Set.Finite {w | qBasisJ w = z}),
        let hf := fun g : G => show Set.Finite (fiber g) from
          Set.Finite.subset (hLFinite (MackeyDiagrams.Generator.mixedPair eα eβ g)) (by
            intro w hw
            apply (MackeyDiagrams.Generator.mixedEquiv eα eβ).injective
            change q w = MackeyDiagrams.Generator.mixedProduct eα eβ
              (MackeyDiagrams.Generator.mixedPair eα eβ g)
            rw [MackeyDiagrams.Generator.mixedProduct_mixedPair]
            exact hw)
        let fiberSum := fun g : G =>
          Finset.sum (Set.Finite.toFinset (hf g)) (fun w => Finsupp.single w (1 : Complex))
        let iotaL : MackeyDiagrams.Diagram Complex ML M :=
          MackeyDiagrams.Diagram.mixedMultiplication eα eβ leftL rightL dL
        let pL : MackeyDiagrams.Diagram Complex M ML :=
          MackeyDiagrams.Diagram.mixedProjection eα eβ leftL rightL dL hLFinite
        let iotaJ : MackeyDiagrams.Diagram Complex MJ M :=
          MackeyDiagrams.Diagram.mixedMultiplication eα eβ leftJ rightJ dJ
        let pJ : MackeyDiagrams.Diagram Complex M MJ :=
          MackeyDiagrams.Diagram.mixedProjection eα eβ leftJ rightJ dJ hJFinite
        let outerL := MackeyDiagrams.Diagram.vertical pL iotaL
        let outerJ := MackeyDiagrams.Diagram.vertical pJ iotaJ
        let innerL := MackeyDiagrams.Diagram.vertical iotaL pL
        let straight := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up leftL))
          (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down rightL))
        MackeyDiagrams.Diagram.eval outerL =
          MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.scale (n : Complex) outerJ) ∧
        Set.range q = orbit ∧
        (∀ (k : K) (h : H),
          q (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction leftL)
              (MackeyDiagrams.Biset.restriction rightL) k h) =
            MackeyDiagrams.ConjEmbedding.toHom eα k * s *
              MackeyDiagrams.ConjEmbedding.toHom eβ h) ∧
        (∀ z : (MackeyDiagrams.Word.basis ML).carrier,
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval iotaL)
              (Finsupp.single z 1) =
            Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ (q z)) 1) ∧
        (∀ g : G, g ∈ orbit →
          Nat.card (fiber g) = n ∧
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval pL)
              (Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ g) 1) = fiberSum g) ∧
        (∀ z : (MackeyDiagrams.Word.basis ML).carrier,
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval innerL)
              (Finsupp.single z 1) = fiberSum (q z)) ∧
        (MackeyDiagrams.Diagram.eval innerL = MackeyDiagrams.Diagram.eval straight ↔ L = Lj)
) :=
(by
  intro U blockSym parabolic K H G α β hα hβ hK hH hG
    eα eβ A B J σ hσ j s orbit a b Lj left right dot
    L hL hParabolicL hIndex leftL rightL leftJ rightJ dL dJ M ML MJ qBasis qBasisJ q fiber n
  -- Xiao, §8.2, the fiber-sum diagram following Proposition 8.3
  -- (archived PDF pp. 35–36, published 28 November revision pp. 37–38),
  -- invokes the smaller-group formula of §5.1.
  -- The reviewed plan supplies no numbered Alphabeta Math proof for this
  -- endpoint. Steps 1–3 of the registered MixedCrossingComposites proof
  -- use the balanced push and its finite-fiber transfer. Steps 4–5 compare
  -- the two composite columns and detect identity by singleton support.
  -- MixedCrossingsThroughSmallerGroup packages these computations with the
  -- range and cardinality for the chosen j. The prescribed section hσ and
  -- finite relative index hIndex meet its hypotheses directly. The route’s
  -- mixedMultiplicationBasis, transferBasis_sum and
  -- inclusion_then_projection_single calculations are already packaged
  -- in this supplier. The parabolic representative theorem builds a
  -- particular tableau section
  -- and a functor decomposition. Here the section is already given and
  -- can be arbitrary, so no additional representative choice is needed.
  obtain ⟨hfL, hfJ, h⟩ :=
    MixedCrossingsThroughSmallerGroup K H G α β hα hβ σ hσ j L hL hIndex
  refine ⟨hfL, hfJ, ?_⟩
  intro hf fiberSum iotaL pL iotaJ pJ outerL outerJ innerL straight
  rcases h with ⟨hOuter, hRange, hPair, hPush, hProject, hInner, hIdentity⟩
  refine ⟨hOuter, hRange, hPair, hPush, hProject, hInner, ?_⟩
  -- The two straight strands have the same evaluation as the identity of
  -- their tensor boundary. Keep the horizontal node in the diagram syntax.
  have hStraight : straight.eval = (MackeyDiagrams.Diagram.id (R := Complex) ML).eval :=
    MackeyDiagrams.Biset.Hom.horizontal_id
      (MackeyDiagrams.Biset.induction leftL) (MackeyDiagrams.Biset.restriction rightL)
  rw [hStraight]
  exact hIdentity)
