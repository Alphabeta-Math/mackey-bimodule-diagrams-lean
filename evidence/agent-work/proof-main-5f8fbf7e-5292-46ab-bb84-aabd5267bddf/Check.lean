import MackeyDiagrams
import Proofs.GeneralizedMackeyDecomposition
import Proofs.MixedCrossingComposites
import Proofs.MackeyIdentityDiagram

set_option maxHeartbeats 2000000

namespace MixedMackeyCancellationSupport

open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {K H : Subgroup U}

private theorem eval_sum (M : Word K H) {J : Type u}
    (drawings : J → LabelledDrawing Complex M M) (indices : Finset J)
    (x : M.basis.carrier →₀ Complex) :
    ((List.foldr LabelledDrawing.add (.ordinary (Diagram.zero M M))
      (List.map drawings indices.toList)).interpret.eval).toLinearMap x =
        ∑ j ∈ indices, (drawings j).interpret.eval.toLinearMap x := by
  classical
  let term (j : J) := (drawings j).interpret.eval.toLinearMap x
  have evalList (L : List J) :
      ((List.foldr LabelledDrawing.add (.ordinary (Diagram.zero M M))
        (L.map drawings)).interpret.eval).toLinearMap x = (L.map term).sum := by
    induction L with
    | nil => rfl
    | cons j L ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons]
      change term j +
          (List.foldr LabelledDrawing.add (.ordinary (Diagram.zero M M))
            (L.map drawings)).interpret.eval.toLinearMap x = term j + (L.map term).sum
      rw [ih]
  rw [evalList]
  conv_rhs => rw [← indices.toList_toFinset, List.sum_toFinset _ indices.nodup_toList]

end MixedMackeyCancellationSupport

open MackeyDiagrams
universe u

theorem MixedReidemeisterTwoMackeyCancellation : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U),
  let conjSubgroup := fun (c : U) (S : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
  let Kα := conjSubgroup α K
  let Hβ := conjSubgroup β H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let eα := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun k => hK ⟨(k : U), k.property, rfl⟩)
    let eβ := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun h => hH ⟨(h : U), h.property, rfl⟩)
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let orbit := fun j : J => DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
      let L := fun j : J => Kα ⊓ conjSubgroup ((σ j : U) * β) H
      let a := α⁻¹
      let b := fun j : J => β⁻¹ * (σ j : U)⁻¹
      let l := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) a
          (by
            intro ℓ
            obtain ⟨k, hk, heq⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at heq
            change k ∈ K at hk
            change α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹ ∈ K
            rw [← heq]
            convert hk using 1
            group)
      let r := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H) (b j)
          (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := ℓ.property.2
            change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
            change h ∈ H at hh
            change (β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) * (β⁻¹ * (σ j : U)⁻¹)⁻¹ ∈ H
            rw [← heq]
            convert hh using 1
            group)
      let d : ∀ j : J, MackeyDiagrams.Dot
          (MackeyDiagrams.ConjEmbedding.comp eα (l j))
          (MackeyDiagrams.ConjEmbedding.comp eβ (r j)) := fun j =>
        MackeyDiagrams.Dot.ofRepresentatives (α * a) (β * b j)
          (by
            intro ℓ
            change α * (a * (ℓ : U) * a⁻¹) * α⁻¹ = _
            simp only [mul_inv_rev, mul_assoc])
          (by
            intro ℓ
            change β * (b j * (ℓ : U) * (b j)⁻¹) * β⁻¹ = _
            simp only [mul_inv_rev, mul_assoc])
          (by
            change (α * α⁻¹) * (β * (β⁻¹ * (σ j : U)⁻¹))⁻¹ ∈ G
            have hs : (α * α⁻¹) * (β * (β⁻¹ * (σ j : U)⁻¹))⁻¹ = (σ j : U) := by
              group
            rw [hs]
            exact (σ j).property)
      let n := fun j : J =>
        Subgroup.relIndex (conjSubgroup (α * a) (L j))
          (Kα ⊓ conjSubgroup ((MackeyDiagrams.Dot.element (d j) : U) * β) H)
      let down := MackeyDiagrams.Word.down eα
      let up := MackeyDiagrams.Word.up eβ
      let M := MackeyDiagrams.Word.tensor down up
      let Mj := fun j : J =>
        MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (l j)) (MackeyDiagrams.Word.down (r j))
      let W := MackeyDiagrams.Word.basis M
      let Wj := fun j : J => MackeyDiagrams.Word.basis (Mj j)
      let V := Finsupp W.carrier Complex
      let groupAlgebra := MonoidAlgebra Complex G
      let coordinates : LinearEquiv (RingHom.id Complex) V groupAlgebra :=
        LinearEquiv.trans
          (Finsupp.domLCongr (MackeyDiagrams.Generator.mixedEquiv eα eβ))
          (MonoidAlgebra.coeffLinearEquiv Complex).symm
      let qBasis := fun j : J => MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ (l j) (r j) (d j)
      let q := fun (j : J) (w : (Wj j).carrier) =>
        MackeyDiagrams.Generator.mixedProduct eα eβ (qBasis j w)
      (∀ (g : K × H) (x : V),
        coordinates (MackeyDiagrams.Biset.actLinear Complex W g x) =
          MonoidAlgebra.of Complex G (MackeyDiagrams.ConjEmbedding.toHom eα g.1) * coordinates x *
            MonoidAlgebra.of Complex G ((MackeyDiagrams.ConjEmbedding.toHom eβ g.2)⁻¹)) ∧
      (∀ g : G, ∃! j : J, g ∈ orbit j) ∧
      (∀ j : J, MackeyDiagrams.Dot.element (d j) = σ j ∧ n j = 1 ∧
        Set.BijOn (q j) Set.univ (orbit j)) ∧
      ∃ hf : ∀ (j : J) (z : W.carrier), Set.Finite {w | qBasis j w = z},
        let ι : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex (Mj j) M := fun j =>
          MackeyDiagrams.LabelledDrawing.mixedMultiplication eα eβ (l j) (r j) [(1, d j)]
        let p : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex M (Mj j) := fun j =>
          MackeyDiagrams.LabelledDrawing.compactProjection eα eβ (l j) (r j)
            [(1, ⟨d j, hf j⟩)]
        let straight : MackeyDiagrams.LabelledDrawing Complex M M :=
          MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id down))
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id up))
        let straightj : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex (Mj j) (Mj j) := fun j =>
          MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.ordinary
              (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up (l j))))
            (MackeyDiagrams.LabelledDrawing.ordinary
              (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down (r j))))
        let eval := fun {bottom top : MackeyDiagrams.Word K H}
            (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
        let summands : J → MackeyDiagrams.LabelledDrawing Complex M M := fun j =>
          MackeyDiagrams.LabelledDrawing.vertical (p j) (ι j)
        let finiteSupport := fun (drawings : J → MackeyDiagrams.LabelledDrawing Complex M M) =>
          ∀ x : V, Set.Finite (Function.support
            (fun j => MackeyDiagrams.Biset.Hom.toLinearMap (eval (drawings j)) x))
        let IndexedSum := {drawings : J → MackeyDiagrams.LabelledDrawing Complex M M //
          finiteSupport drawings}
        let partialSum := fun (sum : IndexedSum) (indices : Finset J) =>
          List.foldr MackeyDiagrams.LabelledDrawing.add
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero M M))
            (List.map sum.val (Finset.toList indices))
        (∀ j : J,
          eval (MackeyDiagrams.LabelledDrawing.vertical (ι j) (p j)) = eval (straightj j)) ∧
        (∀ (i j : J), i ≠ j →
          eval (MackeyDiagrams.LabelledDrawing.vertical (ι i) (p j)) =
            eval (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero (Mj i) (Mj j)))) ∧
        (∃ finite : finiteSupport summands,
          let sum : IndexedSum := ⟨summands, finite⟩
          ∀ x : V,
            MackeyDiagrams.Biset.Hom.toLinearMap
              (eval (partialSum sum (Set.Finite.toFinset (sum.property x)))) x =
            MackeyDiagrams.Biset.Hom.toLinearMap (eval straight) x)
) :=
(by
  classical
  intro U inst K H G α β conjSubgroup Kα Hβ hK hH eα eβ A B J σ reps orbit
    L a b l r d n down up M Mj W Wj V groupAlgebra coordinates qBasis q
  -- Xiao, §5.1, “Mackey cancellation” (archived original PDF p. 16,
  -- revised published PDF p. 18), specializes Proposition 5.1 to the
  -- full intersections of (2.2). The plan records no Alphabeta Math entry
  -- with numbered steps for this endpoint. The steps below follow Xiao's
  -- specialization and the splitting equations (2.3).
  -- Step 1. Match the two-sided group action at the original boundary.
  have action := (GeneralizedMackeyDecomposition.{u, 0} K H G α β hK hH σ reps).1
  -- Step 2. Use the chosen section to identify membership in each orbit.
  have orbitClass (j : J) (g : G) : g ∈ orbit j ↔ DoubleCoset.mk A B g = j := by
    change g ∈ DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G) ↔ _
    rw [DoubleCoset.mem_doubleCoset]
    refine (DoubleCoset.eq (H := A) (K := B) (a := σ j) (b := g)).symm.trans ?_
    rw [reps j]
    exact eq_comm
  have dotElement (j : J) : (d j).element = σ j := by
    apply Subtype.ext
    change (α * α⁻¹) * (β * (β⁻¹ * (σ j : U)⁻¹))⁻¹ = (σ j : U)
    group
  have indexOne (j : J) : n j = 1 := by
    change (conjSubgroup (α * α⁻¹) (L j)).relIndex
      (Kα ⊓ conjSubgroup (((d j).element : U) * β) H) = 1
    rw [dotElement, mul_inv_cancel]
    change (conjSubgroup 1 (L j)).relIndex (L j) = 1
    have himage : conjSubgroup 1 (L j) = L j := by
      change (L j).map (MulAut.conj (1 : U)).toMonoidHom = L j
      have hconj : (MulAut.conj (1 : U)).toMonoidHom = MonoidHom.id U := by
        ext x
        change 1 * x * (1 : U)⁻¹ = x
        simp
      rw [hconj, Subgroup.map_id]
    rw [himage, Subgroup.relIndex_self]
  -- The full intersection gives the injectivity hypothesis directly. The
  -- general MixedCrossingComposites theorem uses image-subgroup quotients
  -- and a finite relative-index hypothesis. Here the registered
  -- MackeyIdentityDiagram already gives all three composites at these
  -- comap-subgroup quotients, once the two dot presentations are identified.
  have injective (j : J) : Function.Injective (qBasis j) := by
    apply Generator.injective_mixedMultiplicationBasis
    intro k h he
    rw [dotElement] at he
    let ell := α * (k : U) * α⁻¹
    have hleft : ell ∈ Kα := ⟨k, k.property, rfl⟩
    have hright : ell ∈ conjSubgroup ((σ j : U) * β) H := by
      refine ⟨h, h.property, ?_⟩
      have hh := congrArg Subtype.val he
      change α * (k : U) * α⁻¹ =
        (σ j : U) * (β * (h : U) * β⁻¹) * (σ j : U)⁻¹ at hh
      change ((σ j : U) * β) * (h : U) * ((σ j : U) * β)⁻¹ =
        α * (k : U) * α⁻¹
      rw [hh]
      group
    refine ⟨⟨ell, hleft, hright⟩, ?_⟩
    apply Subtype.ext
    change α⁻¹ * (α * (k : U) * α⁻¹) * (α⁻¹)⁻¹ = (k : U)
    group
  have rangeOrbit (j : J) (g : G) : g ∈ Set.range (q j) ↔ g ∈ orbit j := by
    have hrange : g ∈ Set.range (q j) ↔ Generator.mixedPair eα eβ g ∈
        Set.range (qBasis j) := by
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w, (Generator.mixedPair_mixedProduct eα eβ (qBasis j w)).symm⟩
      · rintro ⟨w, hw⟩
        exact ⟨w, (congrArg (Generator.mixedProduct eα eβ) hw).trans
          (Generator.mixedProduct_mixedPair eα eβ g)⟩
    rw [hrange, Generator.mixedRange_eq_doubleCoset, DoubleCoset.mem_doubleCoset]
    simp only [dotElement]
    constructor
    · rintro ⟨k, h, hg⟩
      exact ⟨eα.toHom k, ⟨k, k.property, rfl⟩, eβ.toHom h, ⟨h, h.property, rfl⟩, hg⟩
    · rintro ⟨x, hx, y, hy, hg⟩
      change (x : U) ∈ Kα at hx
      change (y : U) ∈ Hβ at hy
      obtain ⟨k, hk, hx⟩ := hx
      obtain ⟨h, hh, hy⟩ := hy
      have hx' : eα.toHom ⟨k, hk⟩ = x := Subtype.ext hx
      have hy' : eβ.toHom ⟨h, hh⟩ = y := Subtype.ext hy
      exact ⟨⟨k, hk⟩, ⟨h, hh⟩, by rw [hx', hy']; exact hg⟩
  refine ⟨action, ?_, ?_, ?_⟩
  · intro g
    let j := DoubleCoset.mk A B g
    exact ⟨j, (orbitClass j g).mpr rfl, fun i hi => ((orbitClass i g).mp hi).symm⟩
  · intro j
    refine ⟨dotElement j, indexOne j, ?_, ?_, ?_⟩
    · intro w _
      exact (rangeOrbit j (q j w)).mp ⟨w, rfl⟩
    · exact ((Generator.mixedEquiv eα eβ).injective.comp (injective j)).injOn
    · intro g hg
      obtain ⟨w, hw⟩ := (rangeOrbit j g).mpr hg
      exact ⟨w, Set.mem_univ w, hw⟩
  ·
    -- Step 3. MackeyIdentityDiagram uses the literal representative as dot
    -- and finite fibers at the full intersection. Identify its dot with the
    -- representative-product dot, then compare the coefficient-one drawings.
    let d₀ (j : J) : Dot (eα.comp (l j)) (eβ.comp (r j)) :=
      ⟨σ j, by simpa only [← dotElement j] using (d j).intertwines⟩
    have hd (j : J) : d₀ j = d j := Dot.ext (dotElement j).symm
    obtain ⟨hf₀, hsum₀, hdiag₀, hoff₀⟩ := MackeyIdentityDiagram K H G α β hK hH σ reps
    change (∀ j (z : W.carrier),
      Set.Finite {w | Generator.mixedMultiplicationBasis eα eβ (l j) (r j) (d₀ j) w = z}) at hf₀
    let hf (j : J) (z : W.carrier) : Set.Finite {w | qBasis j w = z} :=
      by simpa only [hd] using hf₀ j z
    refine ⟨hf, ?_⟩
    intro ι p straight straightj eval summands finiteSupport IndexedSum partialSum
    let io (j : J) : Diagram Complex (Mj j) M :=
      .mixedMultiplication eα eβ (l j) (r j) (d₀ j)
    let po (j : J) : Diagram Complex M (Mj j) :=
      .mixedProjection eα eβ (l j) (r j) (d₀ j) (hf₀ j)
    have ei (j : J) : eval (ι j) = (io j).eval := by
      change (LabelledDrawing.mixedMultiplication eα eβ (l j) (r j) [(1, d j)]).interpret.eval =
        (Diagram.mixedMultiplication eα eβ (l j) (r j) (d₀ j)).eval
      rw [hd]
      exact MackeyCrossingProof.compact_inclusion eα eβ (l j) (r j) (d j)
    have ep (j : J) : eval (p j) = (po j).eval := by
      change (LabelledDrawing.compactProjection eα eβ (l j) (r j)
        [(1, ⟨d j, hf j⟩)]).interpret.eval = (po j).eval
      rw [MackeyCrossingProof.compact_projection]
      have congr_projection
          (d₁ d₂ : Dot (eα.comp (l j)) (eβ.comp (r j))) (h : d₁ = d₂)
          (h₁ : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis eα eβ (l j) (r j) d₁ w = z})
          (h₂ : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis eα eβ (l j) (r j) d₂ w = z}) :
          Diagram.mixedProjection (R := Complex) eα eβ (l j) (r j) d₁ h₁ =
            Diagram.mixedProjection (R := Complex) eα eβ (l j) (r j) d₂ h₂ := by
        cases h
        rfl
      exact congrArg Diagram.eval (congr_projection _ _ (hd j).symm (hf j) (hf₀ j))
    have ecomp {p q t : Word K H} (f : LabelledDrawing Complex p q)
        (g : LabelledDrawing Complex q t) :
        eval (LabelledDrawing.vertical f g) = (eval f).vertical (eval g) := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro j
      rw [ecomp, ei, ep]
      have hs : eval (straightj j) = Biset.Hom.id (Wj j) :=
        Biset.Hom.horizontal_id (Word.up (l j)).basis (Word.down (r j)).basis
      rw [hs]
      exact hdiag₀ j
    · intro i j hij
      rw [ecomp, ei, ep]
      exact hoff₀ i j hij
    · -- Step 4. Evaluate the exact finite support of the labelled sum on
      -- each input. This implements the paper's pointwise sum over all cosets.
      let term (x : V) (j : J) := (eval (summands j)).toLinearMap x
      let ordinary (x : V) (j : J) :=
        (Diagram.vertical (po j) (io j)).eval.toLinearMap x
      have hterm (x : V) : term x = ordinary x := by
        funext j
        change (eval (LabelledDrawing.vertical (p j) (ι j))).toLinearMap x = _
        rw [ecomp, ep, ei]
        rfl
      obtain ⟨finite₀, sum₀⟩ := hsum₀
      have finite : finiteSupport summands := fun x => by
        change Set.Finite (Function.support (term x))
        rw [hterm]
        exact finite₀ x
      refine ⟨finite, ?_⟩
      intro sum x
      rw [MixedMackeyCancellationSupport.eval_sum M summands (finite x).toFinset x]
      change (∑ j ∈ (finite x).toFinset, term x j) = _
      have indices : (finite x).toFinset = (finite₀ x).toFinset := by
        ext j
        simp only [Set.Finite.mem_toFinset]
        change j ∈ Function.support (term x) ↔ j ∈ Function.support (ordinary x)
        rw [hterm]
      rw [indices, hterm]
      exact (sum₀ x).symm
)

#print axioms MixedReidemeisterTwoMackeyCancellation
