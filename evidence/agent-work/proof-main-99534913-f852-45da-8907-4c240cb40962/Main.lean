import MackeyDiagrams
import Proofs.MixedCrossingFiberMaps
import Proofs.TransportToMackeyRepresentative

set_option maxHeartbeats 2000000

universe u

namespace MixedCrossingCompositesAux

open MackeyDiagrams

-- The typed singleton labels have the ordinary crossing evaluations.
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

end Drawings

private theorem fiberCard {X Y : Type*} (f : X → Y) (y : Y)
    (hf : Set.Finite {x | f x = y}) (S : Finset X)
    (hS : ∀ x, x ∈ S ↔ f x = y) :
    Nat.card {x | f x = y} = S.card := by
  have h : hf.toFinset = S := Finset.ext fun x => hf.mem_toFinset.trans (hS x).symm
  let := hf.fintype
  rw [Nat.card_eq_fintype_card, ← hf.card_toFinset, h]

private theorem sum_single_apply {X : Type*} [DecidableEq X] (S : Finset X) (w : X) :
    (S.sum (fun x => Finsupp.single x (1 : Complex))) w =
      if w ∈ S then 1 else 0 := by
  classical
  change (Finsupp.lapply w : (X →₀ Complex) →ₗ[Complex] Complex) _ = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply, Finset.sum_ite_eq']

end MixedCrossingCompositesAux


theorem MixedCrossingComposites : (
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
) :=
(by
  classical
  intro U inst K H G L α β a b hα hβ ha hb hs eα eβ ea eb d s A B J σ hσ
    conjSubgroup Lj leftJ rightJ Mj M ML Ls Limage n qBasis q hIndex
  -- This item has no matching Alphabeta Math portal entry in the reviewed plan.
  -- Steps 1–3 of the argument in Xiao, §5.1, Proposition 5.1: the typed
  -- generators encode the balanced push and the reverse-cup/trace fiber sum.
  -- MixedCrossingFiberMaps supplies the image and stabilizer index at s,
  -- with finite relative index hIndex. This computes the cardinal directly
  -- at the original label, so Lemma 5.2's transport is unnecessary.
  obtain ⟨_, _, _, range_q, card_q, finite_q, _⟩ :=
    MixedCrossingFiberMaps K H G L α β a b hα hβ ha hb hs σ hσ
  have hf : ∀ z : M.basis.carrier, Set.Finite {w | qBasis w = z} := finite_q.mpr hIndex
  refine ⟨hf, ?_⟩
  intro ι p pThenIota iotaThenP straight evaluate orbit P finiteQ j hj
  -- Mathlib's DoubleCoset.eq converts s ∈ orbit j into the equality of classes
  -- using hσ. This connects the supplier's chosen class to the requested P j.
  have hj_eq : DoubleCoset.mk A B s = j := by
    rw [← hσ j]
    exact (DoubleCoset.eq.mpr (DoubleCoset.mem_doubleCoset.mp hj)).symm
  have hRange : Set.range q = orbit j := by
    rw [← hj_eq]
    exact range_q
  have hCard (g : G) (hg : g ∈ orbit j) : Nat.card {w | q w = g} = n := by
    rw [← hj_eq] at hg
    exact card_q g hg hIndex
  have hp : evaluate p = (MackeyDiagrams.Diagram.mixedProjection (R := Complex) eα eβ ea eb d hf).eval :=
    MixedCrossingCompositesAux.projection_eval eα eβ ea eb d hf
  have hι : evaluate ι = (MackeyDiagrams.Diagram.mixedMultiplication (R := Complex) eα eβ ea eb d).eval :=
    MixedCrossingCompositesAux.multiplication_eval eα eβ ea eb d
  let outer := MackeyDiagrams.Generator.mixedEquiv eα eβ
  have memOuter (z : M.basis.carrier) (w : ML.basis.carrier) :
      w ∈ (hf z).toFinset ↔ q w = outer z := by
    rw [(hf z).mem_toFinset]
    change qBasis w = z ↔ outer (qBasis w) = outer z
    exact outer.injective.eq_iff.symm
  have outerCard (z : M.basis.carrier) (hz : outer z ∈ orbit j) :
      (hf z).toFinset.card = n := by
    have hFinite : Set.Finite {w | q w = outer z} :=
      (hf z).subset fun _ hw => outer.injective hw
    exact (MixedCrossingCompositesAux.fiberCard q (outer z) hFinite _ (memOuter z)).symm.trans
      (hCard (outer z) hz)
  have innerFinset (z : ML.basis.carrier) :
      (hf (qBasis z)).toFinset = (finiteQ z).toFinset :=
    Finset.ext fun w => (memOuter (qBasis z) w).trans (finiteQ z).mem_toFinset.symm
  have innerCard (z : ML.basis.carrier) : (finiteQ z).toFinset.card = n := by
    rw [← innerFinset]
    exact outerCard (qBasis z) (hRange ▸ ⟨z, rfl⟩)
  -- Step 4: compose transfer and push in both orders. The compact
  -- projection needs only finite surviving fibers, as in the paragraph
  -- following the proof. The singleton evaluation adapters preserve
  -- the two labelled drawing stacks in the statement.
  have hInner (z : ML.basis.carrier) :
      (evaluate iotaThenP).toLinearMap (Finsupp.single z 1) =
        (finiteQ z).toFinset.sum (fun w => Finsupp.single w (1 : Complex)) := by
    change ((evaluate ι).vertical (evaluate p)).toLinearMap _ = _
    rw [hp, hι, ← innerFinset]
    exact MackeyDiagrams.Diagram.inclusion_then_projection_single Complex eα eβ ea eb d hf z
  have hOuter (z : M.basis.carrier) :
      (evaluate pThenIota).toLinearMap (Finsupp.single z 1) =
        Finsupp.single z ((hf z).toFinset.card : Complex) := by
    change ((evaluate p).vertical (evaluate ι)).toLinearMap _ = _
    rw [hp, hι]
    exact MackeyDiagrams.Diagram.projection_then_inclusion_single Complex eα eβ ea eb d hf z
  -- Step 5: an identity column has its own
  -- coefficient one and every other coefficient zero. The scaled
  -- column therefore imposes incompatible equations when n > 1.
  let z₀ : ML.basis.carrier := MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction ea) (MackeyDiagrams.Biset.restriction eb) 1 1
  have self_mem (z : ML.basis.carrier) : z ∈ (finiteQ z).toFinset :=
    (finiteQ z).mem_toFinset.mpr rfl
  have strict_fiber (hn : 1 < n) :
      ∃ w ∈ (finiteQ z₀).toFinset, w ≠ z₀ := by
    by_contra! h
    have hle := Finset.card_le_one.mpr
      (fun w hw v hv => (h w hw).trans (h v hv).symm)
    exact (not_le_of_gt hn) ((innerCard z₀) ▸ hle)
  have straight_column (z : ML.basis.carrier) :
      (evaluate straight).toLinearMap (Finsupp.single z 1) = Finsupp.single z 1 := rfl
  refine ⟨?_, hInner, ?_, ?_⟩
  · apply Finsupp.lhom_ext'
    intro z
    apply LinearMap.ext_ring
    change (evaluate pThenIota).toLinearMap (Finsupp.single z 1) =
      ((n : Complex) • P j) (Finsupp.single z 1)
    rw [hOuter]
    have hP : (P j) (Finsupp.single z 1) =
        if outer z ∈ orbit j then Finsupp.single z (1 : Complex) else 0 := by
      dsimp only [P]
      rw [Finsupp.lsum_single]
      change (if outer z ∈ orbit j then Finsupp.lsingle z else 0) (1 : Complex) = _
      by_cases hz : outer z ∈ orbit j <;> simp [hz]
    rw [LinearMap.smul_apply, hP]
    by_cases hz : outer z ∈ orbit j
    · rw [ite_eq_left hz, outerCard z hz, Finsupp.smul_single, smul_eq_mul, mul_one]
    · have hEmpty : (hf z).toFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact hz (hRange ▸ ⟨w, (memOuter z w).mp hw⟩)
      simp [hz, hEmpty]
  · constructor
    · intro hEq
      have hle : n ≤ 1 := by
        by_contra! hn
        obtain ⟨w, hw, hne⟩ := strict_fiber hn
        have h := hInner z₀
        rw [hEq, straight_column] at h
        have hwEq := congrArg (fun v : ML.basis.carrier →₀ Complex => v w) h
        change Finsupp.single z₀ (1 : Complex) w = _ at hwEq
        rw [MixedCrossingCompositesAux.sum_single_apply, ite_eq_left hw, Finsupp.single_eq_of_ne hne] at hwEq
        exact zero_ne_one hwEq
      rw [← innerCard z₀]
      exact Nat.le_antisymm ((innerCard z₀).symm ▸ hle)
        (Finset.card_pos.mpr ⟨z₀, self_mem z₀⟩)
    · intro hn
      apply MackeyDiagrams.Biset.Hom.ext
      apply Finsupp.lhom_ext'
      intro z
      apply LinearMap.ext_ring
      change (evaluate iotaThenP).toLinearMap (Finsupp.single z 1) =
        (evaluate straight).toLinearMap (Finsupp.single z 1)
      rw [hInner, straight_column]
      have hOne : (finiteQ z).toFinset = {z} :=
        Finset.card_eq_one.mp ((innerCard z).trans hn) |>.elim fun w hw => by
          have hz := self_mem z
          rw [hw, Finset.mem_singleton] at hz
          simpa [hz] using hw
      rw [hOne, Finset.sum_singleton]
  · intro hn c hEq
    obtain ⟨w, hw, hne⟩ := strict_fiber hn
    have hScaled : c • (evaluate iotaThenP).toLinearMap (Finsupp.single z₀ 1) =
        (evaluate straight).toLinearMap (Finsupp.single z₀ 1) :=
      congrArg (fun f => f.toLinearMap (Finsupp.single z₀ 1)) hEq
    rw [hInner, straight_column] at hScaled
    have hzEq := congrArg (fun v : ML.basis.carrier →₀ Complex => v z₀) hScaled
    have hwEq := congrArg (fun v : ML.basis.carrier →₀ Complex => v w) hScaled
    change (_ • _ : ML.basis.carrier →₀ Complex) z₀ = _ at hzEq
    change (_ • _ : ML.basis.carrier →₀ Complex) w = _ at hwEq
    rw [Finsupp.smul_apply, MixedCrossingCompositesAux.sum_single_apply,
      ite_eq_left (self_mem z₀), Finsupp.single_eq_same, smul_eq_mul, mul_one] at hzEq
    rw [Finsupp.smul_apply, MixedCrossingCompositesAux.sum_single_apply,
      ite_eq_left hw, Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_one] at hwEq
    exact one_ne_zero (hzEq.symm.trans hwEq))

#print axioms MixedCrossingComposites
