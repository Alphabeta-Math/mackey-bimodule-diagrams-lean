import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Coset.Basic
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands

set_option maxHeartbeats 2000000

theorem GroupElementDotCriterion : (∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
  (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
  (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let C := (Subgroup.centralizer (H : Set U) : Set U)
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom a)
  let ψ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom b)
  let up := fun t : MackeyDiagrams.Dot a b =>
    MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.upDot (R := Complex) t)
  let down := fun t : MackeyDiagrams.Dot a b =>
    MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.downDot (R := Complex) t)
  (φ = ψ ↔ LeftCosetEquivalence C α β) ∧
  (∀ d : G,
    let rightMul := fun x : B => x * MonoidAlgebra.single d 1
    let intertwines := ∀ h : H,
      MackeyDiagrams.ConjEmbedding.toHom a h * d = d * MackeyDiagrams.ConjEmbedding.toHom b h
    ((∀ (x : B) (r : A), rightMul (x * φ r) = rightMul x * ψ r) ↔ intertwines) ∧
    (intertwines ↔ (d : U) ∈ Set.image (fun c : U => α * c * β⁻¹) C) ∧
    (intertwines ↔ ∃ α' β' : U, LeftCosetEquivalence C α α' ∧
      LeftCosetEquivalence C β β' ∧ (d : U) = α' * (β')⁻¹) ∧
    (intertwines ↔ ∃ t : MackeyDiagrams.Dot a b, MackeyDiagrams.Dot.element t = d)) ∧
  (∀ (t : MackeyDiagrams.Dot a b) (x : B),
    MackeyDiagrams.Biset.Hom.toLinearMap (up t) (MonoidAlgebra.coeff x) =
      MonoidAlgebra.coeff (x * MonoidAlgebra.single (MackeyDiagrams.Dot.element t) 1) ∧
    MackeyDiagrams.Biset.Hom.toLinearMap (down t) (MonoidAlgebra.coeff x) =
      MonoidAlgebra.coeff (MonoidAlgebra.single (MackeyDiagrams.Dot.element t)⁻¹ 1 * x)) ∧
  (∀ t s : MackeyDiagrams.Dot a b,
    let sameElement := MackeyDiagrams.Dot.element t = MackeyDiagrams.Dot.element s
    (up t = up s ↔ sameElement) ∧ (down t = down s ↔ sameElement))) :=
(by
  intro U inst H G α β hα hβ A B C a b φ ψ up down
  have onA (h : H) (r : Complex) :
      φ (MonoidAlgebra.single h r) = MonoidAlgebra.single (a.toHom h) r :=
    MonoidAlgebra.mapDomain_single
  have onB (h : H) (r : Complex) :
      ψ (MonoidAlgebra.single h r) = MonoidAlgebra.single (b.toHom h) r :=
    MonoidAlgebra.mapDomain_single
  have singleInject : Function.Injective (fun k : G => MonoidAlgebra.single k (1 : Complex)) := by
    intro k l hel
    have hs := congrArg MonoidAlgebra.coeff hel
    change Finsupp.single k (1 : Complex) = Finsupp.single l 1 at hs
    by_contra hn
    have hv := DFunLike.congr_fun hs k
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hn] at hv
    exact one_ne_zero hv
  refine ⟨ConjugationEmbeddingCentralizerCoset H G α β hα hβ, ?_, ?_, ?_⟩
  · intro d rightMul intertwines
    have hlin : (∀ (x : B) (r : A), rightMul (x * φ r) = rightMul x * ψ r) ↔ intertwines := by
      constructor
      · intro he h
        have ha := he 1 (MonoidAlgebra.single h 1)
        dsimp only [rightMul] at ha
        rw [one_mul, one_mul, onA, onB, MonoidAlgebra.single_mul_single,
          MonoidAlgebra.single_mul_single, one_mul] at ha
        exact singleInject ha
      · intro h x r
        have he : φ r * MonoidAlgebra.single d 1 = MonoidAlgebra.single d 1 * ψ r := by
          induction r using MonoidAlgebra.induction_linear with
          | zero => simp
          | add r s hr hs => simp [add_mul, mul_add, hr, hs]
          | single z c =>
            rw [onA, onB, MonoidAlgebra.single_mul_single,
              MonoidAlgebra.single_mul_single, mul_one, one_mul, h z]
        change (x * φ r) * MonoidAlgebra.single d 1 =
          (x * MonoidAlgebra.single d 1) * ψ r
        rw [mul_assoc, he, ← mul_assoc]
    have hcent : intertwines ↔ (d : U) ∈ Set.image (fun c : U => α * c * β⁻¹) C := by
      constructor
      · intro he
        refine ⟨α⁻¹ * (d : U) * β, ?_, by group⟩
        apply Subgroup.mem_centralizer_iff.mpr
        intro k hk
        have h := congrArg Subtype.val (he ⟨k,hk⟩)
        change (α*k*α⁻¹) * (d : U) = (d : U) * (β*k*β⁻¹) at h
        calc
          k * (α⁻¹ * (d : U) * β) = α⁻¹ * ((α*k*α⁻¹) * (d : U)) * β := by group
          _ = α⁻¹ * ((d : U) * (β*k*β⁻¹)) * β := by rw [h]
          _ = (α⁻¹ * (d : U) * β) * k := by group
      · rintro ⟨c,hc,hd⟩ h
        apply Subtype.ext
        change (α*(h : U)*α⁻¹) * (d : U) = (d : U) * (β*(h : U)*β⁻¹)
        have he := Subgroup.mem_centralizer_iff.mp hc (h : U) h.property
        rw [← hd]
        calc
          (α * (h : U) * α⁻¹) * (α*c*β⁻¹) = α * ((h : U) * c) * β⁻¹ := by group
          _ = α * (c * (h : U)) * β⁻¹ := by rw [he]
          _ = (α*c*β⁻¹) * (β * (h : U) * β⁻¹) := by group
    refine ⟨hlin, hcent, hcent.trans ?_, ?_⟩
    · constructor
      · rintro ⟨c, hc, hd⟩
        refine ⟨α*c, β, ?_, rfl, hd.symm⟩
        apply (leftCoset_eq_iff (Subgroup.centralizer (H : Set U))).mpr
        simpa [C] using hc
      · rintro ⟨x,y,hx,hy,hd⟩
        have hx' := (leftCoset_eq_iff (Subgroup.centralizer (H : Set U))).mp hx
        have hy' := (leftCoset_eq_iff (Subgroup.centralizer (H : Set U))).mp hy
        refine ⟨(α⁻¹*x) * (β⁻¹*y)⁻¹,
          (Subgroup.centralizer (H : Set U)).mul_mem hx'
            ((Subgroup.centralizer (H : Set U)).inv_mem hy'), ?_⟩
        rw [hd]
        group
    · exact ⟨fun h => ⟨⟨d,h⟩,rfl⟩, fun ⟨t,h⟩ k => by rw [← h]; exact t.intertwines k⟩
  · intro t x
    constructor
    · change (MackeyDiagrams.Diagram.upDot (R := Complex) t).eval.toLinearMap x.coeff = _
      rw [← MackeyDiagrams.AlgebraUpDot.eval_ofGroupDot]
      rfl
    · exact MackeyDiagrams.Diagram.eval_downDot_groupAlgebra t x
  · intro t s sameElement
    let unitVector := Finsupp.single (1 : G) (1 : Complex)
    constructor
    · constructor
      · intro h
        have e := congrArg (fun d => d.toLinearMap unitVector) h
        dsimp only [up, down, unitVector] at e
        change (MackeyDiagrams.Diagram.upDot (R := Complex) t).eval.toLinearMap
            (Finsupp.single (1 : G) (1 : Complex)) =
          (MackeyDiagrams.Diagram.upDot (R := Complex) s).eval.toLinearMap (Finsupp.single (1 : G) (1 : Complex)) at e
        rw [MackeyDiagrams.Diagram.eval_upDot_single, MackeyDiagrams.Diagram.eval_upDot_single,
          one_mul, one_mul] at e
        exact singleInject (congrArg MonoidAlgebra.ofCoeff e)
      · intro h
        exact congrArg up (MackeyDiagrams.Dot.ext h)
    · constructor
      · intro h
        have e := congrArg (fun d => d.toLinearMap unitVector) h
        dsimp only [up, down, unitVector] at e
        change (MackeyDiagrams.Diagram.downDot (R := Complex) t).eval.toLinearMap
            (Finsupp.single (1 : G) (1 : Complex)) =
          (MackeyDiagrams.Diagram.downDot (R := Complex) s).eval.toLinearMap (Finsupp.single (1 : G) (1 : Complex)) at e
        rw [MackeyDiagrams.Diagram.eval_downDot_single, MackeyDiagrams.Diagram.eval_downDot_single,
          mul_one, mul_one] at e
        exact inv_injective (singleInject (congrArg MonoidAlgebra.ofCoeff e))
      · intro h
        exact congrArg down (MackeyDiagrams.Dot.ext h))
