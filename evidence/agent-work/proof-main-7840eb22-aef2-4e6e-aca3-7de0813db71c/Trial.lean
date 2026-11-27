import Mathlib.RepresentationTheory.FiniteIndex
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.InductionRestrictionAdjunction

universe u v
namespace FiniteIndexReverseAdjunctionSupport

open MackeyDiagrams CategoryTheory Representation

noncomputable section

variable {U : Type u} [Group U] {H G : Subgroup U} (a : ConjEmbedding H G)

local notation "A" => MonoidAlgebra Complex H
local notation "B" => MonoidAlgebra Complex G
local notation "S" => a.toHom.range
local notation "φ" => MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
local notation "bG" => fun g : G => MonoidAlgebra.single g (1 : Complex)
local notation "bH" => fun h : H => MonoidAlgebra.single h (1 : Complex)

private def trace : B →ₗ[Complex] A :=
  (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap ∘ₗ
    freeLift Complex (Generator.traceBasis Complex a) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap

private theorem trace_single (g : G) (c : Complex) :
    trace a (MonoidAlgebra.single g c) =
      MonoidAlgebra.ofCoeff (c • Generator.traceBasis Complex a g) := by
  change MonoidAlgebra.ofCoeff
    (freeLift Complex (Generator.traceBasis Complex a) (Finsupp.single g c)) = _
  rw [freeLift_single]

private theorem trace_image (h : H) : trace a (bG (a.toHom h)) = bH h := by
  rw [trace_single, Generator.traceBasis_image, one_smul]
  rfl

private theorem trace_outside (g : G) (hg : g ∉ S) : trace a (bG g) = 0 := by
  rw [trace_single, Generator.traceBasis_outside _ _ _ hg, smul_zero]
  rfl

private theorem trace_bimodule (r s : A) (x : B) :
    trace a (φ r * x * φ s) = r * trace a x * s := by
  induction r using MonoidAlgebra.induction_on with
  | add r r' hr hr' => simp only [map_add, add_mul, hr, hr']
  | smul c r hr => simp only [map_smul, smul_mul_assoc, hr]
  | of h =>
    induction s using MonoidAlgebra.induction_on with
    | add s s' hs hs' => simp only [map_add, mul_add, hs, hs']
    | smul c s hs => simp only [map_smul, mul_smul_comm, hs]
    | of k =>
      induction x using MonoidAlgebra.induction_on with
      | add x x' hx hx' => simp only [mul_add, add_mul, map_add, hx, hx']
      | smul c x hx => simp only [mul_smul_comm, smul_mul_assoc, map_smul, hx]
      | of g =>
        change trace a (bG (a.toHom h) * bG g * bG (a.toHom k)) =
          bH h * trace a (bG g) * bH k
        by_cases hg : g ∈ S
        · obtain ⟨l,rfl⟩ := hg
          simp only [MonoidAlgebra.single_mul_single, mul_one, ← map_mul, trace_image]
        · have hn : a.toHom h * g * a.toHom k ∉ S := by
            rintro ⟨l,hl⟩
            apply hg
            refine ⟨h⁻¹ * l * k⁻¹, ?_⟩
            simp only [map_mul, map_inv, hl]
            group
          simp only [MonoidAlgebra.single_mul_single, mul_one, trace_outside a _ hg,
            trace_outside a _ hn, mul_zero, zero_mul]

private theorem cap_pair (x y : B) :
    (Diagram.traceCap (R := Complex) a).eval.toLinearMap
      (Biset.pairLinear Complex (Word.down a).basis (Word.up a).basis x.coeff y.coeff) =
      (trace a (x * y)).coeff := by
  let p := Biset.pairLinear Complex (Word.down a).basis (Word.up a).basis
  let cap := (Diagram.traceCap (R := Complex) a).eval.toLinearMap
  let coeff := MonoidAlgebra.coeffLinearEquiv (M := G) (S := Complex) Complex
  let coeffA := MonoidAlgebra.coeffLinearEquiv (M := H) (S := Complex) Complex
  let prod := ((LinearMap.mul Complex B).compl₂ coeff.symm.toLinearMap) ∘ₗ coeff.symm.toLinearMap
  have he : p.compr₂ cap = prod.compr₂ (coeffA.toLinearMap ∘ₗ trace a) := by
    apply Finsupp.lhom_ext
    intro g c
    apply Finsupp.lhom_ext
    intro t d
    change cap (p (Finsupp.single g c) (Finsupp.single t d)) =
      (trace a (MonoidAlgebra.single g c * MonoidAlgebra.single t d)).coeff
    rw [Biset.pairLinear_single, Diagram.eval_traceCap_single,
      MonoidAlgebra.single_mul_single, trace_single]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun he x.coeff) y.coeff

private abbrev IsTransversal (T : Finset G) :=
  ∀ g : G, ∃! t : {t : G // t ∈ T}, g * t.val⁻¹ ∈ S

private def quotientEquiv (T : Finset G) (hT : IsTransversal a T) :
    {t : G // t ∈ T} ≃ Quotient (QuotientGroup.rightRel S) :=
  Equiv.ofBijective (fun t => Quotient.mk _ t.val) (by
    constructor
    · intro t s h
      obtain ⟨r, _, hu⟩ := hT (t : G)
      exact (hu t (by simp)).trans
        (hu s (QuotientGroup.rightRel_apply.mp (Quotient.exact h.symm))).symm
    · intro q
      refine Quotient.inductionOn q (fun g => ?_)
      obtain ⟨t, ht, _⟩ := hT g
      exact ⟨t, Quotient.sound (QuotientGroup.rightRel_apply.mpr ht)⟩)

private theorem transversal_exists (finite : S.FiniteIndex) :
    ∃ T : Finset G, IsTransversal a T := by
  classical
  letI := finite
  letI : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    Fintype.ofEquiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  let T := Finset.univ.image (Quotient.out (s := QuotientGroup.rightRel S))
  refine ⟨T, fun g => ?_⟩
  let q := Quotient.mk (QuotientGroup.rightRel S) g
  refine ⟨⟨q.out, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩, ?_, ?_⟩
  · exact QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq q).symm)
  · intro t ht
    apply Subtype.ext
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp t.property
    have he : Quotient.mk (QuotientGroup.rightRel S) (t : G) = q :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr ht)
    rw [← hp, ← he, ← hp, Quotient.out_eq]
end FiniteIndexReverseAdjunctionSupport
