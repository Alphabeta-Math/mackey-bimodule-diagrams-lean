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
section Representations

local notation "f" => a.toHom
local notation "τ" => fun g : G => trace a (bG g)

private theorem trace_left (h : H) (g : G) : τ (f h * g) = bH h * τ g := by
  simpa only [map_one, mul_one, MonoidAlgebra.single_mul_single, one_mul] using
    trace_bimodule a (bH h) 1 (bG g)

private theorem trace_right (h : H) (g : G) : τ (g * f h) = τ g * bH h := by
  simpa only [map_one, one_mul, MonoidAlgebra.single_mul_single, mul_one] using
    trace_bimodule a 1 (bH h) (bG g)

variable (X : Rep.{max u v} Complex H)

private def kernel (t q : G) : X →ₗ[Complex] X :=
  X.ρ.asAlgebraHom (τ (q * t⁻¹))

private theorem kernel_left (t q : G) (h : H) (x : X) :
    kernel a X t (f h * q) x = X.ρ h (kernel a X t q x) := by
  simp only [kernel, mul_assoc, trace_left, map_mul, Module.End.mul_apply,
    Representation.asAlgebraHom_single_one]

private theorem kernel_balance (t q : G) (h : H) (x : X) :
    kernel a X (f h * t) q (X.ρ h x) = kernel a X t q x := by
  simp only [kernel, mul_inv_rev, ← mul_assoc, ← map_inv, trace_right, map_mul,
    Module.End.mul_apply, Representation.asAlgebraHom_single_one]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem kernel_at (t : G) (x : X) : kernel a X t t x = x := by
  simp only [kernel, mul_inv_cancel, ← map_one f, trace_image,
    Representation.asAlgebraHom_single_one, map_one]
  rfl

private theorem kernel_off (t q : G) (h : q * t⁻¹ ∉ S) (x : X) :
    kernel a X t q x = 0 := by
  simp only [kernel, trace_outside a _ h, map_zero, LinearMap.zero_apply]

-- The coordinator's Mathlib comparison is stated for a subgroup inclusion.
-- Use its indToCoind and coindToInd construction with the image test and
-- the unique preimage supplied by the typed trace. This retains the given
-- embedding in both functors and implements the transport on generators.
private def kernelMap (t : G) : X →ₗ[Complex] coindV f X.ρ :=
  (LinearMap.pi (kernel a X t)).codRestrict _ (by
    intro x h q
    exact kernel_left a X t q h x)

private def toCoindLinear : IndV f X.ρ →ₗ[Complex] coindV f X.ρ :=
  Coinvariants.lift _
    (TensorProduct.lift <| freeLift Complex (kernelMap a X) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap) (by
    intro h
    ext t x q
    simpa [kernelMap] using kernel_balance a X t q h x)

private theorem toCoind_mk (t q : G) (x : X) :
    (toCoindLinear a X (IndV.mk f X.ρ t x)).val q = kernel a X t q x := by
  simp [toCoindLinear, kernelMap]

private def toCoind : Rep.ind f X ⟶ Rep.coind f X :=
  Rep.ofHom ⟨toCoindLinear a X, fun g => by
    apply IndV.hom_ext
    intro t
    ext x q
    change (toCoindLinear a X (ind f X.ρ g (IndV.mk f X.ρ t x))).val q =
      (toCoindLinear a X (IndV.mk f X.ρ t x)).val (q * g)
    rw [ind_mk, toCoind_mk, toCoind_mk]
    simp [kernel, mul_assoc]⟩

private def fromCoind (T : Finset G) : coindV f X.ρ →ₗ[Complex] IndV f X.ρ :=
  ∑ t ∈ T, (IndV.mk f X.ρ t) ∘ₗ (LinearMap.proj t) ∘ₗ (coindV f X.ρ).subtype

private theorem fromCoind_apply (T : Finset G) (w : coindV f X.ρ) :
    fromCoind a X T w = ∑ t ∈ T, IndV.mk f X.ρ t (w.val t) := by
  simp [fromCoind]

private theorem toCoind_fromCoind (T : Finset G) (hT : IsTransversal a T) :
    toCoindLinear a X ∘ₗ fromCoind a X T = LinearMap.id := by
  ext w q
  change (toCoindLinear a X (fromCoind a X T w)).val q = w.val q
  obtain ⟨t, ht, hu⟩ := hT q
  rw [fromCoind_apply, map_sum]
  change (∑ r ∈ T, (toCoindLinear a X (IndV.mk f X.ρ r (w.val r))).val q) = _
  simp only [toCoind_mk]
  rw [Finset.sum_eq_single_of_mem (t : G) t.property]
  · obtain ⟨h, hh⟩ := ht
    have hq : q = f h * (t : G) := by rw [hh]; group
    rw [hq, kernel_left, kernel_at]
    exact (w.property h t).symm
  · intro r hr hrt
    exact kernel_off a X r q (fun hn => hrt (congrArg Subtype.val (hu ⟨r,hr⟩ hn))) _

private theorem fromCoind_toCoind (T : Finset G) (hT : IsTransversal a T) :
    fromCoind a X T ∘ₗ toCoindLinear a X = LinearMap.id := by
  apply IndV.hom_ext
  intro q
  ext x
  change fromCoind a X T (toCoindLinear a X (IndV.mk f X.ρ q x)) = IndV.mk f X.ρ q x
  obtain ⟨t, ht, hu⟩ := hT q
  rw [fromCoind_apply]
  simp only [toCoind_mk]
  rw [Finset.sum_eq_single_of_mem (t : G) t.property]
  · obtain ⟨h, hh⟩ := ht
    have hq : q = f h * (t : G) := by rw [hh]; group
    have hker : kernel a X q t x = X.ρ h⁻¹ x := by
      have he : (t : G) * q⁻¹ = f h⁻¹ := by rw [hq, map_inv]; group
      rw [kernel, he, trace_image, Representation.asAlgebraHom_single_one]
    rw [hker, hq]
    have he : f h * (t : G) = f h⁻¹⁻¹ * (t : G) := by rw [inv_inv]
    rw [he]
    simpa using (Coinvariants.mk_inv_tmul ((leftRegular Complex G).comp f) X.ρ
      (bG (t : G)) x h⁻¹).symm
  · intro r hr hrt
    have hn : r * q⁻¹ ∉ S := fun hm => hrt (congrArg Subtype.val
      (hu ⟨r,hr⟩ (by simpa using S.inv_mem hm)))
    rw [kernel_off a X q r hn, map_zero]

private def indCoind (T : Finset G) (hT : IsTransversal a T) :
    Rep.ind f X ≅ Rep.coind f X :=
  Rep.mkIso (.mk (.ofLinear (toCoindLinear a X) (fromCoind a X T)
    (toCoind_fromCoind a X T hT) (fromCoind_toCoind a X T hT)) (toCoind a X).hom.2)

private theorem indCoind_inv_independent (T T' : Finset G)
    (hT : IsTransversal a T) (hT' : IsTransversal a T') :
    fromCoind a X T = fromCoind a X T' := by
  ext w
  have hi : Function.Injective (toCoindLinear a X) :=
    (LinearEquiv.ofLinear (toCoindLinear a X) (fromCoind a X T)
      (toCoind_fromCoind a X T hT) (fromCoind_toCoind a X T hT)).injective
  apply hi
  exact (LinearMap.congr_fun (toCoind_fromCoind a X T hT) w).trans
    (LinearMap.congr_fun (toCoind_fromCoind a X T' hT') w).symm

private def indCoindNat (T : Finset G) (hT : IsTransversal a T) :
    Rep.indFunctor Complex f ≅ Rep.coindFunctor Complex f :=
  NatIso.ofComponents (fun X => indCoind a X T hT) (by
    intro X Y l
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    apply IndV.hom_ext
    intro t
    ext x q
    change kernel a Y t q (l.hom x) = l.hom (kernel a X t q x)
    unfold kernel
    generalize trace a (bG (q * t⁻¹)) = b
    induction b using MonoidAlgebra.induction_on with
    | of h => simpa only [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one] using
        (Rep.hom_comm_apply l h x).symm
    | add b c hb hc => simp only [map_add, LinearMap.add_apply, hb, hc]
    | smul c b hb => simp only [map_smul, LinearMap.smul_apply, hb])

end Representations
end FiniteIndexReverseAdjunctionSupport
