import Mathlib.RepresentationTheory.FiniteIndex
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.InductionRestrictionAdjunction

universe u v
set_option maxHeartbeats 1500000
namespace FiniteIndexReverseAdjunctionSupport

open MackeyDiagrams CategoryTheory Representation

noncomputable section

variable {U : Type u} [Group U] {H G : Subgroup U} (a : ConjEmbedding H G)

local notation "A" => MonoidAlgebra Complex H
local notation "B" => MonoidAlgebra Complex G
local notation "Img" => a.toHom.range
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

private theorem trace_outside (g : G) (hg : g ∉ Img) : trace a (bG g) = 0 := by
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
        by_cases hg : g ∈ Img
        · obtain ⟨l,rfl⟩ := hg
          simp only [MonoidAlgebra.single_mul_single, mul_one, ← map_mul, trace_image]
        · have hn : a.toHom h * g * a.toHom k ∉ Img := by
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
  ∀ g : G, ∃! t : {t : G // t ∈ T}, g * t.val⁻¹ ∈ Img

private def quotientEquiv (T : Finset G) (hT : IsTransversal a T) :
    {t : G // t ∈ T} ≃ Quotient (QuotientGroup.rightRel Img) :=
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

private theorem transversal_exists (finite : a.toHom.range.FiniteIndex) :
    ∃ T : Finset G, IsTransversal a T := by
  classical
  letI := finite
  letI : Fintype (G ⧸ Img) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel Img)) :=
    Fintype.ofEquiv (G ⧸ Img) (QuotientGroup.quotientRightRelEquivQuotientLeftRel Img).symm
  let T := Finset.univ.image (Quotient.out (s := QuotientGroup.rightRel Img))
  refine ⟨T, fun g => ?_⟩
  let q := Quotient.mk (QuotientGroup.rightRel Img) g
  refine ⟨⟨q.out, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩, ?_, ?_⟩
  · exact QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq q))
  · intro t ht
    apply Subtype.ext
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp t.property
    have he : Quotient.mk (QuotientGroup.rightRel Img) (t : G) = q :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr ht)
    rw [← hp, ← he, ← hp, Quotient.out_eq]

private theorem cup_fiberSum (finite : a.toHom.range.FiniteIndex) (g : G) :
    (Diagram.reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single g 1) =
      ∑ p ∈ (Generator.multiplicationCap_finiteFiber a finite g).toFinset, Finsupp.single p 1 := by
  classical
  change (Generator.reverseCup Complex a finite).toLinearMap (Finsupp.single g 1) = _
  unfold Generator.reverseCup Biset.Hom.transfer
  rw [Biset.Hom.ofBasis_single, one_smul]
  ext p
  rw [Biset.Hom.transferBasis_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]

private theorem cup_leftSum (finite : a.toHom.range.FiniteIndex) (T : Finset G)
    (hT : IsTransversal a T) (g : G) :
    (Diagram.reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single g 1) =
      ∑ t ∈ T, Finsupp.single ((Biset.induction a).pair (Biset.restriction a) (g * t⁻¹) t) 1 := by
  classical
  rw [cup_fiberSum]
  symm
  let e := (quotientEquiv a T hT).trans (Generator.rightCosetEquivCapFiber a g)
  have he (t : G) (ht : t ∈ T) :
      (e ⟨t,ht⟩).val = (Biset.induction a).pair (Biset.restriction a) (g * t⁻¹) t := rfl
  refine Finset.sum_bij (fun t ht => (e ⟨t,ht⟩).val) ?_ ?_ ?_ ?_
  · intro t ht
    exact (Generator.multiplicationCap_finiteFiber a finite g).mem_toFinset.mpr
      (e ⟨t,ht⟩).property
  · intro t ht r hr h
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  · intro p hp
    obtain ⟨t, ht⟩ := e.surjective ⟨p,
      (Generator.multiplicationCap_finiteFiber a finite g).mem_toFinset.mp hp⟩
    exact ⟨t.val,t.property,congrArg Subtype.val ht⟩
  · intro t ht
    rw [he]

private theorem transversal_mul (T : Finset G) (hT : IsTransversal a T) (g : G)
    [DecidableEq G] : IsTransversal a (T.image (· * g)) := by
  intro q
  obtain ⟨t, ht, hu⟩ := hT (q * g⁻¹)
  have hm (x : G) : q * (x * g)⁻¹ = q * g⁻¹ * x⁻¹ := by group
  refine ⟨⟨(t : G) * g, Finset.mem_image.mpr ⟨t, t.property, rfl⟩⟩, ?_, ?_⟩
  · change q * ((t : G) * g)⁻¹ ∈ Img
    rwa [hm]
  · intro s hs
    obtain ⟨r, hr, hrg⟩ := Finset.mem_image.mp s.property
    have hqr : q * g⁻¹ * r⁻¹ ∈ Img := by
      rw [← hm, hrg]
      exact hs
    exact Subtype.ext (hrg.symm.trans (congrArg (fun x : {x // x ∈ T} =>
      (x : G) * g) (hu ⟨r,hr⟩ hqr)))

private theorem cup_rightSum (finite : a.toHom.range.FiniteIndex) (T : Finset G)
    (hT : IsTransversal a T) (g : G) :
    (Diagram.reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single g 1) =
      ∑ t ∈ T, Finsupp.single ((Biset.induction a).pair (Biset.restriction a) t⁻¹ (t * g)) 1 := by
  classical
  rw [cup_leftSum a finite (T.image (· * g)) (transversal_mul a T hT g),
    Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h)]
  apply Finset.sum_congr rfl
  intro t _
  have h : g * (t * g)⁻¹ = t⁻¹ := by group
  rw [h]
section Representations

local notation "f" => a.toHom
local notation "τ" => fun g : G => trace a (bG g)

private theorem trace_left (h : H) (g : G) : τ (f h * g) = bH h * τ g := by
  have e := trace_bimodule a (bH h) 1 (bG g)
  rw [map_one, mul_one, mul_one] at e
  change trace a (bG (f h) * bG g) = _ at e
  simpa only [MonoidAlgebra.single_mul_single, mul_one] using e

private theorem trace_right (h : H) (g : G) : τ (g * f h) = τ g * bH h := by
  have e := trace_bimodule a 1 (bH h) (bG g)
  rw [map_one, one_mul, one_mul] at e
  change trace a (bG g * bG (f h)) = _ at e
  simpa only [MonoidAlgebra.single_mul_single, mul_one] using e

variable (X : Rep.{max u v} Complex H)

private def kernel (t q : G) : X →ₗ[Complex] X :=
  X.ρ.asAlgebraHom (τ (q * t⁻¹))

private theorem kernel_left (t q : G) (h : H) (x : X) :
    kernel a X t (f h * q) x = X.ρ h (kernel a X t q x) := by
  simp only [kernel, mul_assoc, trace_left, map_mul, mul_apply_eq_comp,
    Representation.asAlgebraHom_single_one]

private theorem kernel_balance (t q : G) (h : H) (x : X) :
    kernel a X (f h * t) q (X.ρ h x) = kernel a X t q x := by
  simp only [kernel, mul_inv_rev, ← mul_assoc, ← map_inv, trace_right, map_mul,
    mul_apply_eq_comp, Representation.asAlgebraHom_single_one]
  have hh : X.ρ h⁻¹ (X.ρ h x) = x := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  simp only [mul_apply_eq_comp, hh]

private theorem kernel_at (t : G) (x : X) : kernel a X t t x = x := by
  have h : t * t⁻¹ = f 1 := by rw [mul_inv_cancel, map_one]
  unfold kernel
  rw [h]
  change X.ρ.asAlgebraHom (trace a (bG (f 1))) x = x
  rw [trace_image, Representation.asAlgebraHom_single_one, map_one]
  rfl

private theorem kernel_off (t q : G) (h : q * t⁻¹ ∉ Img) (x : X) :
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
    exact kernel_balance a X t q h x)

private theorem toCoind_mk (t q : G) (x : X) :
    (toCoindLinear a X (IndV.mk f X.ρ t x)).val q = kernel a X t q x := by
  simp [toCoindLinear]
  rfl

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
  let ev : coindV f X.ρ →ₗ[Complex] X := (LinearMap.proj q) ∘ₗ (coindV f X.ρ).subtype
  change ev (toCoindLinear a X (fromCoind a X T w)) = w.val q
  obtain ⟨t, ht, hu⟩ := hT q
  rw [fromCoind_apply, map_sum, map_sum]
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
      unfold kernel
      rw [he]
      change X.ρ.asAlgebraHom (trace a (bG (f h⁻¹))) x = _
      rw [trace_image, Representation.asAlgebraHom_single_one]
    rw [hker, hq]
    have he : f h * (t : G) = f h⁻¹⁻¹ * (t : G) := by rw [inv_inv]
    rw [he]
    simp [Coinvariants.mk_inv_tmul ((leftRegular Complex G).comp f) X.ρ
      (bG (t : G)) x h⁻¹]
  · intro r hr hrt
    have hn : r * q⁻¹ ∉ Img := fun hm => hrt (congrArg Subtype.val
      (hu ⟨r,hr⟩ (by simpa using a.toHom.range.inv_mem hm)))
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
    (show Function.LeftInverse (fromCoind a X T) (toCoindLinear a X) from
      fun x => LinearMap.congr_fun (fromCoind_toCoind a X T hT) x).injective
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
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext q
    change (toCoindLinear a Y (IndV.mk f Y.ρ t (l.hom x))).val q =
      l.hom ((toCoindLinear a X (IndV.mk f X.ρ t x)).val q)
    rw [toCoind_mk, toCoind_mk]
    unfold kernel
    generalize trace a (bG (q * t⁻¹)) = b
    induction b using MonoidAlgebra.induction_on with
    | of h => simpa only [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one] using
        (Rep.hom_comm_apply l h x).symm
    | add b c hb hc => simp only [map_add, LinearMap.add_apply, hb, hc]
    | smul c b hb => simp only [map_smul, LinearMap.smul_apply, hb])

end Representations
end
end FiniteIndexReverseAdjunctionSupport
