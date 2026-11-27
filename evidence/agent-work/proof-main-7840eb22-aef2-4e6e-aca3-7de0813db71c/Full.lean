import Mathlib.RepresentationTheory.Coinduced
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.InductionRestrictionAdjunction

universe u v
set_option maxHeartbeats 2000000
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

private theorem phi_single (h : H) : φ (bH h) = bG (a.toHom h) := by
  change MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single h 1) = _
  rw [MonoidAlgebra.mapDomain_single]

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
        simp only [MonoidAlgebra.of_apply, phi_single]
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
  let := finite
  let : Fintype (G ⧸ Img) := Subgroup.fintypeQuotientOfFiniteIndex
  let : Fintype (Quotient (QuotientGroup.rightRel Img)) :=
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
  rw [Biset.Hom.transferBasis_apply]
  let ev : (((Biset.induction a).tensor (Biset.restriction a)).carrier →₀ Complex) →ₗ[Complex] Complex :=
    Finsupp.lapply p
  change _ = ev (∑ q ∈ _, Finsupp.single q 1)
  rw [map_sum]
  simp only [ev, Finsupp.lapply_apply, Finsupp.single_apply, Finset.sum_ite_eq',
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

-- A right transversal enumerates the entire multiplication-cap fiber.
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

-- Right multiplication by g permutes right cosets. Using t * g in
-- the left formula gives the same balanced class with first leg t⁻¹.
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
  rw [map_one, mul_one, mul_one, phi_single] at e
  simpa only [MonoidAlgebra.single_mul_single, mul_one] using e

private theorem trace_right (h : H) (g : G) : τ (g * f h) = τ g * bH h := by
  have e := trace_bimodule a 1 (bH h) (bG g)
  rw [map_one, one_mul, one_mul, phi_single] at e
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
  simp only [hh]

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
-- Adapt Rep.indToCoind, Rep.coindToInd and Rep.indCoindNatIso to the
-- given embedding by pulling the image-subgroup action back along
-- the unique preimage in the typed trace. This implements the transport
-- on generators and keeps the reviewed IndV presentation.
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
    simp [kernelMap]
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

-- Each inverse check reduces to the unique t with q in Img * t.
-- These are the one-term reductions in Xiao's dual-basis argument.
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
    simp
  · intro r hr hrt
    have hn : r * q⁻¹ ∉ Img := fun hm => hrt (congrArg Subtype.val
      (hu ⟨r,hr⟩ (by simpa using a.toHom.range.inv_mem hm)))
    rw [kernel_off a X q r hn, map_zero]

private def indCoind (T : Finset G) (hT : IsTransversal a T) :
    Rep.ind f X ≅ Rep.coind f X :=
  Rep.mkIso (.mk (.ofLinearMap (toCoindLinear a X) (fromCoind a X T)
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
    by_cases hm : q * t⁻¹ ∈ Img
    · obtain ⟨h, hh⟩ := hm
      unfold kernel
      rw [← hh]
      change Y.ρ.asAlgebraHom (trace a (bG (f h))) (l.hom x) =
        l.hom (X.ρ.asAlgebraHom (trace a (bG (f h))) x)
      rw [trace_image, Representation.asAlgebraHom_single_one,
        Representation.asAlgebraHom_single_one]
      exact (Rep.hom_comm_apply l h x).symm
    · rw [kernel_off a X t q hm, kernel_off a Y t q hm, map_zero])

end Representations

section Modules

local notation "f" => a.toHom

private abbrev Ind : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B :=
  (Rep.ofModuleMonoidAlgebra ⋙ Rep.indFunctor Complex f) ⋙ Rep.toModuleMonoidAlgebra

private abbrev Res : ModuleCat.{max u v} B ⥤ ModuleCat.{max u v} A :=
  ModuleCat.restrictScalars (φ).toRingHom

private abbrev restrictedRep : ModuleCat.{max u v} B ⥤ ModuleCat.{max u v} A :=
  (Rep.ofModuleMonoidAlgebra ⋙ Rep.resFunctor f) ⋙ Rep.toModuleMonoidAlgebra

private theorem restrictionAction (Y : ModuleCat.{max u v} B)
    (r : A) (y : (restrictedRep a).obj Y) :
    r • y = φ r • (show Y from y) := by
  let ρ := Representation.ofModule (k := Complex) (G := G) Y
  let σ : Representation Complex H (RestrictScalars Complex B Y) := ρ.comp f
  have hf : σ.asAlgebraHom = ρ.asAlgebraHom.comp φ := by
    apply (MonoidAlgebra.lift Complex _ H).symm.injective
    apply MonoidHom.ext
    intro h
    change σ.asAlgebraHom (bH h) = ρ.asAlgebraHom (φ (bH h))
    rw [phi_single, Representation.asAlgebraHom_single_one,
      Representation.asAlgebraHom_single_one]
    rfl
  change σ.asAlgebraHom r y = _
  rw [hf]
  exact Representation.ofModule_asAlgebraHom_apply_apply Y (φ r) y

private def restrictionIso : restrictedRep.{u,v} a ≅ Res.{u,v} a :=
  NatIso.ofComponents (fun Y =>
    (show (restrictedRep a).obj Y ≃ₗ[A] (Res a).obj Y from
      { toEquiv := Equiv.refl Y
        map_add' := fun _ _ => rfl
        map_smul' := restrictionAction a Y }).toModuleIso) (by
          intro X Y g
          apply ModuleCat.hom_ext
          ext x
          rfl)

-- Use Rep.resCoindAdjunction for the given homomorphism. The
-- finite-index comparison supplies the change of right adjoint.
private def repAdj (T : Finset G) (hT : IsTransversal a T) :
    Rep.resFunctor.{max u v} f ⊣ Rep.indFunctor Complex f :=
  (Rep.resCoindAdjunction Complex f).ofNatIsoRight (indCoindNat.{u,v} a T hT).symm

private def adjunction (T : Finset G) (hT : IsTransversal a T) :
    Res.{u,v} a ⊣ Ind.{u,v} a :=
  (((Rep.equivalenceModuleMonoidAlgebra (k := Complex) (G := G)).symm.toAdjunction.comp
    (repAdj.{u,v} a T hT)).comp
      (Rep.equivalenceModuleMonoidAlgebra (k := Complex) (G := H)).toAdjunction).ofNatIsoLeft
        (restrictionIso a)

private abbrev pureTensor (X : ModuleCat.{max u v} A) (b : B) (x : X) :
    (Ind a).obj X :=
  let ρ := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X |>.ρ
  (Representation.asModuleEquiv (Representation.ind f ρ)).symm
    (freeLift Complex (fun g : G => Representation.IndV.mk f ρ g⁻¹ x) b.coeff)

private theorem pure_single (X : ModuleCat.{max u v} A) (g : G) (x : X) :
    pureTensor a X (bG g) x =
      let ρ := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X |>.ρ
      (Representation.asModuleEquiv (Representation.ind f ρ)).symm
        (Representation.IndV.mk f ρ g⁻¹ x) := by
  simp only [pureTensor, MonoidAlgebra.coeff_single, freeLift_single, one_smul]
  rfl

private theorem counit_pure (T : Finset G) (hT : IsTransversal a T)
    (X : ModuleCat.{max u v} A) (b : B) (x : X) :
    ((adjunction a T hT).counit.app X).hom (pureTensor a X b x) = trace a b • x := by
  let Xr := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X
  let ev : coindV f Xr.ρ →ₗ[Complex] Xr := (LinearMap.proj 1) ∘ₗ (coindV f Xr.ρ).subtype
  let x' : Xr := x
  change ev (toCoindLinear a Xr (freeLift Complex (fun g : G => IndV.mk f Xr.ρ g⁻¹ x') b.coeff)) =
    trace a b • x
  have hact : ∀ r : A, (Xr.ρ.asAlgebraHom r) x' = r • x :=
    fun r => Representation.ofModule_asAlgebraHom_apply_apply X r x'
  rw [← hact]
  induction b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, freeLift_single, one_smul]
    change (toCoindLinear a Xr (IndV.mk f Xr.ρ g⁻¹ x')).val 1 = _
    rw [toCoind_mk]
    simp [kernel]
  | add b c hb hc =>
    simp only [MonoidAlgebra.coeff_add, map_add, hb, hc]
    rfl
  | smul c b hb =>
    simp only [MonoidAlgebra.coeff_smul, map_smul, hb]
    rfl

private theorem unit_sum (T T' : Finset G) (hT : IsTransversal a T) (hT' : IsTransversal a T')
    (Y : ModuleCat.{max u v} B) (y : Y) :
    ((adjunction a T hT).unit.app Y).hom y =
      ∑ t ∈ T', pureTensor a ((Res a).obj Y) (bG t⁻¹) (bG t • y) := by
  let Yr := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := G)).obj Y
  let X := Rep.res f Yr
  let y' : Yr := y
  let c : coindV f X.ρ := ⟨fun t => Yr.ρ t y', by
    intro h t
    change Yr.ρ (f h * t) y' = Yr.ρ (f h) (Yr.ρ t y')
    rw [map_mul, mul_apply_eq_comp]⟩
  -- Both changes of source representation act by the identity
  -- on the coefficient of each tensor generator.
  let F := Rep.indFunctor Complex f ⋙ Rep.toModuleMonoidAlgebra
  let transport := F.map (Rep.unitIso X).hom
  let comparison := (Ind a).map ((restrictionIso a).hom.app Y)
  let mapFromInd : F.obj X ⟶ (Ind a).obj ((Res a).obj Y) := transport ≫ comparison
  let gen (t : G) : F.obj X :=
    (ind f X.ρ).asModuleEquiv.symm (IndV.mk f X.ρ t (c.val t))
  let raw : F.obj X := (ind f X.ρ).asModuleEquiv.symm (fromCoind a X T c)
  have hsum : raw = ∑ t ∈ T', gen t := by
    change (ind f X.ρ).asModuleEquiv.symm (fromCoind a X T c) =
      ∑ t ∈ T', (ind f X.ρ).asModuleEquiv.symm (IndV.mk f X.ρ t (c.val t))
    rw [indCoind_inv_independent a X T T' hT hT', fromCoind_apply, map_sum]
  change mapFromInd.hom raw = _
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [pure_single, inv_inv]
  have ht : Yr.ρ t y' = bG t • y := by
    rw [← Representation.asAlgebraHom_single_one]
    exact Representation.ofModule_asAlgebraHom_apply_apply Y (bG t) y'
  change mapFromInd.hom (show F.obj X from (ind f X.ρ).asModuleEquiv.symm
    (IndV.mk f X.ρ t (Yr.ρ t y'))) = _
  rw [ht]
  rfl

private theorem unit_at_generator (T T' : Finset G) (hT : IsTransversal a T)
    (hT' : IsTransversal a T') (Y : ModuleCat.{max u v} B) (g : G) (z : Y) :
    ((adjunction a T hT).unit.app Y).hom (bG g • z) =
      ∑ t ∈ T', pureTensor a ((Res a).obj Y) (bG (g * t⁻¹)) (bG t • z) := by
  classical
  rw [unit_sum a T (T'.image (· * g⁻¹)) hT (transversal_mul a T' hT' g⁻¹),
    Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h)]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_inv_rev, inv_inv, ← mul_smul, MonoidAlgebra.single_mul_single, mul_one,
    inv_mul_cancel_right]

end Modules

end
end FiniteIndexReverseAdjunctionSupport
theorem FiniteIndexReverseAdjunction : (
∀ {U : Type u} [Group U] (H G : Subgroup U) (α : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := a.toHom.range
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
  let up := MackeyDiagrams.Word.up a
  let down := MackeyDiagrams.Word.down a
  let cap := MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.traceCap (R := Complex) a)
  let pairDI := fun (x y : B) =>
    MackeyDiagrams.Biset.pairLinear Complex down.basis up.basis
      (MonoidAlgebra.coeff x) (MonoidAlgebra.coeff y)
  let pairID := fun (x y : B) =>
    MackeyDiagrams.Biset.pairLinear Complex up.basis down.basis
      (MonoidAlgebra.coeff x) (MonoidAlgebra.coeff y)
  let basisG := fun g : G => MonoidAlgebra.single g (1 : Complex)
  let E : LinearMap (RingHom.id Complex) B A :=
    LinearMap.comp (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap
      (LinearMap.comp
        (MackeyDiagrams.freeLift Complex (MackeyDiagrams.Generator.traceBasis Complex a))
        (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap)
  (∀ g : G, g ∈ S →
    ∃ h : H, (h : U) = α⁻¹ * (g : U) * α ∧ E (basisG g) = MonoidAlgebra.single h 1) ∧
  (∀ g : G, g ∉ S → E (basisG g) = 0) ∧
  (∀ (r s : A) (x : B), E (φ r * x * φ s) = r * E x * s) ∧
  (∀ x y : B, cap.toLinearMap (pairDI x y) = MonoidAlgebra.coeff (E (x * y))) ∧
  (∀ finite : S.FiniteIndex,
    let cup := MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.reverseCup (R := Complex) a finite)
    let IsTransversal := fun T : Finset G =>
      ∀ g : G, ∃! t : {t : G // t ∈ T}, g * t.val⁻¹ ∈ S
    let toRep : CategoryTheory.Functor (ModuleCat.{max u v} A) (Rep.{max u v} Complex H) :=
      Rep.ofModuleMonoidAlgebra
    let Ind : CategoryTheory.Functor (ModuleCat.{max u v} A) (ModuleCat.{max u v} B) :=
      CategoryTheory.Functor.comp
        (CategoryTheory.Functor.comp toRep (Rep.indFunctor Complex a.toHom))
        (Rep.toModuleMonoidAlgebra (k := Complex) (G := G))
    let Res : CategoryTheory.Functor (ModuleCat.{max u v} B) (ModuleCat.{max u v} A) :=
      ModuleCat.restrictScalars φ.toRingHom
    let pure := fun (X : ModuleCat.{max u v} A) (b : B) (x : X) =>
      let ρ := Rep.ρ (toRep.obj X)
      show Ind.obj X from
        (Representation.asModuleEquiv (Representation.ind a.toHom ρ)).symm
          (MackeyDiagrams.freeLift Complex
            (fun g : G => Representation.IndV.mk a.toHom ρ g⁻¹ x) (MonoidAlgebra.coeff b))
    (∃ T : Finset G, IsTransversal T) ∧
    ∃ adj : CategoryTheory.Adjunction Res Ind,
      (∀ (X : ModuleCat.{max u v} A) (x y : B) (z : X),
        ModuleCat.Hom.hom (adj.counit.app X) (show Res.obj (Ind.obj X) from pure X (x * y) z) =
          (MonoidAlgebra.ofCoeff (cap.toLinearMap (pairDI x y)) : A) • z) ∧
      (∀ (T : Finset G), IsTransversal T →
        (∀ g : G,
          cup.toLinearMap (MonoidAlgebra.coeff (basisG g)) =
            Finset.sum T (fun t => pairID (basisG (g * t⁻¹)) (basisG t)) ∧
          cup.toLinearMap (MonoidAlgebra.coeff (basisG g)) =
            Finset.sum T (fun t => pairID (basisG t⁻¹) (basisG (t * g)))) ∧
        (∀ (Y : ModuleCat.{max u v} B) (g : G) (z : Y),
          ModuleCat.Hom.hom (adj.unit.app Y) (basisG g • z) =
            Finset.sum T (fun t =>
              pure (Res.obj Y) (basisG (g * t⁻¹)) (basisG t • z)))))
) :=
(
by
  open FiniteIndexReverseAdjunctionSupport in
  intro U _ H G α hα A B a S φ up down cap pairDI pairID basisG E
  -- Xiao, § 1.2, pp. 3–4 (Cups and caps). The trace cap ends at the
  -- empty H boundary. The reverse cup starts at the empty G boundary.
  -- The archived PDF and the current published PDF have distinct hashes.
  -- Their reverse unit and counit formulas and the TikZ boundaries agree.
  -- Alphabeta Math's module tensor universal property, Steps 3.1, 4.1
  -- and 5.1, motivates the descent and generator checks. The shared
  -- biset quotient supplies balancing for the diagram evaluation.
  -- For the module adjunction, the coinvariant lift descends by the
  -- trace balance identity, and IndV.hom_ext checks the quotient maps
  -- on tensor generators. The trace calculation holds at every index.
  have hCap : ∀ x y : B, cap.toLinearMap (pairDI x y) = (E (x * y)).coeff :=
    cap_pair a
  refine ⟨?_, trace_outside a, trace_bimodule a, hCap, ?_⟩
  · intro g hg
    obtain ⟨h, rfl⟩ := hg
    refine ⟨h, ?_, trace_image a h⟩
    change (h : U) = α⁻¹ * ((MackeyDiagrams.ConjEmbedding.ofConjugator α hα).toHom h : U) * α
    rw [MackeyDiagrams.ConjEmbedding.ofConjugator_apply]
    group
  · intro finite cup IsT toRep Ind Res pure
    obtain ⟨T, hT⟩ := transversal_exists a finite
    refine ⟨⟨T, hT⟩, adjunction a T hT, ?_, ?_⟩
    · intro X x y z
      rw [hCap]
      exact counit_pure a T hT X (x * y) z
    · intro T' hT'
      refine ⟨fun g => ⟨?_, ?_⟩, unit_at_generator a T T' hT hT'⟩
      · simpa only [pairID, basisG, MonoidAlgebra.coeff_single,
          MackeyDiagrams.Biset.pairLinear_single, mul_one] using cup_leftSum a finite T' hT' g
      · simpa only [pairID, basisG, MonoidAlgebra.coeff_single,
          MackeyDiagrams.Biset.pairLinear_single, mul_one] using cup_rightSum a finite T' hT' g
)
#print axioms FiniteIndexReverseAdjunction
