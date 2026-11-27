import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.Data.Finsupp.ToDFinsupp
import MackeyDiagrams
import Proofs.ComplexEilenbergWatts
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionAdjunction
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.ModuleTensorUniversalProperty
import Proofs.BalancedTensorAssociativity
set_option maxHeartbeats 2000000

open MackeyDiagrams
open scoped ModuleCat.Algebra

namespace DiagramFunctorProof

universe u v
open MonoidAlgebra

private abbrev Alg (H : Type u) [Monoid H] := MonoidAlgebra Complex H

-- Xiao § 1.3. The left cosets index a basis for the right action.
-- No finiteness of the left-coset space is needed.
private theorem freeRight {H G : Type u} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) :
    letI : Module (Alg H)ᵐᵒᵖ (Alg G) :=
      Module.compHom (Alg G) (RingHom.op (mapDomainAlgHom Complex Complex f).toRingHom)
    Module.Free (Alg H)ᵐᵒᵖ (Alg G) := by
  classical
  let A := Alg H
  let B := Alg G
  let I := G ⧸ f.range
  let φ : A →ₐ[Complex] B := mapDomainAlgHom Complex Complex f
  letI : Module Aᵐᵒᵖ B := Module.compHom B (RingHom.op φ.toRingHom)
  let rep (i : I) : G := Quotient.out i
  let keys : (Sigma fun _ : I => H) ≃ G :=
    Equiv.ofBijective (fun ih => rep ih.1 * f ih.2) (by
      have quotient_eq (i : I) (h : H) : ((rep i * f h : G) : I) = i := by
        refine (QuotientGroup.eq.mpr ?_).trans (Quotient.out_eq' i)
        exact ⟨h⁻¹, by simp [rep, mul_inv_rev, mul_assoc]⟩
      constructor
      · rintro ⟨i, h⟩ ⟨j, k⟩ (e : rep i * f h = rep j * f k)
        have eqij : i = j := (quotient_eq i h).symm.trans
          ((congrArg (fun x : G => (x : I)) e).trans (quotient_eq j k))
        subst j
        congr 1
        exact hf (mul_left_cancel e)
      · intro g
        let i : I := (g : I)
        have eqi : ((rep i : G) : I) = (g : I) := Quotient.out_eq' i
        obtain ⟨h, hh⟩ := QuotientGroup.eq.mp eqi
        exact ⟨⟨i, h⟩, by change rep i * f h = g; rw [hh, mul_inv_cancel_left]⟩)
  let summands : (I →₀ A) ≃ₗ[Complex] B :=
    ((finsuppLequivDFinsupp Complex).trans
      ((DFinsupp.mapRange.linearEquiv (fun _ => coeffLinearEquiv Complex)).trans
        (sigmaFinsuppLequivDFinsupp Complex).symm)).trans
      ((Finsupp.domLCongr (R := Complex) keys).trans (coeffLinearEquiv Complex).symm)
  have onSingle (i : I) (h : H) (z : Complex) :
      summands (Finsupp.single i (MonoidAlgebra.single h z)) =
        MonoidAlgebra.single (rep i * f h) z := by
    apply (coeffLinearEquiv Complex).injective
    change (Finsupp.domLCongr (R := Complex) keys)
      ((sigmaFinsuppLequivDFinsupp Complex).symm
        ((DFinsupp.mapRange.linearEquiv (fun _ => coeffLinearEquiv Complex))
          (finsuppLequivDFinsupp Complex (Finsupp.single i (MonoidAlgebra.single h z))))) =
      Finsupp.single (keys ⟨i, h⟩) z
    simp only [finsuppLequivDFinsupp_apply_apply, Finsupp.toDFinsupp_single,
      DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single,
      coeffLinearEquiv_apply]
    have hs : sigmaFinsuppEquivDFinsupp.symm
        (DFinsupp.single i (Finsupp.single h z) : Π₀ _ : I, H →₀ Complex) =
          Finsupp.single (⟨i, h⟩ : Sigma fun _ : I => H) z :=
      sigmaFinsuppEquivDFinsupp.symm_apply_eq.mpr
        (sigmaFinsuppEquivDFinsupp_single (⟨i, h⟩ : Sigma fun _ : I => H) z).symm
    change Finsupp.equivMapDomain keys
      (sigmaFinsuppEquivDFinsupp.symm (DFinsupp.single i (Finsupp.single h z))) = _
    rw [hs, Finsupp.equivMapDomain_single]
  have onSummand (i : I) (a : A) :
      summands (Finsupp.single i a) = MonoidAlgebra.single (rep i) 1 * φ a := by
    induction a using MonoidAlgebra.induction_on with
    | of h =>
        change summands (Finsupp.single i (MonoidAlgebra.single h 1)) = _
        rw [onSingle]
        change _ = MonoidAlgebra.single (rep i) 1 * MonoidAlgebra.mapDomain f
          (MonoidAlgebra.single h 1)
        rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.single_mul_single, one_mul]
    | add a b ha hb => rw [Finsupp.single_add, map_add, ha, hb, map_add, mul_add]
    | smul z a ha =>
        rw [← Finsupp.smul_single, map_smul, ha, map_smul, mul_smul_comm]
  let e : (I →₀ A) ≃ₗ[Aᵐᵒᵖ] B :=
    { toEquiv := summands.toEquiv
      map_add' := summands.map_add
      map_smul' := fun r x => by
        change summands (r • x) = summands x * φ r.unop
        induction x using Finsupp.induction_linear with
        | zero => simp
        | add x y hx hy => simp only [smul_add, map_add, hx, hy, add_mul]
        | single i a =>
            rw [Finsupp.smul_single, onSummand, onSummand]
            change MonoidAlgebra.single (rep i) 1 * φ (a * r.unop) = _
            rw [map_mul, mul_assoc] }
  exact Module.Free.of_equiv ((Finsupp.mapRange.linearEquiv
    (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm).trans e)

end DiagramFunctorProof
open MackeyDiagrams CategoryTheory
open scoped ModuleCat.Algebra
set_option backward.isDefEq.respectTransparency false

namespace DiagramFunctorProof

universe u v

private noncomputable abbrev GC (G : Type u) [Monoid G] := RingCat.of (MonoidAlgebra Complex G)
private abbrev BM (K H : Type u) [Group K] [Group H] := Rep.{max u v} Complex (K × H)
private abbrev BW (K H : Type u) [Group K] [Group H] :=
  WattsFoundation.General.OriginalBimodule.{u,v} (GC H) (GC K)

private noncomputable def leftHom {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) :
    MonoidAlgebra Complex K →ₐ[Complex] Module.End Complex B :=
  Representation.asAlgebraHom (B.ρ.comp (MonoidHom.inl K H))

private noncomputable def rightHom {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) :
    (MonoidAlgebra Complex H)ᵐᵒᵖ →ₐ[Complex] Module.End Complex B :=
  AlgHom.opComm (MonoidAlgebra.lift Complex (Module.End Complex B)ᵐᵒᵖ H
    { toFun := fun h => MulOpposite.op (B.ρ (1, h⁻¹))
      map_one' := by
        rw [inv_one]
        change MulOpposite.op (B.ρ 1) = 1
        rw [map_one, MulOpposite.op_one]
      map_mul' := by
        intro h j
        apply MulOpposite.unop_injective
        change B.ρ (1, (h * j)⁻¹) = B.ρ (1, j⁻¹) * B.ρ (1, h⁻¹)
        rw [← map_mul]
        simp })

private theorem leftHom_apply {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (a : MonoidAlgebra Complex K) (b : B) :
    leftHom B a b = freeLift Complex (fun k : K => B.ρ (k, 1) b) a.coeff := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
      change leftHom B (MonoidAlgebra.single k 1) b =
        freeLift Complex (fun k : K => B.ρ (k, 1) b) (Finsupp.single k 1)
      simp [leftHom]
  | add a a' ha ha' => simp [ha, ha']
  | smul z a ha => simp [ha]

private theorem rightHom_apply {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (a : MonoidAlgebra Complex H) (b : B) :
    rightHom B (MulOpposite.op a) b = freeLift Complex (fun h : H => B.ρ (1, h⁻¹) b) a.coeff := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
      rw [show (MonoidAlgebra.of Complex H h).coeff = Finsupp.single h 1 from rfl,
        freeLift_single, one_smul]
      simp [rightHom]
  | add a a' ha ha' => simp [ha, ha']
  | smul z a ha => simp [ha]

@[simp] private theorem left_of {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (k : K) (b : B) :
    leftHom B (MonoidAlgebra.of Complex K k) b = B.ρ (k, 1) b := by
  rw [leftHom_apply]
  change freeLift Complex (fun k : K => B.ρ (k, 1) b) (Finsupp.single k 1) = _
  rw [freeLift_single, one_smul]

@[simp] private theorem right_of {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (h : H) (b : B) :
    rightHom B (MulOpposite.op (MonoidAlgebra.of Complex H h)) b = B.ρ (1, h⁻¹) b := by
  rw [rightHom_apply]
  change freeLift Complex (fun h : H => B.ρ (1, h⁻¹) b) (Finsupp.single h 1) = _
  rw [freeLift_single, one_smul]

private theorem leftRight_commute {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (s : MonoidAlgebra Complex K) (r : MonoidAlgebra Complex H) (b : B) :
    rightHom B (MulOpposite.op r) (leftHom B s b) = leftHom B s (rightHom B (MulOpposite.op r) b) := by
  induction s using MonoidAlgebra.induction_on with
  | of k =>
    induction r using MonoidAlgebra.induction_on with
    | of h =>
      simp only [left_of, right_of]
      change (B.ρ (1, h⁻¹) * B.ρ (k, 1)) b = (B.ρ (k, 1) * B.ρ (1, h⁻¹)) b
      simp only [← map_mul]
      simp
    | add a a' ha ha' =>
      simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, ha, ha']
    | smul z a ha => simp only [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, ha]
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | smul z a ha => simp only [map_smul, LinearMap.smul_apply, ha]

private noncomputable def toBWObj {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) :
    BW.{u,v} K H := by
  letI : Module (GC K) B := Module.compHom B (leftHom B).toRingHom
  letI : Module (GC H)ᵐᵒᵖ B := Module.compHom B (rightHom B).toRingHom
  let M : ModuleCat.{max u v} (GC K) := ModuleCat.of (GC K) B
  refine ⟨M, ⟨⟨inferInstance, ⟨inferInstance, ?_⟩⟩, rfl⟩⟩
  exact ⟨fun r s b => leftRight_commute B s r.unop b⟩

private theorem leftHom_scalar {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (z : Complex) (b : B) :
    leftHom B (algebraMap Complex (MonoidAlgebra Complex K) z) b = z • b := by
  rw [AlgHom.commutes]
  simp [Algebra.algebraMap_eq_smul_one]

private theorem rightHom_scalar {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (z : Complex) (b : B) :
    rightHom B (MulOpposite.op (algebraMap Complex (MonoidAlgebra Complex H) z)) b = z • b := by
  change rightHom B (algebraMap Complex (MonoidAlgebra Complex H)ᵐᵒᵖ z) b = _
  rw [AlgHom.commutes]
  simp [Algebra.algebraMap_eq_smul_one]

private theorem map_leftHom {K H : Type u} [Group K] [Group H] {B C : BM.{u,v} K H}
    (f : B ⟶ C) (a : MonoidAlgebra Complex K) (b : B) :
    f.hom (leftHom B a b) = leftHom C a (f.hom b) := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
    simp only [left_of]
    exact f.hom.isIntertwining _ _ _ _
  | add q r hq hr => simp [hq, hr]
  | smul z a ha => simp [ha]

private theorem map_rightHom {K H : Type u} [Group K] [Group H] {B C : BM.{u,v} K H}
    (f : B ⟶ C) (a : MonoidAlgebra Complex H) (b : B) :
    f.hom (rightHom B (MulOpposite.op a) b) = rightHom C (MulOpposite.op a) (f.hom b) := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
    simp only [right_of]
    exact f.hom.isIntertwining _ _ _ _
  | add q r hq hr => simp [hq, hr]
  | smul z a ha => simp [ha]

private noncomputable def toBW {K H : Type u} [Group K] [Group H] :
    BM.{u,v} K H ⥤ BW.{u,v} K H where
  obj := toBWObj
  map f := ⟨{ toFun := f.hom
              map_add' := f.hom.toLinearMap.map_add
              map_smul' := map_leftHom f }, map_rightHom f |> Function.swap⟩
  map_id _ := rfl
  map_comp _ _ := rfl


private theorem rho_split {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (k : K) (h : H) (b : B) :
    B.ρ (k, h) b = B.ρ (k, 1) (B.ρ (1, h) b) := by
  change B.ρ (k, h) b = (B.ρ (k, 1) * B.ρ (1, h)) b
  rw [← map_mul]
  simp

private theorem toBW_full {K H : Type u} [Group K] [Group H] :
    (toBW.{u,v} (K := K) (H := H)).Full where
  map_surjective {B C} f := by
    let g : B →ₗ[Complex] C :=
      { toFun := f.val
        map_add' := f.val.map_add
        map_smul' := fun z b => by
          change f.val (z • b) = z • (show C from f.val b)
          have h := f.val.map_smul (algebraMap Complex (GC K) z) b
          change f.val (leftHom B (algebraMap Complex (GC K) z) b) =
            leftHom C (algebraMap Complex (GC K) z) (f.val b) at h
          rw [leftHom_scalar B z b, leftHom_scalar C z (show C from f.val b)] at h
          exact h }
    have left (k : K) (b : B) : g (B.ρ (k, 1) b) = C.ρ (k, 1) (g b) := by
      have e := f.val.map_smul (MonoidAlgebra.of Complex K k) b
      change g (leftHom B (MonoidAlgebra.of Complex K k) b) =
        leftHom C (MonoidAlgebra.of Complex K k) (g b) at e
      simpa only [left_of] using e
    have right (h : H) (b : B) : g (B.ρ (1, h) b) = C.ρ (1, h) (g b) := by
      have hr := f.property b (MonoidAlgebra.of Complex H h⁻¹)
      change g (rightHom B (MulOpposite.op (MonoidAlgebra.of Complex H h⁻¹)) b) =
        rightHom C (MulOpposite.op (MonoidAlgebra.of Complex H h⁻¹)) (g b) at hr
      simpa only [right_of, inv_inv] using hr
    refine ⟨Rep.ofHom ⟨g, ?_⟩, ?_⟩
    · rintro ⟨k, h⟩
      apply LinearMap.ext
      intro b
      change g (B.ρ (k, h) b) = C.ρ (k, h) (g b)
      rw [rho_split, left, right, ← rho_split]
    · apply Subtype.ext
      ext b
      rfl

private theorem toBW_faithful {K H : Type u} [Group K] [Group H] :
    (toBW.{u,v} (K := K) (H := H)).Faithful where
  map_injective hg := by
    apply Rep.hom_ext
    ext x
    exact congrArg (fun f : WattsFoundation.General.OriginalBimoduleHom _ _ _ _ => f.val x) hg

private noncomputable abbrev V {H : Type u} [Group H] (X : ModuleCat.{max u v} (GC H)) :=
  (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X

private theorem module_rho {H : Type u} [Group H] (X : ModuleCat.{max u v} (GC H))
    (h : H) (x : V X) :
    (V X).ρ h x = (MonoidAlgebra.of Complex H h) • (show X from x) := by
  have e := Representation.ofModule_asAlgebraHom_apply_apply X (MonoidAlgebra.of Complex H h) x
  change ((V X).ρ.asAlgebraHom (MonoidAlgebra.of Complex H h)) x = _ at e
  rwa [Representation.asAlgebraHom_of] at e

private noncomputable def fromBWObj {K H : Type u} [Group K] [Group H] (M : BW.{u,v} K H) :
    BM.{u,v} K H := by
  letI : Module (GC H)ᵐᵒᵖ M.1 := M.2.1.2.1
  haveI : SMulCommClass (GC H)ᵐᵒᵖ (GC K) M.1 := by
    rcases M with ⟨X, ⟨⟨left, ⟨right, comm⟩⟩, eq⟩⟩
    cases eq
    exact comm
  let right (h : H) : (GC H)ᵐᵒᵖ := MulOpposite.op (MonoidAlgebra.of Complex H h⁻¹)
  have right_one : right 1 = 1 := by
    change MulOpposite.op (MonoidAlgebra.of Complex H (1 : H)⁻¹) = 1
    rw [inv_one, map_one, MulOpposite.op_one]
  have right_mul (h j : H) : right (h * j) = right h * right j := by
    change MulOpposite.op (MonoidAlgebra.of Complex H (h * j)⁻¹) =
      MulOpposite.op (MonoidAlgebra.of Complex H h⁻¹) *
        MulOpposite.op (MonoidAlgebra.of Complex H j⁻¹)
    rw [mul_inv_rev, map_mul, MulOpposite.op_mul]
  refine Rep.of ({
    toFun := fun kh => {
      toFun := fun x => (MonoidAlgebra.of Complex K kh.1) • (right kh.2 • (show M.1 from x))
      map_add' := fun x y => by
        exact (congrArg (fun w : M.1 => MonoidAlgebra.of Complex K kh.1 • w)
          (smul_add (right kh.2) (show M.1 from x) (show M.1 from y))).trans
            (smul_add _ _ _)
      map_smul' := fun z x => by
        let x' : M.1 := x
        let a := MonoidAlgebra.of Complex K kh.1
        let r := right kh.2
        let c := algebraMap Complex (GC K) z
        change a • (r • (c • x')) = c • (a • (r • x'))
        rw [smul_comm r c, ← mul_smul, ← mul_smul, ← Algebra.commutes z a] }
    map_one' := by
      ext x
      change (MonoidAlgebra.of Complex K 1) • (right 1 • (show M.1 from x)) = x
      rw [map_one, right_one, one_smul, one_smul]
    map_mul' := fun g h => by
      ext x
      change (MonoidAlgebra.of Complex K (g.1 * h.1)) •
          (right (g.2 * h.2) • (show M.1 from x)) =
        (MonoidAlgebra.of Complex K g.1) • (right g.2 •
          ((MonoidAlgebra.of Complex K h.1) • (right h.2 • (show M.1 from x))))
      rw [smul_comm (right g.2), ← mul_smul (MonoidAlgebra.of Complex K g.1),
        ← mul_smul (right g.2), ← map_mul, ← right_mul] } :
    Representation Complex (K × H) (V M.1))

private theorem fromBW_left {K H : Type u} [Group K] [Group H] (M : BW.{u,v} K H)
    (a : MonoidAlgebra Complex K) (x : M.1) :
    leftHom (fromBWObj M) a x = a • x := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
    rw [left_of]
    letI : Module (GC H)ᵐᵒᵖ M.1 := M.2.1.2.1
    change (MonoidAlgebra.of Complex K k) •
      (MulOpposite.op (MonoidAlgebra.of Complex H (1 : H)⁻¹) • x) = _
    rw [inv_one, map_one, MulOpposite.op_one, one_smul]
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, add_smul, ha, ha']
  | smul z a ha =>
    change (leftHom (fromBWObj M) (z • a)) x = (z • a) • x
    rw [map_smul, LinearMap.smul_apply, ha]
    change (algebraMap Complex (GC K) z) • (a • x) = _
    rw [← mul_smul, Algebra.smul_def]

private theorem fromBW_right {K H : Type u} [Group K] [Group H] (M : BW.{u,v} K H)
    (hs : ∀ (z : Complex) (b : M.1),
      algebraMap Complex (GC K) z • b =
        WattsFoundation.General.originalRight _ _ M b (algebraMap Complex (GC H) z))
    (a : MonoidAlgebra Complex H) (x : M.1) :
    rightHom (fromBWObj M) (MulOpposite.op a) x =
      WattsFoundation.General.originalRight _ _ M x a := by
  letI : Module (GC H)ᵐᵒᵖ M.1 := M.2.1.2.1
  change rightHom (fromBWObj M) (MulOpposite.op a) x = MulOpposite.op a • x
  induction a using MonoidAlgebra.induction_on with
  | of h =>
    rw [right_of]
    change (MonoidAlgebra.of Complex K 1) •
      (MulOpposite.op (MonoidAlgebra.of Complex H h⁻¹⁻¹) • x) = _
    rw [map_one, one_smul, inv_inv]
  | add a a' ha ha' =>
    simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, add_smul, ha, ha']
  | smul z a ha =>
    rw [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, ha]
    change (algebraMap Complex (GC K) z) • (MulOpposite.op a • x) = _
    rw [hs z]
    change MulOpposite.op (algebraMap Complex (GC H) z) • (MulOpposite.op a • x) = _
    rw [← mul_smul, Algebra.smul_def, MulOpposite.algebraMap_apply]

private noncomputable def bwIso {K H : Type u} [Group K] [Group H] (M : BW.{u,v} K H)
    (hs : ∀ (z : Complex) (b : M.1),
      algebraMap Complex (GC K) z • b =
        WattsFoundation.General.originalRight _ _ M b (algebraMap Complex (GC H) z)) :
    toBWObj (fromBWObj M) ≅ M where
  hom := ⟨{ toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fromBW_left M }, fun x a => fromBW_right M hs a x⟩
  inv := ⟨{ toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fun a x => (fromBW_left M a x).symm },
            fun x a => (fromBW_right M hs a x).symm⟩
  hom_inv_id := rfl
  inv_hom_id := rfl


open WattsFoundation.General CategoryTheory.Limits
open scoped MonoidAlgebra

private abbrev Mod (H : Type u) [Group H] := ModuleCat.{max u v} (MonoidAlgebra Complex H)
private abbrev Func (K H : Type u) [Group K] [Group H] := Mod.{u,v} H ⥤ Mod.{u,v} K

private abbrev Good₀ (K H : Type u) [Group K] [Group H] : ObjectProperty (Func.{u,v} K H) :=
  fun F => F.Additive ∧ PreservesFiniteColimits F ∧
    ∀ I : Type (max u v), PreservesColimitsOfShape (Discrete I) F

private abbrev Good (K H : Type u) [Group K] [Group H] : ObjectProperty (Func.{u,v} K H) :=
  fun F => F.Linear Complex ∧ PreservesFiniteColimits F ∧
    ∀ I : Type (max u v), PreservesColimitsOfShape (Discrete I) F

private abbrev EqScalars {K H : Type u} [Group K] [Group H] : ObjectProperty (BW.{u,v} K H) :=
  fun M => ∀ (z : Complex) (b : M.1), algebraMap Complex (GC K) z • b =
    originalRight _ _ M b (algebraMap Complex (GC H) z)

private noncomputable abbrev ew (K H : Type u) [Group K] [Group H] :
    BW.{u,v} K H ≌ (Good₀.{u,v} K H).FullSubcategory :=
  Classical.choose _root_.EilenbergWatts.{u,v} (GC K) (GC H)

private abbrev LinearPart (K H : Type u) [Group K] [Group H] :
    ObjectProperty (Good₀.{u,v} K H).FullSubcategory :=
  fun F => F.obj.Linear Complex

private noncomputable def eqScalars_toBW {K H : Type u} [Group K] [Group H] :
    BM.{u,v} K H ⥤ (EqScalars (K := K) (H := H)).FullSubcategory :=
  (EqScalars (K := K) (H := H)).lift toBW (fun B z b => by
    change leftHom B (algebraMap Complex (GC K) z) b =
      rightHom B (MulOpposite.op (algebraMap Complex (GC H) z)) b
    exact (leftHom_scalar B z b).trans (rightHom_scalar B z b).symm)

private noncomputable def eqScalars_equiv (K H : Type u) [Group K] [Group H] :
    BM.{u,v} K H ≌ (EqScalars (K := K) (H := H)).FullSubcategory := by
  letI := toBW_full (K := K) (H := H)
  letI := toBW_faithful (K := K) (H := H)
  let F := eqScalars_toBW.{u,v} (K := K) (H := H)
  letI : F.Full := inferInstanceAs ((EqScalars (K := K) (H := H)).lift toBW _).Full
  letI : F.Faithful := inferInstanceAs ((EqScalars (K := K) (H := H)).lift toBW _).Faithful
  letI : F.EssSurj := ⟨fun M =>
    ⟨fromBWObj M.obj, ⟨(EqScalars (K := K) (H := H)).isoMk (bwIso M.obj M.property)⟩⟩⟩
  letI : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact F.asEquivalence

-- Alphabeta Math, Eilenberg–Watts equivalence of hom categories, Steps 1.1–2.1.
-- Use the actual chosen Watts functor on bimodules. The complex refinement
-- then only cuts down its objects. The product-group presentation needs a
-- separate adapter because the supplier encodes the two module actions.
private theorem good_iff (K H : Type u) [Group K] [Group H] (B : BW.{u,v} K H) :
    EqScalars B ↔ (((ew K H).functor.obj B).obj).Linear Complex :=
  (ComplexEilenbergWatts.{u,v} (GC K) (GC H)).1 B

private noncomputable def linearPart_eq (K H : Type u) [Group K] [Group H] :
    (LinearPart.{u,v} K H).FullSubcategory ≌ (Good.{u,v} K H).FullSubcategory where
  functor := (Good.{u,v} K H).lift ((LinearPart.{u,v} K H).ι ⋙ (Good₀.{u,v} K H).ι) (fun F =>
    ⟨F.property, F.obj.property.2⟩)
  inverse := (LinearPart.{u,v} K H).lift
    ((Good₀.{u,v} K H).lift (Good.{u,v} K H).ι (fun F =>
      letI : PreservesFiniteColimits F.obj := F.property.2.1
      letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts F.obj
      ⟨Functor.additive_of_preservesBinaryBiproducts F.obj, F.property.2⟩)) (fun F => F.property.1)
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

private noncomputable def complexLift (K H : Type u) [Group K] [Group H] :
    BM.{u,v} K H ⥤ (Good.{u,v} K H).FullSubcategory :=
  (Good.{u,v} K H).lift (toBW ⋙ (ew K H).functor ⋙ (Good₀.{u,v} K H).ι) (fun B =>
    ⟨(good_iff K H _).mp ((eqScalars_toBW.obj B).property), ((ew K H).functor.obj _).property.2⟩)

private noncomputable def complexEquiv (K H : Type u) [Group K] [Group H] :
    BM.{u,v} K H ≌ (Good.{u,v} K H).FullSubcategory := by
  let F := complexLift.{u,v} K H
  letI := toBW_full (K := K) (H := H)
  letI := toBW_faithful (K := K) (H := H)
  letI : F.Full := inferInstanceAs ((Good.{u,v} K H).lift
    (toBW ⋙ (ew K H).functor ⋙ (Good₀.{u,v} K H).ι) _).Full
  letI : F.Faithful := inferInstanceAs ((Good.{u,v} K H).lift
    (toBW ⋙ (ew K H).functor ⋙ (Good₀.{u,v} K H).ι) _).Faithful
  letI : F.EssSurj := by
    have hw := (ComplexEilenbergWatts.{u,v} (GC K) (GC H)).2
    obtain ⟨er, hr⟩ := hw
    let e := ((eqScalars_equiv.{u,v} K H).trans er).trans (linearPart_eq.{u,v} K H)
    refine ⟨fun Y => ?_⟩
    let X := e.inverse.obj Y
    refine ⟨X, ⟨(Good.{u,v} K H).isoMk (?_ ≪≫
        (Good.{u,v} K H).ι.mapIso (e.counitIso.app Y))⟩⟩
    apply eqToIso
    have h := Functor.congr_obj hr (eqScalars_toBW.obj X)
    exact congrArg (fun G : (Good₀.{u,v} K H).FullSubcategory => G.obj) h.symm
  letI : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact F.asEquivalence

private noncomputable abbrev trans (K H : Type u) [Group K] [Group H] :=
  (complexEquiv.{u,v} K H).functor ⋙ (Good.{u,v} K H).ι

private noncomputable abbrev tensor {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) :=
  (trans K H).obj B

private noncomputable abbrev VMap {H : Type u} [Group H] {X Y : Mod.{u,v} H} (f : X ⟶ Y) :=
  ((Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).map f).hom.toLinearMap

private noncomputable abbrev rawPure {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (X : Mod.{u,v} H) : B → X → (tensor B).obj X :=
  Classical.choose (Classical.choose_spec (_root_.EilenbergWatts.{u,v}))
    (GC K) (GC H) (toBWObj B) X

private theorem rawUniversal {K H : Type u} [Group K] [Group H]
    (B : BM.{u,v} K H) (X : Mod.{u,v} H) :
    originalBalanced (GC H) (GC K) (toBWObj B) X ((tensor B).obj X) (rawPure B X) ∧
    ∀ (Y : Mod.{u,v} K) (p : B → X → Y),
      originalBalanced (GC H) (GC K) (toBWObj B) X Y p →
        ∃! f : (tensor B).obj X →ₗ[MonoidAlgebra Complex K] Y,
          ∀ b x, f (rawPure B X b x) = p b x := by
  exact (Classical.choose_spec (Classical.choose_spec (_root_.EilenbergWatts.{u,v}))).1
    (GC K) (GC H) (toBWObj B) X

private theorem rawMapInput {K H : Type u} [Group K] [Group H]
    (B : BM.{u,v} K H) {X Y : Mod.{u,v} H} (f : X ⟶ Y) (b : B) (x : X) :
    ((tensor B).map f).hom (rawPure B X b x) = rawPure B Y b (f.hom x) :=
  (Classical.choose_spec (Classical.choose_spec (_root_.EilenbergWatts.{u,v}))).2.1
    (GC K) (GC H) (toBWObj B) X Y f b x

private theorem rawMapBimod {K H : Type u} [Group K] [Group H] {B C : BM.{u,v} K H}
    (f : B ⟶ C) (X : Mod.{u,v} H) (b : B) (x : X) :
    (((trans K H).map f).app X).hom (rawPure B X b x) = rawPure C X (f.hom b) x :=
  (Classical.choose_spec (Classical.choose_spec (_root_.EilenbergWatts.{u,v}))).2.2.1
    (GC K) (GC H) (toBWObj B) (toBWObj C) (toBW.map f) X b x

private abbrev Lin (X Y : Type*) [AddCommGroup X] [Module Complex X]
    [AddCommGroup Y] [Module Complex Y] := X →ₗ[Complex] Y

private noncomputable def pure {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H)
    (X : Mod.{u,v} H) : B →ₗ[Complex] (V X →ₗ[Complex] V ((tensor B).obj X)) := by
  have hp := (rawUniversal B X).1
  have left_smul (z : Complex) (b : B) (x : V X) :
      rawPure B X (z • b) x = z • (show V ((tensor B).obj X) from rawPure B X b x) := by
    have e := hp.2.2.1 (algebraMap Complex (GC K) z) b x
    change rawPure B X (leftHom B (algebraMap Complex (GC K) z) b) x = _
      at e
    rw [leftHom_scalar] at e
    exact e
  have right_smul (z : Complex) (b : B) (x : V X) :
      rawPure B X b (z • x) = z • (show V ((tensor B).obj X) from rawPure B X b x) := by
    have e := hp.2.2.2 (algebraMap Complex (GC H) z) b x
    change rawPure B X (rightHom B (MulOpposite.op (algebraMap Complex (GC H) z)) b) x =
      rawPure B X b (z • x) at e
    rw [rightHom_scalar] at e
    exact e.symm.trans (left_smul z b x)
  exact { toFun := fun b =>
            { toFun := rawPure B X b
              map_add' := hp.2.1 b
              map_smul' := fun z x => right_smul z b x }
          map_add' := fun b c => LinearMap.ext (hp.1 b c)
          map_smul' := fun z b => LinearMap.ext (left_smul z b) }

private abbrev Balanced {K H : Type u} [Group K] [Group H]
    (B : BM.{u,v} K H) (X : Mod.{u,v} H) (Y : Mod.{u,v} K)
    (p : B →ₗ[Complex] (V X →ₗ[Complex] V Y)) : Prop :=
  (∀ (a : MonoidAlgebra Complex K) (b : B) (x : V X),
    p (leftHom B a b) x = a • (show Y from p b x)) ∧
  (∀ (a : MonoidAlgebra Complex H) (b : B) (x : V X),
    p (rightHom B (MulOpposite.op a) b) x = p b (a • (show X from x)))

private theorem universal {K H : Type u} [Group K] [Group H]
    (B : BM.{u,v} K H) (X : Mod.{u,v} H) :
    Balanced B X ((tensor B).obj X) (pure B X) ∧
    ∀ (Y : Mod.{u,v} K) (p : B →ₗ[Complex] (V X →ₗ[Complex] V Y)),
      Balanced B X Y p →
      ∃! f : (tensor B).obj X ⟶ Y, ∀ (b : B) (x : V X), VMap f (pure B X b x) = p b x := by
  obtain ⟨hb, hu⟩ := rawUniversal B X
  refine ⟨⟨hb.2.2.1, hb.2.2.2⟩, fun Y p hp => ?_⟩
  obtain ⟨f, hf, uniq⟩ := hu Y (fun b x => p b x)
    ⟨fun b c x => DFunLike.congr_fun (p.map_add b c) x, fun b => (p b).map_add, hp⟩
  exact ⟨ModuleCat.ofHom f, hf, fun g hg => ModuleCat.hom_injective (uniq g.hom hg)⟩

private noncomputable abbrev regular (H : Type u) [Group H] : Mod.{u,v} H :=
  ModuleCat.of (GC H) (ULift.{v} (MonoidAlgebra Complex H))

private theorem hom_ext_pure {K H : Type u} [Group K] [Group H]
    (B : BM.{u,v} K H) (X : Mod.{u,v} H) {Y : Mod.{u,v} K}
    {f g : (tensor B).obj X ⟶ Y}
    (e : ∀ b x, f.hom (rawPure B X b x) = g.hom (rawPure B X b x)) : f = g := by
  obtain ⟨hb, hu⟩ := rawUniversal B X
  have he : originalBalanced (GC H) (GC K) (toBWObj B) X Y
      (fun b x => g.hom (rawPure B X b x)) := by
    refine ⟨fun b c x => ?_, fun b x y => ?_, fun a b x => ?_, fun a b x => ?_⟩
    · exact (congrArg g.hom (hb.1 b c x)).trans (g.hom.map_add _ _)
    · exact (congrArg g.hom (hb.2.1 b x y)).trans (g.hom.map_add _ _)
    · exact (congrArg g.hom (hb.2.2.1 a b x)).trans (g.hom.map_smul a _)
    · exact congrArg g.hom (hb.2.2.2 a b x)
  obtain ⟨lift, _, un⟩ := hu Y _ he
  exact ModuleCat.hom_injective ((un f.hom e).trans (un g.hom (fun _ _ => rfl)).symm)

private theorem unitDesc {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) :
    ∃ f : (tensor B).obj (regular.{u,v} H) →ₗ[MonoidAlgebra Complex K] (toBWObj B).1,
      ∀ (b : B) (x : regular.{u,v} H),
        f (rawPure B (regular H) b x) = rightHom B (MulOpposite.op x.down) b := by
  let Y := (toBWObj B).1
  let p (b : B) (x : regular.{u,v} H) : Y := rightHom B (MulOpposite.op x.down) b
  have hp : originalBalanced (GC H) (GC K) (toBWObj B) (regular H) Y p := by
    refine ⟨fun b c x => map_add (rightHom B (MulOpposite.op x.down)) b c, ?_, ?_, ?_⟩
    · intro b x y
      change (rightHom B (MulOpposite.op (x.down + y.down))) b = _
      simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, p]
    · intro a b x
      exact leftRight_commute B a x.down b
    · intro a b x
      change rightHom B (MulOpposite.op x.down) (rightHom B (MulOpposite.op a) b) =
        rightHom B (MulOpposite.op (a * x.down)) b
      rw [MulOpposite.op_mul, map_mul]
      rfl
  obtain ⟨f, hf, _⟩ := (rawUniversal B (regular H)).2 Y p hp
  exact ⟨f, hf⟩

private noncomputable def unitFun {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) :
    V ((tensor B).obj (regular.{u,v} H)) →ₗ[Complex] B where
  toFun := fun y => (Classical.choose (unitDesc B)) y
  map_add' := (Classical.choose (unitDesc B)).map_add
  map_smul' z y := by
    let y' : (tensor B).obj (regular.{u,v} H) := y
    let f := Classical.choose (unitDesc B)
    have e := f.map_smul (algebraMap Complex (GC K) z) y'
    change f ((algebraMap Complex (GC K) z) • y') =
      leftHom B (algebraMap Complex (GC K) z) (f y') at e
    rw [leftHom_scalar B z (show B from f y')] at e
    exact e

private theorem unitFun_pure {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) (b : B)
    (x : V (regular.{u,v} H)) :
    unitFun B (pure B (regular H) b x) = rightHom B (MulOpposite.op x.down) b :=
  Classical.choose_spec (unitDesc B) b x

private noncomputable def unit {K H : Type u} [Group K] [Group H] (B : BM.{u,v} K H) :
    V ((tensor B).obj (regular.{u,v} H)) ≃ₗ[Complex] B := by
  let X := regular.{u,v} H
  let one : X := ULift.up 1
  have rightInv (b : B) : unitFun B (rawPure B X b one) = b := by
    change unitFun B (pure B X b one) = b
    rw [unitFun_pure]
    change rightHom B 1 b = b
    rw [map_one]
    rfl
  let inv : (toBWObj B).1 →ₗ[MonoidAlgebra Complex K] (tensor B).obj X :=
    { toFun := fun b => rawPure B X b one
      map_add' := fun b c => (rawUniversal B X).1.1 b c one
      map_smul' := fun a b => (rawUniversal B X).1.2.2.1 a b one }
  have leftInv (y : (tensor B).obj X) : rawPure B X (unitFun B y) one = y := by
    have h : ModuleCat.ofHom (inv.comp (Classical.choose (unitDesc B))) = 𝟙 ((tensor B).obj X) := by
      apply hom_ext_pure B X
      intro b x
      change rawPure B X (unitFun B (pure B X b x)) one = rawPure B X b x
      rw [unitFun_pure]
      have e := (rawUniversal B X).1.2.2.2 x.down b one
      change rawPure B X (rightHom B (MulOpposite.op x.down) b) one =
        rawPure B X b (ULift.up (x.down * 1)) at e
      simpa only [mul_one, ULift.up_down] using e
    exact congrArg (fun f : (tensor B).obj X ⟶ (tensor B).obj X => f.hom y) h
  refine LinearEquiv.ofLinearMap (unitFun B) (pure B X |>.flip one) ?_ ?_
  · exact LinearMap.ext rightInv
  · exact LinearMap.ext leftInv

#print axioms freeRight
#print axioms complexEquiv
#print axioms universal
#print axioms rawMapInput
#print axioms rawMapBimod
#print axioms unit
#print axioms unitFun_pure

end DiagramFunctorProof
