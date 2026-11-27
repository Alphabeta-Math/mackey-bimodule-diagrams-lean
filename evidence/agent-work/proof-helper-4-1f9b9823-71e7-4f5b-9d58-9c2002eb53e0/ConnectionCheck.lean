import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.RepresentationTheory.Rep.Iso
import Proofs.ComplexEilenbergWatts
import Proofs.InductionRestrictionBimoduleStrands
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
-- The portal describes a choice-free construction. Here the already
-- registered Watts equivalence and elementary tensors are selected from the
-- supplier's existence theorem by Classical.choose.
-- https://alphabetamath.cc/item/cor-eilenberg-watts-is-an-equivalence-of-hom-categories
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

-- Alphabeta Math, Universal property of M⊗_R N, Steps 4.1 and 5.1.
-- The proof uses the supplier's module-linear lift and its uniqueness on
-- elementary tensors to compare maps with the same exterior action.
-- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
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

-- The image of the equivalence is closed under pointwise coproducts.
-- The finite-colimit and coproduct conditions follow from commuting colimits,
-- and linearity is checked after precomposing with all coproduct inclusions.
private theorem goodColimit {K H : Type u} [Group K] [Group H]
    {J : Type (max u v)} [Category.{max u v} J] [HasColimitsOfShape J (Mod.{u,v} K)]
    {D : J ⥤ Func.{u,v} K H} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, Good K H (D.obj j)) :
    Good K H c.pt := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Functor.linear_iff]
    intro X z
    apply (isColimitOfPreserves ((evaluation _ _).obj X) hc).hom_ext
    intro j
    letI : (D.obj j).Linear Complex := (hD j).1
    change (c.ι.app j).app X ≫ c.pt.map (z • 𝟙 X) =
      (c.ι.app j).app X ≫ (z • 𝟙 (c.pt.obj X))
    have hn : (D.obj j).map (z • 𝟙 X) ≫ (c.ι.app j).app X =
        (c.ι.app j).app X ≫ c.pt.map (z • 𝟙 X) :=
      (c.ι.app j).naturality (z • 𝟙 X)
    simp only [← hn, Functor.map_smul, (D.obj j).map_id,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    let f : (D.obj j).obj X ⟶ c.pt.obj X := (c.ι.app j).app X
    exact (congrArg (fun g : (D.obj j).obj X ⟶ c.pt.obj X => z • g)
      (Category.comp_id f)).symm
  · constructor
    intro L _ _
    exact (ObjectProperty.preservesColimitsOfShape L).prop_of_isColimit hc
      (fun j => by
        letI : PreservesFiniteColimits (D.obj j) := (hD j).2.1
        infer_instance)
  · intro I
    exact (ObjectProperty.preservesColimitsOfShape (Discrete I)).prop_of_isColimit hc
      (fun j => (hD j).2.2 I)

private theorem preservesCoproduct {K H : Type u} [Group K] [Group H] (I : Type (max u v)) :
    PreservesColimitsOfShape (Discrete I) (trans.{u,v} K H) := by
  let P := Good.{u,v} K H
  letI : PreservesColimitsOfShape (Discrete I) P.ι := by
    constructor
    intro D
    let c := colimit.cocone (D ⋙ P.ι)
    have hc := colimit.isColimit (D ⋙ P.ι)
    let cc : Cocone D :=
      { pt := ⟨c.pt, goodColimit hc (fun j => (D.obj j).property)⟩
        ι := { app := fun j => P.homMk (c.ι.app j)
               naturality := fun i j f => by
                 apply P.ι.map_injective
                 exact c.ι.naturality f } }
    have hcc : IsColimit (P.ι.mapCocone cc) := hc
    exact preservesColimit_of_preserves_colimit_cocone (isColimitOfReflects P.ι hcc) hcc
  infer_instance

variable {U : Type u} [Group U]

private noncomputable abbrev wordVec := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    Finsupp (MackeyDiagrams.Word.basis p).carrier Complex

private noncomputable abbrev lower := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    (ULift.moduleEquiv : LinearEquiv (RingHom.id Complex) (ULift.{v} (wordVec p)) (wordVec p))

private noncomputable abbrev wordBimod := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    (Rep.of
      ({ toFun := fun g => (lower.{u,v} p).symm.toLinearMap.comp
            ((MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) g).comp
              (lower.{u,v} p).toLinearMap)
         map_one' := by
           ext x
           simp
         map_mul' := by
           intro g h
           have actMul :
               MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) (g * h) =
                 (MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) g).comp
                 (MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) h) := by
             apply Finsupp.lhom_ext
             intro i z
             simp [MackeyDiagrams.Biset.mul_act]
           ext x
           simp [actMul] } :
        Representation Complex (Prod K H) (ULift.{v} (wordVec p))) : BM.{u,v} K H)

private noncomputable abbrev wordHom := fun {K H : Subgroup U} (p q : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.Biset.Hom Complex (MackeyDiagrams.Word.basis p) (MackeyDiagrams.Word.basis q)

private noncomputable abbrev conjugateMap := fun {K H : Subgroup U} {p q : MackeyDiagrams.Word K H} (f : wordHom p q) =>
    (lower.{u,v} q).symm.toLinearMap.comp (f.toLinearMap.comp (lower.{u,v} p).toLinearMap)

private noncomputable abbrev wordMap := fun {K H : Subgroup U} {p q : MackeyDiagrams.Word K H} (f : wordHom p q) =>
    (Rep.ofHom
      { toLinearMap := conjugateMap.{u,v} f
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          simpa [wordBimod, conjugateMap] using
            congrArg (fun y => (lower.{u,v} q).symm y)
              (MackeyDiagrams.Biset.Hom.commutes f g (lower.{u,v} p x)) } :
      Quiver.Hom (wordBimod.{u,v} p) (wordBimod.{u,v} q))

private theorem conjugateMap_injective {K H : Subgroup U} {p q : Word K H} :
    Function.Injective (@conjugateMap.{u,v} U _ K H p q) := by
  intro f g e
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun e ((lower.{u,v} p).symm x)
  simpa [conjugateMap] using h

private noncomputable def lowerHom {K H : Subgroup U} {p q : Word K H}
    (f : wordBimod.{u,v} p ⟶ wordBimod.{u,v} q) : wordHom p q where
  toLinearMap := (lower.{u,v} q).toLinearMap.comp (f.hom.toLinearMap.comp (lower.{u,v} p).symm.toLinearMap)
  commutes g x := by
    have h := f.hom.isIntertwining _ _ g ((lower.{u,v} p).symm x)
    simpa [wordBimod] using congrArg (lower.{u,v} q) h

private theorem wordMap_bijective {K H : Subgroup U} {p q : Word K H} :
    Function.Bijective (@wordMap.{u,v} U _ K H p q) := by
  refine ⟨fun f g h => conjugateMap_injective (congrArg (fun k => (Rep.Hom.hom k).toLinearMap) h),
    fun f => ⟨lowerHom f, ?_⟩⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp [wordMap, conjugateMap, lowerHom]

private noncomputable abbrev T {K H : Subgroup U} (p : Word K H) :=
  tensor (wordBimod.{u,v} p)

private noncomputable abbrev liftMap {K H : Subgroup U} {p q : Word K H}
    (f : wordHom p q) : T.{u,v} p ⟶ T.{u,v} q :=
  (trans K H).map (wordMap.{u,v} f)

private noncomputable abbrev onRegular {K H : Subgroup U} {p q : Word K H}
    (η : T.{u,v} p ⟶ T.{u,v} q) :=
  (unit (wordBimod.{u,v} q)).toLinearMap.comp (VMap (η.app (regular H)) |>.comp
    (unit (wordBimod.{u,v} p)).symm.toLinearMap)

private theorem liftMap_bijective {K H : Subgroup U} {p q : Word K H} :
    Function.Bijective (@liftMap.{u,v} U _ K H p q) :=
  ((Functor.FullyFaithful.ofFullyFaithful (F := trans.{u,v} K H)).map_bijective _ _).comp
    wordMap_bijective

-- Alphabeta Math, Eilenberg–Watts equivalence of hom categories, Step 1.2.
-- Evaluate the natural transformation at the regular module and use the
-- left inverse of b ↦ b ⊗ 1 to recover the actual equivariant map.
private theorem onRegular_lift {K H : Subgroup U} {p q : Word K H} (f : wordHom p q) :
    onRegular.{u,v} (liftMap.{u,v} f) = conjugateMap.{u,v} f := by
  let X := regular.{u,v} H
  have atOne (r : Word K H) (b : wordBimod.{u,v} r) :
      unit (wordBimod.{u,v} r) (pure (wordBimod.{u,v} r) X b (ULift.up 1)) = b := by
    change unitFun (wordBimod.{u,v} r) (pure (wordBimod.{u,v} r) X b (ULift.up 1)) = b
    rw [unitFun_pure]
    change rightHom (wordBimod.{u,v} r) 1 b = b
    rw [map_one]
    rfl
  apply LinearMap.ext
  intro b
  change unit (wordBimod.{u,v} q) (((liftMap.{u,v} f).app X).hom
    ((unit (wordBimod.{u,v} p)).symm b)) = conjugateMap.{u,v} f b
  have ep : rawPure (wordBimod.{u,v} p) X b (ULift.up 1) = (unit (wordBimod.{u,v} p)).symm b :=
    (LinearEquiv.eq_symm_apply (unit (wordBimod.{u,v} p))).mpr (atOne p b)
  rw [← ep]
  exact (congrArg (unit (wordBimod.{u,v} q)) (rawMapBimod (wordMap.{u,v} f) X b (ULift.up 1))).trans
    (atOne q (conjugateMap.{u,v} f b))

-- The kernel quotient here uses typed labelled drawings. The project's
-- DiagramVectorSpace.quotient_eq_iff uses a different expression carrier.
-- Quotienting the already admitted drawings directly keeps the exact
-- evaluated equality and retains the individual shapes before quotienting.
private noncomputable def diagramQuotientEquiv {K H : Subgroup U} {p q : Word K H}
    {D : Type*} (eval : D → wordHom p q) :
    Quotient (Setoid.ker eval) ≃ {η : T.{u,v} p ⟶ T.{u,v} q //
      ∃ d : D, onRegular.{u,v} η = conjugateMap.{u,v} (eval d)} := by
  let L : Quotient (Setoid.ker eval) → {η : T.{u,v} p ⟶ T.{u,v} q //
      ∃ d : D, onRegular.{u,v} η = conjugateMap.{u,v} (eval d)} :=
    Quotient.lift (fun d => ⟨liftMap.{u,v} (eval d), ⟨d, onRegular_lift (eval d)⟩⟩)
      (fun d e h => Subtype.ext (congrArg liftMap.{u,v} h))
  refine Equiv.ofBijective L ⟨?_, ?_⟩
  · intro d e
    refine Quotient.inductionOn₂ d e (fun d e h => Quotient.sound ?_)
    exact liftMap_bijective.1 (congrArg Subtype.val h)
  · rintro ⟨η, d, h⟩
    obtain ⟨f, rfl⟩ := liftMap_bijective.2 η
    exact ⟨Quotient.mk _ d, Subtype.ext
      (congrArg liftMap.{u,v} (conjugateMap_injective ((onRegular_lift f).symm.trans h)).symm)⟩

private theorem transportLinear {K H : Type u} [Group K] [Group H] :
    (trans.{u,v} K H).Linear Complex where
  map_smul {B C} f z := by
    apply NatTrans.ext
    funext X
    apply hom_ext_pure B X
    intro b x
    have h₁ := rawMapBimod (z • f) X b x
    have h₂ := rawMapBimod f X b x
    have h₃ : rawPure C X (z • f.hom b) x =
        z • (show V ((tensor C).obj X) from rawPure C X (f.hom b) x) :=
      DFunLike.congr_fun ((pure C X).map_smul z (f.hom b)) x
    exact h₁.trans (h₃.trans (congrArg
      (fun y : V ((tensor C).obj X) => z • y) h₂.symm))

-- Matrix comparison is checked by precomposing with each summand inclusion
-- and postcomposing with each summand projection.
private theorem biproduct_matrix_transport {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] {m n : Nat} (p : Fin m → C) (q : Fin n → C)
    (f : ∀ i j, p i ⟶ q j) :
    F.map (biproduct.matrix f) ≫ (F.mapBiproduct q).hom =
      (F.mapBiproduct p).hom ≫ biproduct.matrix (fun i j => F.map (f i j)) := by
  apply biproduct.hom_ext
  intro j
  have hπ : (F.mapBiproduct q).hom ≫ biproduct.π (F.obj ∘ q) j =
      F.map (biproduct.π q j) := by
    exact Functor.biproductComparison_π F q j
  simp only [Category.assoc, hπ]
  apply (cancel_epi (F.mapBiproduct p).inv).mp
  apply biproduct.hom_ext'
  intro i
  have hι : biproduct.ι (F.obj ∘ p) i ≫ (F.mapBiproduct p).inv =
      F.map (biproduct.ι p i) := by
    exact Functor.ι_biproductComparison' F p i
  calc
    _ = F.map (biproduct.components (biproduct.matrix f) i j) := by
      simp only [← Category.assoc, hι, ← F.map_comp, biproduct.components]
    _ = F.map (f i j) := by rw [biproduct.matrix_components]
    _ = biproduct.components (biproduct.matrix (fun i j => F.map (f i j))) i j :=
      (biproduct.matrix_components (f := F.obj ∘ p) (g := F.obj ∘ q)
        (fun i j => F.map (f i j)) i j).symm
    _ = _ := by
      simp only [biproduct.components, Iso.inv_hom_id_assoc]
      rfl


private theorem matrix_predicate {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {m n : Nat} {p : Fin m → C} {q : Fin n → C}
    (D : Fin m → Fin n → Type*) (dmap : ∀ i j, D i j → (p i ⟶ q j))
    (η : biproduct p ⟶ biproduct q) :
    (∀ i j, ∃ d : D i j, biproduct.components η i j = dmap i j d) ↔
      ∃ d : ∀ i j, D i j, η = biproduct.matrix (fun i j => dmap i j (d i j)) := by
  constructor
  · intro h
    choose d hd using h
    exact ⟨d, (biproduct.components_matrix η).symm.trans
      (congrArg biproduct.matrix (funext fun i => funext fun j => hd i j))⟩
  · rintro ⟨d, rfl⟩ i j
    exact ⟨d i j, biproduct.matrix_components _ i j⟩

private theorem transAdditive {K H : Type u} [Group K] [Group H] :
    (trans.{u,v} K H).Additive where
  map_add {B C} f g := by
    apply NatTrans.ext
    funext X
    apply hom_ext_pure B X
    intro b x
    have hf := rawMapBimod f X b x
    have hg := rawMapBimod g X b x
    have hadd : (((pure C X) (f.hom b + g.hom b)) x) =
        ((pure C X) (f.hom b)) x + ((pure C X) (g.hom b)) x :=
      DFunLike.congr_fun ((pure C X).map_add (f.hom b) (g.hom b)) x
    exact (rawMapBimod (f + g) X b x).trans (hadd.trans (congrArg₂ (· + ·) hf.symm hg.symm))

private theorem wordMap_id {K H : Subgroup U} (p : Word K H) :
    wordMap.{u,v} (Biset.Hom.id p.basis) = 𝟙 (wordBimod.{u,v} p) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  change (lower.{u,v} p).symm (lower.{u,v} p b) = b
  exact (lower.{u,v} p).symm_apply_apply b

private theorem wordMap_vertical {K H : Subgroup U} {p q r : Word K H}
    (f : wordHom p q) (g : wordHom q r) :
    wordMap.{u,v} (f.vertical g) = wordMap.{u,v} f ≫ wordMap.{u,v} g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  change (lower.{u,v} r).symm (g.toLinearMap (f.toLinearMap (lower.{u,v} p b))) =
    (lower.{u,v} r).symm (g.toLinearMap (lower.{u,v} q
      ((lower.{u,v} q).symm (f.toLinearMap (lower.{u,v} p b)))))
  rw [LinearEquiv.apply_symm_apply]

private theorem wordMap_zero {K H : Subgroup U} (p q : Word K H) :
    wordMap.{u,v} (Biset.Hom.zero : wordHom p q) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  change (lower.{u,v} q).symm 0 = 0
  exact map_zero _

private theorem wordMap_add {K H : Subgroup U} {p q : Word K H} (f g : wordHom p q) :
    wordMap.{u,v} (Biset.Hom.add f g) = wordMap.{u,v} f + wordMap.{u,v} g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  exact map_add (lower.{u,v} q).symm _ _

private theorem wordMap_scale {K H : Subgroup U} {p q : Word K H} (z : Complex) (f : wordHom p q) :
    wordMap.{u,v} (Biset.Hom.scale z f) = z • wordMap.{u,v} f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  exact (lower.{u,v} q).symm.map_smul z _

private noncomputable abbrev paired {K L H : Subgroup U} (p : Word K L) (q : Word L H)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) : wordBimod.{u,v} (Word.tensor p q) :=
  (lower.{u,v} (Word.tensor p q)).symm
    (Biset.pairLinear Complex p.basis q.basis (lower.{u,v} p b) (lower.{u,v} q c))

private theorem paired_generators_ext {K L H : Subgroup U} (p : Word K L) (q : Word L H)
    {W : Type*} [AddCommGroup W] [Module Complex W]
    {f g : wordBimod.{u,v} (Word.tensor p q) →ₗ[Complex] W}
    (h : ∀ i j,
      f (paired p q ((lower.{u,v} p).symm (Finsupp.single i 1))
        ((lower.{u,v} q).symm (Finsupp.single j 1))) =
      g (paired p q ((lower.{u,v} p).symm (Finsupp.single i 1))
        ((lower.{u,v} q).symm (Finsupp.single j 1)))) : f = g := by
  let l := lower.{u,v} (Word.tensor p q)
  have eq : f.comp l.symm.toLinearMap = g.comp l.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro z a
    change Quotient (Biset.balance p.basis q.basis) at z
    refine Quotient.inductionOn z ?_
    rintro ⟨i, j⟩
    have h₁ := h i j
    simp only [paired, LinearEquiv.apply_symm_apply, Biset.pairLinear_single, one_mul] at h₁
    have ha : Finsupp.single (Biset.pair p.basis q.basis i j) a =
        a • Finsupp.single (Biset.pair p.basis q.basis i j) (1 : Complex) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    change f (l.symm (Finsupp.single (Biset.pair p.basis q.basis i j) a)) =
      g (l.symm (Finsupp.single (Biset.pair p.basis q.basis i j) a))
    rw [ha, map_smul, map_smul, map_smul, h₁]
  apply LinearMap.ext
  intro b
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using DFunLike.congr_fun eq (l b)

private noncomputable abbrev drawingEval {K H : Subgroup U} {p q : Word K H}
    (d : LabelledDrawing Complex p q) : wordHom p q :=
  ScopedDiagram.eval (LabelledDrawing.interpret d)

private noncomputable abbrev diagramMap {K H : Subgroup U} {p q : Word K H}
    (d : LabelledDrawing Complex p q) :=
  liftMap.{u,v} (drawingEval d)

private theorem evaluated_horizontal_pair {K L H : Subgroup U}
    (p p' : Word K L) (q q' : Word L H) (d : LabelledDrawing Complex p p')
    (e : LabelledDrawing Complex q q') (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    (wordMap.{u,v} (drawingEval (LabelledDrawing.horizontal d e))).hom (paired p q b c) =
      paired p' q' ((wordMap.{u,v} (drawingEval d)).hom b)
        ((wordMap.{u,v} (drawingEval e)).hom c) := by
  have hp := (InductionRestrictionBimoduleStrands.{u, 0, 0} (U := U)).2.2.1
    K L H p p' q q' d e (lower.{u,v} p b) (lower.{u,v} q c)
  change (lower.{u,v} (Word.tensor p' q')).symm
      ((drawingEval (LabelledDrawing.horizontal d e)).toLinearMap
        (lower.{u,v} (Word.tensor p q) ((lower.{u,v} (Word.tensor p q)).symm
          (Biset.pairLinear Complex p.basis q.basis (lower.{u,v} p b) (lower.{u,v} q c))))) =
    (lower.{u,v} (Word.tensor p' q')).symm
      (Biset.pairLinear Complex p'.basis q'.basis
        (lower.{u,v} p' ((lower.{u,v} p').symm ((drawingEval d).toLinearMap (lower.{u,v} p b))))
        (lower.{u,v} q' ((lower.{u,v} q').symm ((drawingEval e).toLinearMap (lower.{u,v} q c)))))
  simpa only [LinearEquiv.apply_symm_apply] using
    congrArg (lower.{u,v} (Word.tensor p' q')).symm hp

private theorem hcomp_pure {K L H : Subgroup U} {p p' : Word K L} {q q' : Word L H}
    (d : LabelledDrawing Complex p p') (e : LabelledDrawing Complex q q')
    (X : Mod.{u,v} H) (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) (x : X) :
    (((diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d)).app X).hom
        (rawPure (wordBimod.{u,v} p) ((T.{u,v} q).obj X) b (rawPure (wordBimod.{u,v} q) X c x)) =
      rawPure (wordBimod.{u,v} p') ((T.{u,v} q').obj X)
        ((wordMap.{u,v} (drawingEval d)).hom b)
        (rawPure (wordBimod.{u,v} q') X ((wordMap.{u,v} (drawingEval e)).hom c) x) := by
  rw [NatTrans.hcomp_app]
  change ((T.{u,v} p').map ((diagramMap.{u,v} e).app X)).hom
      (((diagramMap.{u,v} d).app ((T.{u,v} q).obj X)).hom
        (rawPure (wordBimod.{u,v} p) ((T.{u,v} q).obj X) b (rawPure (wordBimod.{u,v} q) X c x))) = _
  rw [rawMapBimod, rawMapInput, rawMapBimod]

-- Alphabeta Math, balanced tensor associativity, Steps 3.1 and 3.2.
-- Compare the two maps on generators using the already specified associator formula.
private theorem horizontal_comp_of_pure {K L H : Subgroup U}
    (compIso : ∀ (p : Word K L) (q : Word L H),
      T.{u,v} (Word.tensor p q) ≅ T.{u,v} q ⋙ T.{u,v} p)
    (compPure : ∀ (p : Word K L) (q : Word L H) (X : Mod.{u,v} H)
      (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) (x : V X),
      VMap ((compIso p q).hom.app X)
        (pure (wordBimod.{u,v} (Word.tensor p q)) X (paired p q b c) x) =
      pure (wordBimod.{u,v} p) ((T.{u,v} q).obj X) b
        (pure (wordBimod.{u,v} q) X c x))
    (p p' : Word K L) (q q' : Word L H) (d : LabelledDrawing Complex p p')
    (e : LabelledDrawing Complex q q') :
    diagramMap.{u,v} (LabelledDrawing.horizontal d e) ≫ (compIso p' q').hom =
      (compIso p q).hom ≫ (diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d) := by
  apply NatTrans.ext
  funext X
  apply hom_ext_pure (wordBimod.{u,v} (Word.tensor p q)) X
  intro z x
  let left := (diagramMap.{u,v} (LabelledDrawing.horizontal d e) ≫ (compIso p' q').hom).app X
  let right := ((compIso p q).hom ≫ (diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d)).app X
  let test := (pure (wordBimod.{u,v} (Word.tensor p q)) X).flip x
  change (VMap left).comp test z = (VMap right).comp test z
  apply DFunLike.congr_fun (paired_generators_ext p q ?_) z
  intro i j
  let b := (lower.{u,v} p).symm (Finsupp.single i 1)
  let c := (lower.{u,v} q).symm (Finsupp.single j 1)
  change ((compIso p' q').hom.app X).hom
      (((diagramMap.{u,v} (LabelledDrawing.horizontal d e)).app X).hom
        (rawPure (wordBimod.{u,v} (Word.tensor p q)) X (paired p q b c) x)) =
    (((diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d)).app X).hom
      (((compIso p q).hom.app X).hom
        (rawPure (wordBimod.{u,v} (Word.tensor p q)) X (paired p q b c) x))
  have pure_eq (r : Word K L) (s : Word L H) (b' : wordBimod.{u,v} r)
      (c' : wordBimod.{u,v} s) :
      ((compIso r s).hom.app X).hom
        (rawPure (wordBimod.{u,v} (Word.tensor r s)) X (paired r s b' c') x) =
      rawPure (wordBimod.{u,v} r) ((T.{u,v} s).obj X) b'
        (rawPure (wordBimod.{u,v} s) X c' x) :=
    compPure r s X b' c' x
  rw [rawMapBimod, evaluated_horizontal_pair, pure_eq, pure_eq]
  exact (hcomp_pure d e X b c x).symm

private abbrev endpointAllowedOrdinary := fun {K H : Subgroup U} {p q : Word K H}
      (d : MackeyDiagrams.Diagram Complex p q) =>
    MackeyDiagrams.Diagram.rec (motive := fun _ _ _ => Prop)
      (fun _ => True)
      (fun _ => False) (fun _ => False)
      (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ => True) (fun _ => True) (fun _ _ => True) (fun _ => True)
      (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False)
      (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)
      (fun _ _ => True) (fun _ _ a b => a ∧ b) (fun _ _ a => a) d
private abbrev endpointDrawing := fun {K H : Subgroup U} (p q : Word K H) =>
    MackeyDiagrams.LabelledDrawing Complex p q
private abbrev endpointAllowed := fun {K H : Subgroup U} {p q : Word K H} (d : endpointDrawing p q) =>
    MackeyDiagrams.LabelledDrawing.rec (motive := fun _ _ _ => Prop)
      (fun d => endpointAllowedOrdinary d)
      (fun _ => True) (fun _ => True)
      (fun vertex => match MackeyDiagrams.TrivalentVertex.kind vertex with
        | MackeyDiagrams.TrivalentKind.mergeUp | MackeyDiagrams.TrivalentKind.splitUp
        | MackeyDiagrams.TrivalentKind.mergeDown | MackeyDiagrams.TrivalentKind.splitDown => True
        | _ => False)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ => False)
      (fun _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ _ => False)
      (fun _ _ a b => a ∧ b) (fun _ _ a => a)
      (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) d

private abbrev endpointGen {K H : Subgroup U} {p q : Word K H} :=
  {d : endpointDrawing p q // endpointAllowed d}

private noncomputable abbrev endpointSetoid {K H : Subgroup U} (p q : Word K H) :=
  Setoid.ker (fun d : @endpointGen U _ K H p q => drawingEval d.val)

private noncomputable abbrev endpointGenHom {K H : Subgroup U} (p q : Word K H) :=
  Quotient (endpointSetoid p q)

private noncomputable abbrev endpointInDiagram {K H : Subgroup U} {p q : Word K H}
    (η : T.{u,v} p ⟶ T.{u,v} q) :=
  ∃ d : @endpointGen U _ K H p q, onRegular.{u,v} η = conjugateMap.{u,v} (drawingEval d.val)

private theorem endpointInDiagram_iff {K H : Subgroup U} {p q : Word K H}
    (η : T.{u,v} p ⟶ T.{u,v} q) :
    endpointInDiagram.{u,v} η ↔
      ∃ d : @endpointGen U _ K H p q, η = diagramMap.{u,v} d.val := by
  obtain ⟨f, rfl⟩ := liftMap_bijective.2 η
  constructor
  · rintro ⟨d, hd⟩
    rw [onRegular_lift] at hd
    exact ⟨d, congrArg liftMap.{u,v} (conjugateMap_injective hd)⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, (congrArg onRegular.{u,v} hd).trans (onRegular_lift (drawingEval d.val))⟩

private theorem endpointQuotient :
  (∀ (K H : Subgroup U) (p q : Word K H),
    Function.Bijective (@liftMap.{u,v} U _ K H p q) ∧
    (∀ f : wordHom p q, onRegular.{u,v} (liftMap.{u,v} f) = conjugateMap.{u,v} f) ∧
    ∃ e : Equiv (endpointGenHom p q) {η : CategoryTheory.NatTrans (T.{u,v} p) (T.{u,v} q) // endpointInDiagram.{u,v} η},
      ∀ d : @endpointGen U _ K H p q,
        (e (Quotient.mk (endpointSetoid p q) d)).val = diagramMap.{u,v} d.val) := by
  intro K H p q
  exact ⟨liftMap_bijective, onRegular_lift,
    diagramQuotientEquiv (fun d : @endpointGen U _ K H p q => drawingEval d.val),
    fun _ => rfl⟩

private theorem endpointMatrices :
  (∀ K H : Subgroup U,
    letI : CategoryTheory.Limits.HasFiniteBiproducts (BM.{u,v} K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    letI : CategoryTheory.Limits.HasFiniteBiproducts (Func.{u,v} K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    let bimodSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => wordBimod.{u,v} (p i))
    let funSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => T.{u,v} (p i))
    ∃ sumIso : ∀ {n : Nat} (p : Fin n → Word K H),
        CategoryTheory.Iso (tensor.{u,v} (bimodSum p)) (funSum p),
      ∀ {m n : Nat} (p : Fin m → Word K H) (q : Fin n → Word K H),
        (∀ f : ∀ i j, wordHom (p i) (q j),
          CategoryTheory.CategoryStruct.comp
            ((trans.{u,v} K H).map (CategoryTheory.Limits.biproduct.matrix
              (fun i j => wordMap.{u,v} (f i j)))) (sumIso q).hom =
          CategoryTheory.CategoryStruct.comp (sumIso p).hom
            (CategoryTheory.Limits.biproduct.matrix (fun i j => liftMap.{u,v} (f i j)))) ∧
        (∀ η : CategoryTheory.NatTrans (funSum p) (funSum q),
          (∀ i j, endpointInDiagram.{u,v} (CategoryTheory.Limits.biproduct.components
            (f := fun i => T.{u,v} (p i)) (g := fun j => T.{u,v} (q j)) η i j)) ↔
          ∃ d : ∀ i j, @endpointGen U _ K H (p i) (q j),
            η = CategoryTheory.Limits.biproduct.matrix (fun i j => diagramMap.{u,v} (d i j).val))) := by
  intro K H
  letI : HasFiniteBiproducts (BM.{u,v} K H) := HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts (Func.{u,v} K H) := HasFiniteBiproducts.of_hasFiniteProducts
  letI : (trans.{u,v} K H).Additive := transAdditive
  refine ⟨fun p => (trans.{u,v} K H).mapBiproduct (fun i => wordBimod.{u,v} (p i)), ?_⟩
  intro m n p q
  refine ⟨fun f => biproduct_matrix_transport (trans.{u,v} K H)
    (fun i => wordBimod.{u,v} (p i)) (fun j => wordBimod.{u,v} (q j))
    (fun i j => wordMap.{u,v} (f i j)), ?_⟩
  intro η
  refine Iff.trans ?_ (matrix_predicate
    (fun i j => @endpointGen U _ K H (p i) (q j))
    (fun _ _ d => diagramMap.{u,v} d.val) η)
  exact forall_congr' (fun _ => forall_congr' (fun _ => endpointInDiagram_iff _))

#print axioms horizontal_comp_of_pure
#print axioms endpointQuotient
#print axioms endpointMatrices

end DiagramFunctorProof
