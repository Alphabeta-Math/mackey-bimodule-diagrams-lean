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
    rw [← mul_smul, ← MulOpposite.op_mul, Algebra.smul_def, Algebra.commutes]
    rfl

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

end DiagramFunctorProof
