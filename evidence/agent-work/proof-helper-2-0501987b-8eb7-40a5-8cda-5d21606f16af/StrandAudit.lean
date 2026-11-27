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

end DiagramFunctorProof

namespace DiagramFunctorProof
open CategoryTheory
universe u v
variable {U : Type u} [Group U]

private noncomputable abbrev wordVec := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    Finsupp (MackeyDiagrams.Word.basis p).carrier Complex

private noncomputable abbrev lower := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    (ULift.moduleEquiv : LinearEquiv (RingHom.id Complex) (ULift.{v} (wordVec p)) (wordVec p))

private noncomputable abbrev wordBimod := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    (Rep.of
      ({ toFun := fun g => (lower p).symm.toLinearMap.comp
            ((MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) g).comp
              (lower p).toLinearMap)
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

private noncomputable abbrev T {K H : Subgroup U} (p : Word K H) :=
  tensor (wordBimod p)

end DiagramFunctorProof

namespace DiagramFunctorProof

open CategoryTheory

universe u v w i j

private abbrev StrandBalanced {R S : Type u} [Ring R] [Ring S]
    {N : Type i} [AddCommGroup N] (left : S → N → N) (right : R → N → N)
    (X : ModuleCat.{w} R) (Y : ModuleCat.{w} S) (t : N → X → Y) : Prop :=
  (∀ n m x, t (n + m) x = t n x + t m x) ∧
  (∀ n x y, t n (x + y) = t n x + t n y) ∧
  (∀ s n x, t (left s n) x = s • t n x) ∧
  (∀ r n x, t (right r n) x = t n (r • x))

private abbrev StrandPresentation {R S : Type u} [Ring R] [Ring S]
    {N : Type i} [AddCommGroup N] (left : S → N → N) (right : R → N → N)
    {F : ModuleCat.{w} R ⥤ ModuleCat.{w} S}
    (τ : ∀ X : ModuleCat.{w} R, N → X → F.obj X) : Prop :=
  (∀ X, StrandBalanced left right X (F.obj X) (τ X)) ∧
  (∀ (X : ModuleCat.{w} R) (Y : ModuleCat.{w} S) (t : N → X → Y),
     StrandBalanced left right X Y t →
       ∃! f : F.obj X →ₗ[S] Y, ∀ n x, f (τ X n x) = t n x) ∧
  (∀ (X Y : ModuleCat.{w} R) (f : X ⟶ Y) n x,
    (F.map f).hom (τ X n x) = τ Y n (f.hom x))

section Compare

variable {R S : Type u} [Ring R] [Ring S]
  {N : Type i} [AddCommGroup N] [Module Complex N]
  {P : Type j} [AddCommGroup P] [Module Complex P]
  {lN : S → N → N} {rN : R → N → N}
  {lP : S → P → P} {rP : R → P → P}
  {F G : ModuleCat.{w} R ⥤ ModuleCat.{w} S}
  {σ : ∀ X : ModuleCat.{w} R, N → X → F.obj X}
  {τ : ∀ X : ModuleCat.{w} R, P → X → G.obj X}

omit [Module Complex N] in
private theorem strand_hom_ext (hσ : StrandPresentation lN rN σ)
    {X : ModuleCat.{w} R} {Y : ModuleCat.{w} S} {f g : F.obj X ⟶ Y}
    (h : ∀ n x, f.hom (σ X n x) = g.hom (σ X n x)) : f = g := by
  have hb := hσ.1 X
  have hg : StrandBalanced lN rN X Y (fun n x => g.hom (σ X n x)) :=
    ⟨fun n m x => (congrArg g.hom (hb.1 n m x)).trans (g.hom.map_add _ _),
     fun n x y => (congrArg g.hom (hb.2.1 n x y)).trans (g.hom.map_add _ _),
     fun s n x => (congrArg g.hom (hb.2.2.1 s n x)).trans (g.hom.map_smul s _),
     fun r n x => congrArg g.hom (hb.2.2.2 r n x)⟩
  obtain ⟨lift, _, uniq⟩ := hσ.2.1 X Y _ hg
  exact ModuleCat.hom_injective ((uniq f.hom h).trans (uniq g.hom (fun _ _ => rfl)).symm)

variable (e : N ≃ₗ[Complex] P)
    (el : ∀ s n, e (lN s n) = lP s (e n))
    (er : ∀ r n, e (rN r n) = rP r (e n))
    (hσ : StrandPresentation lN rN σ) (hτ : StrandPresentation lP rP τ)

include el er hσ hτ in
private theorem strand_component_exists (X : ModuleCat.{w} R) :
    ∃! f : F.obj X →ₗ[S] G.obj X, ∀ n x, f (σ X n x) = τ X (e n) x := by
  have hb := hτ.1 X
  apply hσ.2.1 X (G.obj X) (fun n x => τ X (e n) x)
  refine ⟨?_, fun n x y => hb.2.1 (e n) x y, ?_, ?_⟩
  · intro n m x
    simpa only [e.map_add] using hb.1 (e n) (e m) x
  · intro s n x
    simpa only [el] using hb.2.2.1 s (e n) x
  · intro r n x
    simpa only [er] using hb.2.2.2 r (e n) x

private noncomputable def strand_component (X : ModuleCat.{w} R) : F.obj X ⟶ G.obj X :=
  ModuleCat.ofHom (Classical.choose (strand_component_exists e el er hσ hτ X))

private theorem strand_component_pure (X : ModuleCat.{w} R) (n : N) (x : X) :
    (strand_component e el er hσ hτ X).hom (σ X n x) = τ X (e n) x :=
  (Classical.choose_spec (strand_component_exists e el er hσ hτ X)).1 n x

private noncomputable def strand_hom : F ⟶ G where
  app := strand_component e el er hσ hτ
  naturality {X Y} f := by
    apply strand_hom_ext hσ
    intro n x
    change (strand_component e el er hσ hτ Y).hom ((F.map f).hom (σ X n x)) =
      (G.map f).hom ((strand_component e el er hσ hτ X).hom (σ X n x))
    rw [hσ.2.2, strand_component_pure, strand_component_pure, hτ.2.2]

private theorem strand_hom_pure (X : ModuleCat.{w} R) (n : N) (x : X) :
    ((strand_hom e el er hσ hτ).app X).hom (σ X n x) = τ X (e n) x :=
  strand_component_pure e el er hσ hτ X n x

include el in
private theorem strand_symm_left (s : S) (p : P) :
    e.symm (lP s p) = lN s (e.symm p) :=
  e.injective (by rw [e.apply_symm_apply, el, e.apply_symm_apply])

include er in
private theorem strand_symm_right (r : R) (p : P) :
    e.symm (rP r p) = rN r (e.symm p) :=
  e.injective (by rw [e.apply_symm_apply, er, e.apply_symm_apply])

private noncomputable def strand_iso : F ≅ G where
  hom := strand_hom e el er hσ hτ
  inv := strand_hom e.symm (strand_symm_left e el) (strand_symm_right e er) hτ hσ
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    apply strand_hom_ext hσ
    intro n x
    change ((strand_hom e.symm _ _ hτ hσ).app X).hom
        (((strand_hom e el er hσ hτ).app X).hom (σ X n x)) = σ X n x
    rw [strand_hom_pure, strand_hom_pure, e.symm_apply_apply]
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    apply strand_hom_ext hτ
    intro p x
    change ((strand_hom e el er hσ hτ).app X).hom
        (((strand_hom e.symm _ _ hτ hσ).app X).hom (τ X p x)) = τ X p x
    rw [strand_hom_pure, strand_hom_pure, e.apply_symm_apply]

private theorem strand_iso_pure (X : ModuleCat.{w} R) (n : N) (x : X) :
    ((strand_iso e el er hσ hτ).hom.app X).hom (σ X n x) = τ X (e n) x :=
  strand_hom_pure e el er hσ hτ X n x

end Compare

end DiagramFunctorProof

namespace DiagramFunctorProof

open CategoryTheory

universe u v

variable {U : Type u} [Group U]

private noncomputable def wordCoeffIso {K H G : Subgroup U} (p : Word K H)
    (h : p.basis.carrier = G) : wordBimod.{u,v} p ≃ₗ[Complex] MonoidAlgebra Complex G :=
  let coeff : (G →₀ Complex) ≃ₗ[Complex] MonoidAlgebra Complex G :=
    (MonoidAlgebra.coeffLinearEquiv Complex).symm
  (lower p).trans (cast (congrArg (fun C : Type u =>
    (C →₀ Complex) ≃ₗ[Complex] MonoidAlgebra Complex G) h.symm) coeff)

private theorem wordPresentation {K H : Subgroup U} (p : Word K H) :
    StrandPresentation (fun s b => leftHom (wordBimod.{u,v} p) s b)
      (fun r => rightHom (wordBimod.{u,v} p) (MulOpposite.op r))
      (rawPure (wordBimod.{u,v} p)) :=
  ⟨fun X => (rawUniversal (wordBimod p) X).1,
   fun X => (rawUniversal (wordBimod p) X).2,
   fun _ _ => rawMapInput (wordBimod p)⟩

private theorem strandActions {K H : Type u} [Group K] [Group H]
    {B : BM.{u,v} K H} {A : Type u} [Ring A] [Algebra Complex A]
    (e : B ≃ₗ[Complex] A) (L : MonoidAlgebra Complex K →ₐ[Complex] A)
    (R : MonoidAlgebra Complex H →ₐ[Complex] A)
    (h : ∀ k h b, e (B.ρ (k, h⁻¹) b) =
      L (MonoidAlgebra.of Complex K k) * (e b * R (MonoidAlgebra.of Complex H h))) :
    (∀ s b, e (leftHom B s b) = L s * e b) ∧
    (∀ r b, e (rightHom B (MulOpposite.op r) b) = e b * R r) := by
  constructor
  · intro s b
    induction s using MonoidAlgebra.induction_on with
    | of k =>
        rw [left_of]
        simpa only [inv_one, map_one, mul_one] using h k 1 b
    | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, add_mul, ha, ha']
    | smul z a ha => simp only [map_smul, LinearMap.smul_apply, smul_mul_assoc, ha]
  · intro r b
    induction r using MonoidAlgebra.induction_on with
    | of h' =>
        rw [right_of]
        simpa only [map_one, one_mul] using h 1 h' b
    | add a a' ha ha' =>
        simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, mul_add, ha, ha']
    | smul z a ha =>
        simp only [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, mul_smul_comm, ha]

private theorem regularWord_group (H : Subgroup U) (k h : H)
    (x : MonoidAlgebra Complex H) :
    MonoidAlgebra.ofCoeff
      (Finsupp.lmapDomain Complex Complex (fun z : H => k * z * h) x.coeff) =
      MonoidAlgebra.single k 1 * (x * MonoidAlgebra.single h 1) := by
  induction x using MonoidAlgebra.induction_on with
  | of z =>
      simp [MonoidAlgebra.of_apply, Finsupp.lmapDomain_apply,
        MonoidAlgebra.single_mul_single, mul_assoc]
  | add x y hx hy =>
      simp only [MonoidAlgebra.coeff_add, map_add, MonoidAlgebra.ofCoeff_add, add_mul,
        mul_add, hx, hy]
  | smul r x hx =>
      simp only [MonoidAlgebra.coeff_smul, map_smul, MonoidAlgebra.ofCoeff_smul,
        smul_mul_assoc, mul_smul_comm, hx]

private theorem regularWord_actions (H : Subgroup U) :
    let e := wordCoeffIso.{u,v} (G := H) (Word.empty H) rfl
    (∀ s b, e (leftHom (wordBimod (Word.empty H)) s b) = s * e b) ∧
    (∀ r b, e (rightHom (wordBimod (Word.empty H)) (MulOpposite.op r) b) = e b * r) := by
  let p := Word.empty H
  let e := wordCoeffIso.{u,v} (G := H) p rfl
  apply strandActions e (AlgHom.id _ _) (AlgHom.id _ _)
  intro k h b
  change MonoidAlgebra.ofCoeff
      (Finsupp.lmapDomain Complex Complex (fun z : H => k * z * (h⁻¹)⁻¹) (lower p b)) =
    MonoidAlgebra.single k 1 * ((e b) * MonoidAlgebra.single h 1)
  rw [inv_inv]
  exact regularWord_group H k h (e b)

private theorem identityPresentation (H : Subgroup U) :
    StrandPresentation (F := 𝟭 (Mod.{u,v} H))
      (fun (s b : MonoidAlgebra Complex H) => s * b) (fun r b => b * r)
      (fun X b x => b • x) := by
  refine ⟨fun X => ⟨fun n m x => add_smul n m x, fun n x y => smul_add n x y,
    fun s n x => mul_smul s n x, fun r n x => mul_smul n r x⟩, ?_, ?_⟩
  · intro X Y t ht
    have at_one (b : MonoidAlgebra Complex H) (x : X) : t b x = t 1 (b • x) := by
      simpa only [one_mul] using ht.2.2.2 b 1 x
    let f : X →ₗ[MonoidAlgebra Complex H] Y :=
      { toFun := t 1
        map_add' := ht.2.1 1
        map_smul' := fun r x => by
          change t 1 (r • x) = r • t 1 x
          rw [← at_one]
          simpa only [mul_one] using ht.2.2.1 r 1 x }
    refine ⟨f, fun b x => (at_one b x).symm, ?_⟩
    intro g hg
    apply LinearMap.ext
    intro x
    change g x = t 1 x
    simpa only [one_smul] using hg 1 x
  · intro X Y f b x
    exact f.hom.map_smul b x

private noncomputable def emptyIso (H : Subgroup U) :
    T.{u,v} (Word.empty H) ≅ 𝟭 (Mod.{u,v} H) :=
  strand_iso (wordCoeffIso (G := H) (Word.empty H) rfl)
    (regularWord_actions H).1 (regularWord_actions H).2
    (wordPresentation (Word.empty H)) (identityPresentation H)

private theorem emptyIso_pure (H : Subgroup U) (X : Mod.{u,v} H)
    (b : wordBimod.{u,v} (Word.empty H)) (x : V X) :
    VMap ((emptyIso H).hom.app X) (DiagramFunctorProof.pure (wordBimod (Word.empty H)) X b x) =
      (MonoidAlgebra.ofCoeff (lower (Word.empty H) b) : MonoidAlgebra Complex H) • (show X from x) :=
  strand_iso_pure (wordCoeffIso (G := H) (Word.empty H) rfl)
    (regularWord_actions H).1 (regularWord_actions H).2
    (wordPresentation (Word.empty H)) (identityPresentation H) X b x

private noncomputable abbrev strandPhi {H G : Subgroup U} (a : ConjEmbedding H G) :=
  MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom

private noncomputable abbrev strandInd {H G : Subgroup U} (a : ConjEmbedding H G) :
    Func.{u,v} G H :=
  (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H) ⋙ Rep.indFunctor Complex a.toHom) ⋙
    Rep.toModuleMonoidAlgebra (k := Complex) (G := G)

private noncomputable abbrev strandRes {H G : Subgroup U} (a : ConjEmbedding H G) :
    Func.{u,v} H G :=
  ModuleCat.restrictScalars (strandPhi a).toRingHom

private theorem strandIsos {H G : Subgroup U} (a : ConjEmbedding H G) :
    Nonempty (T.{u,v} (Word.up a) ≅ strandInd a) ∧
    Nonempty (T.{u,v} (Word.down a) ≅ strandRes a) := by
  obtain ⟨α, hα⟩ := a.hasRepresentative
  have hmem (h : H) : α * (h : U) * α⁻¹ ∈ G := hα h ▸ (a.toHom h).property
  have ha : a = ConjEmbedding.ofConjugator α hmem :=
    ConjEmbedding.ext (MonoidHom.ext fun h => Subtype.ext (hα h))
  rw [ha]
  let a := ConjEmbedding.ofConjugator α hmem
  obtain ⟨I, D, hIleft, hIright, hDleft, hDright, hIgroup, hDgroup, hInd, hRes⟩ :=
    (InductionRestrictionBimoduleStrands.{u,v,u}).1 H G α hmem |>.2.2
  let eu := wordCoeffIso.{u,v} (G := G) (Word.up a) rfl
  let ed := wordCoeffIso.{u,v} (G := G) (Word.down a) rfl
  have upGroup (k : G) (h : H) (b : wordBimod.{u,v} (Word.up a)) :
      eu ((wordBimod (Word.up a)).ρ (k, h⁻¹) b) =
        AlgHom.id Complex (MonoidAlgebra Complex G) (MonoidAlgebra.of Complex G k) *
          (eu b * strandPhi a (MonoidAlgebra.of Complex H h)) := by
    change MonoidAlgebra.ofCoeff
        (Biset.actLinear Complex (Word.up a).basis (k, h⁻¹) (lower (Word.up a) b)) =
      MonoidAlgebra.single k 1 * (eu b * strandPhi a (MonoidAlgebra.single h 1))
    have hcoeff : (eu b).coeff = lower (Word.up a) b := rfl
    have hg := hIgroup k h (eu b)
    rw [hIleft, hIright, hcoeff] at hg
    exact hg
  have downGroup (h : H) (k : G) (b : wordBimod.{u,v} (Word.down a)) :
      ed ((wordBimod (Word.down a)).ρ (h, k⁻¹) b) =
        strandPhi a (MonoidAlgebra.of Complex H h) *
          (ed b * AlgHom.id Complex (MonoidAlgebra Complex G) (MonoidAlgebra.of Complex G k)) := by
    change MonoidAlgebra.ofCoeff
        (Biset.actLinear Complex (Word.down a).basis (h, k⁻¹) (lower (Word.down a) b)) =
      strandPhi a (MonoidAlgebra.single h 1) * (ed b * MonoidAlgebra.single k 1)
    have hcoeff : (ed b).coeff = lower (Word.down a) b := rfl
    have hg := hDgroup h k (ed b)
    rw [hDleft, hDright, hcoeff] at hg
    exact hg
  obtain ⟨ul, ur⟩ := strandActions eu (AlgHom.id _ _) (strandPhi a) upGroup
  obtain ⟨dl, dr⟩ := strandActions ed (strandPhi a) (AlgHom.id _ _) downGroup
  obtain ⟨σ, hσ⟩ := hInd
  obtain ⟨τ, hτ⟩ := hRes
  have hu : StrandPresentation (F := strandInd.{u,v} a)
      (fun s b => s * b) (fun r b => b * strandPhi a r) σ := by
    simpa only [StrandPresentation, StrandBalanced, hIleft, hIright] using hσ
  have hd : StrandPresentation (F := strandRes.{u,v} a)
      (fun r b => strandPhi a r * b) (fun s b => b * s) τ := by
    simpa only [StrandPresentation, StrandBalanced, hDleft, hDright] using hτ
  exact ⟨⟨strand_iso eu ul ur (wordPresentation (Word.up a)) hu⟩,
         ⟨strand_iso ed dl dr (wordPresentation (Word.down a)) hd⟩⟩

end DiagramFunctorProof

#print axioms DiagramFunctorProof.emptyIso
#print axioms DiagramFunctorProof.emptyIso_pure
#print axioms DiagramFunctorProof.strandIsos
