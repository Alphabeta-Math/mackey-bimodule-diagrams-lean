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

section
open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct

namespace DiagramFunctorProof

universe u v
noncomputable section

variable {H G : Type u} [Group H] [Group G] (f : H →* G)

-- This is the coset key bijection used in freeRight. Invert the labels
-- in IndV, whose coinvariant presentation uses the left regular action.
private def cosetKeys (hf : Function.Injective f) : (Σ _ : G ⧸ f.range, H) ≃ G :=
  Equiv.ofBijective (fun ih => Quotient.out ih.1 * f ih.2) (by
    have quotient_eq (i : G ⧸ f.range) (h : H) :
        ((Quotient.out i * f h : G) : G ⧸ f.range) = i := by
      refine (QuotientGroup.eq.mpr ?_).trans (Quotient.out_eq' i)
      exact ⟨h⁻¹, by simp [mul_inv_rev, mul_assoc]⟩
    constructor
    · rintro ⟨i, h⟩ ⟨j, k⟩ (e : Quotient.out i * f h = Quotient.out j * f k)
      have eqij : i = j := (quotient_eq i h).symm.trans
        ((congrArg (fun x : G => (x : G ⧸ f.range)) e).trans (quotient_eq j k))
      subst j
      congr 1
      exact hf (mul_left_cancel e)
    · intro g
      let i : G ⧸ f.range := (g : G ⧸ f.range)
      have eqi : ((Quotient.out i : G) : G ⧸ f.range) = (g : G ⧸ f.range) :=
        Quotient.out_eq' i
      obtain ⟨h, hh⟩ := QuotientGroup.eq.mp eqi
      exact ⟨⟨i, h⟩, by change Quotient.out i * f h = g; rw [hh, mul_inv_cancel_left]⟩)

private theorem cosetKeys_apply (hf : Function.Injective f) (i : G ⧸ f.range) (h : H) :
    cosetKeys f hf ⟨i, h⟩ = Quotient.out i * f h := rfl

variable (hf : Function.Injective f) (A : Rep.{max u v} ℂ H)

private def indCoordinate (g : G) : A →ₗ[ℂ] (G ⧸ f.range →₀ A) :=
  let ih := (cosetKeys f hf).symm g⁻¹
  Finsupp.lsingle ih.1 ∘ₗ A.ρ ih.2

private theorem indCoordinate_onKey (i : G ⧸ f.range) (h : H) (x : A) :
    indCoordinate f hf A (Quotient.out i * f h)⁻¹ x =
      Finsupp.single i (A.ρ h x) := by
  simp [indCoordinate, ← cosetKeys_apply f hf]

private theorem indCoordinate_balance (s : H) (g : G) (x : A) :
    indCoordinate f hf A (f s * g) (A.ρ s x) = indCoordinate f hf A g x := by
  obtain ⟨⟨i, h⟩, hg⟩ := (cosetKeys f hf).surjective g⁻¹
  have hg' : g = (Quotient.out i * f h)⁻¹ := by
    simpa [cosetKeys_apply] using (congrArg Inv.inv hg).symm
  rw [hg', indCoordinate_onKey]
  have ha : f s * (Quotient.out i * f h)⁻¹ = (Quotient.out i * f (h * s⁻¹))⁻¹ := by
    simp [mul_inv_rev, mul_assoc]
  rw [ha, indCoordinate_onKey]
  simp

-- Alphabeta Math, Universal property of M⊗_R N, Steps 3.1, 4.1 and 5.1.
-- Mathlib implements induction by coinvariants. The coordinate map descends
-- after checking the diagonal subgroup action and is compared on pure tensors.
-- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
private def indToCoordinates : IndV f A.ρ →ₗ[ℂ] (G ⧸ f.range →₀ A) :=
  Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift (A →ₗ[ℂ] (G ⧸ f.range →₀ A)) ℂ G (indCoordinate f hf A)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) (by
        intro s
        ext g x i
        simpa [ofMulAction_single] using
          DFunLike.congr_fun (indCoordinate_balance f hf A s g x) i)

private theorem indToCoordinates_mk (g : G) (x : A) :
    indToCoordinates f hf A (IndV.mk f A.ρ g x) = indCoordinate f hf A g x := by
  simp [indToCoordinates, IndV.mk]

private def indFromCoordinates : (G ⧸ f.range →₀ A) →ₗ[ℂ] IndV f A.ρ :=
  Finsupp.lsum ℂ fun i => IndV.mk f A.ρ (Quotient.out i)⁻¹

private theorem indFromCoordinates_single (i : G ⧸ f.range) (x : A) :
    indFromCoordinates f A (Finsupp.single i x) = IndV.mk f A.ρ (Quotient.out i)⁻¹ x := by
  exact Finsupp.lsum_single _ _ i x

private theorem indMk_onKey (i : G ⧸ f.range) (h : H) (x : A) :
    IndV.mk f A.ρ (Quotient.out i * f h)⁻¹ x =
      IndV.mk f A.ρ (Quotient.out i)⁻¹ (A.ρ h x) := by
  simpa [IndV.mk, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply, mul_inv_rev]
    using Coinvariants.mk_inv_tmul ((leftRegular ℂ G).comp f) A.ρ
      (MonoidAlgebra.single (Quotient.out i)⁻¹ 1) x h

private theorem indFromTo :
    (indFromCoordinates f A).comp (indToCoordinates f hf A) = LinearMap.id := by
  apply IndV.hom_ext f A.ρ
  intro g
  apply LinearMap.ext
  intro x
  change indFromCoordinates f A (indToCoordinates f hf A (IndV.mk f A.ρ g x)) =
    IndV.mk f A.ρ g x
  obtain ⟨⟨i, h⟩, hg⟩ := (cosetKeys f hf).surjective g⁻¹
  have hg' : g = (Quotient.out i * f h)⁻¹ := by
    simpa [cosetKeys_apply] using (congrArg Inv.inv hg).symm
  rw [hg', indToCoordinates_mk, indCoordinate_onKey, indFromCoordinates_single, indMk_onKey]

private theorem indToFrom :
    (indToCoordinates f hf A).comp (indFromCoordinates f A) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i x
  change indToCoordinates f hf A (indFromCoordinates f A (Finsupp.single i x)) =
    Finsupp.single i x
  rw [indFromCoordinates_single, indToCoordinates_mk]
  simpa using indCoordinate_onKey.{u,v} f hf A i 1 x

private def indCoordinates : IndV f A.ρ ≃ₗ[ℂ] (G ⧸ f.range →₀ A) :=
  LinearEquiv.ofLinearMap (indToCoordinates f hf A) (indFromCoordinates f A)
    (indToFrom f hf A) (indFromTo f hf A)

private theorem indCoordinates_natural {A B : Rep.{max u v} ℂ H} (a : A ⟶ B) :
    (indCoordinates f hf B).toLinearMap.comp (Rep.indMap f a).hom.toLinearMap =
      (Finsupp.mapRange.linearMap (Rep.Hom.hom a).toLinearMap).comp
        (indCoordinates f hf A).toLinearMap := by
  apply IndV.hom_ext f A.ρ
  intro g
  apply LinearMap.ext
  intro x
  change indToCoordinates f hf B ((Rep.indMap f a).hom (IndV.mk f A.ρ g x)) =
    Finsupp.mapRange.linearMap a.hom.toLinearMap (indToCoordinates f hf A (IndV.mk f A.ρ g x))
  have he : (Rep.indMap f a).hom (IndV.mk f A.ρ g x) = IndV.mk f B.ρ g (a.hom x) := by
    simp [Rep.indMap, IndV.mk]
  rw [he, indToCoordinates_mk, indToCoordinates_mk]
  simp [indCoordinate, Rep.hom_comm_apply]

private abbrev GroupAlgebra (S : Type u) [Group S] := MonoidAlgebra ℂ S

private def moduleInduction : ModuleCat.{max u v} (GroupAlgebra H) ⥤
    ModuleCat.{max u v} (GroupAlgebra G) :=
  (Rep.ofModuleMonoidAlgebra ⋙ Rep.indFunctor ℂ f) ⋙ Rep.toModuleMonoidAlgebra

private def moduleIndCoordinate (X : ModuleCat.{max u v} (GroupAlgebra H)) :
    (moduleInduction f).obj X ≃+ (G ⧸ f.range →₀ X) :=
  (indCoordinates f hf (Rep.ofModuleMonoidAlgebra.obj X)).toAddEquiv

private theorem moduleIndCoordinate_natural {X Y : ModuleCat.{max u v} (GroupAlgebra H)}
    (a : X ⟶ Y) (z : (moduleInduction f).obj X) (i : G ⧸ f.range) :
    moduleIndCoordinate f hf Y ((moduleInduction f).map a z) i =
      a (moduleIndCoordinate f hf X z i) := by
  have he := indCoordinates_natural f hf (Rep.ofModuleMonoidAlgebra.map a)
  exact DFunLike.congr_fun (LinearMap.congr_fun he z) i

include hf in
private theorem moduleInduction_additive : (moduleInduction.{u,v} f).Additive where
  map_add {X Y} a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (moduleIndCoordinate f hf Y).injective
    change moduleIndCoordinate f hf Y ((moduleInduction f).map (a + b) z) =
      moduleIndCoordinate f hf Y (((moduleInduction f).map a z) + ((moduleInduction f).map b z))
    rw [map_add]
    apply Finsupp.ext
    intro i
    rw [Finsupp.add_apply, moduleIndCoordinate_natural, moduleIndCoordinate_natural,
      moduleIndCoordinate_natural]
    rfl

include hf in
private theorem moduleInduction_map_exact (S : ShortComplex (ModuleCat.{max u v} (GroupAlgebra H)))
    (hS : S.Exact) :
    letI := moduleInduction_additive.{u,v} f hf
    (S.map (moduleInduction f)).Exact := by
  haveI := moduleInduction_additive.{u,v} f hf
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  intro z
  change (moduleInduction f).map S.g z = 0 ↔
    z ∈ Set.range (fun w => (moduleInduction f).map S.f w)
  constructor
  · intro hz
    have hr : moduleIndCoordinate f hf S.X₂ z ∈
        Set.range (Finsupp.mapRange (fun x => S.f x) S.f.hom.map_zero) := by
      rw [Finsupp.range_mapRange]
      intro i
      apply (hS _).mp
      rw [← moduleIndCoordinate_natural, hz, map_zero, Finsupp.zero_apply]
    obtain ⟨w, hw⟩ := hr
    refine ⟨(moduleIndCoordinate f hf S.X₁).symm w, ?_⟩
    apply (moduleIndCoordinate f hf S.X₂).injective
    apply Finsupp.ext
    intro i
    rw [moduleIndCoordinate_natural, AddEquiv.apply_symm_apply, ← hw, Finsupp.mapRange_apply]
  · rintro ⟨w, rfl⟩
    apply (moduleIndCoordinate f hf S.X₃).injective
    rw [map_zero]
    apply Finsupp.ext
    intro i
    rw [moduleIndCoordinate_natural, moduleIndCoordinate_natural, Finsupp.zero_apply]
    exact (hS _).mpr ⟨_, rfl⟩

include hf in
private theorem moduleInduction_preservesFiniteLimits :
    PreservesFiniteLimits (moduleInduction.{u,v} f) := by
  haveI := moduleInduction_additive.{u,v} f hf
  have h : PreservesFiniteLimits (moduleInduction.{u,v} f) ∧
      PreservesFiniteColimits (moduleInduction.{u,v} f) :=
    ((Functor.exact_tfae (moduleInduction.{u,v} f)).out 2 4).mp
      (moduleInduction_map_exact.{u,v} f hf)
  exact h.1

private theorem induction_preservesFiniteLimits {U : Type u} [Group U]
    {H G : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H G) :
    PreservesFiniteLimits
      ((Rep.ofModuleMonoidAlgebra (k := ℂ) (G := H) ⋙ Rep.indFunctor ℂ a.toHom) ⋙
        (Rep.toModuleMonoidAlgebra (k := ℂ) (G := G)) :
        ModuleCat.{max u v} (GroupAlgebra H) ⥤ ModuleCat.{max u v} (GroupAlgebra G)) := by
  exact moduleInduction_preservesFiniteLimits.{u,v} a.toHom a.injective


end

end DiagramFunctorProof
end

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
  let keys := cosetKeys f hf
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

-- Alphabeta Math, Universal property of M⊗_R N, Steps 1.2, 4.1 and 5.1.
-- The two presentations come from InductionRestrictionBimoduleStrands.1
-- after transporting the representative conjugator to the given embedding.
-- The lifts here are linear for the exterior group algebra. Their pure
-- formulas determine the inverse identities and naturality.
-- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
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


namespace DiagramFunctorProof
open MackeyDiagrams CategoryTheory WattsFoundation.General

universe u v
variable {U : Type u} [Group U]


section WordComposition
variable {K L H : Subgroup U} (p : Word K L) (q : Word L H)

-- Alphabeta Math, Associativity of tensor products for compatible bimodules,
-- Steps 1.1, 1.2, 2.1, 2.2, 3.1, 3.2 and 4.1. The middle product here
-- linearizes a balanced biset. The inverse on the right group action
-- converts group balance to algebra balance. Induction over the group
-- algebras gives the exterior action laws, and the Watts universal maps
-- then give the component comparison.
-- https://alphabetamath.cc/item/thm-associativity-of-balanced-tensor-products
private noncomputable def wordPair :
    wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex] wordBimod.{u,v} (p.tensor q) :=
  ((LinearMap.llcomp Complex _ _ _) (lower (p.tensor q)).symm.toLinearMap).comp
    (((Biset.pairLinear Complex p.basis q.basis).compl₂ (lower q).toLinearMap).comp
      (lower p).toLinearMap)

private theorem wordPair_apply (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q b c = (lower (p.tensor q)).symm
      (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c)) := rfl

private theorem wordPair_left (a : MonoidAlgebra Complex K)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q (leftHom (wordBimod p) a b) c =
      leftHom (wordBimod (p.tensor q)) a (wordPair p q b c) := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
    rw [left_of (wordBimod.{u,v} p) k b, left_of (wordBimod.{u,v} (p.tensor q)) k]
    apply (lower (p.tensor q)).injective
    change Biset.pairLinear Complex p.basis q.basis
        (p.basis.actLinear Complex (k, 1) (lower p b)) (lower q c) =
      (p.basis.tensor q.basis).actLinear Complex (k, 1)
        (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c))
    simpa only [← Prod.one_eq_mk, Biset.actLinear_one, LinearMap.id_apply] using
      Biset.pairLinear_action Complex p.basis q.basis (k, 1) (1, 1) (k, 1)
        (fun s t => by
          change p.basis.pair q.basis _ _ = p.basis.pair q.basis _ _
          rw [show q.basis.act (1, 1) t = t from q.basis.one_act t])
        (lower p b) (lower q c)
  | add a d ha hd => simp only [map_add, LinearMap.add_apply, ha, hd]
  | smul z a ha => simp only [map_smul, LinearMap.smul_apply, ha]

private theorem wordPair_right (a : MonoidAlgebra Complex H)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q b (rightHom (wordBimod q) (MulOpposite.op a) c) =
      rightHom (wordBimod (p.tensor q)) (MulOpposite.op a) (wordPair p q b c) := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
    rw [right_of (wordBimod.{u,v} q) h c, right_of (wordBimod.{u,v} (p.tensor q)) h]
    apply (lower (p.tensor q)).injective
    change Biset.pairLinear Complex p.basis q.basis
        (lower p b) (q.basis.actLinear Complex (1, h⁻¹) (lower q c)) =
      (p.basis.tensor q.basis).actLinear Complex (1, h⁻¹)
        (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c))
    simpa only [← Prod.one_eq_mk, Biset.actLinear_one, LinearMap.id_apply] using
      Biset.pairLinear_action Complex p.basis q.basis (1, 1) (1, h⁻¹) (1, h⁻¹)
        (fun s t => by
          change p.basis.pair q.basis _ _ = p.basis.pair q.basis _ _
          rw [show p.basis.act (1, 1) s = s from p.basis.one_act s])
        (lower p b) (lower q c)
  | add a d ha hd => simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, ha, hd]
  | smul z a ha => simp only [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, ha]

private theorem wordPairUP {M : Type (max u v)} [AddCommGroup M] [Module Complex M]
    (f : wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex] M)
    (hf : ∀ (a : MonoidAlgebra Complex L) b c,
      f (rightHom (wordBimod p) (MulOpposite.op a) b) c =
      f b (leftHom (wordBimod q) a c)) :
    ∃! g : wordBimod.{u,v} (p.tensor q) →ₗ[Complex] M, ∀ b c, g (wordPair p q b c) = f b c := by
  let f' := (f.compl₂ (lower q).symm.toLinearMap).comp (lower p).symm.toLinearMap
  -- The biset relation acts diagonally. The right algebra action uses the inverse.
  have hf' : Biset.IsBalanced f' := by
    intro l b c
    have e := hf (MonoidAlgebra.of Complex L l)
      ((lower p).symm (p.basis.actLinear Complex (1,l) b)) ((lower q).symm c)
    rw [right_of, left_of] at e
    have undo : (p.basis.actLinear Complex (1,l⁻¹)).comp (p.basis.actLinear Complex (1,l)) =
        LinearMap.id := by
      apply Finsupp.lhom_ext
      intro s r
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Biset.actLinear_single,
        ← Biset.mul_act, Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, Biset.one_act]
    have e' : p.basis.actLinear Complex (1,l⁻¹) (p.basis.actLinear Complex (1,l) b) = b :=
      LinearMap.congr_fun undo b
    change f ((lower p).symm (p.basis.actLinear Complex (1,l⁻¹)
          (p.basis.actLinear Complex (1,l) b))) ((lower q).symm c) =
      f ((lower p).symm (p.basis.actLinear Complex (1,l) b))
        ((lower q).symm (q.basis.actLinear Complex (l,1) c)) at e
    rw [e'] at e
    exact e.symm
  let g := Biset.liftBalanced f' hf'
  have hg := Biset.liftBalanced_pairLinear f' hf'
  refine ⟨g.comp (lower (p.tensor q)).toLinearMap, ?_, ?_⟩
  · intro b c
    change g (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c)) = f b c
    simpa only [f', LinearMap.comp_apply, LinearMap.compl₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using hg (lower p b) (lower q c)
  · intro k hk
    have e : k.comp (lower (p.tensor q)).symm.toLinearMap = g := by
      apply Biset.liftBalanced_unique f' hf'
      intro b c
      change k ((lower (p.tensor q)).symm (Biset.pairLinear Complex p.basis q.basis b c)) =
        f ((lower p).symm b) ((lower q).symm c)
      let x : wordBimod.{u,v} p := (lower p).symm b
      let y : wordBimod.{u,v} q := (lower q).symm c
      have he := hk x y
      rw [wordPair_apply p q x y] at he
      simpa only [x, y, LinearEquiv.apply_symm_apply] using he
    apply LinearMap.ext
    intro y
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      LinearMap.congr_fun e (lower (p.tensor q) y)

end WordComposition

section TensorPureGeneration
variable {K H : Type u} [Group K] [Group H]
variable (B : BM.{u,v} K H) (X : Mod.{u,v} H)

private theorem pure_linear_ext {M : Type (max u v)} [AddCommGroup M] [Module Complex M]
    {f g : V ((tensor B).obj X) →ₗ[Complex] M}
    (eq : ∀ b x, f (pure B X b x) = g (pure B X b x)) : f = g := by
  let Y := (tensor B).obj X
  let S : Set Y := Set.range fun bx : B × X => rawPure B X bx.1 bx.2
  -- The additive subgroup generated by pure tensors is stable under the left algebra.
  -- Its quotient map vanishes on pure tensors, so the Watts uniqueness law makes it zero.
  let A : AddSubgroup Y := AddSubgroup.closure S
  have stable (a : MonoidAlgebra Complex K) :
      A ≤ A.comap (smulAddHom (MonoidAlgebra Complex K) Y a) := by
    apply (AddSubgroup.closure_le _).2
    rintro _ ⟨⟨b,x⟩, rfl⟩
    change a • rawPure B X b x ∈ A
    have e : rawPure B X (leftHom B a b) x = a • rawPure B X b x :=
      (rawUniversal B X).1.2.2.1 a b x
    rw [← e]
    exact AddSubgroup.subset_closure ⟨(leftHom B a b, x), rfl⟩
  let A' : Submodule (MonoidAlgebra Complex K) Y :=
    { A with smul_mem' := fun a _ h => stable a h }
  have hp (b : B) (x : X) : rawPure B X b x ∈ A' :=
    AddSubgroup.subset_closure ⟨(b, x), rfl⟩
  have hz : ModuleCat.ofHom A'.mkQ = (0 : Y ⟶ ModuleCat.of (GC K) (Y ⧸ A')) := by
    apply hom_ext_pure B X
    intro b x
    exact (Submodule.Quotient.mk_eq_zero A').2 (hp b x)
  let E : AddSubgroup Y :=
    { carrier := { y | f (show V Y from y) = g (show V Y from y) }
      zero_mem' := by
        change f (0 : V Y) = g (0 : V Y)
        rw [map_zero, map_zero]
      add_mem' := fun {a b} ha hb => by
        change f (a + b) = g (a + b)
        rw [map_add, map_add, show f a = g a from ha, show f b = g b from hb]
      neg_mem' := fun {a} ha => by
        change f (-a) = g (-a)
        rw [map_neg, map_neg, show f a = g a from ha] }
  have hAE : A ≤ E := (AddSubgroup.closure_le E).2 (by
    rintro _ ⟨⟨b,x⟩, rfl⟩
    exact eq b x)
  apply LinearMap.ext
  intro y
  have hzero : A'.mkQ y = 0 := congrArg (fun h => ModuleCat.Hom.hom h y) hz
  exact hAE ((Submodule.Quotient.mk_eq_zero A').1 hzero)

end TensorPureGeneration

section WordComposition
variable {K L H : Subgroup U} (p : Word K L) (q : Word L H)

private theorem wordPair_middle (a : MonoidAlgebra Complex L)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q (rightHom (wordBimod p) (MulOpposite.op a) b) c =
      wordPair p q b (leftHom (wordBimod q) a c) := by
  induction a using MonoidAlgebra.induction_on with
  | of l =>
    rw [left_of (wordBimod.{u,v} q) l c, right_of (wordBimod.{u,v} p) l b]
    rw [wordPair_apply p q ((wordBimod.{u,v} p).ρ (1,l⁻¹) b) c,
      wordPair_apply p q b ((wordBimod.{u,v} q).ρ (l,1) c)]
    apply congrArg (lower (p.tensor q)).symm
    change Biset.pairLinear Complex p.basis q.basis
        (p.basis.actLinear Complex (1, l⁻¹) (lower p b)) (lower q c) =
      Biset.pairLinear Complex p.basis q.basis (lower p b)
        (q.basis.actLinear Complex (l, 1) (lower q c))
    have E := Biset.pairLinear_balance Complex p.basis q.basis l
      (p.basis.actLinear Complex (1, l⁻¹) (lower p b)) (lower q c)
    have inv : p.basis.actLinear Complex (1,l)
        (p.basis.actLinear Complex (1,l⁻¹) (lower p b)) = lower p b := by
      have e : (p.basis.actLinear Complex (1,l)).comp (p.basis.actLinear Complex (1,l⁻¹)) =
          LinearMap.id := by
        apply Finsupp.lhom_ext
        intro s r
        simp only [LinearMap.comp_apply, LinearMap.id_apply, Biset.actLinear_single,
          ← Biset.mul_act, Prod.mk_mul_mk, one_mul, mul_inv_cancel, ← Prod.one_eq_mk, Biset.one_act]
      exact LinearMap.congr_fun e _
    rw [inv] at E
    exact E.symm
  | add a d ha hd => simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, ha, hd]
  | smul z a ha => simp only [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, ha]

private theorem wordPair_ext {M : Type (max u v)} [AddCommGroup M] [Module Complex M]
    {f g : wordBimod.{u,v} (p.tensor q) →ₗ[Complex] M}
    (h : ∀ b c, f (wordPair p q b c) = g (wordPair p q b c)) : f = g := by
  let t := ((LinearMap.llcomp Complex _ _ _) f).comp (wordPair p q)
  have ht (a : MonoidAlgebra Complex L) (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
      t (rightHom (wordBimod p) (MulOpposite.op a) b) c =
        t b (leftHom (wordBimod q) a c) := by
    change f (wordPair p q (rightHom (wordBimod p) (MulOpposite.op a) b) c) =
      f (wordPair p q b (leftHom (wordBimod q) a c))
    rw [wordPair_middle p q]
  obtain ⟨_, _, uniq⟩ := wordPairUP p q t ht
  exact (uniq f (fun _ _ => rfl)).trans (uniq g (fun b c => (h b c).symm)).symm

private noncomputable def forwardTriple (X : Mod.{u,v} H) :
    wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex]
      V X →ₗ[Complex] V ((T q ⋙ T p).obj X) :=
  { toFun := fun b => ((LinearMap.llcomp Complex _ _ _)
        (pure (wordBimod p) ((T q).obj X) b)).comp (pure (wordBimod q) X)
    map_add' := fun b d => by
      apply LinearMap.ext
      intro c
      apply LinearMap.ext
      intro x
      simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.llcomp_apply]
    map_smul' := fun z b => by
      apply LinearMap.ext
      intro c
      apply LinearMap.ext
      intro x
      simp only [RingHom.id_apply, map_smul, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.llcomp_apply] }

private theorem forwardTriple_balanced (X : Mod.{u,v} H) (a : MonoidAlgebra Complex L)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    forwardTriple p q X (rightHom (wordBimod p) (MulOpposite.op a) b) c =
      forwardTriple p q X b (leftHom (wordBimod q) a c) := by
  apply LinearMap.ext
  intro x
  change pure (wordBimod p) ((T q).obj X) (rightHom (wordBimod p) (MulOpposite.op a) b)
      (pure (wordBimod q) X c x) =
    pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X (leftHom (wordBimod q) a c) x)
  rw [(universal (wordBimod p) ((T q).obj X)).1.2 a b,
    (universal (wordBimod q) X).1.1 a c]

private noncomputable def forwardPairing (X : Mod.{u,v} H) :
    wordBimod.{u,v} (p.tensor q) →ₗ[Complex] V X →ₗ[Complex] V ((T q ⋙ T p).obj X) :=
  Classical.choose ((wordPairUP p q (forwardTriple p q X) (forwardTriple_balanced p q X)).exists)

private theorem forwardPairing_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    forwardPairing p q X (wordPair p q b c) x =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x) := by
  exact LinearMap.congr_fun
    (Classical.choose_spec ((wordPairUP p q (forwardTriple p q X)
      (forwardTriple_balanced p q X)).exists) b c) x

private theorem forwardPairing_balanced (X : Mod.{u,v} H) :
    Balanced (wordBimod (p.tensor q)) X ((T q ⋙ T p).obj X) (forwardPairing p q X) := by
  constructor
  · intro a d x
    let Y := (T q ⋙ T p).obj X
    let act : V Y →ₗ[Complex] V Y := RestrictScalars.lsmul Complex (MonoidAlgebra Complex K) Y a
    have e : ((forwardPairing p q X).flip x).comp (leftHom (wordBimod (p.tensor q)) a) =
        act.comp ((forwardPairing p q X).flip x) := by
      apply wordPair_ext p q
      intro b c
      change forwardPairing p q X (leftHom (wordBimod (p.tensor q)) a (wordPair p q b c)) x =
        a • (show Y from forwardPairing p q X (wordPair p q b c) x)
      rw [← wordPair_left p q, forwardPairing_pure, forwardPairing_pure]
      exact (universal (wordBimod p) ((T q).obj X)).1.1 a b _
    exact LinearMap.congr_fun e d
  · intro a d x
    have e : ((forwardPairing p q X).flip x).comp
        (rightHom (wordBimod (p.tensor q)) (MulOpposite.op a)) =
        (forwardPairing p q X).flip (a • (show X from x)) := by
      apply wordPair_ext p q
      intro b c
      change forwardPairing p q X (rightHom (wordBimod (p.tensor q)) (MulOpposite.op a)
        (wordPair p q b c)) x = forwardPairing p q X (wordPair p q b c) (a • (show X from x))
      rw [← wordPair_right p q, forwardPairing_pure, forwardPairing_pure,
        (universal (wordBimod q) X).1.2 a c x]
    exact LinearMap.congr_fun e d

private noncomputable def compHom (X : Mod.{u,v} H) :
    (T (p.tensor q)).obj X ⟶ (T q ⋙ T p).obj X :=
  Classical.choose (((universal (wordBimod (p.tensor q)) X).2 _
    (forwardPairing p q X) (forwardPairing_balanced p q X)).exists)

private theorem compHom_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    VMap (compHom p q X) (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x) =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x) :=
  (Classical.choose_spec (((universal (wordBimod (p.tensor q)) X).2 _
    (forwardPairing p q X) (forwardPairing_balanced p q X)).exists) (wordPair p q b c) x).trans
      (forwardPairing_pure p q X b c x)

-- Right multiplication on the source gives a left action on the space of linear maps.
private noncomputable def homAction (Y : Mod.{u,v} K) :
    MonoidAlgebra Complex L →+* Module.End Complex (wordBimod.{u,v} p →ₗ[Complex] V Y) where
  toFun a := LinearMap.lcomp Complex (V Y) (rightHom (wordBimod p) (MulOpposite.op a))
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_zero, map_zero, LinearMap.zero_apply]
  map_one' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_one, map_one, one_apply_eq_self]
  map_add' a d := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_add, map_add, LinearMap.add_apply]
  map_mul' a d := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_mul, map_mul, mul_apply_eq_comp]

private noncomputable def homMod (Y : Mod.{u,v} K) : Mod.{u,v} L := by
  letI : Module (MonoidAlgebra Complex L) (wordBimod.{u,v} p →ₗ[Complex] V Y) :=
    Module.compHom _ (homAction p Y)
  exact ModuleCat.of (GC L) (wordBimod.{u,v} p →ₗ[Complex] V Y)

private theorem homMod_smul (Y : Mod.{u,v} K) (a : MonoidAlgebra Complex L)
    (f : homMod p Y) (b : wordBimod.{u,v} p) :
    (show wordBimod.{u,v} p →ₗ[Complex] V Y from a • f) b =
      (show wordBimod.{u,v} p →ₗ[Complex] V Y from f)
        (rightHom (wordBimod p) (MulOpposite.op a) b) := rfl

private noncomputable def inverseTriple (X : Mod.{u,v} H) :
    wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex]
      V X →ₗ[Complex] V ((T (p.tensor q)).obj X) :=
  ((LinearMap.llcomp Complex _ _ _) (pure (wordBimod (p.tensor q)) X)).comp (wordPair p q)

private noncomputable def inverseCurry (X : Mod.{u,v} H) (c : wordBimod.{u,v} q) (x : X) :
    homMod p ((T (p.tensor q)).obj X) :=
  ((inverseTriple p q X).flip c).flip x

private theorem inverseCurry_apply (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from inverseCurry p q X c x) b =
      pure (wordBimod (p.tensor q)) X (wordPair p q b c) x := rfl

private theorem inverseInner_exists (X : Mod.{u,v} H) :
    ∃ g : (T q).obj X →ₗ[MonoidAlgebra Complex L] homMod p ((T (p.tensor q)).obj X),
      ∀ c x, g (rawPure (wordBimod q) X c x) = inverseCurry p q X c x := by
  apply ((rawUniversal (wordBimod q) X).2 _ (inverseCurry p q X) ?_).exists
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c d x
    change ((inverseTriple p q X).flip (c + d)).flip x =
      ((inverseTriple p q X).flip c).flip x + ((inverseTriple p q X).flip d).flip x
    apply LinearMap.ext
    intro b
    simp only [LinearMap.flip_apply, map_add, LinearMap.add_apply]
  · intro c x y
    change ((inverseTriple p q X).flip c).flip (x + y) =
      ((inverseTriple p q X).flip c).flip x + ((inverseTriple p q X).flip c).flip y
    apply LinearMap.ext
    intro b
    simp only [LinearMap.flip_apply, map_add, LinearMap.add_apply]
  · intro a c x
    change inverseCurry p q X (leftHom (wordBimod q) a c) x = a • inverseCurry p q X c x
    apply LinearMap.ext
    intro b
    rw [homMod_smul, inverseCurry_apply, inverseCurry_apply, wordPair_middle p q]
  · intro a c x
    change inverseCurry p q X (rightHom (wordBimod q) (MulOpposite.op a) c) x =
      inverseCurry p q X c (a • x)
    apply LinearMap.ext
    intro b
    rw [inverseCurry_apply, inverseCurry_apply, wordPair_right p q,
      (universal (wordBimod (p.tensor q)) X).1.2]

private noncomputable def inverseInner (X : Mod.{u,v} H) :
    V ((T q).obj X) →ₗ[Complex] wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) where
  toFun y :=
    let g := Classical.choose (inverseInner_exists p q X)
    g (show (T q).obj X from y)
  map_add' y z := by
    let g := Classical.choose (inverseInner_exists p q X)
    exact g.map_add (show (T q).obj X from y) (show (T q).obj X from z)
  map_smul' z y := by
    let g := Classical.choose (inverseInner_exists p q X)
    have e := g.map_smul (algebraMap Complex (GC L) z) (show (T q).obj X from y)
    apply LinearMap.ext
    intro b
    change (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from
        g ((algebraMap Complex (GC L) z) • (show (T q).obj X from y))) b =
      z • (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from g y) b
    rw [e, homMod_smul, rightHom_scalar, map_smul]

private theorem inverseInner_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    inverseInner p q X (pure (wordBimod q) X c x) b =
      pure (wordBimod (p.tensor q)) X (wordPair p q b c) x := by
  exact (congrArg (fun f : homMod p ((T (p.tensor q)).obj X) =>
    (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from f) b)
    (Classical.choose_spec (inverseInner_exists p q X) c x)).trans (inverseCurry_apply p q X b c x)

private theorem inverseInner_balanced (X : Mod.{u,v} H) :
    Balanced (wordBimod p) ((T q).obj X) ((T (p.tensor q)).obj X) (inverseInner p q X).flip := by
  constructor
  · intro a b y
    let Y := (T (p.tensor q)).obj X
    let act : V Y →ₗ[Complex] V Y := RestrictScalars.lsmul Complex (MonoidAlgebra Complex K) Y a
    have e : (inverseInner p q X).flip (leftHom (wordBimod p) a b) =
        act.comp ((inverseInner p q X).flip b) := by
      apply pure_linear_ext (wordBimod q) X
      intro c x
      change inverseInner p q X (pure (wordBimod q) X c x) (leftHom (wordBimod p) a b) =
        a • (show Y from inverseInner p q X (pure (wordBimod q) X c x) b)
      rw [inverseInner_pure, inverseInner_pure, wordPair_left p q,
        (universal (wordBimod (p.tensor q)) X).1.1]
    exact LinearMap.congr_fun e y
  · intro a b y
    let g := Classical.choose (inverseInner_exists p q X)
    have e := g.map_smul a (show (T q).obj X from y)
    exact (congrArg (fun f : homMod p ((T (p.tensor q)).obj X) =>
      (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from f) b) e).symm

private noncomputable def compInv (X : Mod.{u,v} H) :
    (T q ⋙ T p).obj X ⟶ (T (p.tensor q)).obj X :=
  Classical.choose (((universal (wordBimod p) ((T q).obj X)).2 _
    (inverseInner p q X).flip (inverseInner_balanced p q X)).exists)

private theorem compInv_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    VMap (compInv p q X) (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x)) =
      pure (wordBimod (p.tensor q)) X (wordPair p q b c) x :=
  (Classical.choose_spec (((universal (wordBimod p) ((T q).obj X)).2 _
    (inverseInner p q X).flip (inverseInner_balanced p q X)).exists) b
      (pure (wordBimod q) X c x)).trans (inverseInner_pure p q X b c x)

private theorem word_tensor_hom_ext (X : Mod.{u,v} H) {Y : Mod.{u,v} K}
    {f g : (T (p.tensor q)).obj X ⟶ Y}
    (eq : ∀ b c x,
      VMap f (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x) =
      VMap g (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x)) : f = g := by
  apply hom_ext_pure (wordBimod (p.tensor q)) X
  intro d x
  have e : (VMap f).comp ((pure (wordBimod (p.tensor q)) X).flip x) =
      (VMap g).comp ((pure (wordBimod (p.tensor q)) X).flip x) := by
    apply wordPair_ext p q
    intro b c
    exact eq b c x
  exact LinearMap.congr_fun e d

private theorem nested_tensor_hom_ext (X : Mod.{u,v} H) {Y : Mod.{u,v} K}
    {f g : (T q ⋙ T p).obj X ⟶ Y}
    (eq : ∀ b c x,
      VMap f (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x)) =
      VMap g (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x))) : f = g := by
  apply hom_ext_pure (wordBimod p) ((T q).obj X)
  intro b y
  have e : (VMap f).comp (pure (wordBimod p) ((T q).obj X) b) =
      (VMap g).comp (pure (wordBimod p) ((T q).obj X) b) := by
    apply pure_linear_ext (wordBimod q) X
    intro c x
    exact eq b c x
  exact LinearMap.congr_fun e y

private noncomputable def compApp (X : Mod.{u,v} H) :
    (T (p.tensor q)).obj X ≅ (T q ⋙ T p).obj X where
  hom := compHom p q X
  inv := compInv p q X
  hom_inv_id := by
    apply word_tensor_hom_ext p q X
    intro b c x
    change VMap (compInv p q X)
      (VMap (compHom p q X) (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x)) = _
    rw [compHom_pure, compInv_pure] <;> rfl
  inv_hom_id := by
    apply nested_tensor_hom_ext p q X
    intro b c x
    change VMap (compHom p q X)
      (VMap (compInv p q X) (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x))) = _
    rw [compInv_pure, compHom_pure] <;> rfl

private noncomputable def compIso :
    T (p.tensor q) ≅ T q ⋙ T p :=
  NatIso.ofComponents (compApp p q) (by
    intro X Y f
    apply word_tensor_hom_ext p q X
    intro b c x
    let P := wordBimod.{u,v} p
    let Q := wordBimod.{u,v} q
    let R := wordBimod.{u,v} (p.tensor q)
    change VMap (compHom p q Y)
        (((tensor R).map f).hom (rawPure R X (wordPair p q b c) x)) =
      ((tensor P).map ((tensor Q).map f)).hom
        (VMap (compHom p q X) (pure R X (wordPair p q b c) x))
    have eR := rawMapInput R f (wordPair p q b c) x
    have eQ := rawMapInput Q f c x
    have eP := rawMapInput P ((tensor Q).map f) b (rawPure Q X c x)
    calc
      _ = VMap (compHom p q Y) (pure R Y (wordPair p q b c) (f.hom x)) :=
        congrArg (VMap (compHom p q Y)) eR
      _ = rawPure P ((tensor Q).obj Y) b (rawPure Q Y c (f.hom x)) :=
        compHom_pure p q Y b c (f.hom x)
      _ = rawPure P ((tensor Q).obj Y) b (((tensor Q).map f).hom (rawPure Q X c x)) :=
        congrArg (rawPure P ((tensor Q).obj Y) b) eQ.symm
      _ = ((tensor P).map ((tensor Q).map f)).hom (rawPure P ((tensor Q).obj X) b (rawPure Q X c x)) :=
        eP.symm
      _ = _ := congrArg (((tensor P).map ((tensor Q).map f)).hom) (compHom_pure p q X b c x).symm)

private theorem compIso_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    VMap ((compIso p q).hom.app X)
      (pure (wordBimod (p.tensor q)) X
        ((lower (p.tensor q)).symm (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c))) x) =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x) :=
  compHom_pure p q X b c x


end WordComposition
end DiagramFunctorProof

namespace DiagramFunctorProof
open CategoryTheory CategoryTheory.Limits
universe u v
variable {U : Type u} [Group U]

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

-- The registered strand result gives this horizontal formula on typed drawings
-- at all boundaries. The calculation transports it through the carrier lifts.
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

-- Use the reviewed predicate on the typed LabelledDrawing carrier. The project
-- setoid in DiagramVectorSpace.quotient_eq_iff uses finite formal expressions.
-- DiagramAlgebra.evaluation_range_eq has an endomorphism boundary. Here the
-- kernel quotient is formed on admitted drawings at each source and target.
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


open CategoryTheory CategoryTheory.Limits

private theorem wordFiniteLimits {K H : Subgroup U} (p : Word K H) :
    PreservesFiniteLimits (T.{u,v} p) := by
  induction p with
  | empty H => exact preservesFiniteLimits_of_natIso (emptyIso.{u,v} H).symm
  | up a =>
    letI := induction_preservesFiniteLimits.{u,v} a
    obtain ⟨e⟩ := (strandIsos.{u,v} a).1
    exact preservesFiniteLimits_of_natIso e.symm
  | down a =>
    haveI : PreservesFiniteLimits (strandRes.{u,v} a) := by
      dsimp only [strandRes]
      infer_instance
    obtain ⟨e⟩ := (strandIsos.{u,v} a).2
    exact preservesFiniteLimits_of_natIso e.symm
  | tensor p q hp hq =>
    letI := hp
    letI := hq
    exact preservesFiniteLimits_of_natIso (compIso.{u,v} p q).symm

private theorem evaluatedId {K H : Subgroup U} (p : Word K H) :
    diagramMap.{u,v} (LabelledDrawing.ordinary (Diagram.id p)) = 𝟙 (T.{u,v} p) := by
  change (trans K H).map (wordMap.{u,v} (Biset.Hom.id p.basis)) = _
  rw [wordMap_id]
  exact CategoryTheory.Functor.map_id _ _

private theorem evaluatedVertical {K H : Subgroup U} {p q r : Word K H}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) :
    diagramMap.{u,v} (.vertical d e) = diagramMap.{u,v} d ≫ diagramMap.{u,v} e := by
  change (trans K H).map (wordMap.{u,v} ((drawingEval d).vertical (drawingEval e))) = _
  rw [wordMap_vertical, Functor.map_comp]

private theorem evaluatedLinear {K H : Subgroup U} {p q : Word K H}
    (d e : LabelledDrawing Complex p q) (z : Complex) :
    diagramMap.{u,v} (LabelledDrawing.ordinary (Diagram.zero p q)) = 0 ∧
    diagramMap.{u,v} (.add d e) = diagramMap.{u,v} d + diagramMap.{u,v} e ∧
    diagramMap.{u,v} (.scale z d) = z • diagramMap.{u,v} d := by
  letI := transAdditive.{u,v} (K := K) (H := H)
  letI := transportLinear.{u,v} (K := K) (H := H)
  refine ⟨?_, ?_, ?_⟩
  · change (trans K H).map (wordMap.{u,v} (Biset.Hom.zero : wordHom p q)) = _
    rw [wordMap_zero, Functor.map_zero]
  · change (trans K H).map (wordMap.{u,v} ((drawingEval d).add (drawingEval e))) = _
    rw [wordMap_add, Functor.map_add]
  · change (trans K H).map (wordMap.{u,v} ((drawingEval d).scale z)) = _
    rw [wordMap_scale, Functor.map_smul]

end DiagramFunctorProof

set_option backward.isDefEq.respectTransparency true
universe u v
open DiagramFunctorProof

theorem DiagrammaticFunctorCorrespondence : (
∀ {U : Type u} [Group U],
  let Alg := fun H : Subgroup U => MonoidAlgebra Complex H
  let Mod := fun H : Subgroup U => ModuleCat.{max u v} (Alg H)
  let Fun := fun K H : Subgroup U => CategoryTheory.Functor (Mod H) (Mod K)
  let Bimod := fun K H : Subgroup U => Rep.{max u v} Complex (Prod K H)
  let V := fun {H : Subgroup U} (X : Mod H) =>
    (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X
  let VMap := fun {H : Subgroup U} {X Y : Mod H} (f : ModuleCat.Hom X Y) =>
    (Rep.Hom.hom ((Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).map f)).toLinearMap
  let regular := fun H : Subgroup U => ModuleCat.of (Alg H) (ULift.{v} (Alg H))
  let left := fun {K H : Subgroup U} (B : Bimod K H) (k : K) => B.ρ (k, 1)
  let right := fun {K H : Subgroup U} (B : Bimod K H) (h : H) => B.ρ (1, h⁻¹)
  let leftAlg := fun {K H : Subgroup U} (B : Bimod K H) (a : Alg K) (b : B) =>
    MackeyDiagrams.freeLift Complex (fun k : K => left B k b) (MonoidAlgebra.coeff a)
  let rightAlg := fun {K H : Subgroup U} (B : Bimod K H) (b : B) (a : Alg H) =>
    MackeyDiagrams.freeLift Complex (fun h : H => right B h b) (MonoidAlgebra.coeff a)
  let Word := fun K H : Subgroup U => MackeyDiagrams.Word K H
  let wordVec := fun {K H : Subgroup U} (p : Word K H) =>
    Finsupp (MackeyDiagrams.Word.basis p).carrier Complex
  let lower := fun {K H : Subgroup U} (p : Word K H) =>
    (ULift.moduleEquiv : LinearEquiv (RingHom.id Complex) (ULift.{v} (wordVec p)) (wordVec p))
  let wordBimod := fun {K H : Subgroup U} (p : Word K H) =>
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
        Representation Complex (Prod K H) (ULift.{v} (wordVec p))) : Bimod K H)
  let wordHom := fun {K H : Subgroup U} (p q : Word K H) =>
    MackeyDiagrams.Biset.Hom Complex (MackeyDiagrams.Word.basis p) (MackeyDiagrams.Word.basis q)
  let allowedOrdinary := fun {K H : Subgroup U} {p q : Word K H}
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
  let drawing := fun {K H : Subgroup U} (p q : Word K H) =>
    MackeyDiagrams.LabelledDrawing Complex p q
  let allowed := fun {K H : Subgroup U} {p q : Word K H} (d : drawing p q) =>
    MackeyDiagrams.LabelledDrawing.rec (motive := fun _ _ _ => Prop)
      (fun d => allowedOrdinary d)
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
  let drawingEval := fun {K H : Subgroup U} {p q : Word K H} (d : drawing p q) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d)
  let good := fun (K H : Subgroup U) (F : Fun K H) =>
    CategoryTheory.Functor.Linear Complex F ∧
    CategoryTheory.Limits.PreservesFiniteColimits F ∧
    ∀ I : Type (max u v),
      CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F
  let goodFun := fun K H => CategoryTheory.ObjectProperty.FullSubcategory (good K H)
  let Ind := fun {H G : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H G) =>
    (CategoryTheory.Functor.comp
      (CategoryTheory.Functor.comp (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H))
        (Rep.indFunctor Complex a.toHom))
      (Rep.toModuleMonoidAlgebra (k := Complex) (G := G)) : Fun G H)
  let Res := fun {H G : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H G) =>
    (ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom).toRingHom :
      Fun H G)
  let conjugateMap := fun {K H : Subgroup U} {p q : Word K H} (f : wordHom p q) =>
    (lower q).symm.toLinearMap.comp (f.toLinearMap.comp (lower p).toLinearMap)
  let wordMap := fun {K H : Subgroup U} {p q : Word K H} (f : wordHom p q) =>
    (Rep.ofHom
      { toLinearMap := conjugateMap f
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          simpa [wordBimod, conjugateMap] using
            congrArg (fun y => (lower q).symm y)
              (MackeyDiagrams.Biset.Hom.commutes f g (lower p x)) } :
      Quiver.Hom (wordBimod p) (wordBimod q))
  let Balanced := fun {K H : Subgroup U} (B : Bimod K H) (X : Mod H) (Y : Mod K)
      (t : LinearMap (RingHom.id Complex) B
        (LinearMap (RingHom.id Complex) (V X) (V Y))) =>
    (∀ (a : Alg K) (b : B) (x : V X),
      let y : Y := t b x
      t (leftAlg B a b) x = a • y) ∧
    (∀ (a : Alg H) (b : B) (x : V X),
      let x' : X := x
      t (rightAlg B b a) x = t b (a • x'))
  let gen := fun {K H : Subgroup U} {p q : Word K H} =>
    {d : drawing p q // allowed d}
  let evalSetoid := fun {K H : Subgroup U} (p q : Word K H) =>
    Setoid.ker (fun d : @gen K H p q => drawingEval d.val)
  let genHom := fun {K H : Subgroup U} (p q : Word K H) => Quotient (evalSetoid p q)
  (∀ (H G : Subgroup U) (a : MackeyDiagrams.ConjEmbedding H G),
    letI : Module (MulOpposite (Alg H)) (Alg G) :=
      Module.compHom (Alg G) (RingHom.op
        (MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom).toRingHom)
    Module.Free (MulOpposite (Alg H)) (Alg G)) ∧
  ∃ E : ∀ K H : Subgroup U, CategoryTheory.Equivalence (Bimod K H) (goodFun K H),
  let transport := fun K H : Subgroup U =>
    CategoryTheory.Functor.comp (E K H).functor (CategoryTheory.ObjectProperty.ι (good K H))
  let tensor := fun {K H : Subgroup U} (B : Bimod K H) => (transport K H).obj B
  let T := fun {K H : Subgroup U} (p : Word K H) => tensor (wordBimod p)
  let liftMap := fun {K H : Subgroup U} {p q : Word K H} (f : wordHom p q) =>
    (transport K H).map (wordMap f)
  let diagramMap := fun {K H : Subgroup U} {p q : Word K H} (d : drawing p q) =>
    liftMap (drawingEval d)
  ∃ (pure : ∀ {K H : Subgroup U} (B : Bimod K H) (X : Mod H),
        LinearMap (RingHom.id Complex) B (LinearMap (RingHom.id Complex) (V X) (V ((tensor B).obj X))))
    (unit : ∀ {K H : Subgroup U} (B : Bimod K H),
        LinearEquiv (RingHom.id Complex) (V ((tensor B).obj (regular H))) B)
    (compIso : ∀ {K L H : Subgroup U} (p : Word K L) (q : Word L H),
        CategoryTheory.Iso (T (MackeyDiagrams.Word.tensor p q)) (CategoryTheory.Functor.comp (T q) (T p)))
    (emptyIso : ∀ H : Subgroup U,
        CategoryTheory.Iso (T (MackeyDiagrams.Word.empty H)) (CategoryTheory.Functor.id (Mod H))),
  let onRegular := fun {K H : Subgroup U} {p q : Word K H}
      (η : CategoryTheory.NatTrans (T p) (T q)) =>
    (unit (wordBimod q)).toLinearMap.comp
      ((VMap (η.app (regular H))).comp (unit (wordBimod p)).symm.toLinearMap)
  let inDiagram := fun {K H : Subgroup U} {p q : Word K H}
      (η : CategoryTheory.NatTrans (T p) (T q)) =>
    ∃ d : @gen K H p q, onRegular η = conjugateMap (drawingEval d.val)
  let pair := fun {K L H : Subgroup U} (p : Word K L) (q : Word L H)
      (b : wordBimod p) (c : wordBimod q) =>
    (lower (MackeyDiagrams.Word.tensor p q)).symm
      (MackeyDiagrams.Biset.pairLinear Complex
        (MackeyDiagrams.Word.basis p) (MackeyDiagrams.Word.basis q) (lower p b) (lower q c))
  (∀ (K H : Subgroup U) (B : Bimod K H) (z : Complex) (b : B),
    leftAlg B (algebraMap Complex (Alg K) z) b = z • b ∧
    rightAlg B b (algebraMap Complex (Alg H) z) = z • b) ∧
  (∀ K H : Subgroup U, CategoryTheory.Functor.Linear Complex (transport K H)) ∧
  (∀ (K H : Subgroup U) (I : Type (max u v)),
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) (transport K H)) ∧
  (∀ (K H : Subgroup U) (B : Bimod K H) (X : Mod H),
    Balanced B X ((tensor B).obj X) (pure B X) ∧
    ∀ (Y : Mod K) (t : LinearMap (RingHom.id Complex) B
        (LinearMap (RingHom.id Complex) (V X) (V Y))),
      Balanced B X Y t →
      ∃! f : ModuleCat.Hom ((tensor B).obj X) Y,
        ∀ (b : B) (x : V X), VMap f (pure B X b x) = t b x) ∧
  (∀ (K H : Subgroup U) (B : Bimod K H) (X Y : Mod H)
      (f : ModuleCat.Hom X Y) (b : B) (x : V X),
    VMap ((tensor B).map f) (pure B X b x) = pure B Y b (VMap f x)) ∧
  (∀ (K H : Subgroup U) (B C : Bimod K H) (f : Quiver.Hom B C)
      (X : Mod H) (b : B) (x : V X),
    VMap (((transport K H).map f).app X) (pure B X b x) =
      pure C X ((Rep.Hom.hom f).toLinearMap b) x) ∧
  (∀ (K H : Subgroup U) (B : Bimod K H) (b : B) (x : V (regular H)),
    unit B (pure B (regular H) b x) = rightAlg B b (ULift.down x)) ∧
  (∀ (H : Subgroup U) (X : Mod H) (b : wordBimod (MackeyDiagrams.Word.empty H)) (x : V X),
    let p := MackeyDiagrams.Word.empty H
    let x' : X := x
    VMap ((emptyIso H).hom.app X) (pure (wordBimod p) X b x) =
      (MonoidAlgebra.ofCoeff (lower p b) : Alg H) • x') ∧
  (∀ (H G : Subgroup U) (a : MackeyDiagrams.ConjEmbedding H G),
    Nonempty (CategoryTheory.Iso (T (MackeyDiagrams.Word.up a)) (Ind a)) ∧
    Nonempty (CategoryTheory.Iso (T (MackeyDiagrams.Word.down a)) (Res a))) ∧
  (∀ (K L H : Subgroup U) (p : Word K L) (q : Word L H) (X : Mod H)
      (b : wordBimod p) (c : wordBimod q) (x : V X),
    VMap ((compIso p q).hom.app X)
        (pure (wordBimod (MackeyDiagrams.Word.tensor p q)) X (pair p q b c) x) =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x)) ∧
  (∀ (K H : Subgroup U) (p : Word K H), CategoryTheory.Limits.PreservesFiniteLimits (T p)) ∧
  (∀ (K H : Subgroup U) (p q : Word K H),
    Function.Bijective (@liftMap K H p q) ∧
    (∀ f : wordHom p q, onRegular (liftMap f) = conjugateMap f) ∧
    ∃ e : Equiv (genHom p q) {η : CategoryTheory.NatTrans (T p) (T q) // inDiagram η},
      ∀ d : @gen K H p q,
        (e (Quotient.mk (evalSetoid p q) d)).val = diagramMap d.val) ∧
  (∀ (K H : Subgroup U) (p : Word K H),
    diagramMap (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id p)) = CategoryTheory.CategoryStruct.id (T p)) ∧
  (∀ (K H : Subgroup U) (p q r : Word K H)
      (d : drawing p q) (e : drawing q r),
    diagramMap (MackeyDiagrams.LabelledDrawing.vertical d e) =
      CategoryTheory.CategoryStruct.comp (diagramMap d) (diagramMap e)) ∧
  (∀ (K H : Subgroup U) (p q : Word K H) (d e : drawing p q) (z : Complex),
    diagramMap (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero p q)) = 0 ∧
    diagramMap (MackeyDiagrams.LabelledDrawing.add d e) = diagramMap d + diagramMap e ∧
    diagramMap (MackeyDiagrams.LabelledDrawing.scale z d) = z • diagramMap d) ∧
  (∀ (K L H : Subgroup U) (p p' : Word K L) (q q' : Word L H)
      (d : drawing p p') (e : drawing q q'),
    CategoryTheory.CategoryStruct.comp
        (diagramMap (MackeyDiagrams.LabelledDrawing.horizontal d e)) (compIso p' q').hom =
      CategoryTheory.CategoryStruct.comp (compIso p q).hom
        (CategoryTheory.NatTrans.hcomp (diagramMap e) (diagramMap d))) ∧
  (∀ K H : Subgroup U,
    letI : CategoryTheory.Limits.HasFiniteBiproducts (Bimod K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    letI : CategoryTheory.Limits.HasFiniteBiproducts (Fun K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    let bimodSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => wordBimod (p i))
    let funSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => T (p i))
    ∃ sumIso : ∀ {n : Nat} (p : Fin n → Word K H),
        CategoryTheory.Iso (tensor (bimodSum p)) (funSum p),
      ∀ {m n : Nat} (p : Fin m → Word K H) (q : Fin n → Word K H),
        (∀ f : ∀ i j, wordHom (p i) (q j),
          CategoryTheory.CategoryStruct.comp
            ((transport K H).map (CategoryTheory.Limits.biproduct.matrix
              (fun i j => wordMap (f i j)))) (sumIso q).hom =
          CategoryTheory.CategoryStruct.comp (sumIso p).hom
            (CategoryTheory.Limits.biproduct.matrix (fun i j => liftMap (f i j)))) ∧
        (∀ η : CategoryTheory.NatTrans (funSum p) (funSum q),
          (∀ i j, inDiagram (CategoryTheory.Limits.biproduct.components
            (f := fun i => T (p i)) (g := fun j => T (q j)) η i j)) ↔
          ∃ d : ∀ i j, @gen K H (p i) (q j),
            η = CategoryTheory.Limits.biproduct.matrix (fun i j => diagramMap (d i j).val)))
) :=
(by
  intro U inst
  refine ⟨fun H G a => freeRight a.toHom a.injective, ?_⟩
  refine ⟨fun K H => complexEquiv.{u,v} K H, ?_⟩
  refine ⟨(fun {_ _} B X => DiagramFunctorProof.pure.{u,v} B X),
    (fun {_ _} B => DiagramFunctorProof.unit.{u,v} B),
    (fun {_ _ _} p q => compIso.{u,v} p q), (fun H => emptyIso.{u,v} H), ?_⟩
  refine ⟨?_, fun _ _ => transportLinear, fun _ _ I => preservesCoproduct I, ?_,
    fun _ _ => rawMapInput, fun _ _ _ _ => rawMapBimod,
    ?_, emptyIso_pure, fun _ _ a => strandIsos a, fun _ _ _ => compIso_pure,
    fun _ _ => wordFiniteLimits, endpointQuotient,
    fun _ _ => evaluatedId, fun _ _ _ _ _ => evaluatedVertical,
    fun _ _ _ _ => evaluatedLinear, ?_, endpointMatrices⟩
  · intro K H B z b
    exact ⟨(leftHom_apply B _ b).symm.trans (leftHom_scalar B z b),
      (rightHom_apply B _ b).symm.trans (rightHom_scalar B z b)⟩
  · intro K H B X
    obtain ⟨hPure, hUniversal⟩ := universal B X
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro a b x
      have action := congrArg (fun b' : B => DiagramFunctorProof.pure B X b' x)
        (leftHom_apply B a b).symm
      exact action.trans (hPure.1 a b x)
    · intro a b x
      have action := congrArg (fun b' : B => DiagramFunctorProof.pure B X b' x)
        (rightHom_apply B a b).symm
      exact action.trans (hPure.2 a b x)
    · intro Y t ht
      apply hUniversal Y t
      refine ⟨?_, ?_⟩
      · intro a b x
        have action := congrArg (fun b' : B => t b' x) (leftHom_apply B a b)
        exact action.trans (ht.1 a b x)
      · intro a b x
        have action := congrArg (fun b' : B => t b' x) (rightHom_apply B a b)
        exact action.trans (ht.2 a b x)
  · intro K H B b x
    exact (unitFun_pure B b x).trans (rightHom_apply B _ b)
  · intro K L H p p' q q' d e
    exact horizontal_comp_of_pure (fun p q => compIso p q)
      (fun p q => compIso_pure p q) p p' q q' d e)

#print axioms DiagrammaticFunctorCorrespondence
