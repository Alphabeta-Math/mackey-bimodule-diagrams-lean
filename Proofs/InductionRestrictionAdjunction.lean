import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands

set_option maxHeartbeats 2000000

namespace InductionRestrictionAdjunctionSupport

open MackeyDiagrams
universe u

section
variable {U : Type u} [Group U] {H G : Subgroup U} (a : ConjEmbedding H G)

local notation "B" => MonoidAlgebra Complex G
local notation "φ" => MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
local notation "D" => Biset.restriction a
local notation "I" => Biset.induction a

-- The middle actions on D and I are regular. In their balanced quotient
-- [x,y] = [x*y,1]. This is the group-basis form of Alphabeta Math's tensor
-- universal property, Steps 3.1, 4.1 and 5.1. The diagonal action encodes
-- the balance relation, and linearization supplies additivity. This special
-- case has an explicit inverse because the two middle actions are regular.
private def downUpProduct : (Biset.tensor D I).carrier ≃ G where
  toFun := Quotient.lift (fun p : G × G => p.1 * p.2) (by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨g, hx, hy⟩
    change (a.toHom 1 * x * g⁻¹ = x') at hx
    change (g * y * (a.toHom 1)⁻¹ = y') at hy
    change x * y = x' * y'
    rw [← hx, ← hy]
    simp [mul_assoc])
  invFun x := Biset.pair D I x 1
  left_inv z := by
    refine Quotient.inductionOn z ?_
    rintro ⟨x, y⟩
    apply Quotient.sound (s := Biset.balance D I)
    refine ⟨y, ?_, ?_⟩
    · change a.toHom 1 * (x * y) * y⁻¹ = x
      simp [mul_assoc]
    · change y * 1 * (a.toHom 1)⁻¹ = y
      simp
  right_inv x := mul_one x

private noncomputable def downUpLinear : ((Biset.tensor D I).carrier →₀ Complex) ≃ₗ[Complex] B :=
  (Finsupp.domLCongr (downUpProduct a)).trans (MonoidAlgebra.coeffLinearEquiv Complex).symm

private theorem downUpLinear_single (x y : G) (c : Complex) :
    downUpLinear a (Finsupp.single (Biset.pair D I x y) c) = MonoidAlgebra.single (x * y) c := by
  simp only [downUpLinear, LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  rfl

-- Compare both bilinear maps on group elements with arbitrary coefficients.
private theorem bilinear_eq_of_single {G₁ G₂ : Type u} {V : Type u}
    [AddCommMonoid V] [Module Complex V]
    {p q : (G₁ →₀ Complex) →ₗ[Complex] (G₂ →₀ Complex) →ₗ[Complex] V}
    (hs : ∀ (g : G₁) (h : G₂) (r s : Complex),
      p (Finsupp.single g r) (Finsupp.single h s) =
        q (Finsupp.single g r) (Finsupp.single h s)) : p = q := by
  apply Finsupp.lhom_ext
  intro g r
  apply Finsupp.lhom_ext
  intro h s
  exact hs g h r s

private noncomputable def coeffProduct {G : Type u} [Group G] :
    (G →₀ Complex) →ₗ[Complex] (G →₀ Complex) →ₗ[Complex] MonoidAlgebra Complex G :=
  ((LinearMap.mul Complex (MonoidAlgebra Complex G)).compl₂
    (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap

private theorem downUpLinear_pair (x y : B) :
    downUpLinear a (Biset.pairLinear Complex D I x.coeff y.coeff) = x * y := by
  have he : (Biset.pairLinear Complex D I).compr₂ (downUpLinear a).toLinearMap =
      coeffProduct := by
    apply bilinear_eq_of_single
    intro g h r s
    change downUpLinear a (Biset.pairLinear Complex D I (Finsupp.single g r)
      (Finsupp.single h s)) = MonoidAlgebra.single g r * MonoidAlgebra.single h s
    rw [Biset.pairLinear_single, downUpLinear_single, MonoidAlgebra.single_mul_single]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x.coeff) y.coeff

private theorem downUpLinear_action (k l : H) (z : (Biset.tensor D I).carrier →₀ Complex) :
    downUpLinear a (Biset.actLinear Complex (Biset.tensor D I) (k, l⁻¹) z) =
      φ (MonoidAlgebra.single k 1) * downUpLinear a z * φ (MonoidAlgebra.single l 1) := by
  let left : B →ₗ[Complex] B :=
    LinearMap.mul Complex B (φ (MonoidAlgebra.single k 1))
  let right : B →ₗ[Complex] B :=
    (LinearMap.mul Complex B).flip (φ (MonoidAlgebra.single l 1))
  have he :
      (downUpLinear a).toLinearMap.comp (Biset.actLinear Complex (Biset.tensor D I) (k, l⁻¹)) =
        right.comp (left.comp (downUpLinear a).toLinearMap) := by
    apply Finsupp.lhom_ext
    intro q c
    refine Quotient.inductionOn q ?_
    rintro ⟨x, y⟩
    change downUpLinear a (Biset.actLinear Complex (Biset.tensor D I) (k, l⁻¹)
        (Finsupp.single (Biset.pair D I x y) c)) =
      φ (MonoidAlgebra.single k 1) * downUpLinear a (Finsupp.single (Biset.pair D I x y) c) *
        φ (MonoidAlgebra.single l 1)
    rw [Biset.actLinear_single]
    change downUpLinear a (Finsupp.single (Biset.pair D I (a.toHom k * x * (1 : G)⁻¹)
        ((1 : G) * y * (a.toHom l⁻¹)⁻¹)) c) = _
    simp only [downUpLinear_single, inv_one, mul_one, one_mul, map_inv, inv_inv]
    change _ = MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single k 1) * _ *
      MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single l 1)
    simp [MonoidAlgebra.mapDomain_single, MonoidAlgebra.single_mul_single, mul_assoc]
  exact LinearMap.congr_fun he z

private theorem ordinaryCup_pair
    (hφ : ∀ (h : H) (c : Complex), φ (MonoidAlgebra.single h c) = MonoidAlgebra.single (a.toHom h) c)
    (h : MonoidAlgebra Complex H) :
    (Diagram.ordinaryCup (R := Complex) a).eval.toLinearMap h.coeff =
      Biset.pairLinear Complex D I (φ h).coeff (MonoidAlgebra.coeff (1 : B)) := by
  let coeff := MonoidAlgebra.coeffLinearEquiv (M := G) (S := Complex) Complex
  let q := (Biset.pairLinear Complex D I).flip (MonoidAlgebra.coeff (1 : B))
  have he :
      (Diagram.ordinaryCup (R := Complex) a).eval.toLinearMap =
        q.comp (coeff.toLinearMap.comp ((φ).toLinearMap.comp
          (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap)) := by
    apply Finsupp.lhom_ext
    intro k c
    change (Diagram.ordinaryCup (R := Complex) a).eval.toLinearMap (Finsupp.single k c) =
      Biset.pairLinear Complex D I (φ (MonoidAlgebra.single k c)).coeff (Finsupp.single 1 1)
    rw [hφ, MonoidAlgebra.coeff_single, Biset.pairLinear_single, mul_one,
      Diagram.eval_ordinaryCup_single]
  exact LinearMap.congr_fun he h.coeff

private theorem multiplicationCap_pair (x y : B) :
    (Diagram.multiplicationCap (R := Complex) a).eval.toLinearMap
      (Biset.pairLinear Complex I D x.coeff y.coeff) = (x * y).coeff := by
  let coeff := MonoidAlgebra.coeffLinearEquiv (M := G) (S := Complex) Complex
  let cap := (Diagram.multiplicationCap (R := Complex) a).eval.toLinearMap
  apply coeff.symm.injective
  have he : (Biset.pairLinear Complex I D).compr₂ (coeff.symm.toLinearMap.comp cap) =
      coeffProduct := by
    apply bilinear_eq_of_single
    intro g h r s
    change MonoidAlgebra.ofCoeff (cap (Biset.pairLinear Complex I D
      (Finsupp.single g r) (Finsupp.single h s))) =
      MonoidAlgebra.single g r * MonoidAlgebra.single h s
    rw [Biset.pairLinear_single, Diagram.eval_multiplicationCap_single,
      MonoidAlgebra.single_mul_single]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun he x.coeff) y.coeff

end
end InductionRestrictionAdjunctionSupport
namespace InductionRestrictionAdjunctionSupport

open CategoryTheory MackeyDiagrams
universe u v

section
variable {H G : Type u} [Group H] [Group G] (f : H →* G)

local notation "A" => MonoidAlgebra Complex H
local notation "B" => MonoidAlgebra Complex G
local notation "φ" => MonoidAlgebra.mapDomainAlgHom Complex Complex f

private noncomputable abbrev ind :
    ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B :=
  (Rep.ofModuleMonoidAlgebra ⋙ Rep.indFunctor Complex f) ⋙ Rep.toModuleMonoidAlgebra

private noncomputable abbrev res :
    ModuleCat.{max u v} B ⥤ ModuleCat.{max u v} A :=
  ModuleCat.restrictScalars (φ).toRingHom

private noncomputable abbrev restrictedRep :
    ModuleCat.{max u v} B ⥤ ModuleCat.{max u v} A :=
  Rep.ofModuleMonoidAlgebra ⋙ (Rep.resFunctor f ⋙ Rep.toModuleMonoidAlgebra)

-- The carrier is unchanged by both restrictions. The actions agree on the
-- group basis, so the identity is linear for every element of the group algebra.
private theorem restrictionAction (Y : ModuleCat.{max u v} B)
    (r : A) (y : (restrictedRep f).obj Y) :
    r • y = φ r • (show Y from y) := by
  let ρ := Representation.ofModule (k := Complex) (G := G) Y
  let σ : Representation Complex H (RestrictScalars Complex B Y) := ρ.comp f
  have hf : σ.asAlgebraHom = ρ.asAlgebraHom.comp φ := by
    apply (MonoidAlgebra.lift Complex _ H).symm.injective
    apply MonoidHom.ext
    intro h
    change σ.asAlgebraHom (MonoidAlgebra.single h 1) =
      ρ.asAlgebraHom (MonoidAlgebra.mapDomain f (MonoidAlgebra.single h 1))
    rw [MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single_one,
      Representation.asAlgebraHom_single_one]
    rfl
  change σ.asAlgebraHom r y = _
  rw [hf]
  exact Representation.ofModule_asAlgebraHom_apply_apply Y (φ r) y

private noncomputable def restrictionIso : restrictedRep.{u,v} f ≅ res.{u,v} f :=
  NatIso.ofComponents (fun Y =>
    (show (restrictedRep f).obj Y ≃ₗ[A] (res f).obj Y from
      { toEquiv := Equiv.refl Y
        map_add' := fun _ _ => rfl
        map_smul' := restrictionAction f Y }).toModuleIso) (by
          intro X Y g
          apply ModuleCat.hom_ext
          ext x
          rfl)

-- The coordinator's representation adjunction works for this homomorphism
-- at arbitrary index. Transport both sides with the module equivalences.
private noncomputable def adjunction : ind.{u,v} f ⊣ res.{u,v} f :=
  (((Rep.equivalenceModuleMonoidAlgebra (k := Complex) (G := H)).symm.toAdjunction.comp
    (Rep.indResAdjunction Complex f)).comp
      (Rep.equivalenceModuleMonoidAlgebra (k := Complex) (G := G)).toAdjunction).ofNatIsoRight
        (restrictionIso f)

private noncomputable abbrev pureTensor (X : ModuleCat.{max u v} A) (b : B) (x : X) :
    (ind f).obj X :=
  let ρ := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X |>.ρ
  (Representation.asModuleEquiv (Representation.ind f ρ)).symm
    (freeLift Complex (fun g : G => Representation.IndV.mk f ρ g⁻¹ x) b.coeff)

private theorem unitAtOne (X : ModuleCat.{max u v} A) (x : X) :
    ((adjunction f).unit.app X).hom x = pureTensor f X 1 x := by
  let ρ := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X |>.ρ
  let x' : (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X := x
  let σ := Representation.ind f ρ
  have hp : pureTensor f X 1 x = σ.asModuleEquiv.symm (Representation.IndV.mk f ρ 1 x') := by
    change σ.asModuleEquiv.symm
      (freeLift Complex (fun g : G => Representation.IndV.mk f ρ g⁻¹ x')
        (Finsupp.single 1 1)) = _
    rw [freeLift_single, inv_one, one_smul]
  exact (show ((adjunction f).unit.app X).hom x =
    σ.asModuleEquiv.symm (Representation.IndV.mk f ρ 1 x') from rfl).trans hp.symm

private theorem pureTensor_smul_unit (X : ModuleCat.{max u v} A) (b : B) (x : X) :
    pureTensor f X b x = (b • (pureTensor f X 1 x) : (ind f).obj X) := by
  let ρ := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X |>.ρ
  let σ := Representation.ind f ρ
  apply σ.asModuleEquiv.injective
  change freeLift Complex (fun g : G => Representation.IndV.mk f ρ g⁻¹ x) b.coeff =
    σ.asAlgebraHom b (freeLift Complex (fun g : G => Representation.IndV.mk f ρ g⁻¹ x)
      (Finsupp.single (1 : G) 1))
  rw [freeLift_single, inv_one, one_smul]
  induction b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, freeLift_single, one_smul,
      Representation.asAlgebraHom_single_one]
    let x' : (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X := x
    change Representation.IndV.mk f ρ g⁻¹ x' = (Representation.ind f ρ) g
      (Representation.IndV.mk f ρ 1 x')
    rw [Representation.ind_mk, one_mul]
  | add a b ha hb =>
    simp only [MonoidAlgebra.coeff_add, map_add, LinearMap.add_apply, ha, hb]
  | smul c b hb =>
    simp only [MonoidAlgebra.coeff_smul, map_smul, LinearMap.smul_apply, hb]

-- The inverse index converts Mathlib's right multiplication on the group
-- index into left multiplication on the group-algebra input.
private theorem unitAtScalar (X : ModuleCat.{max u v} A) (h : A) (x : X) :
    ((adjunction f).unit.app X).hom (h • x) = pureTensor f X (φ h) x := by
  have he : ((adjunction f).unit.app X).hom (h • x) =
      ((φ h) • (show (ind f).obj X from ((adjunction f).unit.app X).hom x) :
        (ind f).obj X) := ((adjunction f).unit.app X).hom.map_smul h x
  exact he.trans ((congrArg (fun z : (ind f).obj X => φ h • z) (unitAtOne f X x)).trans
    (pureTensor_smul_unit f X (φ h) x).symm)

-- The right triangle evaluates the counit on the generator at 1.
-- Its B-linearity then evaluates every pure tensor.
private theorem counitAtPure (Y : ModuleCat.{max u v} B) (b : B) (y : Y) :
    ((adjunction f).counit.app Y).hom (pureTensor f ((res f).obj Y) b y) = b • y := by
  let X := (res f).obj Y
  let y' : X := y
  let e : (ind f).obj X →ₗ[B] Y := ((adjunction f).counit.app Y).hom
  have h := (adjunction f).right_triangle_components Y
  have h₁ : e (((adjunction f).unit.app X).hom y') = y :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) y
  have hu : (show (ind f).obj X from ((adjunction f).unit.app X).hom y') =
      pureTensor f X 1 y' := unitAtOne f X y'
  have h₂ : e (pureTensor f X 1 y') = y := by
    rw [← hu]
    exact h₁
  change e (pureTensor f X b y') = b • y
  rw [pureTensor_smul_unit f X b y', map_smul, h₂]

end
end InductionRestrictionAdjunctionSupport

theorem InductionRestrictionAdjunction : (∀ {U : Type u} [Group U] (H G : Subgroup U) (α : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
  let up := MackeyDiagrams.Word.up a
  let down := MackeyDiagrams.Word.down a
  let downUp := MackeyDiagrams.Word.tensor down up
  let cup := MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.ordinaryCup (R := Complex) a)
  let cap := MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.multiplicationCap (R := Complex) a)
  let pairDI := fun (x y : B) =>
    MackeyDiagrams.Biset.pairLinear Complex down.basis up.basis
      (MonoidAlgebra.coeff x) (MonoidAlgebra.coeff y)
  let pairID := fun (x y : B) =>
    MackeyDiagrams.Biset.pairLinear Complex up.basis down.basis
      (MonoidAlgebra.coeff x) (MonoidAlgebra.coeff y)
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
  (∀ h : A, cup.toLinearMap (MonoidAlgebra.coeff h) = pairDI (φ h) 1) ∧
  (∀ x y : B, cap.toLinearMap (pairID x y) = MonoidAlgebra.coeff (x * y)) ∧
  ∃ m : LinearEquiv (RingHom.id Complex) (Finsupp downUp.basis.carrier Complex) B,
    (∀ x y : B, m (pairDI x y) = x * y) ∧
    (∀ (k l : H) (z : Finsupp downUp.basis.carrier Complex),
      m (MackeyDiagrams.Biset.actLinear Complex downUp.basis (k, l⁻¹) z) =
        φ (MonoidAlgebra.single k 1) * m z * φ (MonoidAlgebra.single l 1)) ∧
    ∃ adj : CategoryTheory.Adjunction Ind Res,
      (∀ (X : ModuleCat.{max u v} A) (h : A) (x : X),
        ModuleCat.Hom.hom (adj.unit.app X) (h • x) =
          pure X (m (cup.toLinearMap (MonoidAlgebra.coeff h))) x) ∧
      (∀ (Y : ModuleCat.{max u v} B) (x y : B) (z : Y),
        ModuleCat.Hom.hom (adj.counit.app Y) (pure (Res.obj Y) x (y • z)) =
          (MonoidAlgebra.ofCoeff (cap.toLinearMap (pairID x y)) : B) • z)) :=
(by
  intro U _ H G α hα A B a φ up down downUp cup cap pairDI pairID toRep Ind Res pure
  -- Xiao, § 1.2, pp. 3–4. The ordinary cup starts at the empty H
  -- boundary, and the multiplication cap ends at the empty G boundary.
  -- The project TeX and PDF and the current published PDF give the same
  -- formulas and oriented boundaries here.
  -- The strand theorem supplies the image of every group-algebra singleton.
  have hφ := ((InductionRestrictionBimoduleStrands.{u, 0, 0}).1 H G α hα).1
  have hCup : ∀ h : A, cup.toLinearMap (MonoidAlgebra.coeff h) = pairDI (φ h) 1 :=
    InductionRestrictionAdjunctionSupport.ordinaryCup_pair a hφ
  have hCap : ∀ x y : B, cap.toLinearMap (pairID x y) = MonoidAlgebra.coeff (x * y) :=
    InductionRestrictionAdjunctionSupport.multiplicationCap_pair a
  let m := InductionRestrictionAdjunctionSupport.downUpLinear a
  have hm : ∀ x y : B, m (pairDI x y) = x * y :=
    InductionRestrictionAdjunctionSupport.downUpLinear_pair a
  refine ⟨hCup, hCap, m, hm, InductionRestrictionAdjunctionSupport.downUpLinear_action a, ?_⟩
  let adj : CategoryTheory.Adjunction Ind Res :=
    InductionRestrictionAdjunctionSupport.adjunction a.toHom
  refine ⟨adj, ?_, ?_⟩
  · intro X h x
    rw [hCup, hm, mul_one]
    exact InductionRestrictionAdjunctionSupport.unitAtScalar a.toHom X h x
  · intro Y x y z
    rw [hCap]
    exact (InductionRestrictionAdjunctionSupport.counitAtPure a.toHom Y x (y • z)).trans
      (mul_smul x y z).symm)
