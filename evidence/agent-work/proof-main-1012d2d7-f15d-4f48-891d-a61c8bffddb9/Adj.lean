import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Iso
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
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

-- In the coinvariant model the inverse index converts Mathlib's action on
-- the second coordinate into the left action of the group algebra.
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
  have h := (adjunction f).right_triangle_components Y
  have h₁ : ((adjunction f).counit.app Y).hom
      (((adjunction f).unit.app ((res f).obj Y)).hom y) = y :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) y
  have h₂ : ((adjunction f).counit.app Y).hom
      (pureTensor f ((res f).obj Y) 1 y) = y :=
    (congrArg (fun z : (ind f).obj ((res f).obj Y) =>
      ((adjunction f).counit.app Y).hom z) (unitAtOne f ((res f).obj Y) y)).symm.trans h₁
  rw [pureTensor_smul_unit, map_smul, h₂]

end
end InductionRestrictionAdjunctionSupport
