import WattsFoundation.WattsNaturalIso
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Connect Mathlib's preservation typeclasses to the explicit universal
properties used by the Eilenberg–Watts proof. -/

set_option backward.isDefEq.respectTransparency false

namespace WattsFoundation

universe u
open CategoryTheory CategoryTheory.Limits

variable {A B : Type u} [Ring A] [Ring B]
variable (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive]

/-- Mathlib preservation of discrete colimits gives the explicit coproduct
preservation used in the Eilenberg–Watts argument. -/
theorem wattsCoproducts_of_mathlib
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) F] : WattsPreservesCoproducts F := by
  classical
  intro I D P ι hP Q legs
  let c : Cofan D := Cofan.mk P ι
  have hc : IsColimit c := Cofan.IsColimit.mk c
    (fun s => Classical.choose (hP s.pt s.inj))
    (fun s j => (Classical.choose_spec (hP s.pt s.inj)).1 j)
    (fun s m hm => (Classical.choose_spec (hP s.pt s.inj)).2 m hm)
  have hFc : IsColimit (Cofan.mk (F.obj P) (fun i => F.map (ι i))) :=
    isColimitCofanMkObjOfIsColimit F D ι hc
  refine ⟨Cofan.IsColimit.desc hFc legs, ?_, ?_⟩
  · intro i
    exact Cofan.IsColimit.fac hFc legs i
  · intro d hd
    apply Cofan.IsColimit.hom_ext hFc
    intro i
    change F.map (ι i) ≫ d = F.map (ι i) ≫ Cofan.IsColimit.desc hFc legs
    exact (hd i).trans (Cofan.IsColimit.fac hFc legs i).symm

/-- Mathlib preservation of finite colimits gives the explicit cokernel
preservation used in the Eilenberg–Watts argument. -/
theorem wattsCokernels_of_mathlib [PreservesFiniteColimits F] : WattsPreservesCokernels F := by
  classical
  intro L P X f q hzero hcok
  let c : CokernelCofork f := CokernelCofork.ofπ q hzero
  have hc : IsColimit c := Cofork.IsColimit.mk c
    (fun s => Classical.choose (hcok s.pt s.π (CokernelCofork.condition s)))
    (fun s => (Classical.choose_spec (hcok s.pt s.π (CokernelCofork.condition s))).1)
    (fun s m hm => (Classical.choose_spec (hcok s.pt s.π (CokernelCofork.condition s))).2 m hm)
  have hFc : IsColimit (c.map F) := CokernelCofork.mapIsColimit c hc F
  have hz : F.map f ≫ F.map q = ModuleCat.ofHom 0 := by
    have hzero' : f ≫ q = 0 := hzero
    change F.map f ≫ F.map q = 0
    rw [← F.map_comp, hzero', F.map_zero]
  refine ⟨hz, ?_⟩
  intro Z g hg
  let d := Cofork.IsColimit.desc hFc g (by simpa using hg)
  refine ⟨d, ?_, ?_⟩
  · simpa [d, c] using Cofork.IsColimit.π_desc' hFc g (by simpa using hg)
  · intro e he
    apply Cofork.IsColimit.hom_ext hFc
    change F.map q ≫ e = F.map q ≫ d
    rw [he]
    symm
    simpa [d, c] using Cofork.IsColimit.π_desc' hFc g (by simpa using hg)

/-- Eilenberg–Watts using Mathlib's usual finite-colimit and coproduct
preservation typeclasses. -/
noncomputable def wattsNaturalIsoOfMathlib [PreservesFiniteColimits F]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) F] :
    ChoiceFreeWatts.tensorFunctor F ≅ F :=
  wattsNaturalIso F (wattsCokernels_of_mathlib F) (wattsCoproducts_of_mathlib F)

#print axioms wattsCoproducts_of_mathlib
#print axioms wattsCokernels_of_mathlib
#print axioms wattsNaturalIsoOfMathlib

end WattsFoundation
