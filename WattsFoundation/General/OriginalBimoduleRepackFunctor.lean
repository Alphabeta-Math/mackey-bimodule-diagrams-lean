import WattsFoundation.General.OriginalBimoduleRepackIso
import Mathlib.CategoryTheory.NatIso

set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace WattsFoundation.General
universe u v w z
variable (R S : Type u) [Ring R] [Ring S]
variable {C : Type w} [Category.{z} C]
variable (F : C ⥤ OriginalBimodule.{u,v} R S) (N : C ⥤ ModuleCat.{max u v} S)
variable (α : F ⋙ originalForget R S ≅ N)

noncomputable def repackedFunctor : C ⥤ OriginalBimodule.{u,v} R S where
  obj X := repackBimodule R S (F.obj X) (N.obj X) (α.app X)
  map {X Y} f := (repackIso R S (F.obj X) (N.obj X) (α.app X)).inv ≫
    F.map f ≫ (repackIso R S (F.obj Y) (N.obj Y) (α.app Y)).hom
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

noncomputable def repackedFunctorIso : F ≅ repackedFunctor R S F N α :=
  NatIso.ofComponents (fun X => repackIso R S (F.obj X) (N.obj X) (α.app X)) (by
    intro X Y f
    simp [repackedFunctor, Category.assoc])


theorem repackedFunctor_forget : repackedFunctor R S F N α ⋙ originalForget R S = N := by
  refine CategoryTheory.Functor.ext (F := repackedFunctor R S F N α ⋙ originalForget R S) (G := N) (fun X => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (α.app X).inv ≫ (F ⋙ originalForget R S).map f ≫ (α.app Y).hom = N.map f
  have hnat := α.hom.naturality f
  change (F ⋙ originalForget R S).map f ≫ (α.app Y).hom =
    (α.app X).hom ≫ N.map f at hnat
  calc
    _ = (α.app X).inv ≫ ((F ⋙ originalForget R S).map f ≫ (α.app Y).hom) := by simp only [Category.assoc]
    _ = (α.app X).inv ≫ ((α.app X).hom ≫ N.map f) := by rw [hnat]
    _ = _ := by simp


noncomputable def repackedEquivalence (E : C ≌ OriginalBimodule.{u,v} R S)
    (α : E.functor ⋙ originalForget R S ≅ N) : C ≌ OriginalBimodule.{u,v} R S :=
  E.changeFunctor (repackedFunctorIso R S E.functor N α)

theorem repackedEquivalence_forget (E : C ≌ OriginalBimodule.{u,v} R S)
    (α : E.functor ⋙ originalForget R S ≅ N) :
    (repackedEquivalence R S N E α).functor ⋙ originalForget R S = N :=
  repackedFunctor_forget R S E.functor N α

theorem repackedEquivalence_right (E : C ≌ OriginalBimodule.{u,v} R S)
    (α : E.functor ⋙ originalForget R S ≅ N) (X : C) (m : (E.functor.obj X).1) (r : R) :
    originalRight R S ((repackedEquivalence R S N E α).functor.obj X) ((α.app X).hom m) r =
      (α.app X).hom (originalRight R S (E.functor.obj X) m r) :=
  repackRight_hom R S (E.functor.obj X) (N.obj X) (α.app X) m r

end WattsFoundation.General
