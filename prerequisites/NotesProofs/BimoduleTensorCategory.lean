import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsTheorem
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Equivalence

/-! The category of bimodules and its tensor-functor representation. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs

universe u
open CategoryTheory CategoryTheory.Limits

variable (R S : Type u) [Ring R] [Ring S]

/-- A unital S-R bimodule with its commuting actions. -/
structure ConcreteBimodule where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [rightModule : Module (MulOpposite R) carrier]
  [leftModule : Module S carrier]
  [commuting : SMulCommClass (MulOpposite R) S carrier]

attribute [instance] ConcreteBimodule.addCommGroup ConcreteBimodule.rightModule
  ConcreteBimodule.leftModule ConcreteBimodule.commuting

namespace ConcreteBimodule

instance : Category (ConcreteBimodule R S) where
  Hom M N := BimoduleMap (R := R) (S := S) (M := M.carrier) (N := N.carrier)
  id M := ⟨LinearMap.id, fun _ _ => rfl⟩
  comp f g := ⟨g.1.comp f.1, fun r m => by rw [LinearMap.comp_apply, f.2, g.2]; rfl⟩
  id_comp f := by apply Subtype.ext; ext; rfl
  comp_id f := by apply Subtype.ext; ext; rfl
  assoc f g h := by apply Subtype.ext; ext; rfl

/-- The good additive module functors in the Eilenberg–Watts theorem. -/
def Good : ObjectProperty (ModuleCat.{u} R ⥤ ModuleCat.{u} S) := fun F =>
  F.Additive ∧ PreservesFiniteColimits F ∧
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F

abbrev GoodFunctors := ObjectProperty.FullSubcategory (Good R S)

/-- Tensoring sends bimodules and their maps to good module functors and
natural transformations. -/
def tensorRepresentation : ConcreteBimodule R S ⥤ GoodFunctors R S where
  obj M := ⟨concreteTensorFunctor (R := R) (S := S) M.carrier, tensorFunctor_good M.carrier⟩
  map f := ObjectProperty.homMk (tensorBimoduleMapNatTrans f)
  map_id M := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := M.carrier))
    intro m x
    change tensorBimoduleMapComponent (𝟙 M) X (concretePure (R := R) (M := M.carrier) m x) = _
    rw [tensorBimoduleMapComponent_pure]
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := _))
    intro m x
    change tensorBimoduleMapComponent (f ≫ g) X (concretePure (R := R) m x) =
      tensorBimoduleMapComponent g X (tensorBimoduleMapComponent f X (concretePure (R := R) m x))
    rw [tensorBimoduleMapComponent_pure, tensorBimoduleMapComponent_pure,
      tensorBimoduleMapComponent_pure]
    rfl

instance tensorRepresentation_full : (tensorRepresentation R S).Full where
  map_surjective {M N} τ := ⟨tensorNatEvaluationMap τ.hom, by
    apply ObjectProperty.hom_ext
    exact tensorNatEvaluation_complete τ.hom⟩

instance tensorRepresentation_faithful : (tensorRepresentation R S).Faithful where
  map_injective {M N} f g h := by
    have hh : tensorBimoduleMapNatTrans f = tensorBimoduleMapNatTrans g := congrArg (fun k => k.hom) h
    have h' := congrArg tensorNatEvaluationMap hh
    simpa only [tensorNatEvaluation_induced] using h'

/-- The bimodule obtained by evaluating at the regular module. -/
def wattsBimodule (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] : ConcreteBimodule R S where
  carrier := ChoiceFreeWatts.M F
  rightModule := wattsRightModule F
  commuting := wattsRight_commutes F

/-- The two concrete tensor functors attached to the regular-module value
agree, using the checked comparison of their induced maps. -/
def wattsTensorFunctorIso (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] :
    concreteTensorFunctor (R := R) (S := S) (wattsBimodule R S F).carrier ≅
      ChoiceFreeWatts.tensorFunctor F := by
  refine NatIso.ofComponents (fun X => Iso.refl _) ?_
  intro X Y f
  letI : Module (MulOpposite R) (ChoiceFreeWatts.M F) := wattsRightModule F
  letI : SMulCommClass (MulOpposite R) S (ChoiceFreeWatts.M F) := wattsRight_commutes F
  apply ModuleCat.hom_ext
  change concreteTensorMap (M := ChoiceFreeWatts.M F) (S := S) f.hom =
    (ChoiceFreeWatts.tensorMap F f).hom
  exact watts_concrete_map F f

instance tensorRepresentation_essSurj : (tensorRepresentation R S).EssSurj where
  mem_essImage G := by
    let F := G.obj
    letI : F.Additive := G.property.1
    letI : PreservesFiniteColimits F := G.property.2.1
    letI : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F := G.property.2.2
    refine ⟨wattsBimodule R S F, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    exact wattsTensorFunctorIso R S F ≪≫ eilenbergWattsIso F

instance tensorRepresentation_isEquivalence : (tensorRepresentation R S).IsEquivalence where

/-- The category of S-R bimodules is equivalent to the category of additive
finite-colimit- and coproduct-preserving module functors. -/
noncomputable def eilenbergWattsEquivalence : ConcreteBimodule R S ≌ GoodFunctors R S :=
  (tensorRepresentation R S).asEquivalence

#print axioms wattsBimodule
#print axioms wattsTensorFunctorIso
#print axioms tensorRepresentation_full
#print axioms tensorRepresentation_faithful
#print axioms tensorRepresentation_essSurj
#print axioms eilenbergWattsEquivalence

end ConcreteBimodule
end NotesProofs
