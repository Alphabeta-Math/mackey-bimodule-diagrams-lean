import NotesProofs.General.BimoduleTensorCategory
import Mathlib.CategoryTheory.Whiskering
import NotesProofs.General.EquivalenceFromCounit

/-! Naturality of the canonical Eilenberg–Watts isomorphism with respect to
the functor, for the explicit regular-evaluation candidate inverse. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs.General.ConcreteBimodule

universe u v
open CategoryTheory CategoryTheory.Limits

variable (R S : Type u) [Ring R] [Ring S]

/-- The canonical tensor comparison at a good functor. -/
noncomputable def regularCounitComponent (G : GoodFunctors.{u,v} R S) :
    (tensorRepresentation.{u,v} R S).obj ((regularEvaluation.{u,v} R S).obj G) ≅ G := by
  let F := G.obj
  letI : F.Additive := G.property.1
  letI : PreservesFiniteColimits F := G.property.2.1
  letI : ∀ I : Type (max u v), PreservesColimitsOfShape (Discrete I) F := G.property.2.2
  apply ObjectProperty.isoMk
  exact wattsTensorFunctorIso.{u,v} R S F ≪≫ eilenbergWattsIso.{u,v} F

/-- The comparison has the expected formula on pure tensors. -/
theorem regularCounitComponent_pure (G : GoodFunctors.{u,v} R S)
    (X : ModuleCat.{max u v} R) (m : ((regularEvaluation.{u,v} R S).obj G).carrier) (x : X) :
    ((regularCounitComponent R S G).hom.hom.app X).hom
        (concretePure (R := R) (M := ((regularEvaluation.{u,v} R S).obj G).carrier) m x) =
      (G.obj.map (ChoiceFreeWatts.ell X x)).hom m := by
  letI : G.obj.Additive := G.property.1
  letI : Module (MulOpposite R) (ChoiceFreeWatts.M G.obj) := wattsRightModule G.obj
  letI : SMulCommClass (MulOpposite R) S (ChoiceFreeWatts.M G.obj) := wattsRight_commutes G.obj
  change ChoiceFreeWatts.comparison G.obj X
    (ChoiceFreeWatts.pure (fun a m => ChoiceFreeWatts.right G.obj a m) m x) = _
  exact ChoiceFreeWatts.comparison_pure G.obj X m x

/-- The regular-evaluation comparisons form a natural isomorphism. -/
noncomputable def regularCounit :
    regularEvaluation.{u,v} R S ⋙ tensorRepresentation.{u,v} R S ≅ 𝟭 (GoodFunctors.{u,v} R S) := by
  refine NatIso.ofComponents (regularCounitComponent R S) ?_
  intro G H η
  letI : G.obj.Additive := G.property.1
  letI : H.obj.Additive := H.property.1
  letI : Module (MulOpposite R) (ChoiceFreeWatts.M G.obj) := wattsRightModule G.obj
  letI : SMulCommClass (MulOpposite R) S (ChoiceFreeWatts.M G.obj) := wattsRight_commutes G.obj
  letI : Module (MulOpposite R) (ChoiceFreeWatts.M H.obj) := wattsRightModule H.obj
  letI : SMulCommClass (MulOpposite R) S (ChoiceFreeWatts.M H.obj) := wattsRight_commutes H.obj
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := ((regularEvaluation.{u,v} R S).obj G).carrier))
  intro m x
  change ((regularCounitComponent R S H).hom.hom.app X).hom
      (tensorBimoduleMapComponent ((regularEvaluation R S).map η) X
        (concretePure (R := R) (M := ((regularEvaluation.{u,v} R S).obj G).carrier) m x)) =
    (η.hom.app X).hom (((regularCounitComponent R S G).hom.hom.app X).hom
      (concretePure (R := R) (M := ((regularEvaluation.{u,v} R S).obj G).carrier) m x))
  rw [tensorBimoduleMapComponent_pure, regularCounitComponent_pure, regularCounitComponent_pure]
  have hn := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (η.hom.naturality (ChoiceFreeWatts.ell X x))) m
  exact hn.symm

/-- The checked equivalence can take evaluation at the regular module as its
actual inverse functor. -/
noncomputable def eilenbergWattsEquivalenceWithEvaluation :
    ConcreteBimodule.{u,v} R S ≌ GoodFunctors.{u,v} R S := by
  let E := eilenbergWattsEquivalence.{u,v} R S
  let G := regularEvaluation.{u,v} R S
  let F := tensorRepresentation.{u,v} R S
  have h : G ≅ E.inverse :=
    (Functor.rightUnitor G).symm ≪≫
      Functor.isoWhiskerLeft G E.unitIso ≪≫
      (Functor.associator G F E.inverse).symm ≪≫
      Functor.isoWhiskerRight (regularCounit R S) E.inverse ≪≫
      Functor.leftUnitor E.inverse
  exact E.changeInverse h.symm

/-- The inverse functor is definitionally evaluation at the regular module. -/
theorem eilenbergWattsEquivalenceWithEvaluation_inverse :
    (eilenbergWattsEquivalenceWithEvaluation.{u,v} R S).inverse = regularEvaluation.{u,v} R S := rfl

/-- The canonical equivalence with both the explicit regular-evaluation
inverse and the canonical tensor-comparison counit. -/
noncomputable def eilenbergWattsCanonical :
    ConcreteBimodule.{u,v} R S ≌ GoodFunctors.{u,v} R S :=
  equivalenceFromFullyFaithfulCounit (tensorRepresentation.{u,v} R S)
    (regularEvaluation.{u,v} R S) (regularCounit.{u,v} R S)

/-- The inverse and counit are the explicitly constructed ones. -/
theorem eilenbergWattsCanonical_inverse :
    (eilenbergWattsCanonical.{u,v} R S).inverse = regularEvaluation.{u,v} R S := rfl

theorem eilenbergWattsCanonical_counit :
    (eilenbergWattsCanonical.{u,v} R S).counitIso = regularCounit.{u,v} R S := rfl

/-- Applying the tensor representation to the inverse unit yields the
canonical comparison at the corresponding tensor functor. -/
theorem eilenbergWattsCanonical_map_unit_inv (B : ConcreteBimodule.{u,v} R S) :
    (tensorRepresentation.{u,v} R S).map ((eilenbergWattsCanonical.{u,v} R S).unitIso.inv.app B) =
      (regularCounit.{u,v} R S).hom.app ((tensorRepresentation.{u,v} R S).obj B) := by
  let ff := Functor.FullyFaithful.ofFullyFaithful (tensorRepresentation.{u,v} R S)
  change (tensorRepresentation.{u,v} R S).map
      (ff.preimage ((regularCounit.{u,v} R S).hom.app ((tensorRepresentation.{u,v} R S).obj B))) = _
  exact ff.map_preimage _

/-- The inverse unit is the standard tensor unitor on the underlying map. -/
theorem eilenbergWattsCanonical_unit_inv_unitor (B : ConcreteBimodule.{u,v} R S) :
    HEq ((eilenbergWattsCanonical.{u,v} R S).unitIso.inv.app B).1
      (concreteTensorUnitor.{u,v} (R := R) (S := S) B.carrier) := by
  let TB := (tensorRepresentation.{u,v} R S).obj B
  let τ := ((regularCounit.{u,v} R S).hom.app TB).hom
  have ev : tensorNatEvaluationMap τ = (eilenbergWattsCanonical.{u,v} R S).unitIso.inv.app B := by
    dsimp [τ, TB]
    rw [← eilenbergWattsCanonical_map_unit_inv]
    exact tensorNatEvaluation_induced _
  apply heq_of_eq
  apply LinearMap.ext
  intro b
  have evb := congrArg (fun f => f.1 b) ev
  apply evb.symm.trans
  change concreteTensorUnitor (R := R) (S := S) B.carrier
    ((τ.app (ChoiceFreeWatts.regular R)).hom
      (concretePure (R := R) (M := ((regularEvaluation R S).obj TB).carrier) b (⟨1⟩ : ULift.{v} R))) = _
  have h := regularCounitComponent_pure R S TB (ChoiceFreeWatts.regular R) b (⟨1⟩ : ULift.{v} R)
  have hid : ChoiceFreeWatts.ell (ChoiceFreeWatts.regular R) (⟨1⟩ : ULift.{v} R) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    ext a
    change (a.down • (⟨1⟩ : ULift.{v} R)).down = a.down
    exact mul_one a.down
  rw [hid] at h
  change (τ.app (ChoiceFreeWatts.regular R)).hom
    (concretePure (R := R) (M := ((regularEvaluation R S).obj TB).carrier) b (⟨1⟩ : ULift.{v} R)) =
      (TB.obj.map (𝟙 (ChoiceFreeWatts.regular R))).hom b at h
  have idb : (TB.obj.map (𝟙 (ChoiceFreeWatts.regular R))).hom b = b :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (TB.obj.map_id (ChoiceFreeWatts.regular R))) b
  exact (congrArg (concreteTensorUnitor (R := R) (S := S) B.carrier) h).trans
    (congrArg (concreteTensorUnitor (R := R) (S := S) B.carrier) idb)

#print axioms eilenbergWattsCanonical_unit_inv_unitor
#print axioms eilenbergWattsCanonical_map_unit_inv
#print axioms eilenbergWattsCanonical
#print axioms eilenbergWattsCanonical_inverse
#print axioms eilenbergWattsCanonical_counit
#print axioms eilenbergWattsEquivalenceWithEvaluation
#print axioms eilenbergWattsEquivalenceWithEvaluation_inverse
#print axioms regularCounitComponent_pure
#print axioms regularCounit

end NotesProofs.General.ConcreteBimodule
