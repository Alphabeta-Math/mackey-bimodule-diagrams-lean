import NotesProofs.ReviewedWattsConnection
import NotesProofs.ReviewedWattsMorphismsConnection
import NotesProofs.ReviewedWattsCategoryConnection

universe u v

#check (ReviewedWattsConnection.{u} :
∀ (R S : Type u) [Ring R] [Ring S],
  (∀ (F : CategoryTheory.Functor (ModuleCat.{u} R) (ModuleCat.{u} S))
    [CategoryTheory.Functor.Additive F],
    NotesProofs.WattsPreservesCokernels F →
    NotesProofs.WattsPreservesCoproducts F →
    CategoryTheory.IsIso (NotesProofs.wattsComparisonNatTrans F)) ∧
  (∀ (B : Type u) [AddCommGroup B] [Module S B] [Module (MulOpposite R) B]
    [SMulCommClass (MulOpposite R) S B],
    let T := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    CategoryTheory.Functor.Additive T ∧
      NotesProofs.WattsPreservesCokernels T ∧
      NotesProofs.WattsPreservesCoproducts T))
#print axioms ReviewedWattsConnection

#check (ReviewedWattsMorphismsConnection.{u} :
∀ (R S : Type u) [Ring R] [Ring S],
  (∀ (F G : CategoryTheory.Functor (ModuleCat.{u} R) (ModuleCat.{u} S))
      [CategoryTheory.Functor.Additive F] [CategoryTheory.Functor.Additive G],
    NotesProofs.WattsPreservesCokernels F →
    NotesProofs.WattsPreservesCoproducts F →
    NotesProofs.WattsPreservesCokernels G →
    NotesProofs.WattsPreservesCoproducts G →
    let A := ChoiceFreeWatts.regular.{u, u} R
    let B₀ := CategoryTheory.Functor.obj F A
    let D₀ := CategoryTheory.Functor.obj G A
    letI _rightF : Module (MulOpposite R) (ModuleCat.carrier B₀) :=
      NotesProofs.wattsRightModule F
    letI _rightG : Module (MulOpposite R) (ModuleCat.carrier D₀) :=
      NotesProofs.wattsRightModule G
    ∃ e : Equiv (CategoryTheory.NatTrans F G)
        (NotesProofs.BimoduleMap (R := R) (S := S)
          (M := ModuleCat.carrier B₀) (N := ModuleCat.carrier D₀)),
      ∀ η : CategoryTheory.NatTrans F G,
        Subtype.val (Equiv.toFun e η) = ModuleCat.Hom.hom (CategoryTheory.NatTrans.app η A)) ∧
  (∀ (B D : Type u) [AddCommGroup B] [AddCommGroup D]
      [Module S B] [Module S D] [Module (MulOpposite R) B] [Module (MulOpposite R) D]
      [SMulCommClass (MulOpposite R) S B] [SMulCommClass (MulOpposite R) S D],
    let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    let TD := NotesProofs.concreteTensorFunctor (R := R) (S := S) D
    ∀ η : CategoryTheory.NatTrans TB TD,
      ∃! β : NotesProofs.BimoduleMap (R := R) (S := S) (M := B) (N := D),
        η = NotesProofs.tensorBimoduleMapNatTrans β))
#print axioms ReviewedWattsMorphismsConnection

#check (ReviewedWattsCategoryConnection.{u,v} :
∀ (R S : Type u) [Ring R] [Ring S],
  let tensor := NotesProofs.General.ConcreteBimodule.tensorRepresentation.{u,v} R S
  let regular := ChoiceFreeWatts.regular.{u,v} R
  CategoryTheory.Functor.Full tensor ∧
  CategoryTheory.Functor.Faithful tensor ∧
  CategoryTheory.Functor.EssSurj tensor ∧
  ∃ E : CategoryTheory.Equivalence
      (NotesProofs.General.ConcreteBimodule.{u,v} R S)
      (NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S),
    CategoryTheory.Equivalence.functor E = tensor ∧
    (∀ F : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S,
      letI : CategoryTheory.Functor.Additive (CategoryTheory.ObjectProperty.FullSubcategory.obj F) :=
        (CategoryTheory.ObjectProperty.FullSubcategory.property F).1
      CategoryTheory.Functor.obj (CategoryTheory.Equivalence.inverse E) F =
        NotesProofs.General.ConcreteBimodule.wattsBimodule.{u,v} R S
          (CategoryTheory.ObjectProperty.FullSubcategory.obj F)) ∧
    (∀ {F G : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S} (η : Quiver.Hom F G),
      HEq (Subtype.val (CategoryTheory.Functor.map (CategoryTheory.Equivalence.inverse E) η))
        (ModuleCat.Hom.hom (CategoryTheory.NatTrans.app (CategoryTheory.InducedCategory.Hom.hom η) regular))) ∧
    (∀ (F : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S)
        (X : ModuleCat.{max u v} R),
      letI : CategoryTheory.Functor.Additive (CategoryTheory.ObjectProperty.FullSubcategory.obj F) :=
        (CategoryTheory.ObjectProperty.FullSubcategory.property F).1
      HEq
        (ModuleCat.Hom.hom (CategoryTheory.NatTrans.app
          (CategoryTheory.InducedCategory.Hom.hom
            (CategoryTheory.NatTrans.app (CategoryTheory.Iso.hom (CategoryTheory.Equivalence.counitIso E)) F)) X))
        (ChoiceFreeWatts.comparison (CategoryTheory.ObjectProperty.FullSubcategory.obj F) X)) ∧
    (∀ B : NotesProofs.General.ConcreteBimodule.{u,v} R S,
      HEq
        (Subtype.val (CategoryTheory.NatTrans.app (CategoryTheory.Iso.inv (CategoryTheory.Equivalence.unitIso E)) B))
        (NotesProofs.General.concreteTensorUnitor.{u,v} (R := R) (S := S)
          (NotesProofs.General.ConcreteBimodule.carrier B))))
#print axioms ReviewedWattsCategoryConnection
