import NotesProofs.General.BimoduleTensorCategory

universe u v

def auditedEndpoint : Prop :=
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
            (NotesProofs.General.ConcreteBimodule.carrier B)))

#print axioms auditedEndpoint
