import WattsFoundation.ReconstructionSupport
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

set_option linter.style.haveILetI false

universe u v

theorem ClassicalReconstruction : (
∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Preadditive C] (P : C),
  let isKernel := fun {X Y K : C} (f : Quiver.Hom X Y) (ι : Quiver.Hom K X) =>
    CategoryTheory.CategoryStruct.comp ι f = 0 ∧
      ∀ (T : C) (g : Quiver.Hom T X),
        CategoryTheory.CategoryStruct.comp g f = 0 →
        ExistsUnique (fun h : Quiver.Hom T K => CategoryTheory.CategoryStruct.comp h ι = g)
  let isCokernel := fun {X Y Q : C} (f : Quiver.Hom X Y) (π : Quiver.Hom Y Q) =>
    CategoryTheory.CategoryStruct.comp f π = 0 ∧
      ∀ (T : C) (g : Quiver.Hom Y T),
        CategoryTheory.CategoryStruct.comp f g = 0 →
        ExistsUnique (fun h : Quiver.Hom Q T => CategoryTheory.CategoryStruct.comp π h = g)
  let isCoproduct := fun {I : Type v} (X : I → C) (Q : C)
      (ι : ∀ i, Quiver.Hom (X i) Q) =>
    ∀ (T : C) (g : ∀ i, Quiver.Hom (X i) T),
      ExistsUnique (fun h : Quiver.Hom Q T =>
        ∀ i, CategoryTheory.CategoryStruct.comp (ι i) h = g i)
  let A := MulOpposite (CategoryTheory.End P)
  let M := ModuleCat.{v} A
  let H : CategoryTheory.Functor C M := CategoryTheory.preadditiveCoyonedaObj P
  let homGroup := fun X : C => AddCommGrpCat.of (Quiver.Hom P X)
  let homGroupMap := fun {X Y : C} (f : Quiver.Hom X Y) =>
    (AddCommGrpCat.ofHom
      (LinearMap.toAddMonoidHom (ModuleCat.Hom.hom (H.map f))) :
      Quiver.Hom (homGroup X) (homGroup Y))
  (∀ (J : Type v) [CategoryTheory.Category.{v} J] (F : CategoryTheory.Functor J C),
    ∃ (Q : C) (ι : ∀ j, Quiver.Hom (F.obj j) Q),
      (∀ (i j : J) (f : Quiver.Hom i j),
        CategoryTheory.CategoryStruct.comp (F.map f) (ι j) = ι i) ∧
      ∀ (T : C) (g : ∀ j, Quiver.Hom (F.obj j) T),
        (∀ (i j : J) (f : Quiver.Hom i j),
          CategoryTheory.CategoryStruct.comp (F.map f) (g j) = g i) →
        ExistsUnique (fun h : Quiver.Hom Q T =>
          ∀ j, CategoryTheory.CategoryStruct.comp (ι j) h = g j)) →
  (∀ (n : Nat) (X : Fin n → C),
    ∃ (Q : C) (π : ∀ i, Quiver.Hom Q (X i)),
      ∀ (T : C) (g : ∀ i, Quiver.Hom T (X i)),
        ExistsUnique (fun h : Quiver.Hom T Q =>
          ∀ i, CategoryTheory.CategoryStruct.comp h (π i) = g i)) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), ∃ (K : C) (ι : Quiver.Hom K X), isKernel f ι) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), ∃ (Q : C) (π : Quiver.Hom Y Q), isCokernel f π) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), CategoryTheory.Mono f →
    ∃ (Z : C) (g : Quiver.Hom Y Z), isKernel g f) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), CategoryTheory.Epi f →
    ∃ (Z : C) (g : Quiver.Hom Z X), isCokernel g f) →
  CategoryTheory.Projective P →
  CategoryTheory.IsSeparator P →
  (∀ (I : Type v) (X : I → C) (Q : C) (ι : ∀ i, Quiver.Hom (X i) Q),
    isCoproduct X Q ι →
    ∀ (T : AddCommGrpCat.{v}) (g : ∀ i, Quiver.Hom (homGroup (X i)) T),
      ExistsUnique (fun h : Quiver.Hom (homGroup Q) T =>
        ∀ i, CategoryTheory.CategoryStruct.comp (homGroupMap (ι i)) h = g i)) →
  ∀ (copower : ∀ I : Type v,
      Σ Q : C, Σ ι : I → Quiver.Hom P Q,
        ∀ T : C,
          { e : Equiv (Quiver.Hom Q T) (I → Quiver.Hom P T) //
            ∀ (h : Quiver.Hom Q T) (i : I),
              e h i = CategoryTheory.CategoryStruct.comp (ι i) h })
    (cokernel : ∀ {X Y : C} (f : Quiver.Hom X Y),
      Σ Q : C, Σ π : { p : Quiver.Hom Y Q //
        CategoryTheory.CategoryStruct.comp f p = 0 },
        ∀ T : C,
          { e : Equiv (Quiver.Hom Q T)
              { g : Quiver.Hom Y T // CategoryTheory.CategoryStruct.comp f g = 0 } //
            ∀ h : Quiver.Hom Q T,
              (e h).val = CategoryTheory.CategoryStruct.comp π.val h }),
  let coefficients := fun I : Type v =>
    Σ s : Finset I, { a : I → A // ∀ i, Multiset.Mem s.val i ↔ a i ≠ 0 }
  let relations := fun V : M =>
    { r : coefficients (↥V) //
      Finset.sum r.1 (fun x => r.2.val x • x) = (0 : ↥V) }
  let transpose := fun V : M =>
    let generators := copower (↥V)
    let relationCopower := copower (relations V)
    ((relationCopower.2.2 generators.1).val.symm) (fun r : relations V =>
      Finset.sum r.val.1 (fun x =>
        CategoryTheory.CategoryStruct.comp
          (CategoryTheory.End.asHom (MulOpposite.unop (r.val.2.val x)))
          (generators.2.1 x)))
  let presentationCokernel := fun V : M => cokernel (transpose V)
  ∀ (L : CategoryTheory.Functor M C),
  let HL : CategoryTheory.Functor M M :=
    { obj := fun V => H.obj (L.obj V)
      map := fun f => H.map (L.map f)
      map_id := fun V => (congrArg H.map (L.map_id V)).trans (H.map_id (L.obj V))
      map_comp := fun f g => (congrArg H.map (L.map_comp f g)).trans (H.map_comp _ _) }
  let LH : CategoryTheory.Functor C C :=
    { obj := fun X => L.obj (H.obj X)
      map := fun f => L.map (H.map f)
      map_id := fun X => (congrArg L.map (H.map_id X)).trans (L.map_id (H.obj X))
      map_comp := fun f g => (congrArg L.map (H.map_comp f g)).trans (L.map_comp _ _) }
  ∀ (adj :
      Σ η : CategoryTheory.NatTrans (CategoryTheory.Functor.id M) HL,
        { ε : CategoryTheory.NatTrans LH (CategoryTheory.Functor.id C) //
          (∀ V : M,
            CategoryTheory.CategoryStruct.comp (L.map (η.app V)) (ε.app (L.obj V)) =
              CategoryTheory.CategoryStruct.id (L.obj V)) ∧
          (∀ X : C,
            CategoryTheory.CategoryStruct.comp (η.app (H.obj X)) (H.map (ε.app X)) =
              CategoryTheory.CategoryStruct.id (H.obj X)) })
    (presentationIso : ∀ V : M, CategoryTheory.Iso (presentationCokernel V).1 (L.obj V)),
    let η := adj.1
    let ε := adj.2.val
    (∀ (V : M) (x : ↥V),
      (η.app V) x =
        CategoryTheory.CategoryStruct.comp ((copower (↥V)).2.1 x)
          (CategoryTheory.CategoryStruct.comp
            (presentationCokernel V).2.1.val (presentationIso V).hom)) →
    ∃ (ηInv : CategoryTheory.NatTrans HL (CategoryTheory.Functor.id M))
      (εInv : CategoryTheory.NatTrans (CategoryTheory.Functor.id C) LH),
      (∀ V : M,
        CategoryTheory.CategoryStruct.comp (η.app V) (ηInv.app V) =
          CategoryTheory.CategoryStruct.id V ∧
        CategoryTheory.CategoryStruct.comp (ηInv.app V) (η.app V) =
          CategoryTheory.CategoryStruct.id (HL.obj V)) ∧
      (∀ X : C,
        CategoryTheory.CategoryStruct.comp (ε.app X) (εInv.app X) =
          CategoryTheory.CategoryStruct.id (LH.obj X) ∧
        CategoryTheory.CategoryStruct.comp (εInv.app X) (ε.app X) =
          CategoryTheory.CategoryStruct.id X)
) :=
(by
  classical
  intro C cat pre P isKernel isCokernel isCoproduct A M H homGroup homGroupMap
    hcol hfin kernels cokernels normalMonos normalEpis projective separator hAb copower cokernel
    coefficients relations transpose presentationCokernel L HL LH adj presentationIso η ε hη
  have point := ReconstructionCheck.PointwiseReconstruction C P hcol hfin kernels cokernels
    normalMonos normalEpis projective separator hAb copower cokernel L adj presentationIso hη
  letI : ∀ V : M, CategoryTheory.IsIso (η.app V) := fun V =>
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (η.app V)).2 (point.1 V)
  letI : ∀ X : C, CategoryTheory.IsIso (ε.app X) := fun X => ⟨(point.2 X).exists⟩
  haveI := CategoryTheory.NatIso.isIso_of_isIso_app η
  haveI := CategoryTheory.NatIso.isIso_of_isIso_app ε
  let ηInv : CategoryTheory.NatTrans HL (CategoryTheory.Functor.id M) := @CategoryTheory.inv (CategoryTheory.Functor M M) _ (CategoryTheory.Functor.id M) HL η (CategoryTheory.NatIso.isIso_of_isIso_app η)
  let εInv : CategoryTheory.NatTrans (CategoryTheory.Functor.id C) LH := @CategoryTheory.inv (CategoryTheory.Functor C C) _ LH (CategoryTheory.Functor.id C) ε (CategoryTheory.NatIso.isIso_of_isIso_app ε)
  refine ⟨ηInv, εInv, ?_, ?_⟩
  · intro V
    exact ⟨CategoryTheory.NatTrans.congr_app (@CategoryTheory.IsIso.hom_inv_id (CategoryTheory.Functor M M) _ (CategoryTheory.Functor.id M) HL η (CategoryTheory.NatIso.isIso_of_isIso_app η)) V,
      CategoryTheory.NatTrans.congr_app (@CategoryTheory.IsIso.inv_hom_id (CategoryTheory.Functor M M) _ (CategoryTheory.Functor.id M) HL η (CategoryTheory.NatIso.isIso_of_isIso_app η)) V⟩
  · intro X
    exact ⟨CategoryTheory.NatTrans.congr_app (@CategoryTheory.IsIso.hom_inv_id (CategoryTheory.Functor C C) _ LH (CategoryTheory.Functor.id C) ε (CategoryTheory.NatIso.isIso_of_isIso_app ε)) X,
      CategoryTheory.NatTrans.congr_app (@CategoryTheory.IsIso.inv_hom_id (CategoryTheory.Functor C C) _ LH (CategoryTheory.Functor.id C) ε (CategoryTheory.NatIso.isIso_of_isIso_app ε)) X⟩
)

#print axioms ClassicalReconstruction
