import Mathlib.CategoryTheory.Preadditive.Biproducts

noncomputable def translatedEndpoint : Prop :=
  ∀ {C : Type*} [CategoryTheory.Category.{_} C] [CategoryTheory.Preadditive C]
    {J K : Type*} [Finite J] [Finite K]
    {X : J → C} {Y : K → C}
    (BX : CategoryTheory.Limits.Bicone X) (BY : CategoryTheory.Limits.Bicone Y),
    letI : Fintype J := Fintype.ofFinite J
    letI : Fintype K := Fintype.ofFinite K
    let entry {U A B V : C} (i : Quiver.Hom U A) (f : Quiver.Hom A B)
        (p : Quiver.Hom B V) : Quiver.Hom U V :=
      CategoryTheory.CategoryStruct.comp i (CategoryTheory.CategoryStruct.comp f p)
    (Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (BX.π j) (BX.ι j)) =
      CategoryTheory.CategoryStruct.id BX.pt) →
    (Finset.sum Finset.univ (fun k => CategoryTheory.CategoryStruct.comp (BY.π k) (BY.ι k)) =
      CategoryTheory.CategoryStruct.id BY.pt) →
    Function.Injective (fun (f : Quiver.Hom BX.pt BY.pt) (k : K) (j : J) =>
      entry (BX.ι j) f (BY.π k)) ∧
    (∀ f : Quiver.Hom BX.pt BY.pt,
      f = Finset.sum Finset.univ (fun k => Finset.sum Finset.univ (fun j =>
        entry (BX.π j) (entry (BX.ι j) f (BY.π k)) (BY.ι k)))) ∧
    (∀ {L : Type*} [Finite L] {Z : L → C} (BZ : CategoryTheory.Limits.Bicone Z),
      letI : Fintype L := Fintype.ofFinite L
      (Finset.sum Finset.univ (fun l => CategoryTheory.CategoryStruct.comp (BZ.π l) (BZ.ι l)) =
        CategoryTheory.CategoryStruct.id BZ.pt) →
      ∀ (f : Quiver.Hom BX.pt BY.pt) (g : Quiver.Hom BY.pt BZ.pt) (l : L) (j : J),
        entry (BX.ι j) (CategoryTheory.CategoryStruct.comp f g) (BZ.π l) =
          Finset.sum Finset.univ (fun k => CategoryTheory.CategoryStruct.comp
            (entry (BX.ι j) f (BY.π k)) (entry (BY.ι k) g (BZ.π l)))) ∧
    (∀ (f f' : Quiver.Hom BX.pt BY.pt) (k : K) (j : J),
      entry (BX.ι j) (f + f') (BY.π k) =
        entry (BX.ι j) f (BY.π k) + entry (BX.ι j) f' (BY.π k))

#check translatedEndpoint
#print axioms translatedEndpoint
#check CategoryTheory.Limits.Bicone.ι_π
#check CategoryTheory.Limits.biproduct.total
