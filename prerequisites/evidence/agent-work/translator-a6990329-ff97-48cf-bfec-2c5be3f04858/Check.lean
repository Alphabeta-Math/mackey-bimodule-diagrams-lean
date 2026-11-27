import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

private theorem compThroughBicone
    {C : Type*} [Category.{_} C] [Preadditive C]
    {K : Type*} [Fintype K] {Y : K → C} (B : Bicone Y)
    (hB : ∑ k, B.π k ≫ B.ι k = 𝟙 B.pt)
    {U V : C} (a : U ⟶ B.pt) (b : B.pt ⟶ V) :
    a ≫ b = ∑ k, (a ≫ B.π k) ≫ B.ι k ≫ b := by
  calc
    a ≫ b = a ≫ 𝟙 B.pt ≫ b := by simp
    _ = _ := by
      simp only [← hB, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]

private theorem reconstructBicone
    {C : Type*} [Category.{_} C] [Preadditive C]
    {J K : Type*} [Fintype J] [Fintype K] {X : J → C} {Y : K → C}
    (BX : Bicone X) (BY : Bicone Y)
    (hX : ∑ j, BX.π j ≫ BX.ι j = 𝟙 BX.pt)
    (hY : ∑ k, BY.π k ≫ BY.ι k = 𝟙 BY.pt)
    (f : BX.pt ⟶ BY.pt) :
    f = ∑ k, ∑ j, BX.π j ≫ (BX.ι j ≫ f ≫ BY.π k) ≫ BY.ι k := by
  calc
    f = 𝟙 BX.pt ≫ f ≫ 𝟙 BY.pt := by simp
    _ = _ := by
      rw [← hX, ← hY]
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]

#check CategoryTheory.Limits.biproduct.total

theorem BiproductMatrixCalculus :
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
  := by
    intros C _ _ J K _ _ X Y BX BY
    let : Fintype J := Fintype.ofFinite J
    let : Fintype K := Fintype.ofFinite K
    dsimp only
    intro hX hY
    refine ⟨?_, reconstructBicone BX BY hX hY, ?_, ?_⟩
    · intro f f' h
      calc
        f = _ := reconstructBicone BX BY hX hY f
        _ = f' := by
          rw [reconstructBicone BX BY hX hY f']
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by
            exact congrArg (fun e : X j ⟶ Y k => BX.π j ≫ e ≫ BY.ι k) (congrFun (congrFun h k) j)
    · intro L _ Z BZ _ f g l j
      simpa only [Category.assoc] using
        compThroughBicone BY hY (BX.ι j ≫ f) (g ≫ BZ.π l)
    · intro f f' k j
      simp only [Preadditive.add_comp, Preadditive.comp_add]

#print axioms BiproductMatrixCalculus
