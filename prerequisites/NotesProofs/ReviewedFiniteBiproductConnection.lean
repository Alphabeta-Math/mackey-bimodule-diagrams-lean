import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory CategoryTheory.Limits

theorem ReviewedFiniteBiproductConnection : (∀ {C : Type*} [CategoryTheory.Category.{_} C] [CategoryTheory.Preadditive C]
  {J : Type*} [Finite J] (X : J → C),
  letI : Fintype J := Fintype.ofFinite J
  (∀ (B : CategoryTheory.Limits.Bicone X),
    Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (B.π j) (B.ι j)) =
        CategoryTheory.CategoryStruct.id B.pt →
    Nonempty (CategoryTheory.Limits.Bicone.IsBilimit B)) ∧
  (∀ (P : CategoryTheory.Limits.Fan X) (hP : CategoryTheory.Limits.IsLimit P),
    let B := CategoryTheory.Limits.Bicone.ofLimitCone hP
    Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (B.π j) (B.ι j)) =
      CategoryTheory.CategoryStruct.id B.pt) ∧
  (∀ (Q : CategoryTheory.Limits.Cofan X) (hQ : CategoryTheory.Limits.IsColimit Q),
    let B := CategoryTheory.Limits.Bicone.ofColimitCocone hQ
    Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (B.π j) (B.ι j)) =
      CategoryTheory.CategoryStruct.id B.pt)) := by
  classical
  intro C _ _ J _ X
  letI : Fintype J := Fintype.ofFinite J
  refine ⟨?_, ?_, ?_⟩
  · intro B h
    exact ⟨isBilimitOfTotal B h⟩
  · intro P hP
    exact IsBilimit.total (biconeIsBilimitOfLimitConeOfIsLimit hP)
  · intro Q hQ
    exact IsBilimit.total (biconeIsBilimitOfColimitCoconeOfIsColimit hQ)

#print axioms ReviewedFiniteBiproductConnection
