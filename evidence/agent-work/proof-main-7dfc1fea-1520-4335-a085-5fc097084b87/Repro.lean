import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory

-- Step 4.1 needs a function, even after uniqueness of each component has
-- been proved. Keep the domain generic to expose the elimination restriction.
def pointwiseInverseAttempt {C D : Type*} [Category C] [Category D]
    {G H : C ⥤ D} (τ : G ⟶ H)
    (h : ∀ X : C, ∃! a : H.obj X ⟶ G.obj X,
      τ.app X ≫ a = 𝟙 (G.obj X) ∧ a ≫ τ.app X = 𝟙 (H.obj X))
    (X : C) : H.obj X ⟶ G.obj X := by
  obtain ⟨a, _, _⟩ := h X
  exact a
