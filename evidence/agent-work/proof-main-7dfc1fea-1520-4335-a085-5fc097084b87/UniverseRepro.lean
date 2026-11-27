import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory

universe u z w v

-- The coproduct hypothesis tests only Type w modules. Step 2.1 would
-- instantiate it with the explicit tensor construction at Type (max u z w).
example {B : Type v} [Ring B] {I : Type (max u z)} {D : I → ModuleCat.{w} B}
    {P : ModuleCat.{w} B} (ι : ∀ i, D i ⟶ P)
    (h : ∀ (Q : ModuleCat.{w} B) (legs : ∀ i, D i ⟶ Q),
      ∃! d : P ⟶ Q, ∀ i, ι i ≫ d = legs i)
    (Q : ModuleCat.{max u z w} B) : True := by
  have attempt := h Q
  exact True.intro
