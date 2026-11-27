import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.SingleObj

universe r s b i m t

noncomputable def endpoint : Prop :=
  ∀ {R : Type r} [Ring R] {S : Type s} [Ring S],
    let Bimod := CategoryTheory.AdditiveFunctor
      (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{b} S)
    let star := CategoryTheory.SingleObj.star (MulOpposite R)
    ∀ (B : Bimod),
      let carrier := B.obj.obj star
      let right := fun (a : R) (x : carrier) =>
        (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) x
      let Balanced := fun (X : ModuleCat.{max i m} R)
          (A : Type (max b i m t)) [AddCommGroup A] (p : carrier → X → A) =>
        (∀ x x' y, p (x + x') y = p x y + p x' y) ∧
        (∀ x y y', p x (y + y') = p x y + p x y') ∧
        (∀ a x y, p (right a x) y = p x (a • y))
      ∀ (T : ModuleCat.{max i m} R → ModuleCat.{max b i m t} S)
        (pure : ∀ (X : ModuleCat.{max i m} R), carrier → X → T X),
        (∀ (X : ModuleCat.{max i m} R),
          Balanced X (T X) (pure X) ∧
          (∀ (A : AddCommGrpCat.{max b i m t}) (p : carrier → X → A),
            Balanced X A p →
              ∃! h : AddMonoidHom (T X) A, ∀ x y, h (pure X x y) = p x y) ∧
          (∀ (c : S) (x : carrier) (y : X), c • pure X x y = pure X (c • x) y)) →
        ∀ {I : Type i} (M : I → ModuleCat.{max i m} R),
          letI : DecidableEq I := Classical.decEq I
          let sum := ModuleCat.of R (DirectSum I (fun j => ↥(M j)))
          ∃ e : LinearEquiv (RingHom.id S) (DirectSum I (fun j => ↥(T (M j)))) (T sum),
            ∀ (j : I) (x : carrier) (y : M j),
              e (DirectSum.lof S I (fun k => ↥(T (M k))) j (pure (M j) x y)) =
                pure sum x (DirectSum.lof R I (fun k => ↥(M k)) j y)
