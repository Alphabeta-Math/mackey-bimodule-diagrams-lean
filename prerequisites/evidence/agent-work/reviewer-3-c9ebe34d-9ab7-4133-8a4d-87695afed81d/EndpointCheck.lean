import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.CategoryTheory.Products.Basic

universe r s v w t

def reviewedEndpoint : Prop :=
∀ (R : Type r) [Ring R] (S : Type s) [Ring S],
  let Bimod := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{v} S)
  let star := CategoryTheory.SingleObj.star (MulOpposite R)
  let carrier := fun (B : Bimod) => B.obj.obj star
  let right := fun (B : Bimod) (a : R) (b : carrier B) =>
    (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) b
  let Balanced := fun (B : Bimod) (M : ModuleCat.{w} R)
      (A : Type (max v w t)) [AddCommGroup A] (p : carrier B → M → A) =>
    (∀ (b b' : carrier B) (m : M), p (b + b') m = p b m + p b' m) ∧
    (∀ (b : carrier B) (m m' : M), p b (m + m') = p b m + p b m') ∧
    (∀ (a : R) (b : carrier B) (m : M), p (right B a b) m = p b (a • m))
  ∃ (F : CategoryTheory.Functor (Prod Bimod (ModuleCat.{w} R)) (ModuleCat.{max v w t} S))
    (pure : ∀ (B : Bimod) (M : ModuleCat.{w} R), carrier B → M → F.obj (B, M)),
    (∀ (B : Bimod) (M : ModuleCat.{w} R),
      Balanced B M ((F.obj (B, M)) : Type (max v w t)) (pure B M) ∧
      (∀ (A : AddCommGrpCat.{max v w t}) (p : carrier B → M → A),
        Balanced B M A p →
        ∃! h : AddMonoidHom (F.obj (B, M)) A, ∀ b m, h (pure B M b m) = p b m) ∧
      (∀ (a : S) (b : carrier B) (m : M), a • pure B M b m = pure B M (a • b) m)) ∧
    (∀ {B B' : Bimod} {M M' : ModuleCat.{w} R}
        (u : Quiver.Hom B B') (f : Quiver.Hom M M') (b : carrier B) (m : M),
      (F.map (CategoryTheory.Prod.mkHom u f)) (pure B M b m) =
        pure B' M' ((u.hom.app star) b) (f m)) ∧
    (∀ M : ModuleCat.{w} R,
      CategoryTheory.Functor.Additive (CategoryTheory.Functor.comp
        (CategoryTheory.Prod.sectL Bimod M) F)) ∧
    (∀ B : Bimod,
      CategoryTheory.Functor.Additive (CategoryTheory.Functor.comp
        (CategoryTheory.Prod.sectR B (ModuleCat.{w} R)) F))
