import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Opposite

universe u v w t

def endpoint : Prop :=
  ∀ (R : Type u) [Ring R] (B : Type v) [AddCommGroup B] [Module (MulOpposite R) B]
      (M : Type w) [AddCommGroup M] [Module R M],
    let Bal := fun (A : AddCommGrpCat.{max v w t}) =>
      { f : B → M → A //
        (∀ (b b' : B) (m : M), f (b + b') m = f b m + f b' m) ∧
        (∀ (b : B) (m m' : M), f b (m + m') = f b m + f b m') ∧
        (∀ (r : R) (b : B) (m : M), f (MulOpposite.op r • b) m = f b (r • m)) }
    let Universal := fun (T : AddCommGrpCat.{max v w t}) (p : Bal T) =>
      ∀ (A : AddCommGrpCat.{max v w t}),
        ∃ e : Equiv (AddMonoidHom T A) (Bal A),
          ∀ (h : AddMonoidHom T A) (b : B) (m : M), (e h).val b m = h (p.val b m)
    ∃ (T : AddCommGrpCat.{max v w t}) (p : Bal T),
      Universal T p ∧
      (∀ x : T, ∃ pairs : List (Prod B M),
        List.sum (List.map (fun bm => p.val bm.1 bm.2) pairs) = x) ∧
      (∀ (T' : AddCommGrpCat.{max v w t}) (p' : Bal T'), Universal T' p' →
        ∃! e : AddEquiv T T', ∀ (b : B) (m : M), e (p.val b m) = p'.val b m)

set_option pp.universes true in
#check endpoint
