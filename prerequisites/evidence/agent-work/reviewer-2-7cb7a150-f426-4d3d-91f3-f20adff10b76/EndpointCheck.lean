import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Ring.Opposite

universe r s v w t

def TranslatedEndpoint : Prop :=
  ∀ (R : Type r) [Ring R] (S : Type s) [Ring S],
    let Bimod := CategoryTheory.AdditiveFunctor
      (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{v} S)
    let star := CategoryTheory.SingleObj.star (MulOpposite R)
    ∀ (B : Bimod),
      let carrier := B.obj.obj star
      let right := fun (a : R) (b : carrier) =>
        (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) b
      let Balanced := fun (M : ModuleCat.{w} R)
          (A : Type (max v w t)) [AddCommGroup A] (p : carrier → M → A) =>
        (∀ (b b' : carrier) (m : M), p (b + b') m = p b m + p b' m) ∧
        (∀ (b : carrier) (m m' : M), p b (m + m') = p b m + p b m') ∧
        (∀ (a : R) (b : carrier) (m : M), p (right a b) m = p b (a • m))
      ∀ (T : CategoryTheory.Functor (ModuleCat.{w} R) (ModuleCat.{max v w t} S))
        [CategoryTheory.Functor.Additive T]
        (pure : ∀ M : ModuleCat.{w} R, carrier → M → T.obj M),
        (∀ M : ModuleCat.{w} R,
          Balanced M (T.obj M : Type (max v w t)) (pure M) ∧
          (∀ (A : AddCommGrpCat.{max v w t}) (p : carrier → M → A),
            Balanced M A p →
            ∃! h : AddMonoidHom (T.obj M) A, ∀ b m, h (pure M b m) = p b m) ∧
          (∀ (a : S) (b : carrier) (m : M), a • pure M b m = pure M (a • b) m)) →
        (∀ {M N : ModuleCat.{w} R} (f : Quiver.Hom M N) (b : carrier) (m : M),
          (T.map f) (pure M b m) = pure N b (f m)) →
        (∀ C : CategoryTheory.ShortComplex (ModuleCat.{w} R),
          CategoryTheory.ShortComplex.Exact C → CategoryTheory.Epi C.g →
          CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.map C T) ∧
            CategoryTheory.Epi (T.map C.g)) ∧
        (∀ C : CategoryTheory.ShortComplex (ModuleCat.{w} R),
          Nonempty (CategoryTheory.Limits.IsColimit
            (CategoryTheory.Limits.CokernelCofork.ofπ C.g C.zero)) →
          Nonempty (CategoryTheory.Limits.IsColimit
            (CategoryTheory.Limits.CokernelCofork.ofπ
              (CategoryTheory.ShortComplex.map C T).g (CategoryTheory.ShortComplex.map C T).zero)))

open CategoryTheory CategoryTheory.Limits

private theorem exactTail {R : Type r} [Ring R]
    (C : ShortComplex (ModuleCat.{w} R)) :
    (C.Exact ∧ Epi C.g) ↔
      (LinearMap.range C.f.hom = LinearMap.ker C.g.hom ∧ Function.Surjective C.g) := by
  rw [C.moduleCat_exact_iff_range_eq_ker, ModuleCat.epi_iff_surjective]

private theorem cokernelTail {R : Type r} [Ring R]
    (C : ShortComplex (ModuleCat.{w} R)) :
    (C.Exact ∧ Epi C.g) ↔ Nonempty (IsColimit (CokernelCofork.ofπ C.g C.zero)) :=
  C.exact_and_epi_g_iff_g_is_cokernel
