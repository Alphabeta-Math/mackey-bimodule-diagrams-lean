import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic

universe u v

axiom GroupAlgebraRingLaws : ∀ (k : Type u) [Field k] (G : Type v) [Group G],
  Nonempty (Ring (MonoidAlgebra k G)) ∧
  (∀ x y : MonoidAlgebra k G,
    x * y = Finsupp.sum (MonoidAlgebra.coeff x) (fun g a =>
      Finsupp.sum (MonoidAlgebra.coeff y) (fun h b =>
        MonoidAlgebra.single (g * h) (a * b)))) ∧
  (1 : MonoidAlgebra k G) = MonoidAlgebra.single (1 : G) (1 : k) ∧
  Nonempty (Algebra k (MonoidAlgebra k G)) ∧
  (∀ a : k, algebraMap k (MonoidAlgebra k G) a = MonoidAlgebra.single (1 : G) a) ∧
  Function.Injective (⇑(algebraMap k (MonoidAlgebra k G))) ∧
  (∀ (a : k) (x : MonoidAlgebra k G),
    algebraMap k (MonoidAlgebra k G) a * x = x * algebraMap k (MonoidAlgebra k G) a) ∧
  (∀ g : G, ∃ z : Units (MonoidAlgebra k G),
    (↑z : MonoidAlgebra k G) = MonoidAlgebra.single g (1 : k) ∧
    (↑(z⁻¹) : MonoidAlgebra k G) = MonoidAlgebra.single g⁻¹ (1 : k)) ∧
  ((∀ x y : MonoidAlgebra k G, x * y = y * x) ↔ (∀ g h : G, g * h = h * g))

#check MonoidAlgebra.ring
#check MonoidAlgebra.mul_def
#check MonoidAlgebra.one_def
#check MonoidAlgebra.algebra
#check MonoidAlgebra.single_mul_single
#check MonoidAlgebra.single_left_injective
#check MonoidAlgebra.single_right_injective
#check MonoidAlgebra.commRing
#check Algebra.commutes

example (k : Type u) [Field k] (G : Type v) [Group G] (a : k) :
    algebraMap k (MonoidAlgebra k G) a = MonoidAlgebra.single (1 : G) a := rfl
