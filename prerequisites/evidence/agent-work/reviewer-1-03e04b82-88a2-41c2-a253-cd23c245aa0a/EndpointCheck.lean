import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.Module.Submodule.Ker

universe u v w x y

def reviewedEndpoint : Prop :=
∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
  (∀ {I : Type w} (m : I → M),
    ∃! f : LinearMap (RingHom.id R) (Finsupp I R) M,
      ∀ i : I, f (Finsupp.single i 1) = m i) ∧
  (∃ (I : Type v) (J : Type (max u v))
      (d : LinearMap (RingHom.id R) (Finsupp J R) (Finsupp I R))
      (q : LinearMap (RingHom.id R) (Finsupp I R) M),
    LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) ∧
  (∀ {I : Type w} {J : Type x}
      (d : LinearMap (RingHom.id R) (Finsupp J R) (Finsupp I R))
      (q : LinearMap (RingHom.id R) (Finsupp I R) M),
    (LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) ↔
      (LinearMap.comp q d = 0 ∧
        ∀ (N : Type (max u v w x y)) [AddCommGroup N] [Module R N]
          (g : LinearMap (RingHom.id R) (Finsupp I R) N),
          LinearMap.comp g d = 0 →
            ∃! h : LinearMap (RingHom.id R) M N, LinearMap.comp h q = g))

#check @finsuppLEquivDirectSum_single
#check @Finsupp.single
#check @LinearMap.range
#check @LinearMap.ker
