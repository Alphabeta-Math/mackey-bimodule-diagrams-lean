import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Opposite

/-! Balanced maps descend across a module cokernel. This is the universal
property step in right exactness of tensoring over a noncommutative ring. -/

namespace WattsFoundation

universe u v

variable {R : Type u} [Ring R]
variable {M L N Q D : Type v}
variable [AddCommGroup M] [Module (MulOpposite R) M]
variable [AddCommGroup L] [Module R L] [AddCommGroup N] [Module R N]
variable [AddCommGroup Q] [Module R Q] [AddCommGroup D]

/-- A balanced biadditive map that kills the image of `f` descends uniquely
along a surjective `q` whose kernel is the image of `f`. -/
theorem balanced_cokernel_descent
    (f : L →ₗ[R] N) (q : N →ₗ[R] Q)
    (q_surj : Function.Surjective q)
    (exact : ∀ n, q n = 0 → ∃ l, f l = n)
    (b : M →+ (N →+ D))
    (balance : ∀ (r : R) (m : M) (n : N),
      b (MulOpposite.op r • m) n = b m (r • n))
    (kill : ∀ (m : M) (l : L), b m (f l) = 0) :
    ∃! c : M →+ (Q →+ D),
      (∀ m n, c m (q n) = b m n) ∧
      (∀ (r : R) (m : M) (x : Q),
        c (MulOpposite.op r • m) x = c m (r • x)) := by
  classical
  have well_defined (m : M) (n n' : N) (h : q n = q n') : b m n = b m n' := by
    have hz : q (n - n') = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨l, hl⟩ := exact _ hz
    have hz' : b m (n - n') = 0 := by rw [← hl]; exact kill m l
    simpa only [map_sub, sub_eq_zero] using hz'
  let d (m : M) (x : Q) : D := b m (Classical.choose (q_surj x))
  have d_spec (m : M) (n : N) : d m (q n) = b m n :=
    well_defined m _ n (Classical.choose_spec (q_surj (q n)))
  let c : M →+ (Q →+ D) :=
    { toFun := fun m =>
        { toFun := d m
          map_zero' := by simpa only [map_zero] using d_spec m 0
          map_add' := by
            intro x y
            obtain ⟨n, rfl⟩ := q_surj x
            obtain ⟨n', rfl⟩ := q_surj y
            rw [← map_add q, d_spec, d_spec, d_spec, map_add] }
      map_zero' := by
        ext x
        obtain ⟨n, rfl⟩ := q_surj x
        change d 0 (q n) = 0
        rw [d_spec, map_zero]
        rfl
      map_add' := by
        intro m m'
        ext x
        obtain ⟨n, rfl⟩ := q_surj x
        change d (m + m') (q n) = d m (q n) + d m' (q n)
        rw [d_spec, d_spec, d_spec, map_add]
        rfl }
  refine ⟨c, ⟨d_spec, ?_⟩, ?_⟩
  · intro r m x
    obtain ⟨n, rfl⟩ := q_surj x
    change d (MulOpposite.op r • m) (q n) = d m (r • q n)
    rw [← q.map_smul, d_spec, d_spec, balance]
  · intro c' hc'
    ext m x
    obtain ⟨n, rfl⟩ := q_surj x
    exact (hc'.1 m n).trans (d_spec m n).symm

/-- Linearity for an outer ring passes to the descended balanced map. -/
theorem balanced_cokernel_descent_outer_linear
    {S : Type u} [Ring S] [Module S M] [Module S D]
    (q : N →ₗ[R] Q) (q_surj : Function.Surjective q)
    (b : M →+ (N →+ D)) (c : M →+ (Q →+ D))
    (factor : ∀ m n, c m (q n) = b m n)
    (outer_linear : ∀ (s : S) (m : M) (n : N), b (s • m) n = s • b m n) :
    ∀ (s : S) (m : M) (x : Q), c (s • m) x = s • c m x := by
  intro s m x
  obtain ⟨n, rfl⟩ := q_surj x
  rw [factor, factor, outer_linear]

#print axioms balanced_cokernel_descent
#print axioms balanced_cokernel_descent_outer_linear

end WattsFoundation
