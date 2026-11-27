import Mathlib.Algebra.Module.LinearMap.Basic

/-! A diagram chase for transferring a cokernel presentation across a natural
comparison. This is the algebraic step used after the free cases of an
Eilenberg–Watts comparison have been established. -/

namespace NotesProofs

universe u v

variable {R : Type u} [Ring R]
variable {L P X L' P' X' : Type v}
variable [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]
variable [AddCommGroup X] [Module R X] [AddCommGroup L'] [Module R L']
variable [AddCommGroup P'] [Module R P'] [AddCommGroup X'] [Module R X']

/-- The comparison on cokernels is bijective when it is surjective on
relations and bijective on generators. The bottom presentation is exact at
its middle term; the top composite vanishes. -/
theorem presentation_comparison_bijective
    (f : L →ₗ[R] P) (q : P →ₗ[R] X)
    (f' : L' →ₗ[R] P') (q' : P' →ₗ[R] X')
    (a : L →ₗ[R] L') (b : P →ₗ[R] P') (c : X →ₗ[R] X')
    (comm_f : ∀ l, b (f l) = f' (a l))
    (comm_q : ∀ p, c (q p) = q' (b p))
    (zero_fq : ∀ l, q (f l) = 0)
    (exact' : ∀ p', q' p' = 0 → ∃ l', f' l' = p')
    (q_surj : Function.Surjective q) (q'_surj : Function.Surjective q')
    (a_surj : Function.Surjective a) (b_bij : Function.Bijective b) :
    Function.Bijective c := by
  constructor
  · intro x y hxy
    obtain ⟨p, rfl⟩ := q_surj x
    obtain ⟨t, rfl⟩ := q_surj y
    have hz : q' (b (p - t)) = 0 := by
      rw [map_sub, map_sub, ← comm_q, ← comm_q, hxy, sub_self]
    obtain ⟨l', hl'⟩ := exact' _ hz
    obtain ⟨l, rfl⟩ := a_surj l'
    have hp : p - t = f l := b_bij.1 (by rw [comm_f, hl'])
    have hq := congrArg q hp
    rw [map_sub, zero_fq] at hq
    exact sub_eq_zero.mp hq
  · intro x'
    obtain ⟨p', rfl⟩ := q'_surj x'
    obtain ⟨p, rfl⟩ := b_bij.2 p'
    exact ⟨q p, comm_q p⟩

#print axioms presentation_comparison_bijective

end NotesProofs
