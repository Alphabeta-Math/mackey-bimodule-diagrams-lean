import NotesProofs.CokernelExact
import NotesProofs.PresentationFiveLemma

namespace NotesProofs

universe u v

variable {R : Type u} [Ring R]
variable {L P X L' P' X' : Type v}
variable [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]
variable [AddCommGroup X] [Module R X] [AddCommGroup L'] [Module R L']
variable [AddCommGroup P'] [Module R P'] [AddCommGroup X'] [Module R X']

/-- A comparison between module presentations is bijective when the lower
map has the cokernel factorization property, and the comparisons on the free
terms have the indicated surjectivity and bijectivity properties. -/
theorem presentation_comparison_of_cokernel
    (f : L →ₗ[R] P) (q : P →ₗ[R] X)
    (f' : L' →ₗ[R] P') (q' : P' →ₗ[R] X')
    (a : L →ₗ[R] L') (b : P →ₗ[R] P') (c : X →ₗ[R] X')
    (comm_f : ∀ l, b (f l) = f' (a l))
    (comm_q : ∀ p, c (q p) = q' (b p))
    (zero_fq : ∀ l, q (f l) = 0)
    (factor' : ∀ (Z : Type v) [AddCommGroup Z] [Module R Z] (g : P' →ₗ[R] Z),
      (∀ l, g (f' l) = 0) → ∃ h : X' →ₗ[R] Z, ∀ p, h (q' p) = g p)
    (q_surj : Function.Surjective q) (q'_surj : Function.Surjective q')
    (a_surj : Function.Surjective a) (b_bij : Function.Bijective b) :
    Function.Bijective c :=
  presentation_comparison_bijective f q f' q' a b c comm_f comm_q zero_fq
    (cokernel_universal_exact f' q' factor') q_surj q'_surj a_surj b_bij

/-- The same comparison criterion expressed with categorical cancellation
for both quotient maps. -/
theorem presentation_comparison_of_cokernels
    (f : L →ₗ[R] P) (q : P →ₗ[R] X)
    (f' : L' →ₗ[R] P') (q' : P' →ₗ[R] X')
    (a : L →ₗ[R] L') (b : P →ₗ[R] P') (c : X →ₗ[R] X')
    (comm_f : ∀ l, b (f l) = f' (a l))
    (comm_q : ∀ p, c (q p) = q' (b p))
    (zero_fq : ∀ l, q (f l) = 0)
    (factor' : ∀ (Z : Type v) [AddCommGroup Z] [Module R Z] (g : P' →ₗ[R] Z),
      (∀ l, g (f' l) = 0) → ∃ h : X' →ₗ[R] Z, ∀ p, h (q' p) = g p)
    (cancel : ∀ (Z : Type v) [AddCommGroup Z] [Module R Z] (h k : X →ₗ[R] Z),
      (∀ p, h (q p) = k (q p)) → h = k)
    (cancel' : ∀ (Z : Type v) [AddCommGroup Z] [Module R Z] (h k : X' →ₗ[R] Z),
      (∀ p, h (q' p) = k (q' p)) → h = k)
    (a_surj : Function.Surjective a) (b_bij : Function.Bijective b) :
    Function.Bijective c :=
  presentation_comparison_of_cokernel f q f' q' a b c comm_f comm_q zero_fq factor'
    (epi_universal_surjective q cancel) (epi_universal_surjective q' cancel') a_surj b_bij

#print axioms presentation_comparison_of_cokernel
#print axioms presentation_comparison_of_cokernels

end NotesProofs
