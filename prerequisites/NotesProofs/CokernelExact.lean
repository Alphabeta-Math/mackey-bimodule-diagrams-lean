import Mathlib.LinearAlgebra.Quotient.Basic

/-! The universal property of a module cokernel implies the elementwise
exactness required by the presentation comparison lemma. -/

namespace NotesProofs

universe u v

variable {R : Type u} [Ring R]
variable {L P X : Type v}
variable [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]
variable [AddCommGroup X] [Module R X]

theorem cokernel_universal_exact (f : L →ₗ[R] P) (q : P →ₗ[R] X)
    (factor : ∀ (Z : Type v) [AddCommGroup Z] [Module R Z] (g : P →ₗ[R] Z),
      (∀ l, g (f l) = 0) → ∃ h : X →ₗ[R] Z, ∀ p, h (q p) = g p) :
    ∀ p, q p = 0 → ∃ l, f l = p := by
  let S := LinearMap.range f
  obtain ⟨h, hh⟩ := factor (P ⧸ S) S.mkQ (by
    intro l
    change (LinearMap.range f).mkQ (f l) = 0
    exact DFunLike.congr_fun (LinearMap.range_mkQ_comp f) l)
  intro p hp
  have hp' : S.mkQ p = 0 := by rw [← hh p, hp, map_zero]
  have hm : p ∈ S := by
    rw [← Submodule.ker_mkQ S]
    exact hp'
  exact hm

/-- Categorical right-cancellation for a module map implies surjectivity.
Only cancellation into its range quotient is needed. -/
theorem epi_universal_surjective (q : P →ₗ[R] X)
    (cancel : ∀ (Z : Type v) [AddCommGroup Z] [Module R Z] (h k : X →ₗ[R] Z),
      (∀ p, h (q p) = k (q p)) → h = k) : Function.Surjective q := by
  have hrange : LinearMap.range q = ⊤ :=
    LinearMap.range_eq_top_of_cancel (fun h k hcomp =>
      cancel _ h k (fun p => DFunLike.congr_fun hcomp p))
  exact LinearMap.range_eq_top.mp hrange

/-- A map with the cokernel universal property is surjective. -/
theorem cokernel_factorization_surjective (f : L →ₗ[R] P) (q : P →ₗ[R] X)
    (zero : ∀ l, q (f l) = 0)
    (factor : ∀ (Z : Type v) [AddCommGroup Z] [Module R Z] (g : P →ₗ[R] Z),
      (∀ l, g (f l) = 0) → ∃! h : X →ₗ[R] Z, ∀ p, h (q p) = g p) :
    Function.Surjective q := by
  apply epi_universal_surjective q
  intro Z _ _ h k eq
  let g : P →ₗ[R] Z := h.comp q
  have hg : ∀ l, g (f l) = 0 := by
    intro l
    change h (q (f l)) = 0
    rw [zero, map_zero]
  obtain ⟨d, hd, unique⟩ := factor Z g hg
  have hh : ∀ p, h (q p) = g p := by intro p; rfl
  have hk : ∀ p, k (q p) = g p := by intro p; exact (eq p).symm
  exact (unique h hh).trans (unique k hk).symm

#print axioms cokernel_factorization_surjective
#print axioms cokernel_universal_exact
#print axioms epi_universal_surjective

end NotesProofs
