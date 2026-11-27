import MackeyDiagrams.Linear

/-!
# Universal property of horizontal composition

Balancing for the group elements is enough for the group algebra because
its elements are finite linear combinations of those group elements.
-/

namespace MackeyDiagrams.Biset

universe u v
noncomputable section

variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {R : Type v} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
variable {X : Biset K H} {Y : Biset H J}

def IsBalanced (f : (X.carrier →₀ R) →ₗ[R] (Y.carrier →₀ R) →ₗ[R] M) : Prop :=
  ∀ (h : H) (x : X.carrier →₀ R) (y : Y.carrier →₀ R),
    f (X.actLinear R (1,h) x) (Y.actLinear R (h,1) y) = f x y

private def liftBalancedBasis (f : (X.carrier →₀ R) →ₗ[R] (Y.carrier →₀ R) →ₗ[R] M)
    (hf : IsBalanced f) : (X.tensor Y).carrier → M :=
  Quotient.lift (fun (z : X.carrier × Y.carrier) =>
    f (Finsupp.single z.1 1) (Finsupp.single z.2 1)) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    rw [← hx, ← hy, ← X.actLinear_single R (1,h), ← Y.actLinear_single R (h,1)]
    exact (hf h _ _).symm)

def liftBalanced (f : (X.carrier →₀ R) →ₗ[R] (Y.carrier →₀ R) →ₗ[R] M)
    (hf : IsBalanced f) : ((X.tensor Y).carrier →₀ R) →ₗ[R] M :=
  freeLift R (liftBalancedBasis f hf)

@[simp] theorem liftBalanced_single (f : (X.carrier →₀ R) →ₗ[R] (Y.carrier →₀ R) →ₗ[R] M)
    (hf : IsBalanced f) (x : X.carrier) (y : Y.carrier) (r : R) :
    liftBalanced f hf (Finsupp.single (X.pair Y x y) r) =
      r • f (Finsupp.single x 1) (Finsupp.single y 1) := by
  exact freeLift_single R (liftBalancedBasis f hf) (X.pair Y x y) r

theorem liftBalanced_pairLinear (f : (X.carrier →₀ R) →ₗ[R] (Y.carrier →₀ R) →ₗ[R] M)
    (hf : IsBalanced f) (x : X.carrier →₀ R) (y : Y.carrier →₀ R) :
    liftBalanced f hf (pairLinear R X Y x y) = f x y := by
  have outer :
      (liftBalanced f hf).comp ((pairLinear R X Y).flip y) = f.flip y := by
    apply Finsupp.lhom_ext
    intro a r
    have inner :
        (liftBalanced f hf).comp (pairLinear R X Y (Finsupp.single a r)) =
          f (Finsupp.single a r) := by
      apply Finsupp.lhom_ext
      intro b s
      rw [LinearMap.comp_apply, pairLinear_single, liftBalanced_single]
      have hr : Finsupp.single a r = r • Finsupp.single a (1 : R) := by
        simp [Finsupp.smul_single, smul_eq_mul]
      have hs : Finsupp.single b s = s • Finsupp.single b (1 : R) := by
        simp [Finsupp.smul_single, smul_eq_mul]
      conv_rhs => rw [hr, hs]
      simp only [map_smul, LinearMap.smul_apply, ← mul_smul]
      rw [mul_comm]
    exact LinearMap.congr_fun inner y
  exact LinearMap.congr_fun outer x

theorem liftBalanced_unique (f : (X.carrier →₀ R) →ₗ[R] (Y.carrier →₀ R) →ₗ[R] M)
    (hf : IsBalanced f) (g : ((X.tensor Y).carrier →₀ R) →ₗ[R] M)
    (hg : ∀ x y, g (pairLinear R X Y x y) = f x y) : g = liftBalanced f hf := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun p => ?_)
  rcases p with ⟨x,y⟩
  change g (Finsupp.single (X.pair Y x y) r) =
    liftBalanced f hf (Finsupp.single (X.pair Y x y) r)
  have heq := hg (Finsupp.single x 1) (Finsupp.single y 1)
  rw [pairLinear_single, mul_one] at heq
  rw [liftBalanced_single, ← heq, ← g.map_smul]
  simp [Finsupp.smul_single, smul_eq_mul]

end
end MackeyDiagrams.Biset

