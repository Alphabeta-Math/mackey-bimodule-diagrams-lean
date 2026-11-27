import Mathlib.LinearAlgebra.Quotient.Basic

set_option pp.universes true in
#check (
∀ (R : Type _) [Ring R] (M : Type _) [AddCommGroup M] [Module R M]
  (U : Submodule R M),
  (∀ m n : M, Submodule.mkQ U m + Submodule.mkQ U n = Submodule.mkQ U (m + n)) ∧
  (∀ (r : R) (m : M), r • Submodule.mkQ U m = Submodule.mkQ U (r • m)) ∧
  Function.Surjective (⇑(Submodule.mkQ U)) ∧
  (∀ (N : Type _) [AddCommGroup N] [Module R N] (f : LinearMap (RingHom.id R) M N),
    U ≤ LinearMap.ker f →
      ExistsUnique (fun g : LinearMap (RingHom.id R) (HasQuotient.Quotient M U) N =>
        LinearMap.comp g (Submodule.mkQ U) = f))
)
