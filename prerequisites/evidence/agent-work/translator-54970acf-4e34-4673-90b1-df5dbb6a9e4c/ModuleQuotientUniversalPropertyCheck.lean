import Mathlib.LinearAlgebra.Quotient.Basic

theorem ModuleQuotientUniversalProperty :
  ∀ (R : Type _) [Ring R] (M : Type _) [AddCommGroup M] [Module R M]
  (U : Submodule R M),
  (∀ m n : M, Submodule.mkQ U m + Submodule.mkQ U n = Submodule.mkQ U (m + n)) ∧
  (∀ (r : R) (m : M), r • Submodule.mkQ U m = Submodule.mkQ U (r • m)) ∧
  Function.Surjective (⇑(Submodule.mkQ U)) ∧
  (∀ (N : Type _) [AddCommGroup N] [Module R N] (f : LinearMap (RingHom.id R) M N),
    U ≤ LinearMap.ker f →
      ExistsUnique (fun g : LinearMap (RingHom.id R) (HasQuotient.Quotient M U) N =>
        LinearMap.comp g (Submodule.mkQ U) = f)) := by
  intro R _ M _ _ U
  refine ⟨?_, ?_, Submodule.mkQ_surjective U, ?_⟩
  · intro m n
    exact (Submodule.Quotient.mk_add (p := U) (x := m) (y := n)).symm
  · intro r m
    exact (Submodule.Quotient.mk_smul (p := U) r m).symm
  · intro N _ _ f h
    refine ⟨Submodule.liftQ U f h, Submodule.liftQ_mkQ U f h, ?_⟩
    intro g hg
    exact Submodule.linearMap_qext U (hg.trans (Submodule.liftQ_mkQ U f h).symm)

#print axioms ModuleQuotientUniversalProperty
