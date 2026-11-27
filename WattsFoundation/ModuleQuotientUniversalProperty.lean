import Mathlib.LinearAlgebra.Quotient.Basic
import MackeyDiagrams
import WattsFoundation.ConcreteTensorBimoduleMap
import WattsFoundation.WattsMathlibReverse
import WattsFoundation.General.OriginalBimoduleAdapter
import WattsFoundation.ClassicalReconstruction

set_option maxHeartbeats 2000000

theorem ModuleQuotientUniversalProperty : (
∀ (R : Type _) [Ring R] (M : Type _) [AddCommGroup M] [Module R M]
  (U : Submodule R M),
  (∀ m n : M, Submodule.mkQ U m + Submodule.mkQ U n = Submodule.mkQ U (m + n)) ∧
  (∀ (r : R) (m : M), r • Submodule.mkQ U m = Submodule.mkQ U (r • m)) ∧
  Function.Surjective (⇑(Submodule.mkQ U)) ∧
  (∀ (N : Type _) [AddCommGroup N] [Module R N] (f : LinearMap (RingHom.id R) M N),
    U ≤ LinearMap.ker f →
      ExistsUnique (fun g : LinearMap (RingHom.id R) (HasQuotient.Quotient M U) N =>
        LinearMap.comp g (Submodule.mkQ U) = f))
) :=
(by
  intro R _ M _ _ U
  refine ⟨fun m n => (map_add U.mkQ m n).symm,
    fun r m => (U.mkQ.map_smul r m).symm, U.mkQ_surjective, ?_⟩
  intro N _ _ f hf
  refine ⟨U.liftQ f hf, U.liftQ_mkQ f hf, ?_⟩
  intro g hg
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := U.mkQ_surjective q
  exact (DFunLike.congr_fun hg m).trans (DFunLike.congr_fun (U.liftQ_mkQ f hf) m).symm
)
