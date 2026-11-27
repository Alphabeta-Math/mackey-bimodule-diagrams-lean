import NotesProofs.WattsMathlibReverse

/-! Both object-level directions of Eilenberg–Watts over arbitrary unital
rings, expressed with Mathlib's preservation typeclasses. -/

namespace NotesProofs

universe u
open CategoryTheory CategoryTheory.Limits

variable {R S : Type u} [Ring R] [Ring S]

/-- Tensoring with a bimodule is additive, preserves finite colimits, and
preserves all coproducts in the indicated universe. -/
theorem tensorFunctor_good (M : Type u) [AddCommGroup M] [Module (MulOpposite R) M]
    [Module S M] [SMulCommClass (MulOpposite R) S M] :
    (concreteTensorFunctor (R := R) (S := S) M).Additive ∧
    PreservesFiniteColimits (concreteTensorFunctor (R := R) (S := S) M) ∧
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (concreteTensorFunctor (R := R) (S := S) M) := by
  let T := concreteTensorFunctor (R := R) (S := S) M
  refine ⟨inferInstance, ?_, ?_⟩
  · exact mathlibFiniteColimits_of_watts T (concreteTensorFunctor_preservesCokernels M)
  · intro I
    exact mathlibCoproducts_of_watts T (concreteTensorFunctor_preservesCoproducts M) I

/-- An additive functor with Mathlib's preservation hypotheses is naturally
isomorphic to the concrete tensor functor attached to its regular value. -/
noncomputable def eilenbergWattsIso
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [PreservesFiniteColimits F]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) F] :
    ChoiceFreeWatts.tensorFunctor F ≅ F :=
  wattsNaturalIsoOfMathlib F

#print axioms tensorFunctor_good
#print axioms eilenbergWattsIso

end NotesProofs
