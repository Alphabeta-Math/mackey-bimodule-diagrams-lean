import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Coset.Basic
import MackeyDiagrams

set_option maxHeartbeats 2000000

theorem ConjugationEmbeddingCentralizerCoset : (∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
  (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
  (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  MonoidAlgebra.mapDomainAlgHom Complex Complex
      (MackeyDiagrams.ConjEmbedding.ofConjugator α hα).toHom =
    MonoidAlgebra.mapDomainAlgHom Complex Complex
      (MackeyDiagrams.ConjEmbedding.ofConjugator β hβ).toHom ↔
  LeftCosetEquivalence (Subgroup.centralizer (H : Set U) : Set U) α β) :=
(by
  intro U _ H G α β hα hβ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  change MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom =
    MonoidAlgebra.mapDomainAlgHom Complex Complex b.toHom ↔
      LeftCosetEquivalence (Subgroup.centralizer (H : Set U) : Set U) α β
  have coset : a = b ↔ LeftCosetEquivalence (Subgroup.centralizer (H : Set U) : Set U) α β :=
    (MackeyDiagrams.ConjEmbedding.ofConjugator_eq_iff α β hα hβ).trans
      (leftCoset_eq_iff (Subgroup.centralizer (H : Set U))).symm
  constructor
  · intro eq
    apply coset.mp
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro h
    have coeffEq := congrArg (fun f :
        MonoidAlgebra Complex H →ₐ[Complex] MonoidAlgebra Complex G =>
      (f (MonoidAlgebra.single h 1)).coeff) eq
    change (MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single h 1)).coeff =
      (MonoidAlgebra.mapDomain b.toHom (MonoidAlgebra.single h 1)).coeff at coeffEq
    rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single] at coeffEq
    exact Finsupp.single_left_injective (one_ne_zero : (1 : Complex) ≠ 0) coeffEq
  · intro eq
    rw [coset.mpr eq])
