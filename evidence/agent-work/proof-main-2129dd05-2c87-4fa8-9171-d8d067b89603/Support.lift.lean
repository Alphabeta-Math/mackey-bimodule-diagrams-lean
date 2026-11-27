open MackeyDiagrams

namespace MultipliersUnderRelabellingProof

variable {U : Type*} [Group U] {H K : Subgroup U}

private noncomputable abbrev dotValue {a b : ConjEmbedding H K} (label : DotLabel Complex a b) :
    MonoidAlgebra Complex K :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element label)

private theorem dotValue_identity (a : ConjEmbedding H K) :
    dotValue (DotLabel.identity (R := Complex) a) = 1 := by
  simp only [dotValue, DotLabel.identity, Finsupp.mapDomain_single]
  rfl

private theorem dotElement_injective {a b : ConjEmbedding H K} :
    Function.Injective (Dot.element (a := a) (b := b)) :=
  fun _ _ h => Dot.ext h

private noncomputable def liftMultiplier {a b : ConjEmbedding H K}
    (m : MonoidAlgebra Complex K) : DotLabel Complex a b :=
  Finsupp.comapDomain Dot.element m.coeff dotElement_injective.injOn

private theorem liftMultiplier_value {a b : ConjEmbedding H K}
    (m : MonoidAlgebra Complex K)
    (eligible : ∀ p ∈ m.coeff.support, ∀ f : H,
      a.toHom f * p = p * b.toHom f) :
    dotValue (liftMultiplier (a := a) (b := b) m) = m := by
  have inRange : (↑m.coeff.support : Set K) ⊆ Set.range (Dot.element (a := a) (b := b)) := by
    intro p hp
    exact ⟨⟨p, eligible p hp⟩, rfl⟩
  exact congrArg MonoidAlgebra.ofCoeff
    (Finsupp.mapDomain_comapDomain Dot.element dotElement_injective m.coeff inRange)

end MultipliersUnderRelabellingProof

open MultipliersUnderRelabellingProof
