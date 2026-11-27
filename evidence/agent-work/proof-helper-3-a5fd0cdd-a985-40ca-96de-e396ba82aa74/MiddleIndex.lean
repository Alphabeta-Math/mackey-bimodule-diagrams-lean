import Proofs.EvaluationForTwoProjections

namespace MackeyDiagrams.CaseOneLocal
open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {G A B C : Subgroup U}

/-- The first conjunct of the registered two-projection theorem specializes
to the middle vertex by making the adjacent up strands identities. -/
private theorem middleProjection_hasFiniteIndex
    (a : ConjEmbedding G A) (j : ConjEmbedding B A)
    (d : ConjEmbedding C G) (v : ConjEmbedding C B)
    (t : ProjectionDot.Mixed a j d v) :
    ((a.comp d).toHom.range.subgroupOf
      (a.toHom.range ⊓ Subgroup.map (MulAut.conj t.dot.element).toMonoidHom j.toHom.range)).FiniteIndex := by
  have h := (EvaluationForTwoProjections a j (ConjEmbedding.id B) d (ConjEmbedding.id C) v).1 t.dot
  exact h.2.1.mp t.finite

#print axioms middleProjection_hasFiniteIndex
end MackeyDiagrams.CaseOneLocal
