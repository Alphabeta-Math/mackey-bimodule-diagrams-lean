import Calculation

set_option maxHeartbeats 200000

universe u

open MackeyDiagrams in
theorem RightUpCurlSupport.eval_trivalent {U : Type u} [Group U] {K H G : Subgroup U}
    (a : ConjEmbedding H G) (d : ConjEmbedding K H) (finite : d.toHom.range.FiniteIndex) :
    let lower := LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.upToUpDown a d finite)
    let upper := LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.upDownToUp a d)
    let straight := LabelledDrawing.ordinary (Diagram.id (R := Complex) (Word.up a))
    (lower.vertical upper).interpret.eval =
      (straight.scale (d.toHom.range.index : Complex)).interpret.eval :=
  RightUpCurlSupport.calculation a d finite

#print axioms RightUpCurlSupport.eval_trivalent
