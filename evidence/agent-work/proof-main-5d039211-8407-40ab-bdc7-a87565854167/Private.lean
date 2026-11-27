import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
open Lean Elab Tactic
open MackeyDiagrams
example {U : Type*} [Group U] {K H P L : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (d : ConjEmbedding L K) (e : ConjEmbedding L H)
    (p : Dot (a.comp d) (b.comp e)) :
    (∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b d e p w = z}) ↔
      ((a.comp d).toHom.range.subgroupOf (a.toHom.range ⊓
        Subgroup.map (MulAut.conj p.element).toMonoidHom b.toHom.range)).FiniteIndex := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "index_formula"
    evalTactic (← `(tactic| exact ($(mkIdent n) $(mkIdent `a) $(mkIdent `b) $(mkIdent `d) $(mkIdent `e) $(mkIdent `p)).1))

private noncomputable def indexAlias := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "index_formula"
    evalTactic (← `(tactic| exact @$(mkIdent n)))
#check indexAlias
