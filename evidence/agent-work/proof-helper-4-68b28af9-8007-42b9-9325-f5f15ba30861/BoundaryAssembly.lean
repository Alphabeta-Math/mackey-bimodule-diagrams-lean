import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
import Proofs.CaseTwoLeftProjectionConstruction
import Mathlib.GroupTheory.SemidirectProduct

namespace CaseTwoAudit

open MackeyDiagrams

section BoundaryComposition

variable {V : Type*} [Group V] {K H : Subgroup V}
variable {R : Type*} [CommSemiring R]
variable {p q r s : Word K H}

theorem atBoundary_eval_vertical (d : ScopedDiagram R p q) (e : ScopedDiagram R q r) :
    (ScopedDiagram.vertical d e).atBoundary.eval =
      d.atBoundary.eval.vertical e.atBoundary.eval := by
  change (p.reorderFromBoundary (R := R)).eval.vertical
      (d.eval.vertical (e.eval.vertical (r.reorderToBoundary (R := R)).eval)) =
    ((p.reorderFromBoundary (R := R)).eval.vertical
      (d.eval.vertical (q.reorderToBoundary (R := R)).eval)).vertical
    ((q.reorderFromBoundary (R := R)).eval.vertical
      (e.eval.vertical (r.reorderToBoundary (R := R)).eval))
  have hcancel : (q.reorderToBoundary (R := R)).eval.vertical q.reorderFromBoundary.eval =
      Biset.Hom.id q.basis := Word.eval_reorderToFrom q
  simp only [Biset.Hom.vertical_assoc]
  rw [← Biset.Hom.vertical_assoc (q.reorderToBoundary (R := R)).eval,
    hcancel, Biset.Hom.id_vertical]

theorem atBoundary_eval_stack (d₁ : ScopedDiagram R p q) (d₂ : ScopedDiagram R q r)
    (d₃ : ScopedDiagram R r s) :
    (ScopedDiagram.vertical d₁ (ScopedDiagram.vertical d₂ d₃)).atBoundary.eval =
      d₁.atBoundary.eval.vertical (d₂.atBoundary.eval.vertical d₃.atBoundary.eval) := by
  rw [atBoundary_eval_vertical, atBoundary_eval_vertical]

theorem cut_eval_atBoundary {d : ScopedDiagram R p s}
    {d₁ : ScopedDiagram R p q} {d₂ : ScopedDiagram R q r} {d₃ : ScopedDiagram R r s}
    (h : d.eval = d₁.eval.vertical (d₂.eval.vertical d₃.eval)) :
    d.atBoundary.eval =
      d₁.atBoundary.eval.vertical (d₂.atBoundary.eval.vertical d₃.atBoundary.eval) := by
  have h' : d.eval = (ScopedDiagram.vertical d₁ (ScopedDiagram.vertical d₂ d₃)).eval := h
  exact ((ScopedDiagram.eval_atBoundary_eq_iff _ _).mpr h').trans
    (atBoundary_eval_stack d₁ d₂ d₃)

def reindexBoundaryHom {a b a' b' : Boundary K H}
    (ha : a = a') (hb : b = b') (f : Biset.Hom R a.word.basis b.word.basis) :
    Biset.Hom R a'.word.basis b'.word.basis := by
  subst a'
  subst b'
  exact f

theorem reindexBoundaryHom_vertical {a b c a' b' c' : Boundary K H}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (f : Biset.Hom R a.word.basis b.word.basis) (g : Biset.Hom R b.word.basis c.word.basis) :
    reindexBoundaryHom ha hc (f.vertical g) =
      (reindexBoundaryHom ha hb f).vertical (reindexBoundaryHom hb hc g) := by
  subst a'
  subst b'
  subst c'
  rfl

theorem eval_planarAtBoundary {a b : Boundary K H} {shape : PlanarShape}
    (replacement : LabelledDrawing.PlanarAtBoundary R a b shape) :
    replacement.interpret.eval = reindexBoundaryHom replacement.bottom_eq replacement.top_eq
      replacement.diagram.interpret.atBoundary.eval := by
  obtain ⟨bottom, top, drawing, hb, ht, hs⟩ := replacement
  subst a
  subst b
  rfl

theorem combine_cut_stage_equalities
    {p' q' r' s' : Word K H}
    {d : ScopedDiagram R p s}
    {d₁ : ScopedDiagram R p q} {d₂ : ScopedDiagram R q r} {d₃ : ScopedDiagram R r s}
    {e₁ : ScopedDiagram R p' q'} {e₂ : ScopedDiagram R q' r'} {e₃ : ScopedDiagram R r' s'}
    (hp : p.boundary = p'.boundary) (hq : q.boundary = q'.boundary)
    (hr : r.boundary = r'.boundary) (hs : s.boundary = s'.boundary)
    (h : d.eval = d₁.eval.vertical (d₂.eval.vertical d₃.eval))
    (h₁ : reindexBoundaryHom hp hq d₁.atBoundary.eval = e₁.atBoundary.eval)
    (h₂ : reindexBoundaryHom hq hr d₂.atBoundary.eval = e₂.atBoundary.eval)
    (h₃ : reindexBoundaryHom hr hs d₃.atBoundary.eval = e₃.atBoundary.eval) :
    reindexBoundaryHom hp hs d.atBoundary.eval =
      (ScopedDiagram.vertical e₁ (ScopedDiagram.vertical e₂ e₃)).atBoundary.eval := by
  rw [cut_eval_atBoundary h, reindexBoundaryHom_vertical hp hq hs,
    reindexBoundaryHom_vertical hq hr hs, h₁, h₂, h₃, atBoundary_eval_stack]

end BoundaryComposition
end CaseTwoAudit

#print axioms CaseTwoAudit.combine_cut_stage_equalities
#print axioms CaseTwoAudit.eval_planarAtBoundary
