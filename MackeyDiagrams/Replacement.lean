import MackeyDiagrams.ScopedCup
import MackeyDiagrams.BoundaryEvaluation

/-! For fixed boundary words, a diagram shape has a family of valid labellings.
The shape determines the labelling type. Its interpretation is a typed diagram. -/

namespace MackeyDiagrams.ScopedDiagram

universe u v w t

section

variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R] {p q : Word K H}

/-- Place the same typed diagram between ordered boundary words. -/
def atBoundary (d : ScopedDiagram R p q) : ScopedDiagram R p.boundary.word q.boundary.word :=
  .vertical (.ordinary p.reorderFromBoundary)
    (.vertical d (.ordinary q.reorderToBoundary))

theorem eval_atBoundary_eq_iff (d e : ScopedDiagram R p q) :
    d.atBoundary.eval = e.atBoundary.eval ↔ d.eval = e.eval := by
  constructor
  · intro h
    let toP := (p.reorderToBoundary (R := R)).eval
    let fromQ := (q.reorderFromBoundary (R := R)).eval
    have cancel (f : ScopedDiagram R p q) :
        (toP.vertical f.atBoundary.eval).vertical fromQ = f.eval := by
      change (toP.vertical ((p.reorderFromBoundary (R := R)).eval.vertical
        (f.eval.vertical (q.reorderToBoundary (R := R)).eval))).vertical fromQ = f.eval
      have hp : toP.vertical (p.reorderFromBoundary (R := R)).eval = Biset.Hom.id p.basis :=
        Word.eval_reorderToFrom p
      have hq : (q.reorderToBoundary (R := R)).eval.vertical fromQ = Biset.Hom.id q.basis :=
        Word.eval_reorderToFrom q
      rw [← Biset.Hom.vertical_assoc toP, hp, Biset.Hom.id_vertical,
        Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]
    exact (cancel d).symm.trans ((congrArg (fun x => (toP.vertical x).vertical fromQ) h).trans (cancel e))
  · intro h
    change (p.reorderFromBoundary (R := R)).eval.vertical
        (d.eval.vertical (q.reorderToBoundary (R := R)).eval) =
      (p.reorderFromBoundary (R := R)).eval.vertical
        (e.eval.vertical (q.reorderToBoundary (R := R)).eval)
    rw [h]

end

section

variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R] {p q : Word K H}
variable {Shape : Type w} {Labelling : Shape → Type t}
variable (diagram : ∀ s : Shape, Labelling s → ScopedDiagram R p q)

/-- The maps produced by all valid labellings of this shape at the fixed boundary. -/
noncomputable def attainable (s : Shape) : Set (Biset.Hom R p.basis q.basis) :=
  Set.range fun label => (diagram s label).eval

/-- Every labelling of the first shape can be replaced by some labelling of the second. -/
def Replaces (s t : Shape) : Prop :=
  ∀ a : Labelling s, ∃ b : Labelling t, (diagram s a).eval = (diagram t b).eval

theorem replaces_iff_attainable_subset (s t : Shape) :
    Replaces diagram s t ↔ attainable diagram s ⊆ attainable diagram t := by
  change (∀ a : Labelling s, ∃ b : Labelling t, (diagram s a).eval = (diagram t b).eval) ↔
    Set.range (fun a => (diagram s a).eval) ⊆ Set.range (fun b => (diagram t b).eval)
  constructor
  · rintro h _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := h a
    exact ⟨b, hb.symm⟩
  · intro h a
    obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
    exact ⟨b, hb.symm⟩

theorem replaces_refl (s : Shape) : Replaces diagram s s :=
  fun a => ⟨a, rfl⟩

theorem replaces_trans {s t w : Shape}
    (h : Replaces diagram s t) (k : Replaces diagram t w) : Replaces diagram s w := by
  intro a
  obtain ⟨b, hb⟩ := h a
  obtain ⟨c, hc⟩ := k b
  exact ⟨c, hb.trans hc⟩

end

end MackeyDiagrams.ScopedDiagram
