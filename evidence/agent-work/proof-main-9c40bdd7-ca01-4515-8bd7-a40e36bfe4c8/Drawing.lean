import Structural
import Geo

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

universe u
variable {V : Type u} [Group V] {A B : Subgroup V} {w t : Word A B}

theorem SupportRule.reject {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {events : Code} (hne : events ≠ []) (hn : ∀ j, events.head? ≠ some (.vertex j .mixedProjection)) :
    SupportRule f events :=
  ⟨fun he => False.elim (hne he), fun j hj => False.elim (hn j hj)⟩

theorem reject_head {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {events : Code} {e : PlanarEvent}
    (he : events.head? = some e) (hn : ∀ j, e ≠ .vertex j .mixedProjection) :
    SupportRule f events := by
  apply SupportRule.reject
  · intro h
    rw [h] at he
    cases he
  · intro j h
    exact hn j (Option.some.inj (he.symm.trans h))

theorem support_diagram (d : Diagram Complex w t) : SupportRule d.eval (geoInfo d.drawing).events := by
  induction d with
  | id p => exact .structural (preserve_id p)
  | leftUnit p => exact .structural (preserve_leftUnit p)
  | rightUnit p => exact .structural (preserve_rightUnit p)
  | insertLeftUnit p => exact .structural (preserve_insertLeftUnit p)
  | insertRightUnit p => exact .structural (preserve_insertRightUnit p)
  | associate p q r => exact .structural (preserve_associate p q r)
  | unassociate p q r => exact .structural (preserve_unassociate p q r)
  | mixedProjection a b l r s hf => exact .projection (support_projection a b l r ⟨s, hf⟩)
  | vertical d e hd he =>
    change SupportRule (d.eval.vertical e.eval) (geoInfo (d.drawing.stack e.drawing)).events
    rw [(sized_seq (sized_diagram d) (sized_diagram e)).2]
    exact support_seq hd he
  | horizontal d e hd he =>
    have h := sized_diagram d
    rw [show geoInfo (Diagram.horizontal d e).drawing = _ from (sized_par h (sized_diagram e)).2]
    simpa only [Diagram.eval, LabelledDrawing.interpret, ScopedDiagram.eval, ShapeInfo.par, h.2.2] using support_par hd he
  | _ => exact SupportRule.other (fun j h => by cases h)

theorem support_drawing (d : LabelledDrawing Complex w t) :
    SupportRule d.interpret.eval (geoInfo d.erase).events := by
  induction d with
  | ordinary d => exact support_diagram d
  | trivalent v => cases v <;> exact SupportRule.other (fun j h => by cases h)
  | bentVertex v => cases v <;> exact SupportRule.other (fun j h => by cases h)
  | parallelUpChain _ _ _ _ ls =>
    exact reject_head (parallel_chain_width ls.length).2.2 (fun j h => by cases h)
  | parallelDownChain _ _ _ _ ls =>
    exact reject_head (down_chain_width ls.length).2.2 (fun j h => by cases h)
  | expandedProjection _ _ _ _ _ o c =>
    exact .reject (expanded_info 1 o c).2.2.1 (expanded_info 1 o c).2.2.2
  | expandedProjectionChain _ _ _ _ ls _ o c =>
    exact .reject (expanded_info ls.length o c).2.2.1 (expanded_info ls.length o c).2.2.2
  | expandedLinearDotProjection _ _ _ _ ls _ o c =>
    exact .reject (expanded_info ls.length o c).2.2.1 (expanded_info ls.length o c).2.2.2
  | compactProjection a b l r ss => exact .projection (support_projections a b l r ss)
  | vertical d e hd he =>
    change SupportRule (d.interpret.eval.vertical e.interpret.eval) (geoInfo (d.erase.stack e.erase)).events
    rw [(sized_seq (sized_drawing d) (sized_drawing e)).2]
    exact support_seq hd he
  | horizontal d e hd he =>
    have h := sized_drawing d
    rw [show geoInfo (LabelledDrawing.horizontal d e).erase = _ from (sized_par h (sized_drawing e)).2]
    simpa only [Diagram.eval, LabelledDrawing.interpret, ScopedDiagram.eval, ShapeInfo.par, h.2.2] using support_par hd he
  | _ => exact SupportRule.other (fun j h => by cases h)

theorem support_atBoundary {b t : Boundary A B} {s : PlanarShape}
    (d : LabelledDrawing.PlanarAtBoundary Complex b t s) :
    SupportRule d.interpret.eval (geoInfo d.diagram.erase).events := by
  cases d with
  | mk w q d hb ht hs =>
    subst b t
    change SupportRule ((w.reorderFromBoundary (R := Complex)).eval.vertical
      (d.interpret.eval.vertical (q.reorderToBoundary (R := Complex)).eval)) _
    simpa only [List.nil_append, List.append_nil] using
      support_seq (.structural (preserve_reorder_from w))
        (support_seq (support_drawing d) (.structural (preserve_reorder_to q)))

end CaseFiveInfiniteAux
