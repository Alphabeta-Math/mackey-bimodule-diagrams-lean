import Layout
import Mathlib.Basic.Complex.Basic

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

theorem dot_width (n : Nat) :
    (info (DrawingShape.upwardDots n)).ins = 1 ∧
    (info (DrawingShape.upwardDots n)).outs = 1 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h : (info (.vertex .upDot)).outs = (info (DrawingShape.upwardDots n)).ins := ih.1.symm
    unfold DrawingShape.upwardDots
    rw [info_stack _ _ h]
    exact ⟨rfl,ih.2⟩

theorem down_dot_width (n : Nat) :
    (info (DrawingShape.downwardDots n)).ins = 1 ∧
    (info (DrawingShape.downwardDots n)).outs = 1 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h : (info (.vertex .downDot)).outs = (info (DrawingShape.downwardDots n)).ins := ih.1.symm
    unfold DrawingShape.downwardDots
    rw [info_stack _ _ h]
    exact ⟨rfl,ih.2⟩

theorem parallel_chain_width (n : Nat) :
    (geoInfo (.vertex (.parallelUpChain n))).ins = 2 ∧
    (geoInfo (.vertex (.parallelUpChain n))).outs = 2 ∧
    (geoInfo (.vertex (.parallelUpChain n))).events.head? = some (.vertex 0 (.trivalent .mergeUp)) := by
  let ds := DrawingShape.upwardDots n
  have h := dot_width n
  have hs : (info ds).outs = (info (.vertex .splitUp)).ins := h.2
  have ht : (info (.vertex .mergeUp)).outs = (info (ds.stack (.vertex .splitUp))).ins := by
    rw [info_stack _ _ hs]
    exact h.1.symm
  change (info ((.vertex .mergeUp : DrawingShape).stack (ds.stack (.vertex .splitUp)))).ins = _ ∧
    (info ((.vertex .mergeUp : DrawingShape).stack (ds.stack (.vertex .splitUp)))).outs = _ ∧
    (info ((.vertex .mergeUp : DrawingShape).stack (ds.stack (.vertex .splitUp)))).events.head? = _
  rw [info_stack _ _ ht, info_stack _ _ hs]
  exact ⟨rfl,rfl,rfl⟩

theorem down_chain_width (n : Nat) :
    (geoInfo (.vertex (.parallelDownChain n))).ins = 2 ∧
    (geoInfo (.vertex (.parallelDownChain n))).outs = 2 ∧
    (geoInfo (.vertex (.parallelDownChain n))).events.head? = some (.vertex 0 (.trivalent .mergeDown)) := by
  let ds := DrawingShape.downwardDots n
  have h := down_dot_width n
  have hs : (info ds).outs = (info (.vertex .splitDown)).ins := h.2
  have ht : (info (.vertex .mergeDown)).outs = (info (ds.stack (.vertex .splitDown))).ins := by
    rw [info_stack _ _ hs]
    exact h.1.symm
  change (info ((.vertex .mergeDown : DrawingShape).stack (ds.stack (.vertex .splitDown)))).ins = _ ∧
    (info ((.vertex .mergeDown : DrawingShape).stack (ds.stack (.vertex .splitDown)))).outs = _ ∧
    (info ((.vertex .mergeDown : DrawingShape).stack (ds.stack (.vertex .splitDown)))).events.head? = _
  rw [info_stack _ _ ht, info_stack _ _ hs]
  exact ⟨rfl,rfl,rfl⟩

theorem expanded_info (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    let I := info (DrawingShape.expandedProjectionGeometry n o c)
    I.ins = 2 ∧ I.outs = 2 ∧ I.events ≠ [] ∧
      ∀ j : Nat, I.events.head? ≠ some (.vertex j .mixedProjection) := by
  let middle : DrawingShape := .horizontal (.straight [false])
    (.horizontal (DrawingShape.upwardDots n) (.straight [false]))
  have mw : (info middle).ins = 3 ∧ (info middle).outs = 3 := by
    unfold middle
    rw [info_horizontal, info_horizontal]
    have h := dot_width n
    simp [ShapeInfo.par, h.1, h.2]
    exact ⟨rfl,rfl⟩
  have frame (a b : DrawingShape) (ha : (info a).outs = 3) (hb : (info b).ins = 3) :
      info (a.stack (middle.stack b)) = (info a).seq ((info middle).seq (info b)) := by
    have hm := mw.2.trans hb.symm
    have hn : (info a).outs = (info (middle.stack b)).ins := by
      rw [info_stack _ _ hm]
      exact ha.trans mw.1.symm
    rw [info_stack _ _ hn, info_stack _ _ hm]
  dsimp only [DrawingShape.expandedProjectionGeometry]
  cases o <;> cases c <;>
    change
      let a : DrawingShape := _
      let b : DrawingShape := _
      (info (a.stack (middle.stack b))).ins = 2 ∧
        (info (a.stack (middle.stack b))).outs = 2 ∧ (info (a.stack (middle.stack b))).events ≠ [] ∧
        ∀ j, (info (a.stack (middle.stack b))).events.head? ≠
          some (.vertex j .mixedProjection)
  all_goals
    dsimp only
    rw [frame _ _ (by rfl) (by rfl)]
    refine ⟨rfl, rfl, (fun h => by cases h), ?_⟩
    intro j h
    -- The first event is the opening cup vertex in both allowed frames.
    cases h

universe u
variable {V : Type u} [Group V] {A B C : Subgroup V}
variable {p q t : Word A B}

def Sized (s : DrawingShape) (p q : Word A B) : Prop :=
  Valid s ∧ (geoInfo s).ins = p.directions.length ∧ (geoInfo s).outs = q.directions.length

theorem sized_seq {a b : DrawingShape} (ha : Sized a p q) (hb : Sized b q t) :
    Sized (a.stack b) p t ∧ geoInfo (a.stack b) = (geoInfo a).seq (geoInfo b) := by
  obtain ⟨hv, he⟩ := geo_stack ha.1 hb.1 (ha.2.2.trans hb.2.1.symm)
  exact ⟨⟨hv, (congrArg ShapeInfo.ins he).trans ha.2.1,
    (congrArg ShapeInfo.outs he).trans hb.2.2⟩, he⟩

theorem sized_par {r s : Word B C} {a b : DrawingShape} (ha : Sized a p q) (hb : Sized b r s) :
    Sized (a.juxtapose b) (p.tensor r) (q.tensor s) ∧
      geoInfo (a.juxtapose b) = (geoInfo a).par (geoInfo b) := by
  obtain ⟨hv, he⟩ := geo_juxtapose ha.1 hb.1
  refine ⟨⟨hv, ?_, ?_⟩, he⟩ <;>
    simp only [he, ShapeInfo.par, ha.2.1, ha.2.2, hb.2.1, hb.2.2,
      Word.directions, List.length_append]

theorem sized_diagram (d : Diagram Complex p q) : Sized d.drawing p q := by
  induction d with
  | vertical _ _ ha hb => exact (sized_seq ha hb).1
  | horizontal _ _ ha hb => exact (sized_par ha hb).1
  | add _ _ ha _ => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | scale _ _ ha => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | associate | unassociate =>
    exact ⟨trivial, by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry,
      DrawingShape.inputs, Word.directions, List.append_assoc],
      by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry, DrawingShape.outputs,
        Word.directions, List.append_assoc]⟩
  | leftUnit | rightUnit | insertLeftUnit | insertRightUnit =>
    exact ⟨trivial, by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry,
      DrawingShape.inputs, Word.directions],
      by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry,
        DrawingShape.outputs, Word.directions]⟩
  | _ => exact ⟨trivial,rfl,rfl⟩

theorem sized_drawing (d : LabelledDrawing Complex p q) : Sized d.erase p q := by
  induction d with
  | ordinary d => exact sized_diagram d
  | vertical _ _ ha hb => exact (sized_seq ha hb).1
  | horizontal _ _ ha hb => exact (sized_par ha hb).1
  | add _ _ ha _ => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | scale _ _ ha => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | trivalent v => cases v <;> exact ⟨trivial,rfl,rfl⟩
  | bentVertex v => cases v <;> exact ⟨trivial,rfl,rfl⟩
  | parallelUpChain _ _ _ _ ls => exact ⟨trivial, (parallel_chain_width ls.length).1, (parallel_chain_width ls.length).2.1⟩
  | parallelDownChain _ _ _ _ ls => exact ⟨trivial, (down_chain_width ls.length).1, (down_chain_width ls.length).2.1⟩
  | expandedProjection _ _ _ _ _ o c =>
    exact ⟨trivial, (expanded_info 1 o c).1, (expanded_info 1 o c).2.1⟩
  | expandedProjectionChain _ _ _ _ ls _ o c =>
    exact ⟨trivial, (expanded_info ls.length o c).1, (expanded_info ls.length o c).2.1⟩
  | expandedLinearDotProjection _ _ _ _ ls _ o c =>
    exact ⟨trivial, (expanded_info ls.length o c).1, (expanded_info ls.length o c).2.1⟩
  | _ => exact ⟨trivial,rfl,rfl⟩

end CaseFiveInfiniteAux
