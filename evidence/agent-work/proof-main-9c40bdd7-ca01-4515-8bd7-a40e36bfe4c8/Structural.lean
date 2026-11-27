import SupportRule

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

universe u
variable {V : Type u} [Group V] {A B C D : Subgroup V}

theorem PreservesSlots.seq {p q t : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {g : Biset.Hom Complex q.basis t.basis} (hf : PreservesSlots f) (hg : PreservesSlots g) :
    PreservesSlots (f.vertical g) :=
  (support_seq (.structural hf) (.structural hg)).1 rfl

theorem PreservesSlots.par {p q : Word A B} {r s : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    (hf : PreservesSlots f) (hg : PreservesSlots g) : PreservesSlots (p := p.tensor r) (q := q.tensor s) (f.horizontal g) :=
  (support_par (.structural hf) (.structural hg)).1 rfl

theorem preserve_id (p : Word A B) : PreservesSlots (Diagram.id (R := Complex) p).eval := by
  intro x
  exact ⟨x,rfl,Diagram.eval_id_apply p _⟩

theorem preserve_leftUnit (p : Word A B) :
    PreservesSlots (Diagram.leftUnit (R := Complex) p).eval := by
  intro x
  refine ⟨x.2, rfl, ?_⟩
  unfold basisVector
  change (Diagram.leftUnit (R := Complex) p).eval.toLinearMap
    (Finsupp.single ((Biset.regular A).pair p.basis 1 (rawPoint p x.2)) 1) = _
  rw [Diagram.eval_leftUnit_single, show ((1,1) : A × B) = 1 from rfl, p.basis.one_act]

theorem preserve_rightUnit (p : Word A B) :
    PreservesSlots (Diagram.rightUnit (R := Complex) p).eval := by
  intro x
  refine ⟨x.1, by simp [slots], ?_⟩
  unfold basisVector
  change (Diagram.rightUnit (R := Complex) p).eval.toLinearMap
    (Finsupp.single (p.basis.pair (Biset.regular B) (rawPoint p x.1) 1) 1) = _
  rw [Diagram.eval_rightUnit_single, inv_one, show ((1,1) : A × B) = 1 from rfl, p.basis.one_act]

theorem preserve_insertLeftUnit (p : Word A B) :
    PreservesSlots (Diagram.insertLeftUnit (R := Complex) p).eval := by
  intro x
  exact ⟨(PUnit.unit,x), rfl, Diagram.eval_insertLeftUnit_single p (rawPoint p x) 1⟩

theorem preserve_insertRightUnit (p : Word A B) :
    PreservesSlots (Diagram.insertRightUnit (R := Complex) p).eval := by
  intro x
  refine ⟨(x,PUnit.unit), by simp [slots], ?_⟩
  change (Biset.insertRightUnit p.basis Complex).toLinearMap (Finsupp.single (rawPoint p x) 1) =
    Finsupp.single (p.basis.pair (Biset.regular B) (rawPoint p x) 1) 1
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]

theorem preserve_associate (p : Word A B) (q : Word B C) (t : Word C D) :
    PreservesSlots (Diagram.associate (R := Complex) p q t).eval := by
  intro x
  exact ⟨(x.1.1,x.1.2,x.2), by simp [slots,List.append_assoc],
    Diagram.eval_associate_single p q t (rawPoint p x.1.1) (rawPoint q x.1.2) (rawPoint t x.2) 1⟩

theorem preserve_unassociate (p : Word A B) (q : Word B C) (t : Word C D) :
    PreservesSlots (Diagram.unassociate (R := Complex) p q t).eval := by
  intro x
  exact ⟨((x.1,x.2.1),x.2.2), by simp [slots,List.append_assoc],
    Diagram.eval_unassociate_single p q t (rawPoint p x.1) (rawPoint q x.2.1) (rawPoint t x.2.2) 1⟩

theorem preserve_boundary_append (a : Boundary A B) (b : Boundary B C) :
    PreservesSlots (a.appendDiagram (R := Complex) b).eval := by
  induction a with
  | empty => exact preserve_leftUnit b.word
  | cons s t ih =>
    exact (preserve_associate s.word t.word b.word).seq ((preserve_id s.word).par (ih b))

theorem preserve_boundary_split (a : Boundary A B) (b : Boundary B C) :
    PreservesSlots (a.splitDiagram (R := Complex) b).eval := by
  induction a with
  | empty => exact preserve_insertLeftUnit b.word
  | cons s t ih =>
    exact ((preserve_id s.word).par (ih b)).seq (preserve_unassociate s.word t.word b.word)

theorem preserve_reorder_to (p : Word A B) : PreservesSlots (p.reorderToBoundary (R := Complex)).eval := by
  induction p with
  | empty => exact preserve_id _
  | up | down => exact preserve_insertRightUnit _
  | tensor p q hp hq => exact (hp.par hq).seq (preserve_boundary_append p.boundary q.boundary)

theorem preserve_reorder_from (p : Word A B) : PreservesSlots (p.reorderFromBoundary (R := Complex)).eval := by
  induction p with
  | empty => exact preserve_id _
  | up | down => exact preserve_rightUnit _
  | tensor p q hp hq => exact (preserve_boundary_split p.boundary q.boundary).seq (hp.par hq)

end CaseFiveInfiniteAux
