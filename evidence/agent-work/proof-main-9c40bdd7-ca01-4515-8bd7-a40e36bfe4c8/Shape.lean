import MackeyDiagrams

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

structure ShapeInfo where
  ins : Nat
  outs : Nat
  events : Code

def info (s : DrawingShape) : ShapeInfo :=
  ⟨s.inputs.length, s.outputs.length, encode s⟩

def ShapeInfo.seq (a b : ShapeInfo) : ShapeInfo :=
  ⟨a.ins, b.outs, a.events ++ b.events⟩

def ShapeInfo.par (a b : ShapeInfo) : ShapeInfo :=
  ⟨a.ins + b.ins, a.outs + b.outs, a.events ++ shift a.outs b.events⟩

theorem shift_add (n m : Nat) (xs : Code) : shift n (shift m xs) = shift (n + m) xs := by
  unfold shift
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  cases e <;> simp [PlanarEvent.place, PlanarEvent.position, Nat.add_assoc]

theorem shift_zero (xs : Code) : shift 0 xs = xs := by
  unfold shift
  conv_rhs => rw [← List.map_id xs]
  apply List.map_congr_left
  intro e _
  cases e <;> simp [PlanarEvent.place, PlanarEvent.position]

theorem ShapeInfo.par_assoc (a b c : ShapeInfo) : (a.par b).par c = a.par (b.par c) := by
  simp [ShapeInfo.par, shift, Nat.add_assoc, List.map_append, List.append_assoc, List.map_map,
    show ∀ e : PlanarEvent, (e.place (b.outs + e.position)).position = b.outs + e.position by
      intro e; cases e <;> rfl,
    show ∀ (e : PlanarEvent) (j k : Nat), (e.place j).place k = e.place k by
      intro e j k; cases e <;> rfl]

theorem info_vertical (a b : DrawingShape) : info (.vertical a b) = (info a).seq (info b) := rfl

theorem info_horizontal (a b : DrawingShape) : info (.horizontal a b) = (info a).par (info b) := by
  simp [info, ShapeInfo.par, DrawingShape.inputs, DrawingShape.outputs, encode]

theorem info_stack (a b : DrawingShape) (h : (info a).outs = (info b).ins) :
    info (a.stack b) = (info a).seq (info b) := by
  induction a generalizing b with
  | straight s =>
    cases b <;> simp_all [DrawingShape.stack, info, ShapeInfo.seq, DrawingShape.inputs,
      DrawingShape.outputs, encode]
  | vertical f rest ihf ihr =>
    cases b with
    | straight s =>
      simp_all [DrawingShape.stack, info, ShapeInfo.seq, DrawingShape.inputs,
        DrawingShape.outputs, encode]
    | vertex k =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | vertical x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | horizontal x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | zero x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | add x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | scale d =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
  | vertex | horizontal | zero | add | scale =>
    cases b <;> simp_all [DrawingShape.stack, info, ShapeInfo.seq, DrawingShape.inputs,
      DrawingShape.outputs, encode]

theorem info_juxtapose (a b : DrawingShape) :
    info (a.juxtapose b) = (info a).par (info b) := by
  induction a generalizing b with
  | straight s =>
    cases s with
    | nil => simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
        DrawingShape.outputs, encode, shift_zero]
    | cons d s =>
      cases b with
      | straight t =>
        cases t <;>
          simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
            DrawingShape.outputs, encode, shift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      | vertex | vertical | horizontal | zero | add | scale =>
        exact info_horizontal _ _
  | horizontal f rest ihf ihr =>
    cases b with
    | straight s =>
      cases s with
      | nil => simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
          DrawingShape.outputs, encode, shift]
      | cons d s =>
        change info (.horizontal f (rest.juxtapose _)) = _
        simp only [info_horizontal, ihr, ShapeInfo.par_assoc]
    | vertex | vertical | horizontal | zero | add | scale =>
      change info (.horizontal f (rest.juxtapose _)) = _
      simp only [info_horizontal, ihr, ShapeInfo.par_assoc]
  | vertex | vertical | zero | add | scale =>
    cases b with
    | straight s =>
      cases s with
      | nil => simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
          DrawingShape.outputs, encode, shift]
      | cons d s => exact info_horizontal _ _
    | vertex | vertical | horizontal | zero | add | scale =>
      exact info_horizontal _ _

end CaseFiveInfiniteAux
