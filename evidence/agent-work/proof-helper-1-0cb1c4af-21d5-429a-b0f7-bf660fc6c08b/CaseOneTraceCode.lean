import MackeyDiagrams.PlanarShape
set_option maxHeartbeats 2000000

namespace CaseOneTraceCode

open MackeyDiagrams

universe u v
variable {R : Type v} [CommSemiring R]
variable {U : Type u} [Group U] {A B C : Subgroup U}

theorem inputs_stack {s t : DrawingShape} (h : s.outputs = t.inputs) :
    (s.stack t).inputs = s.inputs := by
  induction s with
  | straight => exact h.symm
  | vertical a b ia ib =>
    cases t <;> rfl
  | vertex | horizontal | zero | add | scale =>
    cases t <;> rfl

theorem outputs_stack {s t : DrawingShape} (h : s.outputs = t.inputs) :
    (s.stack t).outputs = t.outputs := by
  induction s with
  | straight => rfl
  | vertical a b ia ib =>
    cases t <;> first | exact h | exact ib h
  | vertex | horizontal | zero | add | scale =>
    cases t <;> first | exact h | rfl

theorem inputs_juxtapose (s t : DrawingShape) :
    (s.juxtapose t).inputs = s.inputs ++ t.inputs := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.inputs]
    | cons x xs =>
      cases t with
      | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.inputs]
      | _ => rfl
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, DrawingShape.inputs, ib, List.append_assoc]
    | _ => simp [DrawingShape.juxtapose, DrawingShape.inputs, ib, List.append_assoc]
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.inputs]
    | _ => rfl

theorem outputs_juxtapose (s t : DrawingShape) :
    (s.juxtapose t).outputs = s.outputs ++ t.outputs := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.outputs]
    | cons x xs =>
      cases t with
      | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs]
      | _ => rfl
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs, ib, List.append_assoc]
    | _ => simp [DrawingShape.juxtapose, DrawingShape.outputs, ib, List.append_assoc]
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs]
    | _ => rfl

theorem shift_append (i : Nat) (a b : PlanarCode.Code) :
    PlanarCode.shift i (a ++ b) = PlanarCode.shift i a ++ PlanarCode.shift i b :=
  List.map_append

theorem shift_shift (i j : Nat) (a : PlanarCode.Code) :
    PlanarCode.shift i (PlanarCode.shift j a) = PlanarCode.shift (i+j) a := by
  simp only [PlanarCode.shift, List.map_map]
  congr 1
  funext e
  cases e <;> simp [PlanarEvent.place, PlanarEvent.position, Nat.add_assoc]

theorem shift_zero (a : PlanarCode.Code) : PlanarCode.shift 0 a = a := by
  unfold PlanarCode.shift
  have h : (fun e : PlanarEvent => e.place (0 + e.position)) = id := by
    funext e
    cases e <;> simp [PlanarEvent.place, PlanarEvent.position]
  rw [h, List.map_id]

theorem encode_stack (s t : DrawingShape) :
    PlanarCode.encode (s.stack t) = PlanarCode.encode s ++ PlanarCode.encode t := by
  induction s with
  | straight => rfl
  | vertical a b ia ib =>
    cases t <;> simp [DrawingShape.stack, PlanarCode.encode, ib, List.append_assoc]
  | vertex | horizontal | zero | add | scale =>
    cases t <;> simp [DrawingShape.stack, PlanarCode.encode]

theorem encode_juxtapose (s t : DrawingShape) :
    PlanarCode.encode (s.juxtapose t) =
      PlanarCode.encode s ++ PlanarCode.shift s.outputs.length (PlanarCode.encode t) := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.outputs, PlanarCode.encode, shift_zero]
    | cons x xs =>
      cases t with
      | straight r =>
        cases r <;> simp [DrawingShape.juxtapose, PlanarCode.encode, PlanarCode.shift]
      | _ => rfl
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r with
      | nil => simp [DrawingShape.juxtapose, PlanarCode.encode, PlanarCode.shift]
      | cons x xs =>
        simp [DrawingShape.juxtapose, PlanarCode.encode, ib, PlanarCode.shift]
    | _ => simp [DrawingShape.juxtapose, DrawingShape.outputs, PlanarCode.encode,
      ib, shift_append, shift_shift, List.append_assoc, List.length_append, Nat.add_assoc]
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs, PlanarCode.encode,
        PlanarCode.shift]
    | _ => rfl


def Fits : DrawingShape → Prop
  | .vertical s t => Fits s ∧ Fits t ∧ s.outputs = t.inputs
  | .horizontal s t => Fits s ∧ Fits t
  | .add s _ | .scale s => Fits s
  | _ => True

theorem fits_stack {s t : DrawingShape} (hs : Fits s) (ht : Fits t)
    (h : s.outputs = t.inputs) : Fits (s.stack t) := by
  induction s with
  | straight => exact ht
  | vertical a b ia ib =>
    obtain ⟨ha,hb,hab⟩ := hs
    change b.outputs = t.inputs at h
    cases t with
    | straight => exact ⟨ha, hb, hab⟩
    | _ => exact ⟨ha, ib hb h, hab.trans (inputs_stack h).symm⟩
  | vertex | horizontal | zero | add | scale =>
    cases t <;> first | exact hs | exact ⟨hs, ht, h⟩

theorem fits_juxtapose {s t : DrawingShape} (hs : Fits s) (ht : Fits t) :
    Fits (s.juxtapose t) := by
  induction s with
  | straight l =>
    cases l with
    | nil => exact ht
    | cons x xs =>
      cases t with
      | straight r => cases r <;> trivial
      | _ => exact ⟨hs, ht⟩
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r with
      | nil => exact hs
      | cons x xs => exact ⟨hs.1, ib hs.2⟩
    | _ => exact ⟨hs.1, ib hs.2⟩
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r =>
      cases r with
      | nil => exact hs
      | cons x xs => exact ⟨hs, ht⟩
    | _ => exact ⟨hs, ht⟩

theorem upward_dirs (n : Nat) :
    (DrawingShape.upwardDots n).inputs = [true] ∧
      (DrawingShape.upwardDots n).outputs = [true] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h : (DrawingShape.vertex .upDot).outputs = (DrawingShape.upwardDots n).inputs := ih.1.symm
    exact ⟨inputs_stack h, (outputs_stack h).trans ih.2⟩

theorem downward_dirs (n : Nat) :
    (DrawingShape.downwardDots n).inputs = [false] ∧
      (DrawingShape.downwardDots n).outputs = [false] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h : (DrawingShape.vertex .downDot).outputs = (DrawingShape.downwardDots n).inputs := ih.1.symm
    exact ⟨inputs_stack h, (outputs_stack h).trans ih.2⟩

theorem expanded_dirs (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    (DrawingShape.expandedProjectionGeometry n o c).inputs = [false, true] ∧
    (DrawingShape.expandedProjectionGeometry n o c).outputs = [true, false] := by
  unfold DrawingShape.expandedProjectionGeometry
  dsimp only
  have h₁ : (match o with
    | .junction => (DrawingShape.straight [false]).horizontal (.vertex .bentReverseCup)
    | .cupAndMerge => ((DrawingShape.straight [false, true]).horizontal (.vertex .reverseCup)).stack
        ((DrawingShape.straight [false]).horizontal ((DrawingShape.vertex .mergeUp).horizontal (.straight [false])))).outputs =
      [false, true, false] := by cases o <;> rfl
  have h₂ : (match c with
    | .junction => (DrawingShape.vertex .bentTraceCapOnLeft).horizontal (.straight [false])
    | .splitAndTrace => ((DrawingShape.straight [false]).horizontal
        ((DrawingShape.vertex .splitUp).horizontal (.straight [false]))).stack
          ((DrawingShape.vertex .traceCap).horizontal (.straight [true, false]))).inputs =
      [false, true, false] := by cases c <;> rfl
  let mid := (DrawingShape.straight [false]).horizontal
    ((DrawingShape.upwardDots n).horizontal (.straight [false]))
  have hm₁ : mid.inputs = [false,true,false] := by
    simp [mid, DrawingShape.inputs, upward_dirs]
  have hm₂ : mid.outputs = [false,true,false] := by
    simp [mid, DrawingShape.outputs, upward_dirs]
  have hm := hm₂.trans h₂.symm
  have hh := h₁.trans ((inputs_stack hm).trans hm₁).symm
  constructor
  · exact (inputs_stack hh).trans (by cases o <;> rfl)
  · exact (outputs_stack hh).trans ((outputs_stack hm).trans (by cases c <;> rfl))

theorem geometry_dirs {s : DrawingShape} (hs : Fits s) :
    s.geometry.inputs = s.inputs ∧ s.geometry.outputs = s.outputs := by
  induction s with
  | straight => exact ⟨rfl,rfl⟩
  | vertex k =>
    cases k <;> try exact ⟨rfl,rfl⟩
    case parallelUpChain n =>
      simp only [DrawingShape.geometry, DrawingShape.inputs, DrawingShape.outputs]
      have h₁ : (.vertex .mergeUp : DrawingShape).outputs = (DrawingShape.upwardDots n).inputs := (upward_dirs n).1.symm
      have h₂ : (DrawingShape.upwardDots n).outputs = (.vertex .splitUp : DrawingShape).inputs := (upward_dirs n).2
      rw [inputs_stack (h₁.trans (inputs_stack h₂).symm), outputs_stack (h₁.trans (inputs_stack h₂).symm),
        outputs_stack h₂]
      exact ⟨rfl,rfl⟩
    case parallelDownChain n =>
      simp only [DrawingShape.geometry, DrawingShape.inputs, DrawingShape.outputs]
      have h₁ : (.vertex .mergeDown : DrawingShape).outputs = (DrawingShape.downwardDots n).inputs := (downward_dirs n).1.symm
      have h₂ : (DrawingShape.downwardDots n).outputs = (.vertex .splitDown : DrawingShape).inputs := (downward_dirs n).2
      rw [inputs_stack (h₁.trans (inputs_stack h₂).symm), outputs_stack (h₁.trans (inputs_stack h₂).symm),
        outputs_stack h₂]
      exact ⟨rfl,rfl⟩
    case expandedMixedProjection o c => exact expanded_dirs 1 o c
    case expandedProjectionChain n o c => exact expanded_dirs n o c
  | vertical s t ihs iht =>
    obtain ⟨hs, ht, hst⟩ := hs
    obtain ⟨hs₁,hs₂⟩ := ihs hs
    obtain ⟨ht₁,ht₂⟩ := iht ht
    have h : s.geometry.outputs = t.geometry.inputs := hs₂.trans (hst.trans ht₁.symm)
    exact ⟨(inputs_stack h).trans hs₁, (outputs_stack h).trans ht₂⟩
  | horizontal s t ihs iht =>
    obtain ⟨hs, ht⟩ := hs
    obtain ⟨hs₁,hs₂⟩ := ihs hs
    obtain ⟨ht₁,ht₂⟩ := iht ht
    exact ⟨by simp [DrawingShape.geometry, inputs_juxtapose, DrawingShape.inputs, hs₁, ht₁],
      by simp [DrawingShape.geometry, outputs_juxtapose, DrawingShape.outputs, hs₂, ht₂]⟩
  | zero => exact ⟨rfl,rfl⟩
  | add l r ihl ihr => exact ihl hs
  | scale d ih => exact ih hs

def code (s : DrawingShape) : PlanarCode.Code :=
  PlanarCode.encode s.geometry

theorem code_stack (s t : DrawingShape) : code (s.stack t) = code s ++ code t := by
  induction s generalizing t with
  | straight => rfl
  | vertical a b ia ib =>
    have h (t : DrawingShape) : PlanarCode.encode (b.stack t).geometry =
        PlanarCode.encode b.geometry ++ PlanarCode.encode t.geometry := ib t
    cases t <;>
      simp [DrawingShape.stack, code, DrawingShape.geometry, encode_stack, h, List.append_assoc]
    rfl
  | vertex | horizontal | zero | add | scale =>
    cases t <;> simp [DrawingShape.stack, code, DrawingShape.geometry, encode_stack] <;> rfl

theorem code_juxtapose {s t : DrawingShape} (hs : Fits s) (ht : Fits t) :
    code (s.juxtapose t) = code s ++ PlanarCode.shift s.outputs.length (code t) := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.outputs, code, PlanarCode.encode,
        DrawingShape.geometry, shift_zero]
    | cons x xs =>
      cases t with
      | straight r =>
        cases r <;> simp [DrawingShape.juxtapose, code, DrawingShape.geometry, PlanarCode.encode,
          PlanarCode.shift]
      | _ =>
        first | rfl | simp [DrawingShape.juxtapose, code, DrawingShape.geometry, encode_juxtapose]
  | horizontal a b ia ib =>
    have h₁ := (geometry_dirs hs.1).2
    cases t with
    | straight r =>
      cases r with
      | nil =>
        simp [DrawingShape.juxtapose, code, DrawingShape.geometry, PlanarCode.encode, PlanarCode.shift]
      | cons x xs =>
        have hb : PlanarCode.encode (b.juxtapose (.straight (x :: xs))).geometry =
            PlanarCode.encode b.geometry := by
          have h := ib hs.2
          simpa [code, DrawingShape.geometry, PlanarCode.encode, PlanarCode.shift] using h
        simp [DrawingShape.juxtapose, code, DrawingShape.geometry, PlanarCode.encode,
          encode_juxtapose, hb, PlanarCode.shift]
    | _ =>
      have hb := ib hs.2
      unfold code at hb
      simp [DrawingShape.juxtapose, code, DrawingShape.geometry, encode_juxtapose,
        hb, h₁, DrawingShape.outputs, shift_append, shift_shift, List.append_assoc,
        List.length_append, Nat.add_assoc]
  | vertex | vertical | zero | add | scale =>
    have h := (geometry_dirs hs).2
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, code, DrawingShape.geometry,
        encode_juxtapose, PlanarCode.encode, PlanarCode.shift]
    | _ =>
      simp [DrawingShape.juxtapose, code, DrawingShape.geometry, encode_juxtapose, ← h] <;> rfl


omit [CommSemiring R] in
theorem diagram_fits {p q : Word A B} (d : Diagram R p q) :
    Fits d.drawing ∧ d.drawing.inputs = p.directions ∧ d.drawing.outputs = q.directions := by
  induction d <;> try exact ⟨trivial, rfl, rfl⟩
  case associate p q r =>
    exact ⟨trivial, rfl, List.append_assoc _ _ _⟩
  case unassociate p q r =>
    exact ⟨trivial, List.append_assoc _ _ _, rfl⟩
  case rightUnit p =>
    exact ⟨trivial, (List.append_nil _).symm, rfl⟩
  case insertRightUnit p =>
    exact ⟨trivial, rfl, (List.append_nil _).symm⟩
  case vertical d e hd he =>
    have h := hd.2.2.trans he.2.1.symm
    exact ⟨fits_stack hd.1 he.1 h, (inputs_stack h).trans hd.2.1,
      (outputs_stack h).trans he.2.2⟩
  case horizontal d e hd he =>
    exact ⟨fits_juxtapose hd.1 he.1, (inputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.1 he.2.1), (outputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.2 he.2.2)⟩
  case add d e hd he => exact hd
  case scale r d hd => exact hd

theorem drawing_fits {p q : Word A B} (d : LabelledDrawing R p q) :
    Fits d.erase ∧ d.erase.inputs = p.directions ∧ d.erase.outputs = q.directions := by
  induction d <;> try exact ⟨trivial, rfl, rfl⟩
  case ordinary d => exact diagram_fits d
  case trivalent v => cases v <;> exact ⟨trivial, rfl, rfl⟩
  case bentVertex v => cases v <;> exact ⟨trivial, rfl, rfl⟩
  case add d e hd he => exact hd
  case scale c d hd => exact hd
  case vertical d e hd he =>
    have h := hd.2.2.trans he.2.1.symm
    exact ⟨fits_stack hd.1 he.1 h, (inputs_stack h).trans hd.2.1,
      (outputs_stack h).trans he.2.2⟩
  case horizontal d e hd he =>
    exact ⟨fits_juxtapose hd.1 he.1, (inputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.1 he.2.1), (outputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.2 he.2.2)⟩

theorem drawing_code_vert {p q r : Word A B}
    (d : LabelledDrawing R p q) (e : LabelledDrawing R q r) :
    code (d.vertical e).erase = code d.erase ++ code e.erase :=
  code_stack _ _

theorem drawing_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : LabelledDrawing R p q) (e : LabelledDrawing R p' q') :
    code (d.horizontal e).erase = code d.erase ++ PlanarCode.shift q.directions.length (code e.erase) := by
  have hd := drawing_fits d
  have he := drawing_fits e
  change code (d.erase.juxtapose e.erase) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]

omit [CommSemiring R] in
theorem diagram_code_vert {p q r : Word A B}
    (d : Diagram R p q) (e : Diagram R q r) :
    code (d.vertical e).drawing = code d.drawing ++ code e.drawing :=
  code_stack _ _

omit [CommSemiring R] in
theorem diagram_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : Diagram R p q) (e : Diagram R p' q') :
    code (d.horizontal e).drawing = code d.drawing ++ PlanarCode.shift q.directions.length (code e.drawing) := by
  have hd := diagram_fits d
  have he := diagram_fits e
  change code (d.drawing.juxtapose e.drawing) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]

theorem drawing_geometry_dirs {p q : Word A B} (d : LabelledDrawing R p q) :
    d.erase.geometry.inputs = p.directions ∧ d.erase.geometry.outputs = q.directions :=
  let h := drawing_fits d
  let hg := geometry_dirs h.1
  ⟨hg.1.trans h.2.1, hg.2.trans h.2.2⟩

omit [CommSemiring R] in
theorem diagram_geometry_dirs {p q : Word A B} (d : Diagram R p q) :
    d.drawing.geometry.inputs = p.directions ∧ d.drawing.geometry.outputs = q.directions :=
  let h := diagram_fits d
  let hg := geometry_dirs h.1
  ⟨hg.1.trans h.2.1, hg.2.trans h.2.2⟩

private theorem upward_fits (n : Nat) : Fits (DrawingShape.upwardDots n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact fits_stack trivial ih (upward_dirs n).1.symm

private theorem downward_fits (n : Nat) : Fits (DrawingShape.downwardDots n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact fits_stack trivial ih (downward_dirs n).1.symm

private theorem expanded_fits (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    Fits (DrawingShape.expandedProjectionGeometry n o c) := by
  let mid := (DrawingShape.straight [false]).horizontal
    ((DrawingShape.upwardDots n).horizontal (.straight [false]))
  have hm : Fits mid := ⟨trivial, upward_fits n, trivial⟩
  have hi : mid.inputs = [false, true, false] :=
    congrArg (fun ds : List Bool => [false] ++ ds ++ [false]) (upward_dirs n).1
  have ho : mid.outputs = [false, true, false] :=
    congrArg (fun ds : List Bool => [false] ++ ds ++ [false]) (upward_dirs n).2
  cases o <;> cases c <;>
    simp only [DrawingShape.expandedProjectionGeometry] <;>
    change Fits (DrawingShape.stack _ (mid.stack _)) <;>
    apply fits_stack
  all_goals first
    | exact fits_stack hm (by
        simp [Fits, DrawingShape.stack, DrawingShape.inputs, DrawingShape.outputs,
          VertexKind.inputs, VertexKind.outputs]) ho
    | simp [Fits, DrawingShape.stack, DrawingShape.inputs, DrawingShape.outputs,
        VertexKind.inputs, VertexKind.outputs, hi]

theorem geometry_fits {s : DrawingShape} (hs : Fits s) : Fits s.geometry := by
  induction s with
  | straight | zero => trivial
  | vertex k =>
    cases k <;> try trivial
    case parallelUpChain n =>
      have h : (DrawingShape.upwardDots n).outputs = (DrawingShape.vertex .splitUp).inputs :=
        (upward_dirs n).2
      exact fits_stack trivial (fits_stack (upward_fits n) trivial h)
        ((inputs_stack h).trans (upward_dirs n).1).symm
    case parallelDownChain n =>
      have h : (DrawingShape.downwardDots n).outputs = (DrawingShape.vertex .splitDown).inputs :=
        (downward_dirs n).2
      exact fits_stack trivial (fits_stack (downward_fits n) trivial h)
        ((inputs_stack h).trans (downward_dirs n).1).symm
    case expandedMixedProjection o c => exact expanded_fits 1 o c
    case expandedProjectionChain n o c => exact expanded_fits n o c
  | vertical s t ihs iht =>
    exact fits_stack (ihs hs.1) (iht hs.2.1)
      ((geometry_dirs hs.1).2.trans (hs.2.2.trans (geometry_dirs hs.2.1).1.symm))
  | horizontal s t ihs iht => exact fits_juxtapose (ihs hs.1) (iht hs.2)
  | add s t ihs iht => exact ihs hs
  | scale s ih => exact ih hs

/-- Replay the ordered orientation word, checking the input slice at each event. -/
inductive Trace : PlanarCode.Code → List Bool → List Bool → Prop
  | nil (directions : List Bool) : Trace [] directions directions
  | step {code : PlanarCode.Code} {top : List Bool} (e : PlanarEvent)
      (left right : List Bool) (position : e.position = left.length)
      (tail : Trace code (left ++ e.outputs ++ right) top) :
      Trace (e :: code) (left ++ e.inputs ++ right) top

namespace Trace

theorem append {a b : PlanarCode.Code} {p q r : List Bool}
    (ha : Trace a p q) (hb : Trace b q r) : Trace (a ++ b) p r := by
  induction ha with
  | nil => exact hb
  | step e left right h _ ih => exact .step e left right h (ih hb)

theorem padRight {a : PlanarCode.Code} {p q : List Bool}
    (h : Trace a p q) (suffix : List Bool) : Trace a (p ++ suffix) (q ++ suffix) := by
  induction h with
  | nil => exact .nil _
  | step e left right he _ ih =>
    simpa only [List.append_assoc] using
      Trace.step e left (right ++ suffix) he (by simpa only [List.append_assoc] using ih)

theorem padLeft {a : PlanarCode.Code} {p q : List Bool}
    (h : Trace a p q) (padding : List Bool) :
    Trace (PlanarCode.shift padding.length a) (padding ++ p) (padding ++ q) := by
  induction h with
  | nil => exact .nil _
  | @step events top e left right he _ ih =>
    let moved := e.place (padding.length + e.position)
    have hp : moved.position = (padding ++ left).length := by
      cases e <;> simp_all [moved, PlanarEvent.position, PlanarEvent.place]
    have hi : moved.inputs = e.inputs := by cases e <;> rfl
    have ho : moved.outputs = e.outputs := by cases e <;> rfl
    have ht : Trace (PlanarCode.shift padding.length events)
        ((padding ++ left) ++ moved.outputs ++ right) (padding ++ top) := by
      simpa only [ho, List.append_assoc] using ih
    simpa only [hi, PlanarCode.shift, List.map_cons, List.append_assoc, moved] using
      Trace.step moved (padding ++ left) right hp ht

end Trace

private theorem canonical_directions (k : VertexKind) :
    k.canonical.inputs = k.inputs ∧ k.canonical.outputs = k.outputs := by
  cases k <;> exact ⟨rfl, rfl⟩

private theorem trace_singleton (e : PlanarEvent) (h : e.position = 0) :
    Trace [e] e.inputs e.outputs := by
  simpa only [List.nil_append, List.append_nil] using Trace.step e [] [] h (.nil _)

theorem encode_trace {s : DrawingShape} (h : Fits s) :
    Trace (PlanarCode.encode s) s.inputs s.outputs := by
  induction s with
  | straight => exact .nil _
  | vertex k =>
    have hk := canonical_directions k
    simpa only [PlanarCode.encode, DrawingShape.inputs, DrawingShape.outputs, PlanarEvent.inputs,
      PlanarEvent.outputs, hk.1, hk.2] using trace_singleton (.vertex 0 k.canonical) rfl
  | vertical s t ihs iht =>
    exact (ihs h.1).append (h.2.2.symm ▸ iht h.2.1)
  | horizontal s t ihs iht =>
    exact ((ihs h.1).padRight t.inputs).append ((iht h.2).padLeft s.outputs)
  | zero below above => exact trace_singleton (.zero 0 below above) rfl
  | add l r =>
    exact trace_singleton (.add 0 l.inputs l.outputs (PlanarCode.encode l) (PlanarCode.encode r)) rfl
  | scale s => exact trace_singleton (.scale 0 s.inputs s.outputs (PlanarCode.encode s)) rfl

theorem drawing_trace {p q : Word A B} (d : LabelledDrawing R p q) :
    Trace (code d.erase) p.directions q.directions := by
  obtain ⟨hp, hq⟩ := drawing_geometry_dirs d
  rw [← hp, ← hq]
  exact encode_trace (geometry_fits (drawing_fits d).1)

omit [CommSemiring R] in
theorem diagram_trace {p q : Word A B} (d : Diagram R p q) :
    Trace (code d.drawing) p.directions q.directions := by
  obtain ⟨hp, hq⟩ := diagram_geometry_dirs d
  rw [← hp, ← hq]
  exact encode_trace (geometry_fits (diagram_fits d).1)

theorem malformed_shape_counterexample :
    let s := DrawingShape.vertical (.vertex .upDot) (.straight [true, true])
    let t := DrawingShape.vertex .parallelUp
    code (s.juxtapose t) ≠ code s ++ PlanarCode.shift s.outputs.length (code t) := by
  dsimp only
  intro h
  have hh := congrArg (List.map PlanarEvent.position) h
  change [0, 1] = [0, 2] at hh
  cases hh

/-- Apply the orientation change of an event at its recorded position.
`Trace` certifies that the overwritten slice is the event's input word. -/
def applyEvent (directions : List Bool) (event : PlanarEvent) : List Bool :=
  directions.take event.position ++ event.outputs ++
    directions.drop (event.position + event.inputs.length)

private theorem applyEvent_step (e : PlanarEvent) (l r : List Bool)
    (h : e.position = l.length) :
    applyEvent (l ++ e.inputs ++ r) e = l ++ e.outputs ++ r := by
  simp [applyEvent, h, List.append_assoc, List.drop_length_add_append]

namespace Trace

theorem foldl_eq {a : PlanarCode.Code} {p q : List Bool}
    (h : Trace a p q) : a.foldl applyEvent p = q := by
  induction h with
  | nil => rfl
  | step e l r hp _ ih =>
    simpa only [List.foldl_cons, applyEvent_step e l r hp] using ih

/-- A nonempty trace of two-input events uses at least two input strands.
If all the events also have two outputs it preserves the total width. -/
theorem width_of_crossings {a : PlanarCode.Code} {p q : List Bool}
    (h : Trace a p q)
    (hw : ∀ e ∈ a, e.inputs.length = 2 ∧ e.outputs.length = 2) :
    p.length = q.length ∧ (a ≠ [] → 2 ≤ p.length) := by
  induction h with
  | nil => exact ⟨rfl, fun hn => (hn rfl).elim⟩
  | step e l r _ _ ih =>
    obtain ⟨hi, ho⟩ := hw e (List.mem_cons_self ..)
    have h' := (ih fun x hx => hw x (List.mem_cons_of_mem _ hx)).1
    simp only [List.length_append, hi, ho] at h' ⊢
    exact ⟨h', fun _ => by omega⟩

end Trace

abbrev parallelAt (i : Nat) : PlanarEvent := .vertex i .parallelUp
abbrev projectionAt (i : Nat) : PlanarEvent := .vertex i .mixedProjection

theorem right_prefix_one {q : List Bool}
    (h : Trace [parallelAt 1] [false, true, true] q) :
    q = [false, true, true] :=
  h.foldl_eq.symm

theorem right_prefix_two {q : List Bool}
    (h : Trace [parallelAt 1, projectionAt 0] [false, true, true] q) :
    q = [true, false, true] :=
  h.foldl_eq.symm

theorem right_prefix_three {q : List Bool}
    (h : Trace [parallelAt 1, projectionAt 0, projectionAt 1] [false, true, true] q) :
    q = [true, true, false] :=
  h.foldl_eq.symm

private theorem widths_place (e : PlanarEvent) (i : Nat) :
    (e.place i).inputs = e.inputs ∧ (e.place i).outputs = e.outputs := by
  cases e <;> exact ⟨rfl, rfl⟩

theorem Trace.horizontal_empty_of_width_le_three {a b : PlanarCode.Code}
    {p q r s : List Bool} (ha : Trace a p q) (hb : Trace b r s)
    (hw : ∀ e ∈ a ++ PlanarCode.shift q.length b,
      e.inputs.length = 2 ∧ e.outputs.length = 2)
    (hwidth : (p ++ r).length ≤ 3) :
    a = [] ∨ b = [] := by
  classical
  by_contra! h
  have hleft := (ha.width_of_crossings (fun e he => hw e (List.mem_append_left _ he))).2 h.1
  have hright := (hb.width_of_crossings (fun e he => by
    have he' : e.place (q.length + e.position) ∈ PlanarCode.shift q.length b :=
      List.mem_map_of_mem he
    have hm := hw _ (List.mem_append_right _ he')
    simpa only [(widths_place e _).1, (widths_place e _).2] using hm)).2 h.2
  simp only [List.length_append] at hwidth
  omega

end CaseOneTraceCode
