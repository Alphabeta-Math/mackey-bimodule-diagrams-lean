import FactorPart
import Proofs.DotSlidePreorderNotSymmetric

set_option maxHeartbeats 2000000

namespace CaseTwoStage
open MackeyDiagrams
universe u
variable {U : Type u} [Group U] {A B C D : Subgroup U}

-- Code equations from FactorPart.lean, whose proof of the cut uses these same equations.
private theorem inputs_stack {s t : DrawingShape} (h : s.outputs = t.inputs) :
    (s.stack t).inputs = s.inputs := by
  induction s with
  | straight => exact h.symm
  | vertical a b ia ib =>
    cases t <;> rfl
  | vertex | horizontal | zero | add | scale =>
    cases t <;> rfl

private theorem outputs_stack {s t : DrawingShape} (h : s.outputs = t.inputs) :
    (s.stack t).outputs = t.outputs := by
  induction s with
  | straight => rfl
  | vertical a b ia ib =>
    cases t <;> first | exact h | exact ib h
  | vertex | horizontal | zero | add | scale =>
    cases t <;> first | exact h | rfl

private theorem inputs_juxtapose (s t : DrawingShape) :
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

private theorem outputs_juxtapose (s t : DrawingShape) :
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

private theorem shift_append (i : Nat) (a b : PlanarCode.Code) :
    PlanarCode.shift i (a ++ b) = PlanarCode.shift i a ++ PlanarCode.shift i b :=
  List.map_append

private theorem shift_shift (i j : Nat) (a : PlanarCode.Code) :
    PlanarCode.shift i (PlanarCode.shift j a) = PlanarCode.shift (i+j) a := by
  simp only [PlanarCode.shift, List.map_map]
  congr 1
  funext e
  cases e <;> simp [PlanarEvent.place, PlanarEvent.position, Nat.add_assoc]

private theorem shift_zero (a : PlanarCode.Code) : PlanarCode.shift 0 a = a := by
  unfold PlanarCode.shift
  have h : (fun e : PlanarEvent => e.place (0 + e.position)) = id := by
    funext e
    cases e <;> simp [PlanarEvent.place, PlanarEvent.position]
  rw [h, List.map_id]

private theorem encode_stack (s t : DrawingShape) :
    PlanarCode.encode (s.stack t) = PlanarCode.encode s ++ PlanarCode.encode t := by
  induction s with
  | straight => rfl
  | vertical a b ia ib =>
    cases t <;> simp [DrawingShape.stack, PlanarCode.encode, ib, List.append_assoc]
  | vertex | horizontal | zero | add | scale =>
    cases t <;> simp [DrawingShape.stack, PlanarCode.encode]

private theorem encode_juxtapose (s t : DrawingShape) :
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


private def Fits : DrawingShape → Prop
  | .vertical s t => Fits s ∧ Fits t ∧ s.outputs = t.inputs
  | .horizontal s t => Fits s ∧ Fits t
  | .add s _ | .scale s => Fits s
  | _ => True

private theorem fits_stack {s t : DrawingShape} (hs : Fits s) (ht : Fits t)
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

private theorem fits_juxtapose {s t : DrawingShape} (hs : Fits s) (ht : Fits t) :
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

private theorem upward_dirs (n : Nat) :
    (DrawingShape.upwardDots n).inputs = [true] ∧
      (DrawingShape.upwardDots n).outputs = [true] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h : (DrawingShape.vertex .upDot).outputs = (DrawingShape.upwardDots n).inputs := ih.1.symm
    exact ⟨inputs_stack h, (outputs_stack h).trans ih.2⟩

private theorem downward_dirs (n : Nat) :
    (DrawingShape.downwardDots n).inputs = [false] ∧
      (DrawingShape.downwardDots n).outputs = [false] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h : (DrawingShape.vertex .downDot).outputs = (DrawingShape.downwardDots n).inputs := ih.1.symm
    exact ⟨inputs_stack h, (outputs_stack h).trans ih.2⟩

private theorem expanded_dirs (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
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

private theorem geometry_dirs {s : DrawingShape} (hs : Fits s) :
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

private def code (s : DrawingShape) : PlanarCode.Code :=
  PlanarCode.encode s.geometry

private theorem code_stack (s t : DrawingShape) : code (s.stack t) = code s ++ code t := by
  induction s generalizing t with
  | straight => rfl
  | vertical a b ia ib =>
    have h (t : DrawingShape) : PlanarCode.encode (b.stack t).geometry =
        PlanarCode.encode b.geometry ++ PlanarCode.encode t.geometry := ib t
    cases t <;>
      simp [DrawingShape.stack, code, DrawingShape.geometry, encode_stack, h, List.append_assoc]
    all_goals rfl
  | vertex | horizontal | zero | add | scale =>
    cases t <;> simp [DrawingShape.stack, code, DrawingShape.geometry, encode_stack] <;> rfl

private theorem code_juxtapose {s t : DrawingShape} (hs : Fits s) (ht : Fits t) :
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


private theorem diagram_fits {p q : Word A B} (d : Diagram Complex p q) :
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

private theorem drawing_fits {p q : Word A B} (d : LabelledDrawing Complex p q) :
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

private theorem drawing_code_vert {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) :
    code (d.vertical e).erase = code d.erase ++ code e.erase :=
  code_stack _ _

private theorem drawing_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex p' q') :
    code (d.horizontal e).erase = code d.erase ++ PlanarCode.shift q.directions.length (code e.erase) := by
  have hd := drawing_fits d
  have he := drawing_fits e
  change code (d.erase.juxtapose e.erase) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]

private theorem diagram_code_vert {p q r : Word A B}
    (d : Diagram Complex p q) (e : Diagram Complex q r) :
    code (d.vertical e).drawing = code d.drawing ++ code e.drawing :=
  code_stack _ _

private theorem diagram_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : Diagram Complex p q) (e : Diagram Complex p' q') :
    code (d.horizontal e).drawing = code d.drawing ++ PlanarCode.shift q.directions.length (code e.drawing) := by
  have hd := diagram_fits d
  have he := diagram_fits e
  change code (d.drawing.juxtapose e.drawing) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]

private def isCompactCrossing : PlanarEvent → Prop
  | .vertex _ .mixedProjection | .vertex _ .parallelUp => True
  | _ => False

private def goodCode (c : PlanarCode.Code) : Prop :=
  ∀ e ∈ c, isCompactCrossing e

private theorem good_left {l r : PlanarCode.Code} (h : goodCode (l ++ r)) :
    goodCode l := fun e he => h e (List.mem_append_left _ he)

private theorem no_expandedProjection (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    ¬ goodCode (PlanarCode.encode (DrawingShape.expandedProjectionGeometry n o c)) := by
  intro h
  unfold DrawingShape.expandedProjectionGeometry at h
  rw [encode_stack] at h
  have hs := good_left h
  cases o
  · exact hs (.vertex 1 (.trivalent .upToUpDown)) List.mem_cons_self
  · exact hs (.vertex 2 .reverseCup) List.mem_cons_self

-- Structural framing follows Proofs/DotSlidePreorderNotSymmetric.lean.
open Biset.Hom
private def boundaryDirections : {A B : Subgroup U} → Boundary A B → List Bool
  | _, _, .empty _ => []
  | _, _, .cons (.up _) rest => true :: boundaryDirections rest
  | _, _, .cons (.down _) rest => false :: boundaryDirections rest

private theorem boundaryDirections_append (p : Boundary A B) (q : Boundary B C) :
    boundaryDirections (p.append q) = boundaryDirections p ++ boundaryDirections q := by
  induction p with
  | empty => rfl
  | cons s rest ih => cases s <;> simp only [Boundary.append, boundaryDirections, List.cons_append, ih]

private theorem boundaryDirections_word (p : Word A B) :
    boundaryDirections p.boundary = p.directions := by
  induction p with
  | empty | up | down => rfl
  | tensor p q ihp ihq => rw [Word.boundary, boundaryDirections_append, ihp, ihq, Word.directions]

private noncomputable def canon {p q : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) :
    Biset.Hom Complex p.boundary.word.basis q.boundary.word.basis :=
  (p.reorderFromBoundary (R := Complex)).eval.vertical
    (f.vertical (q.reorderToBoundary (R := Complex)).eval)

private theorem canon_vertical {p q r : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) (g : Biset.Hom Complex q.basis r.basis) :
    canon (f.vertical g) = (canon f).vertical (canon g) := by
  unfold canon
  simp only [vertical_assoc]
  have h := Word.eval_reorderToFrom (R := Complex) q
  change ((q.reorderToBoundary (R := Complex)).eval.vertical q.reorderFromBoundary.eval) = Biset.Hom.id _ at h
  rw [← vertical_assoc (q.reorderToBoundary (R := Complex)).eval, h, id_vertical]

private abbrev BoundaryMap {A B : Subgroup U} (p q : Boundary A B) :=
  Biset.Hom Complex p.word.basis q.word.basis

private noncomputable def boundaryId {p q : Boundary A B} (h : p = q) : BoundaryMap p q :=
  h ▸ (Biset.Hom.id p.word.basis : BoundaryMap p p)

/-- Empty code preserves the ordered labelled boundary, and its evaluation there is
the identity transported along the boundary equality. -/
private def EmptyCodeCoherence (U : Type u) [Group U] : Prop :=
  ∀ {A B : Subgroup U} {p q : Word A B} (d : LabelledDrawing Complex p q),
    code d.erase = [] →
      ∃ h : p.boundary = q.boundary, canon d.interpret.eval = boundaryId h

private def Wire (p q : Word A B) :=
  {d : LabelledDrawing Complex p q // code d.erase = []}

private noncomputable def Wire.eval {p q : Word A B} (d : Wire p q) :=
  d.val.interpret.eval

private def Wire.id (p : Word A B) : Wire p p := ⟨.ordinary (.id p), rfl⟩

private def Wire.vertical {p q r : Word A B} (d : Wire p q) (e : Wire q r) : Wire p r :=
  ⟨d.val.vertical e.val, by rw [drawing_code_vert, d.property, e.property]; rfl⟩

private def Wire.horizontal {p q : Word A B} {r s : Word B C}
    (d : Wire p q) (e : Wire r s) : Wire (p.tensor r) (q.tensor s) :=
  ⟨d.val.horizontal e.val, by rw [drawing_code_horiz, d.property, e.property]; rfl⟩

private theorem Wire.boundary (hc : EmptyCodeCoherence U)
    {p q : Word A B} (d : Wire p q) : p.boundary = q.boundary :=
  (hc d.val d.property).choose

private theorem Wire.directions (hc : EmptyCodeCoherence U)
    {p q : Word A B} (d : Wire p q) : p.directions = q.directions := by
  simpa only [boundaryDirections_word] using congrArg boundaryDirections (d.boundary hc)

private theorem appendCode (p : Boundary A B) (q : Boundary B C) :
    code (p.appendDiagram (R := Complex) q).drawing = [] ∧
    code (p.splitDiagram (R := Complex) q).drawing = [] := by
  induction p with
  | empty => exact ⟨rfl, rfl⟩
  | cons s rest ih =>
    constructor
    · change code ((Diagram.associate (R := Complex) s.word rest.word q.word).vertical
        ((Diagram.id s.word).horizontal (rest.appendDiagram q))).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, (ih q).1]
      rfl
    · change code (((Diagram.id (R := Complex) s.word).horizontal (rest.splitDiagram q)).vertical
        (Diagram.unassociate s.word rest.word q.word)).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, (ih q).2]
      rfl

private theorem reorderCode (p : Word A B) :
    code (p.reorderToBoundary (R := Complex)).drawing = [] ∧
    code (p.reorderFromBoundary (R := Complex)).drawing = [] := by
  induction p with
  | empty | up | down => exact ⟨rfl, rfl⟩
  | tensor p q hp hq =>
    constructor
    · change code (((p.reorderToBoundary (R := Complex)).horizontal q.reorderToBoundary).vertical
        (p.boundary.appendDiagram q.boundary)).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, hp.1, hq.1, (appendCode _ _).1]
      rfl
    · change code (((p.boundary.splitDiagram (R := Complex) q.boundary)).vertical
        (p.reorderFromBoundary.horizontal q.reorderFromBoundary)).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, hp.2, hq.2, (appendCode _ _).2]
      rfl

private def Wire.between (p q : Word A B) (h : p.boundary = q.boundary) : Wire p q :=
  (show Wire p p.boundary.word from ⟨.ordinary p.reorderToBoundary, (reorderCode p).1⟩).vertical
    (show Wire p.boundary.word q from h.symm ▸
      (show Wire q.boundary.word q from ⟨.ordinary q.reorderFromBoundary, (reorderCode q).2⟩))

private def Framed {p q r s : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) (g : Biset.Hom Complex r.basis s.basis) : Prop :=
  ∃ (pre : Wire p r) (post : Wire s q), f = pre.eval.vertical (g.vertical post.eval)

private theorem Framed.self {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) :
    Framed f f := by
  refine ⟨Wire.id p, Wire.id q, ?_⟩
  change f = (Biset.Hom.id _).vertical (f.vertical (Biset.Hom.id _))
  rw [id_vertical, vertical_id]

private theorem Framed.vertLeft {p q r s t : Word A B}
    (d : Wire p q) {f : Biset.Hom Complex q.basis r.basis}
    {g : Biset.Hom Complex s.basis t.basis} (h : Framed f g) : Framed (d.eval.vertical f) g := by
  obtain ⟨pre, post, rfl⟩ := h
  exact ⟨d.vertical pre, post, (vertical_assoc _ _ _).symm⟩

private theorem Framed.vertRight {p q r s t : Word A B}
    (d : Wire q r) {f : Biset.Hom Complex p.basis q.basis}
    {g : Biset.Hom Complex s.basis t.basis} (h : Framed f g) : Framed (f.vertical d.eval) g := by
  obtain ⟨pre, post, rfl⟩ := h
  refine ⟨pre, post.vertical d, ?_⟩
  simp only [Wire.vertical, Wire.eval, Subtype.coe_mk, LabelledDrawing.interpret, ScopedDiagram.eval, vertical_assoc]

private theorem Framed.trans {p q r s t z : Word A B}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    {k : Biset.Hom Complex t.basis z.basis} (h : Framed f g) (h' : Framed g k) : Framed f k := by
  obtain ⟨pre, post, rfl⟩ := h
  obtain ⟨pre', post', rfl⟩ := h'
  refine ⟨pre.vertical pre', post'.vertical post, ?_⟩
  simp only [Wire.vertical, Wire.eval, Subtype.coe_mk, LabelledDrawing.interpret, ScopedDiagram.eval, vertical_assoc]

private theorem Framed.horizontal {p q r s : Word A B} {p' q' r' s' : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    {f' : Biset.Hom Complex p'.basis q'.basis} {g' : Biset.Hom Complex r'.basis s'.basis}
    (h : Framed f g) (h' : Framed f' g') :
    Framed (p := p.tensor p') (q := q.tensor q') (r := r.tensor r') (s := s.tensor s')
      (f.horizontal f') (g.horizontal g') := by
  obtain ⟨pre, post, rfl⟩ := h
  obtain ⟨pre', post', rfl⟩ := h'
  refine ⟨pre.horizontal pre', post.horizontal post', ?_⟩
  change _ = (pre.eval.horizontal pre'.eval).vertical ((g.horizontal g').vertical (post.eval.horizontal post'.eval))
  simp only [horizontal_vertical]

private theorem Framed.boundaries (hc : EmptyCodeCoherence U) {p q r s : Word A B}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    (h : Framed f g) : p.boundary = r.boundary ∧ q.boundary = s.boundary :=
  ⟨h.choose.boundary hc, (h.choose_spec.choose.boundary hc).symm⟩

private theorem boundaryId_cancel {P Q R S : Boundary A B}
    (hp : P = R) (hq : S = Q) (m : BoundaryMap R S) :
    HEq ((boundaryId hp).vertical (m.vertical (boundaryId hq))) m := by
  subst P
  subst Q
  simp only [boundaryId, id_vertical, vertical_id]
  rfl

private theorem Framed.canonical (hc : EmptyCodeCoherence U) {p q r s : Word A B}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    (h : Framed f g) : HEq (canon f) (canon g) := by
  obtain ⟨pre, post, rfl⟩ := h
  obtain ⟨hp, ep⟩ := hc pre.val pre.property
  obtain ⟨hq, eq⟩ := hc post.val post.property
  change canon pre.eval = _ at ep
  change canon post.eval = _ at eq
  rw [canon_vertical, canon_vertical, ep, eq]
  exact boundaryId_cancel hp hq (canon g)

private theorem Wire.eval_eq (hc : EmptyCodeCoherence U) {p q : Word A B}
    (d e : Wire p q) : d.eval = e.eval := by
  obtain ⟨hp, hd⟩ := hc d.val d.property
  obtain ⟨hq, he⟩ := hc e.val e.property
  apply (ScopedDiagram.eval_atBoundary_eq_iff d.val.interpret e.val.interpret).mp
  exact hd.trans he.symm

private theorem frameStraight (hc : EmptyCodeCoherence U) {p q r : Word A B}
    (d : Wire p q) (h : p.boundary = r.boundary) :
    Framed d.eval (Biset.Hom.id (R := Complex) r.basis) := by
  let pre := Wire.between p r h
  let post := Wire.between r q (h.symm.trans (d.boundary hc))
  refine ⟨pre, post, ?_⟩
  rw [id_vertical]
  exact Wire.eval_eq hc d (pre.vertical post)

private theorem insertLeft_natural {p q : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) :
    (Biset.insertLeftUnit p.basis Complex).vertical
      ((Biset.Hom.id (Biset.regular A)).horizontal f) =
    f.vertical (Biset.insertLeftUnit q.basis Complex) := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  change (((Biset.Hom.id (Biset.regular A)).horizontal f).toLinearMap
      ((Biset.insertLeftUnit p.basis Complex).toLinearMap (Finsupp.single x r))) = _
  rw [Biset.insertLeftUnit, Biset.Hom.ofFunction_single, horizontal_single]
  change r • Biset.pairLinear Complex (Biset.regular A) q.basis (Finsupp.single 1 1)
      (f.toLinearMap (Finsupp.single x 1)) =
    (Biset.insertLeftUnit q.basis Complex).toLinearMap (f.toLinearMap (Finsupp.single x r))
  have aux (z : q.basis.carrier →₀ Complex) :
      Biset.pairLinear Complex (Biset.regular A) q.basis (Finsupp.single 1 1) z =
        (Biset.insertLeftUnit q.basis Complex).toLinearMap z := by
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro y s
    rw [Biset.pairLinear_single, one_mul, Biset.insertLeftUnit, Biset.Hom.ofFunction_single]
  rw [aux, ← map_smul, ← map_smul]
  simp [Finsupp.smul_single, smul_eq_mul]

private theorem insertRight_natural {p q : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) :
    (Biset.insertRightUnit p.basis Complex).vertical
      (f.horizontal (Biset.Hom.id (Biset.regular B))) =
    f.vertical (Biset.insertRightUnit q.basis Complex) := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  change ((f.horizontal (Biset.Hom.id (Biset.regular B))).toLinearMap
      ((Biset.insertRightUnit p.basis Complex).toLinearMap (Finsupp.single x r))) = _
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single, horizontal_single]
  change r • Biset.pairLinear Complex q.basis (Biset.regular B)
      (f.toLinearMap (Finsupp.single x 1)) (Finsupp.single 1 1) =
    (Biset.insertRightUnit q.basis Complex).toLinearMap (f.toLinearMap (Finsupp.single x r))
  have aux (z : q.basis.carrier →₀ Complex) :
      Biset.pairLinear Complex q.basis (Biset.regular B) z (Finsupp.single 1 1) =
        (Biset.insertRightUnit q.basis Complex).toLinearMap z := by
    change (Biset.pairLinear Complex q.basis (Biset.regular B)).flip (Finsupp.single 1 1) z = _
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro y s
    simp only [LinearMap.flip_apply, Biset.insertRightUnit, Biset.Hom.ofFunction_single]
    exact (Biset.pairLinear_single (R := Complex) q.basis (Biset.regular B) y 1 s 1).trans (by rw [mul_one])
  rw [aux, ← map_smul, ← map_smul]
  simp [Finsupp.smul_single, smul_eq_mul]

private theorem stripLeft {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) :
    Framed (p := (Word.empty A).tensor p) (q := (Word.empty A).tensor q)
      ((Biset.Hom.id (Biset.regular A)).horizontal f) f := by
  refine ⟨⟨.ordinary (.leftUnit p), rfl⟩, ⟨.ordinary (.insertLeftUnit q), rfl⟩, ?_⟩
  change _ = (Biset.leftUnit p.basis Complex).vertical (f.vertical (Biset.insertLeftUnit q.basis Complex))
  rw [← insertLeft_natural, ← vertical_assoc, Biset.leftUnit_insertLeftUnit, id_vertical]

private theorem stripRight {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) :
    Framed (p := p.tensor (Word.empty B)) (q := q.tensor (Word.empty B))
      (f.horizontal (Biset.Hom.id (Biset.regular B))) f := by
  refine ⟨⟨.ordinary (.rightUnit p), rfl⟩, ⟨.ordinary (.insertRightUnit q), rfl⟩, ?_⟩
  change _ = (Biset.rightUnit p.basis Complex).vertical (f.vertical (Biset.insertRightUnit q.basis Complex))
  rw [← insertRight_natural, ← vertical_assoc, Biset.rightUnit_insertRightUnit, id_vertical]

private theorem splitSingleton {c d : PlanarCode.Code} {e : PlanarEvent}
    (h : c ++ d = [e]) : (c = [] ∧ d = [e]) ∨ (c = [e] ∧ d = []) := by
  cases c with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons x xs =>
    simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, rfl⟩

private theorem shiftEmpty {i : Nat} {c : PlanarCode.Code}
    (h : PlanarCode.shift i c = []) : c = [] := by
  simpa only [PlanarCode.shift, List.map_eq_nil_iff] using h

private theorem transport_id_eq_boundaryId {G K : Subgroup U}
    {P Q : Boundary G K} (h : P = Q) :
    DotSlideStructuralCoherence.transport h
      (Biset.Hom.id (R := Complex) P.word.basis) = boundaryId h := by
  subst Q
  rfl

private theorem dot_empty_coherence : EmptyCodeCoherence U := by
  intro G K p q d h
  obtain ⟨he, hev⟩ := DotSlidePreorderProof.empty_geometry_atBoundary d h
  exact ⟨he, hev.trans (transport_id_eq_boundaryId he)⟩

private inductive ShortWord : {A B : Subgroup U} → Word A B → Type u
  | empty (A : Subgroup U) : ShortWord (.empty A)
  | strand {A B : Subgroup U} (s : Strand A B) : ShortWord s.word

private theorem shortBoundary (p : Boundary A B) (h : (boundaryDirections p).length ≤ 1) :
    ∃ r : Word A B, Nonempty (ShortWord r) ∧ p = r.boundary := by
  cases p with
  | empty => exact ⟨.empty _, ⟨.empty _⟩, rfl⟩
  | cons s t =>
    cases t with
    | empty => exact ⟨s.word, ⟨.strand s⟩, by cases s <;> rfl⟩
    | cons t rest => cases s <;> cases t <;> simp [boundaryDirections] at h

private inductive Atom : {A B : Subgroup U} → VertexKind → Word A B → Word A B → Type u
  | project {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
      (r : ConjEmbedding L H) (xs : List (Complex × ProjectionDot.Mixed a b l r)) :
      Atom .mixedProjection ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | parallel {K H H' G : Subgroup U}
      (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
      (zs : List (Complex × Dot (b.comp a) (b'.comp a'))) :
      Atom .parallelUp ((Word.up b).tensor (.up a)) ((Word.up b').tensor (.up a'))

private abbrev drawingId (p : Word A B) : LabelledDrawing Complex p p := .ordinary (.id p)

private def Atom.drawing {k : VertexKind} {p q : Word A B} :
    Atom k p q → LabelledDrawing Complex p q
  | .project a b l r xs => .compactProjection a b l r xs
  | .parallel b a b' a' zs => .parallelUp b a b' a' zs

private theorem Atom.width {k : VertexKind} {p q : Word A B} (a : Atom k p q) :
    p.directions.length = 2 := by cases a <;> rfl

private inductive Core : {A B : Subgroup U} → VertexKind → Nat →
    Word A B → Word A B → Type u
  | bare {A B : Subgroup U} {k : VertexKind} {p q : Word A B} (a : Atom k p q) : Core k 0 p q
  | left {A B C : Subgroup U} {k : VertexKind} {p q : Word B C} (s : Strand A B) (a : Atom k p q) :
      Core k 1 (s.word.tensor p) (s.word.tensor q)
  | right {A B C : Subgroup U} {k : VertexKind} {p q : Word A B} (a : Atom k p q) (s : Strand B C) :
      Core k 0 (p.tensor s.word) (q.tensor s.word)

private def Core.drawing {k : VertexKind} {n : Nat} {p q : Word A B} :
    Core k n p q → LabelledDrawing Complex p q
  | .bare a => a.drawing
  | .left s a => (drawingId s.word).horizontal a.drawing
  | .right a s => a.drawing.horizontal (drawingId s.word)

private theorem strandWidth (s : Strand A B) : s.word.directions.length = 1 := by cases s <;> rfl

private theorem Core.width {k : VertexKind} {n : Nat} {p q : Word A B} (c : Core k n p q) :
    2 ≤ p.directions.length := by
  cases c with
  | bare a => rw [a.width]
  | left s a => simp [Word.directions, strandWidth, a.width]
  | right a s => simp [Word.directions, strandWidth, a.width]

private def Normal {p q : Word A B} (k : VertexKind) (n : Nat)
    (f : Biset.Hom Complex p.basis q.basis) : Prop :=
  ∃ (r s : Word A B) (c : Core k n r s), Framed (p := p) (q := q) f c.drawing.interpret.eval

private theorem ShortWord.padLeft {k : VertexKind} {n : Nat} {p : Word A B}
    {r s : Word B C} (w : ShortWord p) (c : Core k n r s)
    (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := p.tensor s) k (p.directions.length + n)
      ((Biset.Hom.id p.basis).horizontal c.drawing.interpret.eval) := by
  cases w with
  | empty =>
    simp only [Word.directions, List.length_nil, Nat.zero_add]
    exact ⟨_, _, c, stripLeft _⟩
  | strand t =>
    rw [strandWidth]
    cases c with
    | bare a => exact ⟨_, _, .left t a, Framed.self _⟩
    | left t' a => simp [Word.directions, strandWidth, a.width] at hw
    | right a t' => simp [Word.directions, strandWidth, a.width] at hw

private theorem ShortWord.padRight {k : VertexKind} {n : Nat} {p q : Word A B}
    {r : Word B C} (c : Core k n p q) (w : ShortWord r)
    (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor r) k n
      (c.drawing.interpret.eval.horizontal (Biset.Hom.id r.basis)) := by
  cases w with
  | empty => exact ⟨_, _, c, stripRight _⟩
  | strand t =>
    cases c with
    | bare a => exact ⟨_, _, .right a t, Framed.self _⟩
    | left t' a => simp [Word.directions, strandWidth, a.width] at hw
    | right a t' => simp [Word.directions, strandWidth, a.width] at hw

private theorem padLeft {k : VertexKind} {n : Nat}
    {p q : Word A B} {r s : Word B C} (d : Wire p q)
    {f : Biset.Hom Complex r.basis s.basis} (h : Normal (p := r) (q := s) k n f)
    (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor s) k (q.directions.length + n)
      (d.eval.horizontal f) := by
  let hc : DotSlidePreorderProof.EmptyCodeCoherence U := dot_empty_coherence
  obtain ⟨r', s', c, hf⟩ := h
  have hr : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (hf.boundaries hc).1
  have hp : p.directions.length ≤ 1 := by
    rw [List.length_append, hr] at hw
    have := c.width
    omega
  obtain ⟨p', ⟨w⟩, hb⟩ := shortBoundary p.boundary (by rwa [boundaryDirections_word])
  have hp' : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  rw [← d.directions hc, hp']
  rw [hp', hr] at hw
  obtain ⟨v, z, c', h'⟩ := w.padLeft c hw
  exact ⟨v, z, c', ((frameStraight hc d hb).horizontal hf).trans h'⟩

private theorem padRight {k : VertexKind} {n : Nat}
    {p q : Word A B} {r s : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} (h : Normal (p := p) (q := q) k n f)
    (d : Wire r s) (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor s) k n (f.horizontal d.eval) := by
  let hc : DotSlidePreorderProof.EmptyCodeCoherence U := dot_empty_coherence
  obtain ⟨p', q', c, hf⟩ := h
  have hp : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (hf.boundaries hc).1
  have hr : r.directions.length ≤ 1 := by
    rw [List.length_append, hp] at hw
    have := c.width
    omega
  obtain ⟨r', ⟨w⟩, hb⟩ := shortBoundary r.boundary (by rwa [boundaryDirections_word])
  have hr' : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  rw [hp, hr'] at hw
  obtain ⟨v, z, c', h'⟩ := w.padRight c hw
  exact ⟨v, z, c', (hf.horizontal (frameStraight hc d hb)).trans h'⟩

private theorem shiftSingleton {k : VertexKind} {i n : Nat} {c : PlanarCode.Code}
    (h : PlanarCode.shift i c = [.vertex n k]) :
    ∃ m : Nat, c = [.vertex m k] ∧ i + m = n := by
  cases c with
  | nil => simp [PlanarCode.shift] at h
  | cons e es =>
    have ht := congrArg List.length h
    simp only [PlanarCode.shift, List.length_map, List.length_cons, List.length_nil] at ht
    have hz : es = [] := List.length_eq_zero_iff.mp (by omega)
    subst es
    cases e <;> simp [PlanarCode.shift, PlanarEvent.place, PlanarEvent.position] at h
    next m k' =>
      obtain ⟨hm, rfl⟩ := h
      exact ⟨m, rfl, hm⟩

private def Supported (k : VertexKind) : Prop := k = .mixedProjection ∨ k = .parallelUp

private abbrev Normalizes {p q : Word A B} (d : LabelledDrawing Complex p q) (k : VertexKind) :=
  ∀ n, code d.erase = [.vertex n k] → p.directions.length ≤ 3 →
    Normal (p := p) (q := q) k n d.interpret.eval

private theorem normalVertical {k : VertexKind} {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r)
    (hd : Normalizes d k) (he : Normalizes e k) : Normalizes (d.vertical e) k := by
  intro n h hw
  rw [drawing_code_vert] at h
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · let w : Wire p q := ⟨d, hd0⟩
    have hew : q.directions.length ≤ 3 := by rw [← w.directions dot_empty_coherence]; exact hw
    obtain ⟨s, t, c, hf⟩ := he n he1 hew
    exact ⟨s, t, c, hf.vertLeft w⟩
  · obtain ⟨s, t, c, hf⟩ := hd n hd1 hw
    exact ⟨s, t, c, hf.vertRight ⟨e, he0⟩⟩

private theorem normalHorizontal {k : VertexKind} {p q : Word A B} {r s : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex r s)
    (hd : Normalizes d k) (he : Normalizes e k) : Normalizes (d.horizontal e) k := by
  intro n h hw
  rw [drawing_code_horiz] at h
  change (p.directions ++ r.directions).length ≤ 3 at hw
  have hw' := hw
  rw [List.length_append] at hw'
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · obtain ⟨m, hm, rfl⟩ := shiftSingleton he1
    exact padLeft ⟨d, hd0⟩ (he m hm (by omega)) hw
  · exact padRight (hd n hd1 (by omega)) ⟨e, shiftEmpty he0⟩ hw

private theorem ordinaryProjection_eval {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (x : ProjectionDot.Mixed a b l r) :
    (Diagram.mixedProjection (R := Complex) a b l r x.dot x.finite).eval =
      (LabelledDrawing.compactProjection a b l r [(1, x)]).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change _ = (ScopedDiagram.linearCombination
    [(1, ScopedDiagram.ordinary (.mixedProjection a b l r x.dot x.finite))]).eval.toLinearMap z
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul]
  rfl

private theorem ordinarySingleton {k : VertexKind} (hk : Supported k)
    {p q : Word A B} (d : Diagram Complex p q) : Normalizes (.ordinary d) k := by
  induction d
  case vertical d e hd he => exact normalVertical (.ordinary d) (.ordinary e) hd he
  case horizontal d e hd he => exact normalHorizontal (.ordinary d) (.ordinary e) hd he
  case mixedProjection a b l r x hf =>
    intro n h _
    have h' : (.vertex 0 .mixedProjection : PlanarEvent) = .vertex n k := (List.cons.inj h).1
    cases h'
    let z : ProjectionDot.Mixed a b l r := ⟨x, hf⟩
    refine ⟨_, _, .bare (.project a b l r [(1, z)]), ?_⟩
    change Framed (Diagram.mixedProjection (R := Complex) a b l r x hf).eval
      (LabelledDrawing.compactProjection a b l r [(1, z)]).interpret.eval
    rw [← ordinaryProjection_eval a b l r z]
    exact Framed.self _
  all_goals
    intro n h _
    rcases hk with rfl | rfl <;>
      simp [code, LabelledDrawing.erase, Diagram.drawing, DrawingShape.geometry,
        PlanarCode.encode, VertexKind.canonical] at h

private theorem expanded_no_mark {k : VertexKind} (hk : Supported k) (n count : Nat)
    (opening : ProjectionOpening) (closing : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry count opening closing) ≠
      [.vertex n k] := by
  intro h
  apply (no_expandedProjection count opening closing).elim
  rw [h]
  rcases hk with rfl | rfl <;> simp [goodCode, isCompactCrossing]

private theorem drawingSingleton {k : VertexKind} (hk : Supported k)
    {p q : Word A B} (d : LabelledDrawing Complex p q) : Normalizes d k := by
  induction d
  case ordinary d => exact ordinarySingleton hk d
  case vertical d e hd he => exact normalVertical d e hd he
  case horizontal d e hd he => exact normalHorizontal d e hd he
  case compactProjection a b l r xs =>
    intro n h _
    have h' : (.vertex 0 .mixedProjection : PlanarEvent) = .vertex n k := (List.cons.inj h).1
    cases h'
    exact ⟨_, _, .bare (.project a b l r xs), Framed.self _⟩
  case parallelUp b a b' a' zs =>
    intro n h _
    have h' : (.vertex 0 .parallelUp : PlanarEvent) = .vertex n k := (List.cons.inj h).1
    cases h'
    exact ⟨_, _, .bare (.parallel b a b' a' zs), Framed.self _⟩
  case trivalent v =>
    intro n h _
    cases v <;> rcases hk with rfl | rfl <;>
      simp [code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode,
        VertexKind.canonical, TrivalentVertex.kind] at h
  case bentVertex v =>
    intro n h _
    cases v <;> rcases hk with rfl | rfl <;>
      simp [code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode,
        VertexKind.canonical, BentVertex.kind] at h
  case parallelUpChain labels =>
    intro n h _
    change PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack _) = _ at h
    rw [encode_stack] at h
    rcases hk with rfl | rfl <;> simp [PlanarCode.encode, VertexKind.canonical] at h
  case parallelDownChain labels =>
    intro n h _
    change PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack _) = _ at h
    rw [encode_stack] at h
    rcases hk with rfl | rfl <;> simp [PlanarCode.encode, VertexKind.canonical] at h
  case rightCurlUp =>
    intro n h _
    rcases hk with rfl | rfl <;>
      simp [code, LabelledDrawing.erase, DrawingShape.geometry, DrawingShape.rightCurlGeometry,
        DrawingShape.stack, PlanarCode.encode, VertexKind.canonical, PlanarCode.shift,
        DrawingShape.outputs, PlanarEvent.place, PlanarEvent.position] at h
  case expandedProjection _ _ _ _ xs opening closing =>
    intro n h _
    exact (expanded_no_mark hk n 1 opening closing h).elim
  case expandedProjectionChain _ _ _ _ xs _ opening closing =>
    intro n h _
    exact (expanded_no_mark hk n xs.length opening closing h).elim
  case expandedLinearDotProjection _ _ _ _ xs _ opening closing =>
    intro n h _
    exact (expanded_no_mark hk n xs.length opening closing h).elim
  all_goals
    intro n h _
    rcases hk with rfl | rfl <;>
      simp [code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h


abbrev upDownUp {G B D F : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) : Word G F :=
  ((Word.up r).tensor (.down s)).tensor (.up c)

abbrev upUpDown {G B L F : Subgroup U} (r : ConjEmbedding B G)
    (t : ConjEmbedding L B) (j : ConjEmbedding L F) : Word G F :=
  ((Word.up r).tensor (.up t)).tensor (.down j)

def rightProjection {G B D F L : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) (t : ConjEmbedding L B)
    (j : ConjEmbedding L F) (xs : List (Complex × ProjectionDot.Mixed s c t j)) :
    LabelledDrawing Complex (upDownUp r s c) (upUpDown r t j) :=
  LabelledDrawing.vertical (.ordinary (.associate (.up r) (.down s) (.up c)))
    (((drawingId (.up r)).horizontal (.compactProjection s c t j xs)).vertical
      (.ordinary (.unassociate (.up r) (.up t) (.down j))))

/-- Evaluate at the specified, ordered labelled boundaries. -/
noncomputable def evalAt {p q : Word A B} {P Q : Boundary A B}
    (d : LabelledDrawing Complex p q) (hp : p.boundary = P) (hq : q.boundary = Q) :
    Biset.Hom Complex P.word.basis Q.word.basis := by
  subst P
  subst Q
  exact d.interpret.atBoundary.eval

private theorem evalAt_heq {p q : Word A B} {P Q : Boundary A B}
    (d : LabelledDrawing Complex p q) (hp : p.boundary = P) (hq : q.boundary = Q) :
    HEq (evalAt d hp hq) (canon d.interpret.eval) := by
  cases hp
  cases hq
  rfl

private theorem rightProjection_canon {G B D F L : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) (t : ConjEmbedding L B)
    (j : ConjEmbedding L F) (xs : List (Complex × ProjectionDot.Mixed s c t j)) :
    HEq (canon (rightProjection r s c t j xs).interpret.eval)
      (canon ((drawingId (.up r)).horizontal
        (.compactProjection s c t j xs)).interpret.eval) := by
  let cross := (drawingId (.up r)).horizontal (.compactProjection s c t j xs)
  have h : Framed (rightProjection r s c t j xs).interpret.eval cross.interpret.eval :=
    ⟨⟨.ordinary (.associate (.up r) (.down s) (.up c)), rfl⟩,
     ⟨.ordinary (.unassociate (.up r) (.up t) (.down j)), rfl⟩, rfl⟩
  exact h.canonical dot_empty_coherence

private theorem upDownUp_inj {G B B' D D' F : Subgroup U}
    {r : ConjEmbedding B G} {s : ConjEmbedding B D} {c : ConjEmbedding F D}
    {r' : ConjEmbedding B' G} {s' : ConjEmbedding B' D'} {c' : ConjEmbedding F D'}
    (h : (upDownUp r' s' c').boundary = (upDownUp r s c).boundary) :
    B' = B ∧ D' = D ∧ HEq r' r ∧ HEq s' s ∧ HEq c' c := by
  change Boundary.cons (.up r') (Boundary.cons (.down s') (Boundary.cons (.up c') (.empty F))) =
    Boundary.cons (.up r) (Boundary.cons (.down s) (Boundary.cons (.up c) (.empty F))) at h
  injection h with _ eB _ hr htail
  subst B'
  have ht := eq_of_heq htail
  injection ht with _ eD _ hs htail'
  subst D'
  have hlast := eq_of_heq htail'
  injection hlast with _ _ _ hc _
  have rr := eq_of_heq hr
  have ss := eq_of_heq hs
  have er : r' = r := by injection rr
  have es : s' = s := by injection ss
  have ec : c' = c := by injection hc
  exact ⟨rfl, rfl, heq_of_eq er, heq_of_eq es, heq_of_eq ec⟩

/-- Normalize stage two at the shared input and its actual ordered output.
Each retained list entry carries its termwise finite-fibre proof. -/
theorem secondStage {G B D F : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) {p q : Word G F}
    (draw : LabelledDrawing Complex p q)
    (hcode : PlanarCode.encode draw.erase.geometry = [.vertex 1 .mixedProjection])
    (hin : p.boundary = (upDownUp r s c).boundary) :
    ∃ (L : Subgroup U) (t : ConjEmbedding L B) (j : ConjEmbedding L F)
      (ys : List (Complex × ProjectionDot.Mixed s c t j))
      (hout : (upUpDown r t j).boundary = q.boundary),
      evalAt draw hin rfl = evalAt (rightProjection r s c t j ys) rfl hout := by
  have hdirs : p.directions = [true, false, true] := by
    have hh := congrArg boundaryDirections hin
    rw [boundaryDirections_word] at hh
    exact hh
  have hwidth : p.directions.length ≤ 3 := by rw [hdirs]; decide
  obtain ⟨_, _, core, hf⟩ := drawingSingleton (.inl rfl) draw 1 hcode hwidth
  cases core with
  | left head atom =>
    obtain ⟨hb, ht⟩ := hf.boundaries dot_empty_coherence
    cases atom with
    | project s' c' t j ys =>
      have hb' := hb.symm.trans hin
      cases head with
      | down r' =>
        have bad := congrArg boundaryDirections hb'
        change [false, false, true] = [true, false, true] at bad
        contradiction
      | up r' =>
        obtain ⟨eB, eD, er, es, ec⟩ := upDownUp_inj hb'
        subst_vars
        have er' := eq_of_heq er
        have es' := eq_of_heq es
        have ec' := eq_of_heq ec
        subst r'
        subst s'
        subst c'
        have hout : (upUpDown r t j).boundary = q.boundary := ht.symm
        refine ⟨_, t, j, ys, hout, ?_⟩
        exact eq_of_heq ((evalAt_heq draw hin rfl).trans
          ((hf.canonical dot_empty_coherence).trans
            ((rightProjection_canon r s c t j ys).symm.trans
              (evalAt_heq (rightProjection r s c t j ys) rfl hout).symm)))


/-- Retain the actual last strand, including its starting subgroup and label. -/
def suffix : {G F : Subgroup U} → Boundary G F → Option (Σ L : Subgroup U, Strand L F)
  | _, _, .empty _ => none
  | _, _, .cons s (.empty _) => some ⟨_, s⟩
  | _, _, .cons _ (.cons t rest) => suffix (.cons t rest)

/-- A left parallel crossing on a three-strand input preserves the labelled suffix. -/
theorem parallelSuffix {p q : Word A B} (draw : LabelledDrawing Complex p q)
    (hcode : PlanarCode.encode draw.erase.geometry = [.vertex 0 .parallelUp])
    (hwidth : p.directions.length = 3) :
    suffix p.boundary = suffix q.boundary := by
  obtain ⟨_, _, core, hf⟩ :=
    drawingSingleton (.inr rfl) draw 0 hcode (by rw [hwidth])
  obtain ⟨hb, ht⟩ := hf.boundaries dot_empty_coherence
  cases core with
  | bare atom =>
    have hd := congrArg (fun b => (boundaryDirections b).length) hb
    simp only [boundaryDirections_word, hwidth, atom.width] at hd
    contradiction
  | right atom s =>
    refine (congrArg suffix hb).trans (Eq.trans ?_ (congrArg suffix ht.symm))
    cases atom
    cases s <;> rfl

/-- The exact top boundary fixes both the common subgroup and the outgoing restriction. -/
theorem secondStage_fixedSuffix {G B D F C T : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (e : ConjEmbedding T C) (f : ConjEmbedding T F)
    {p q v : Word G F} (stage₂ : LabelledDrawing Complex p q)
    (stage₃ : LabelledDrawing Complex q v)
    (hc₂ : PlanarCode.encode stage₂.erase.geometry = [.vertex 1 .mixedProjection])
    (hc₃ : PlanarCode.encode stage₃.erase.geometry = [.vertex 0 .parallelUp])
    (hin : p.boundary = (upDownUp r s c).boundary)
    (htop : v.boundary = (upUpDown d e f).boundary) :
    ∃ (t : ConjEmbedding T B) (ys : List (Complex × ProjectionDot.Mixed s c t f))
      (hout : (upUpDown r t f).boundary = q.boundary),
      evalAt stage₂ hin rfl = evalAt (rightProjection r s c t f ys) rfl hout := by
  obtain ⟨L, t, j, ys, hout, heval⟩ := secondStage r s c stage₂ hc₂ hin
  have hwidth : q.directions.length = 3 := by
    have h := congrArg (fun b => (boundaryDirections b).length) hout.symm
    simpa only [boundaryDirections_word] using h
  have hsuff := (congrArg suffix hout).trans
    ((parallelSuffix stage₃ hc₃ hwidth).trans (congrArg suffix htop))
  change some (⟨L, Strand.down j⟩ : Σ X : Subgroup U, Strand X F) =
    some ⟨T, Strand.down f⟩ at hsuff
  have hpair := Option.some.inj hsuff
  have hgroup : L = T := congrArg Sigma.fst hpair
  subst L
  have hstrand := eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
  have hj : j = f := by injection hstrand
  subst j
  exact ⟨t, ys, hout, heval⟩

/-- Apply the checked cut to supply the second and third exact singleton stages. -/
theorem factor_connection {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : PlanarCode.encode d.erase.geometry =
      [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp]) :
    ∃ (m n : Word A B) (d₁ : LabelledDrawing Complex p m)
      (d₂ : LabelledDrawing Complex m n) (d₃ : LabelledDrawing Complex n q),
      PlanarCode.encode d₁.erase.geometry = [.vertex 0 .mixedProjection] ∧
      PlanarCode.encode d₂.erase.geometry = [.vertex 1 .mixedProjection] ∧
      PlanarCode.encode d₃.erase.geometry = [.vertex 0 .parallelUp] ∧
      d.interpret.eval = d₁.interpret.eval.vertical
        (d₂.interpret.eval.vertical d₃.interpret.eval) :=
  CaseTwoFactor.factor_left d h

end CaseTwoStage

#print axioms CaseTwoStage.secondStage
#print axioms CaseTwoStage.secondStage_fixedSuffix
#print axioms CaseTwoStage.factor_connection
