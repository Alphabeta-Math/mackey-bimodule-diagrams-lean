import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.PlanarShape
import Proofs.InductionMergeDotSlide
import Proofs.FixedBoundaryReplacementPreorder
import Proofs.RightInputDotSlideObstruction

set_option maxHeartbeats 2000000

namespace DotSlidePreorderProof

open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {A B C D : Subgroup U}

private abbrev mark (n : Nat) : PlanarEvent := .vertex n .upDot
private abbrev join (n : Nat) : PlanarEvent := .vertex n (.trivalent .mergeUp)
private abbrev rightCode : PlanarCode.Code := [mark 1, join 0]

private theorem rigid_rightCode {a b : PlanarCode.Code} (h : PlanarCode.Equivalent a b) :
    (∀ l r, l ++ a ++ r = rightCode → a = b) ∧
    (∀ l r, l ++ b ++ r = rightCode → a = b) := by
  induction h with
  | refl => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | symm h ih =>
    exact ⟨fun l r e => (ih.2 l r e).symm, fun l r e => (ih.1 l r e).symm⟩
  | trans _ _ ih₁ ih₂ =>
    constructor
    · intro l r e
      have h₁ := ih₁.1 l r e
      exact h₁.trans (ih₂.1 l r (h₁ ▸ e))
    · intro l r e
      have h₂ := ih₂.2 l r e
      exact (ih₁.2 l r (h₂.symm ▸ e)).trans h₂
  | context l r h ih =>
    exact ⟨fun l' r' e => congrArg (fun x => l ++ x ++ r)
      (ih.1 (l' ++ l) (r ++ r') (by simpa only [List.append_assoc] using e)),
      fun l' r' e => congrArg (fun x => l ++ x ++ r)
      (ih.2 (l' ++ l) (r ++ r') (by simpa only [List.append_assoc] using e))⟩
  | exchange before after i gap left right =>
    constructor <;> intro l r e <;>
      have hlen := congrArg List.length e <;>
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen <;>
      have hb : before = [] := List.length_eq_zero_iff.mp (by omega) <;>
      have ha : after = [] := List.length_eq_zero_iff.mp (by omega) <;>
      have hl : l = [] := List.length_eq_zero_iff.mp (by omega) <;>
      have hr : r = [] := List.length_eq_zero_iff.mp (by omega) <;>
      subst before <;> subst after <;> subst l <;> subst r <;>
      simp only [List.nil_append, List.append_nil, List.cons.injEq] at e
    · have h₁ := congrArg PlanarEvent.position e.1
      have h₂ := congrArg PlanarEvent.position e.2.1
      cases left <;> cases right <;> simp [PlanarEvent.place, PlanarEvent.position] at h₁ h₂ <;> omega
    · have h₁ := congrArg PlanarEvent.position e.1
      have h₂ := congrArg PlanarEvent.position e.2.1
      have hk : left.place i = join 0 := e.2.1
      have hind : (left.place i).inputs.length = 2 := by rw [hk]; rfl
      cases left <;> cases right <;> simp [PlanarEvent.place, PlanarEvent.position, PlanarEvent.inputs] at h₁ h₂ hind ⊢ <;> omega
  | @scale i below above a b _ _ =>
    constructor <;> intro l r e
    · have hm : PlanarEvent.scale i below above a ∈ rightCode := by rw [← e]; simp
      simp at hm
    · have hm : PlanarEvent.scale i below above b ∈ rightCode := by rw [← e]; simp
      simp at hm
  | @add i below above a b c d _ _ _ _ =>
    constructor <;> intro l r e
    · have hm : PlanarEvent.add i below above a c ∈ rightCode := by rw [← e]; simp
      simp at hm
    · have hm : PlanarEvent.add i below above b d ∈ rightCode := by rw [← e]; simp
      simp at hm

private theorem code_eq_of_right {a : PlanarCode.Code}
    (h : Quotient.mk PlanarCode.setoid a = Quotient.mk PlanarCode.setoid rightCode) :
    a = rightCode :=
  (rigid_rightCode (Quotient.exact h)).2 [] [] rfl

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

private theorem fiber_code {p q : Boundary A B}
    (v : LabelledDrawing.PlanarAtBoundary Complex p q
      ⟨[true,true], [true], Quotient.mk PlanarCode.setoid rightCode⟩) :
    PlanarCode.encode v.diagram.erase.geometry = rightCode := by
  apply code_eq_of_right
  exact congrArg PlanarShape.wiring v.shape_eq


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

variable {G H K : Subgroup U}

private abbrev BoundaryMap (p q : Boundary G K) :=
  Biset.Hom Complex p.word.basis q.word.basis

private noncomputable abbrev normalize {p q : Word G K} (d : ScopedDiagram Complex p q) :
    BoundaryMap p.boundary q.boundary := d.atBoundary.eval

private abbrev upPair (l : ConjEmbedding H G) (a : ConjEmbedding K H) :=
  (Word.up l).tensor (.up a)

private inductive StraightAt : (p q : Boundary G K) → BoundaryMap p q → Prop
  | id (p : Boundary G K) : StraightAt p p (Biset.Hom.id _)

private inductive MergeAt : (p q : Boundary G K) → BoundaryMap p q → Prop
  | vertex (H : Subgroup U) (l : ConjEmbedding H G) (a : ConjEmbedding K H) :
    MergeAt (upPair l a).boundary (Word.up (l.comp a)).boundary
      (normalize (.ordinary (.mergeUp l a)))

/-- The only coherence input. Empty code evaluates to the identity at the
common ordered labelled boundary. -/
private def EmptyCodeCoherence (U : Type u) [Group U] : Prop :=
  ∀ {G K : Subgroup U} {p q : Word G K} (d : LabelledDrawing Complex p q),
    code d.erase = [] → StraightAt p.boundary q.boundary (normalize d.interpret)

private noncomputable def juxtaposeMap
    {p q : Boundary G H} {r s : Boundary H K}
    (f : BoundaryMap p q) (g : BoundaryMap r s) : BoundaryMap (p.append r) (q.append s) :=
  (p.splitDiagram r).eval.vertical ((f.horizontal g).vertical (q.appendDiagram s).eval)

private theorem normalize_vertical {p q r : Word G K}
    (d : ScopedDiagram Complex p q) (e : ScopedDiagram Complex q r) :
    normalize (d.vertical e) = (normalize d).vertical (normalize e) := by
  let fp := (p.reorderFromBoundary (R := Complex)).eval
  let tq := (q.reorderToBoundary (R := Complex)).eval
  let fq := (q.reorderFromBoundary (R := Complex)).eval
  let tr := (r.reorderToBoundary (R := Complex)).eval
  change fp.vertical ((d.eval.vertical e.eval).vertical tr) =
    (fp.vertical (d.eval.vertical tq)).vertical (fq.vertical (e.eval.vertical tr))
  have h : tq.vertical fq = Biset.Hom.id _ := Word.eval_reorderToFrom q
  simp only [Biset.Hom.vertical_assoc]
  rw [← Biset.Hom.vertical_assoc tq, h, Biset.Hom.id_vertical]

private theorem normalize_horizontal {p q : Word G H} {r s : Word H K}
    (d : ScopedDiagram Complex p q) (e : ScopedDiagram Complex r s) :
    normalize (d.horizontal e) = juxtaposeMap (normalize d) (normalize e) := by
  change ((p.boundary.splitDiagram (R := Complex) r.boundary).eval.vertical
      ((p.reorderFromBoundary (R := Complex)).eval.horizontal r.reorderFromBoundary.eval)).vertical
      ((d.eval.horizontal e.eval).vertical
        (((q.reorderToBoundary (R := Complex)).eval.horizontal s.reorderToBoundary.eval).vertical
          (q.boundary.appendDiagram s.boundary).eval)) = _
  unfold juxtaposeMap
  change _ = (p.boundary.splitDiagram (R := Complex) r.boundary).eval.vertical
    ((((p.reorderFromBoundary (R := Complex)).eval.vertical
        (d.eval.vertical q.reorderToBoundary.eval)).horizontal
      ((r.reorderFromBoundary (R := Complex)).eval.vertical
        (e.eval.vertical s.reorderToBoundary.eval))).vertical
      (q.boundary.appendDiagram s.boundary).eval)
  rw [← Biset.Hom.horizontal_vertical, ← Biset.Hom.horizontal_vertical]
  simp only [Biset.Hom.vertical_assoc]

private theorem normalize_id (p : Word G K) :
    normalize (.ordinary (.id p)) = Biset.Hom.id _ := Word.eval_reorderFromTo p

private theorem straight_boundary_eq {p q : Boundary G K} {f : BoundaryMap p q}
    (h : StraightAt p q f) : p = q := by
  cases h
  rfl

private theorem vertical_straight_left
    {p q r : Boundary G K} {f : BoundaryMap p q} {g : BoundaryMap q r}
    (hf : StraightAt p q f) (hg : MergeAt q r g) :
    MergeAt p r (f.vertical g) := by
  cases hf
  simpa only [Biset.Hom.id_vertical] using hg

private theorem vertical_straight_right
    {p q r : Boundary G K} {f : BoundaryMap p q} {g : BoundaryMap q r}
    (hf : MergeAt p q f) (hg : StraightAt q r g) :
    MergeAt p r (f.vertical g) := by
  cases hg
  simpa only [Biset.Hom.vertical_id] using hf

private theorem pad_left_eval {X Y : Biset G K} (f : Biset.Hom Complex X Y) :
    ((Biset.insertLeftUnit X Complex).vertical
      ((Biset.Hom.id (Biset.regular G)).horizontal f)).vertical
        (Biset.leftUnit Y Complex) = f := by
  have h (Z : Biset G K) (w : Z.carrier →₀ Complex) :
      (Biset.insertLeftUnit Z Complex).toLinearMap w =
        Biset.pairLinear Complex (Biset.regular G) Z (Finsupp.single 1 1) w := by
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro z c
    rw [Biset.pairLinear_single, one_mul]
    exact Biset.Hom.ofFunction_single _ _ _ _
  have commute : (Biset.insertLeftUnit X Complex).vertical
      ((Biset.Hom.id (Biset.regular G)).horizontal f) =
      f.vertical (Biset.insertLeftUnit Y Complex) := by
    apply Biset.Hom.ext
    apply LinearMap.ext
    intro w
    change (((Biset.Hom.id (Biset.regular G)).horizontal f).toLinearMap
        ((Biset.insertLeftUnit X Complex).toLinearMap w)) =
      (Biset.insertLeftUnit Y Complex).toLinearMap (f.toLinearMap w)
    rw [h, h, Biset.Hom.horizontal_pairLinear]
    rfl
  rw [commute, Biset.Hom.vertical_assoc, Biset.insertLeftUnit_leftUnit, Biset.Hom.vertical_id]

private theorem pad_right_eval {X Y : Biset G K} (f : Biset.Hom Complex X Y) :
    ((Biset.insertRightUnit X Complex).vertical
      (f.horizontal (Biset.Hom.id (Biset.regular K)))).vertical
        (Biset.rightUnit Y Complex) = f := by
  have h (Z : Biset G K) (w : Z.carrier →₀ Complex) :
      (Biset.insertRightUnit Z Complex).toLinearMap w =
        Biset.pairLinear Complex Z (Biset.regular K) w (Finsupp.single 1 1) := by
    change (Biset.insertRightUnit Z Complex).toLinearMap w =
      ((Biset.pairLinear Complex Z (Biset.regular K)).flip (Finsupp.single 1 1)) w
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro z c
    change (Biset.insertRightUnit Z Complex).toLinearMap (Finsupp.single z c) =
      Biset.pairLinear Complex Z (Biset.regular K) (Finsupp.single z c) (Finsupp.single 1 1)
    rw [Biset.pairLinear_single, mul_one]
    exact Biset.Hom.ofFunction_single _ _ _ _
  have commute : (Biset.insertRightUnit X Complex).vertical
      (f.horizontal (Biset.Hom.id (Biset.regular K))) =
      f.vertical (Biset.insertRightUnit Y Complex) := by
    apply Biset.Hom.ext
    apply LinearMap.ext
    intro w
    change ((f.horizontal (Biset.Hom.id (Biset.regular K))).toLinearMap
        ((Biset.insertRightUnit X Complex).toLinearMap w)) =
      (Biset.insertRightUnit Y Complex).toLinearMap (f.toLinearMap w)
    rw [h, h, Biset.Hom.horizontal_pairLinear]
    rfl
  rw [commute, Biset.Hom.vertical_assoc, Biset.insertRightUnit_rightUnit, Biset.Hom.vertical_id]

private theorem remove_padding
    {p q p' q' : Boundary G K} {f : BoundaryMap p p'} {g : BoundaryMap p' q'}
    {h : BoundaryMap q' q} (hf : StraightAt p p' f) (hh : StraightAt q' q h)
    (hm : MergeAt p q ((f.vertical g).vertical h)) : MergeAt p' q' g := by
  cases hf
  cases hh
  simpa only [Biset.Hom.id_vertical, Biset.Hom.vertical_id] using hm

private theorem merge_pad_left (empty : EmptyCodeCoherence U)
    {p q : Boundary G K} {f : BoundaryMap p q} (h : MergeAt p q f) :
    MergeAt ((Boundary.empty G).append p) ((Boundary.empty G).append q)
      (juxtaposeMap (Biset.Hom.id (R := Complex) (Boundary.empty G).word.basis) f) := by
  cases h with
  | vertex H l a =>
    let p := upPair l a
    let q := Word.up (l.comp a)
    let merge : ScopedDiagram Complex p q := .ordinary (.mergeUp l a)
    let padded := (ScopedDiagram.ordinary (Diagram.id (R := Complex) (Word.empty G))).horizontal merge
    let ins : Diagram Complex p ((Word.empty G).tensor p) := .insertLeftUnit p
    let rem : Diagram Complex ((Word.empty G).tensor q) q := .leftUnit q
    have he : ((ScopedDiagram.ordinary ins).vertical padded |>.vertical (.ordinary rem)).eval =
        merge.eval := pad_left_eval merge.eval
    have hm : MergeAt p.boundary q.boundary (normalize (((ScopedDiagram.ordinary ins).vertical padded).vertical (.ordinary rem))) := by
      have hn : normalize (((ScopedDiagram.ordinary ins).vertical padded).vertical (.ordinary rem)) =
          normalize merge := (ScopedDiagram.eval_atBoundary_eq_iff _ _).2 he
      rw [hn]
      exact MergeAt.vertex H l a
    rw [normalize_vertical, normalize_vertical] at hm
    have hpad := remove_padding (empty (.ordinary ins) rfl) (empty (.ordinary rem) rfl) hm
    dsimp only [padded] at hpad
    rw [normalize_horizontal, normalize_id] at hpad
    exact hpad

private theorem merge_pad_right (empty : EmptyCodeCoherence U)
    {p q : Boundary G K} {f : BoundaryMap p q} (h : MergeAt p q f) :
    MergeAt (p.append (.empty K)) (q.append (.empty K))
      (juxtaposeMap f (Biset.Hom.id (R := Complex) (Boundary.empty K).word.basis)) := by
  cases h with
  | vertex H l a =>
    let p := upPair l a
    let q := Word.up (l.comp a)
    let merge : ScopedDiagram Complex p q := .ordinary (.mergeUp l a)
    let padded := merge.horizontal (ScopedDiagram.ordinary (Diagram.id (R := Complex) (Word.empty K)))
    let ins : Diagram Complex p (p.tensor (.empty K)) := .insertRightUnit p
    let rem : Diagram Complex (q.tensor (.empty K)) q := .rightUnit q
    have he : ((ScopedDiagram.ordinary ins).vertical padded |>.vertical (.ordinary rem)).eval =
        merge.eval := pad_right_eval merge.eval
    have hm : MergeAt p.boundary q.boundary (normalize (((ScopedDiagram.ordinary ins).vertical padded).vertical (.ordinary rem))) := by
      have hn : normalize (((ScopedDiagram.ordinary ins).vertical padded).vertical (.ordinary rem)) =
          normalize merge := (ScopedDiagram.eval_atBoundary_eq_iff _ _).2 he
      rw [hn]
      exact MergeAt.vertex H l a
    rw [normalize_vertical, normalize_vertical] at hm
    have hpad := remove_padding (empty (.ordinary ins) rfl) (empty (.ordinary rem) rfl) hm
    dsimp only [padded] at hpad
    rw [normalize_horizontal, normalize_id] at hpad
    exact hpad

private def boundaryDirs : {G K : Subgroup U} → Boundary G K → List Bool
  | _, _, .empty _ => []
  | _, _, .cons (.up _) rest => true :: boundaryDirs rest
  | _, _, .cons (.down _) rest => false :: boundaryDirs rest

private theorem boundaryDirs_append (p : Boundary G H) (q : Boundary H K) :
    boundaryDirs (p.append q) = boundaryDirs p ++ boundaryDirs q := by
  induction p with
  | empty => rfl
  | cons s rest ih => cases s <;> simp only [Boundary.append, boundaryDirs, ih, List.cons_append]

private theorem word_boundaryDirs (p : Word G K) : boundaryDirs p.boundary = p.directions := by
  induction p with
  | empty | up | down => rfl
  | tensor p q hp hq => simp only [Word.boundary, Word.directions, boundaryDirs_append, hp, hq]

private theorem merge_input_dirs {p q : Boundary G K} {f : BoundaryMap p q}
    (h : MergeAt p q f) : boundaryDirs p = [true, true] := by
  cases h
  rfl

private theorem merge_horizontal_left
    (empty : EmptyCodeCoherence U)
    {p q : Boundary G H} {r s : Boundary H K}
    {f : BoundaryMap p q} {g : BoundaryMap r s}
    (hf : MergeAt p q f) (hg : StraightAt r s g) (hr : boundaryDirs r = []) :
    MergeAt (p.append r) (q.append s) (juxtaposeMap f g) := by
  cases hg
  rename_i r
  cases r with
  | empty => exact merge_pad_right empty hf
  | cons t tail => cases t <;> cases hr

private theorem merge_horizontal_right
    (empty : EmptyCodeCoherence U)
    {p q : Boundary G H} {r s : Boundary H K}
    {f : BoundaryMap p q} {g : BoundaryMap r s}
    (hf : StraightAt p q f) (hg : MergeAt r s g) (hp : boundaryDirs p = []) :
    MergeAt (p.append r) (q.append s) (juxtaposeMap f g) := by
  cases hf
  rename_i p
  cases p with
  | empty => exact merge_pad_left empty hg
  | cons t tail => cases t <;> cases hp

private theorem append_singleton {x y : PlanarCode.Code} {v : PlanarEvent}
    (h : x ++ y = [v]) : (x = [] ∧ y = [v]) ∨ (x = [v] ∧ y = []) := by
  cases x with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons w xs =>
    have ⟨hw, ht⟩ := List.cons.inj h
    have ⟨hx, hy⟩ := List.append_eq_nil_iff.mp ht
    exact Or.inr ⟨by rw [hw, hx], hy⟩

private theorem shift_eq_nil {n : Nat} {x : PlanarCode.Code}
    (h : PlanarCode.shift n x = []) : x = [] := by
  cases x with
  | nil => rfl
  | cons e es => cases h

private theorem shift_merge {n : Nat} {x : PlanarCode.Code}
    (h : PlanarCode.shift n x = [join 0]) : x = [join 0] := by
  cases x with
  | nil => cases h
  | cons e es =>
    have ⟨he, ht⟩ := List.cons.inj h
    have hn : n + e.position = 0 := by
      have hh := congrArg PlanarEvent.position he
      cases e <;> exact hh
    have hn' : n = 0 := by omega
    rwa [hn', shift_zero] at h

private def MergeClaim {p q : Word G K} (d : LabelledDrawing Complex p q) : Prop :=
  code d.erase = [join 0] → p.directions.length ≤ 2 →
    MergeAt p.boundary q.boundary (normalize d.interpret)

private theorem merge_vertical_step (empty : EmptyCodeCoherence U)
    {p q r : Word G K} (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r)
    (hd : MergeClaim d) (he : MergeClaim e) : MergeClaim (d.vertical e) := by
  intro hc hw
  rw [drawing_code_vert] at hc
  change MergeAt p.boundary r.boundary (normalize (d.interpret.vertical e.interpret))
  rw [normalize_vertical]
  rcases append_singleton hc with ⟨hd₀, he₁⟩ | ⟨hd₁, he₀⟩
  · have h := empty d hd₀
    have hdirs := congrArg boundaryDirs (straight_boundary_eq h)
    rw [word_boundaryDirs, word_boundaryDirs] at hdirs
    exact vertical_straight_left h (he he₁ (hdirs ▸ hw))
  · exact vertical_straight_right (hd hd₁ hw) (empty e he₀)

private theorem merge_horizontal_step (empty : EmptyCodeCoherence U)
    {p q : Word G H} {r s : Word H K} (d : LabelledDrawing Complex p q)
    (e : LabelledDrawing Complex r s) (hd : MergeClaim d) (he : MergeClaim e) :
    MergeClaim (d.horizontal e) := by
  intro hc hw
  rw [drawing_code_horiz] at hc
  change (p.directions ++ r.directions).length ≤ 2 at hw
  rw [List.length_append] at hw
  change MergeAt (p.boundary.append r.boundary) (q.boundary.append s.boundary)
    (normalize (d.interpret.horizontal e.interpret))
  rw [normalize_horizontal]
  rcases append_singleton hc with ⟨hd₀, he₁⟩ | ⟨hd₁, he₀⟩
  · have h := he (shift_merge he₁) (by omega)
    have hlen := congrArg List.length (merge_input_dirs h)
    rw [word_boundaryDirs] at hlen
    have hp : p.directions.length = 0 := by
      change r.directions.length = 2 at hlen
      omega
    exact merge_horizontal_right empty (empty d hd₀) h
      (by rw [word_boundaryDirs]; exact List.length_eq_zero_iff.mp hp)
  · have h := hd hd₁ (by omega)
    have hlen := congrArg List.length (merge_input_dirs h)
    rw [word_boundaryDirs] at hlen
    have hr : r.directions.length = 0 := by
      change p.directions.length = 2 at hlen
      omega
    exact merge_horizontal_left empty h (empty e (shift_eq_nil he₀))
      (by rw [word_boundaryDirs]; exact List.length_eq_zero_iff.mp hr)

private theorem diagram_merge (empty : EmptyCodeCoherence U) {p q : Word G K}
    (d : Diagram Complex p q) : MergeClaim (.ordinary d) := by
  induction d with
  | mergeUp l a => exact fun _ _ => MergeAt.vertex _ l a
  | vertical d e hd he => exact merge_vertical_step empty (.ordinary d) (.ordinary e) hd he
  | horizontal d e hd he => exact merge_horizontal_step empty (.ordinary d) (.ordinary e) hd he
  | id | upDot | downDot | splitUp | mergeDown | splitDown | multiplicationCap | traceCap
  | reverseCup | ordinaryCup | leftUnit | rightUnit | insertLeftUnit | insertRightUnit
  | associate | unassociate | mixedMultiplication | mixedProjection | zero | add | scale =>
    intro hc
    cases hc

private theorem expanded_no_singleton_merge (n : Nat) (opening : ProjectionOpening)
    (closing : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry n opening closing) ≠ [join 0] := by
  cases opening <;>
    simp only [DrawingShape.expandedProjectionGeometry, encode_stack]
  all_goals
    intro h
    have hh := congrArg List.head? h
    cases hh

private theorem drawing_merge (empty : EmptyCodeCoherence U) {p q : Word G K}
    (d : LabelledDrawing Complex p q) : MergeClaim d := by
  induction d with
  | ordinary d => exact diagram_merge empty d
  | trivalent v =>
    cases v with
    | mergeUp l a => exact fun _ _ => MergeAt.vertex _ l a
    | _ => intro hc; cases hc
  | bentVertex v => cases v <;> intro hc <;> cases hc
  | vertical d e hd he => exact merge_vertical_step empty d e hd he
  | horizontal d e hd he => exact merge_horizontal_step empty d e hd he
  | expandedProjection _ _ _ _ _ opening closing =>
    exact fun h => (expanded_no_singleton_merge _ opening closing h).elim
  | expandedProjectionChain _ _ _ _ _ _ opening closing =>
    exact fun h => (expanded_no_singleton_merge _ opening closing h).elim
  | expandedLinearDotProjection _ _ _ _ _ _ opening closing =>
    exact fun h => (expanded_no_singleton_merge _ opening closing h).elim
  | parallelUpChain _ _ _ _ labels =>
    intro h
    change PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack
      ((DrawingShape.upwardDots labels.length).stack (.vertex .splitUp))) = [join 0] at h
    rw [encode_stack, encode_stack] at h
    change join 0 :: (PlanarCode.encode (DrawingShape.upwardDots labels.length) ++
      [.vertex 0 (.trivalent .splitUp)]) = [join 0] at h
    have ht := (List.cons.inj h).2
    have hs := (List.append_eq_nil_iff.mp ht).2
    cases hs
  | parallelDownChain _ _ _ _ labels =>
    intro h
    change PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack
      ((DrawingShape.downwardDots labels.length).stack (.vertex .splitDown))) = [join 0] at h
    rw [encode_stack] at h
    have hh := congrArg List.head? h
    cases hh
  | upDot | downDot | parallelUp | parallelDown | mixedMultiplication | rightCurlUp
  | compactProjection | add | scale =>
    intro hc
    cases hc

private theorem mergeAt_witness {p q : Boundary G K} {f : BoundaryMap p q}
    (h : MergeAt p q f) :
    ∃ (M : Subgroup U) (l : ConjEmbedding M G) (a : ConjEmbedding K M)
      (hp : p = (upPair l a).boundary) (hq : q = (Word.up (l.comp a)).boundary),
      cast (congrArg₂ (fun b c : Boundary G K => BoundaryMap b c) hp hq) f =
        normalize (ScopedDiagram.ordinary (Diagram.mergeUp l a)) := by
  cases h with
  | vertex M l a => exact ⟨M, l, a, rfl, rfl, rfl⟩

/-- Normalize a singleton merge at any parenthesization of its ordered inputs
and output. The stronger width-bound hypothesis suffices. -/
private theorem singleton_merge_normal_form (empty : EmptyCodeCoherence U)
    {p q : Word G K} (d : LabelledDrawing Complex p q)
    (hc : code d.erase = [join 0]) (hw : p.directions.length ≤ 2) :
    ∃ (M : Subgroup U) (l : ConjEmbedding M G) (a : ConjEmbedding K M)
      (hp : p.boundary = (upPair l a).boundary)
      (hq : q.boundary = (Word.up (l.comp a)).boundary),
      cast (congrArg₂ (fun b c : Boundary G K => BoundaryMap b c) hp hq)
          d.interpret.atBoundary.eval =
        (LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.mergeUp l a)).interpret.atBoundary.eval :=
  mergeAt_witness (drawing_merge empty d hc hw)

private theorem straightAt_of_eq {p q : Boundary G K} {f : BoundaryMap p q}
    (h : p = q)
    (he : cast (congrArg (fun b => BoundaryMap p b) h.symm) f = Biset.Hom.id _) :
    StraightAt p q f := by
  subst q
  change f = Biset.Hom.id _ at he
  subst f
  exact StraightAt.id p

end DotSlidePreorderProof

namespace DotSlidePreorderBridge

open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {K H G H' : Subgroup U}

private def rightShape : PlanarShape :=
  ⟨[true,true], [true],
    Quotient.mk PlanarCode.setoid [.vertex 1 .upDot, .vertex 0 (.trivalent .mergeUp)]⟩

private def trunkShape : PlanarShape :=
  ⟨[true,true], [true],
    Quotient.mk PlanarCode.setoid [.vertex 0 (.trivalent .mergeUp), .vertex 0 .upDot]⟩

private abbrev pair (l : ConjEmbedding H G) (a : ConjEmbedding K H) : Word G K :=
  (Word.up l).tensor (.up a)

private noncomputable def branch (l : ConjEmbedding H G)
    {a b : ConjEmbedding K H} (label : DotLabel Complex a b) :
    LabelledDrawing Complex (pair l a) (.up (l.comp b)) :=
  (LabelledDrawing.horizontal (.ordinary (.id (.up l))) (DotLabel.upDrawing label)).vertical
    (.trivalent (.mergeUp l b))

private noncomputable def trunk (l : ConjEmbedding H G)
    {a b : ConjEmbedding K H} (terms : List (Complex × Dot (l.comp a) (l.comp b))) :
    LabelledDrawing Complex (pair l a) (.up (l.comp b)) :=
  (LabelledDrawing.trivalent (.mergeUp l a)).vertical (.upDot terms)

private theorem branch_shape (l : ConjEmbedding H G)
    {a b : ConjEmbedding K H} (label : DotLabel Complex a b) :
    (branch l label).planarShape = rightShape := rfl

private theorem trunk_shape (l : ConjEmbedding H G)
    {a b : ConjEmbedding K H} (terms : List (Complex × Dot (l.comp a) (l.comp b))) :
    (trunk l terms).planarShape = trunkShape := rfl

private def atBoundary {p q : Word G K} {v : PlanarShape}
    (d : LabelledDrawing Complex p q) (hs : d.planarShape = v) :
    LabelledDrawing.PlanarAtBoundary Complex p.boundary q.boundary v :=
  ⟨p, q, d, rfl, rfl, hs⟩

/- Proposition 3.2, first proof paragraph, applies the right-leg case of
   (3.1). The registered InductionMergeDotSlide specializes to dots formed
   from named representatives. The shared Diagram.mergeUp_slide_right
   takes any eligible Dot, exactly the hypothesis supplied by each term
   in the finite label. Extend that equality by linearity term by term. -/
set_option maxHeartbeats 2000000 in
private theorem slide (l : ConjEmbedding H G) {a b : ConjEmbedding K H}
    (label : DotLabel Complex a b) :
    (branch l label).interpret.eval =
      (trunk l (label.terms.map fun (r,d) => (r, d.whisker l))).interpret.eval := by
  let pre := (Diagram.id (R := Complex) (Word.up l)).eval
  let after := (Diagram.mergeUp (R := Complex) l b).eval
  let before := (Diagram.mergeUp (R := Complex) l a).eval
  let terms := label.terms
  have hl (terms : List (Complex × Dot a b)) :
      ((pre.horizontal (ScopedDiagram.weightedUpDot terms).eval).vertical after :
        Biset.Hom Complex (pair l a).basis (Word.up (l.comp b)).basis) =
      before.vertical (ScopedDiagram.weightedUpDot
        (terms.map fun (r,d) => (r, d.whisker l))).eval := by
    apply Biset.Hom.ext
    apply Finsupp.lhom_ext
    intro x c
    refine Quotient.inductionOn x (fun z => ?_)
    rcases z with ⟨x,y⟩
    let input := Finsupp.single ((Biset.induction l).pair (Biset.induction a) x y) c
    let combine := Biset.pairLinear Complex (Biset.induction l) (Biset.induction b)
      (Finsupp.single x 1)
    change after.toLinearMap ((pre.horizontal (ScopedDiagram.weightedUpDot terms).eval).toLinearMap input) =
      (ScopedDiagram.weightedUpDot _).eval.toLinearMap (before.toLinearMap input)
    rw [show (pre.horizontal (ScopedDiagram.weightedUpDot terms).eval).toLinearMap input =
      c • combine ((ScopedDiagram.weightedUpDot terms).eval.toLinearMap (Finsupp.single y 1))
        from Biset.Hom.horizontal_single _ _ x y c]
    have weighted {X Y : ConjEmbedding K H}
        (ts : List (Complex × Dot X Y)) (z : H →₀ Complex) :
        (ScopedDiagram.weightedUpDot ts).eval.toLinearMap z =
          (ts.map fun (r,d) => r • (Diagram.upDot d).eval.toLinearMap z).sum := by
      change (Diagram.finiteSum (ts.map fun (r,d) => Diagram.scale r (.upDot d))).eval.toLinearMap z = _
      rw [Diagram.eval_finiteSum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨r,d⟩ _
      rfl
    have weighted' {X Y : ConjEmbedding K G}
        (ts : List (Complex × Dot X Y)) (z : G →₀ Complex) :
        (ScopedDiagram.weightedUpDot ts).eval.toLinearMap z =
          (ts.map fun (r,d) => r • (Diagram.upDot d).eval.toLinearMap z).sum := by
      change (Diagram.finiteSum (ts.map fun (r,d) => Diagram.scale r (.upDot d))).eval.toLinearMap z = _
      rw [Diagram.eval_finiteSum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨r,d⟩ _
      rfl
    rw [weighted, weighted']
    simp only [List.map_map]
    -- The tensor product and the following merge are linear in this label.
    induction terms with
    | nil => simp
    | cons term tail ih =>
      obtain ⟨r,d⟩ := term
      simp only [List.map_cons, List.sum_cons, map_add, smul_add, ← ih]
      congr 1
      have h := congrArg (fun f : Biset.Hom Complex
          (pair l a).basis (Word.up (l.comp b)).basis =>
          f.toLinearMap input) (Diagram.mergeUp_slide_right (R := Complex) l d)
      change after.toLinearMap ((pre.horizontal (Diagram.upDot d).eval).toLinearMap input) =
        (Diagram.upDot (d.whisker l)).eval.toLinearMap (before.toLinearMap input) at h
      rw [show (pre.horizontal (Diagram.upDot d).eval).toLinearMap input =
        c • combine ((Diagram.upDot d).eval.toLinearMap (Finsupp.single y 1))
        from Biset.Hom.horizontal_single _ _ x y c] at h
      simp only [map_smul] at h ⊢
      rw [smul_comm c r, h]
      rfl
  exact hl terms

private theorem branchBoundary_inj (l : ConjEmbedding H G) (a : ConjEmbedding K H)
    (l' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (h : (pair l' a').boundary = (pair l a).boundary) :
    ∃ _he : H' = H, HEq l' l ∧ HEq a' a := by
  change Boundary.cons (.up l') (Boundary.cons (.up a') (.empty K)) =
    Boundary.cons (.up l) (Boundary.cons (.up a) (.empty K)) at h
  injection h with _ e _ hhead hrest
  subst H'
  have hl : l' = l := by
    have h := eq_of_heq hhead
    injection h
  have ha : a' = a := by
    have h := eq_of_heq hrest
    injection h with _ _ _ hhead _
    injection hhead
  exact ⟨rfl, heq_of_eq hl, heq_of_eq ha⟩

private theorem upBoundary_inj (a b : ConjEmbedding K G)
    (h : (Word.up a).boundary = (Word.up b).boundary) : a = b := by
  change Boundary.cons (.up a) (.empty K) = Boundary.cons (.up b) (.empty K) at h
  injection h with _ _ _ hhead _
  injection hhead

/-- Exact normal-form hypothesis on the full right-input shape fiber. -/
def NormalForm (U : Type u) [Group U] : Prop :=
  ∀ (G K : Subgroup U) (p q : Boundary G K)
    (v : LabelledDrawing.PlanarAtBoundary Complex p q rightShape),
    ∃ (H : Subgroup U) (l : ConjEmbedding H G) (a b : ConjEmbedding K H)
      (label : DotLabel Complex a b) (hp : (pair l a).boundary = p)
      (hq : (Word.up (l.comp b)).boundary = q),
      v.interpret.eval =
        (show LabelledDrawing.PlanarAtBoundary Complex p q rightShape
          from ⟨_, _, branch l label, hp, hq, branch_shape l label⟩).interpret.eval

/- FixedBoundaryReplacementPreorder identifies replacement with inclusion
   of attained maps. Work directly with its equivalent witness formulation
   so that the constructed trunk drawing and both transports are explicit. -/
private theorem forward (normal : NormalForm U) :
    LabelledDrawing.PlanarReplaces (U := U) Complex rightShape trunkShape := by
  intro G K p q v
  obtain ⟨H,l,a,b,label,hp,hq,hv⟩ := normal G K p q v
  refine ⟨⟨_, _, trunk l (label.terms.map fun (r,d) => (r, d.whisker l)),
    hp, hq, trunk_shape _ _⟩, hv.trans ?_⟩
  subst p
  subst q
  apply (ScopedDiagram.eval_atBoundary_eq_iff _ _).2
  exact slide l label


private theorem reverseAt (normal : NormalForm U) (l : ConjEmbedding H G)
    (a : ConjEmbedding K H) (d : Dot (l.comp a) (l.comp a))
    (obstruction : ∀ label : DotLabel Complex a a,
      (branch l label).interpret.eval ≠
        ((LabelledDrawing.trivalent (TrivalentVertex.mergeUp l a)).vertical
          (DotLabel.upDrawing (Finsupp.single d (1 : Complex)))).interpret.eval) :
    ¬ LabelledDrawing.PlanarReplaces (U := U) Complex trunkShape rightShape := by
  intro repl
  let p := (pair l a).boundary
  let q := (Word.up (l.comp a)).boundary
  let bad : LabelledDrawing.PlanarAtBoundary Complex p q trunkShape :=
    ⟨_, _, (LabelledDrawing.trivalent (TrivalentVertex.mergeUp l a)).vertical
        (DotLabel.upDrawing (Finsupp.single d (1 : Complex))), rfl, rfl, rfl⟩
  obtain ⟨v, hv⟩ := repl G K p q bad
  obtain ⟨J,l',a',b,label,hp,hq,hn⟩ := normal G K p q v
  obtain ⟨hJ,hl,ha⟩ := branchBoundary_inj l a l' a' hp
  subst J
  have hl' := eq_of_heq hl
  have ha' := eq_of_heq ha
  subst l'
  subst a'
  have hb : b = a :=
    Diagram.mergeUp_rightEmbedding_eq l (upBoundary_inj _ _ hq)
  subst b
  apply obstruction label
  apply (ScopedDiagram.eval_atBoundary_eq_iff _ _).1
  exact (hv.trans hn).symm

private abbrev S4 := Equiv.Perm (Fin 4)
private abbrev large : Subgroup S4 := ⊤
private abbrev middle : Subgroup S4 := MulAction.stabilizer S4 (3 : Fin 4)
private abbrev small : Subgroup S4 := middle ⊓ MulAction.stabilizer S4 (2 : Fin 4)
private def outer : ConjEmbedding middle large :=
  ConjEmbedding.ofConjugator 1 (fun _ => Subgroup.mem_top _)
private def inner : ConjEmbedding small middle :=
  ConjEmbedding.ofConjugator 1 (by
    intro k
    simpa only [one_mul, inv_one, mul_one] using (inf_le_left : small ≤ middle) k.property)

/- Proposition 3.2, second proof paragraph, invokes Example 3.2. The
   registered RightInputDotSlideObstruction gives the coefficient-one
   swap in S4 and excludes every admissible finite label at its fixed
   two-input boundary. The fixed bottom boundary determines the outer
   embedding and input right embedding. Injectivity of the outer
   embedding then fixes the right embedding after the dot. -/
set_option maxHeartbeats 2000000 in
private theorem reverse (normal : NormalForm S4) :
    ¬ LabelledDrawing.PlanarReplaces (U := S4) Complex trunkShape rightShape := by
  obtain ⟨d, _, _, hd⟩ := RightInputDotSlideObstruction.2.2.2
  refine reverseAt normal outer inner d fun label => ?_
  exact (hd inner label rfl).2.2


/-- A checked reduction of both clauses of Proposition 3.2 to the same
right-input normal form. The trunk counterexample is already in ordinary
merge-and-dot form, so there is no need to invert that shape fiber. -/
private theorem proposition32
    (normal : ∀ {V : Type u} [Group V], NormalForm V)
    (finiteNormal : NormalForm S4) :
    (let boundary : List Bool × List Bool := ([true, true], [true])
let S4 := Equiv.Perm (Fin 4)
let G : Subgroup S4 := ⊤
let H := MulAction.stabilizer S4 (3 : Fin 4)
let K := H ⊓ MulAction.stabilizer S4 (2 : Fin 4)
let left : MackeyDiagrams.ConjEmbedding H G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (fun _ => Subgroup.mem_top _)
let right : MackeyDiagrams.ConjEmbedding K H :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (by
    intro k
    simpa only [one_mul, inv_one, mul_one] using
      (inf_le_left : K ≤ H) (Subtype.property k))
let leftWire := MackeyDiagrams.LabelledDrawing.ordinary
  (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up left))
let merge := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
  (MackeyDiagrams.TrivalentVertex.mergeUp left right)
let rightDot := MackeyDiagrams.DotLabel.upDrawing
  (MackeyDiagrams.DotLabel.identity (R := Complex) right)
let trunkDot := MackeyDiagrams.DotLabel.upDrawing
  (MackeyDiagrams.DotLabel.identity (R := Complex)
    (MackeyDiagrams.ConjEmbedding.comp left right))
let rightMarked := MackeyDiagrams.LabelledDrawing.vertical
  (MackeyDiagrams.LabelledDrawing.horizontal leftWire rightDot) merge
let trunkMarked := MackeyDiagrams.LabelledDrawing.vertical merge trunkDot
let A₄ : MackeyDiagrams.LabelledDrawing.Shapes (U := S4) Complex boundary :=
  ⟨MackeyDiagrams.LabelledDrawing.planarShape rightMarked, ⟨G, K, _, _, rightMarked, rfl, rfl⟩⟩
let B₄ : MackeyDiagrams.LabelledDrawing.Shapes (U := S4) Complex boundary :=
  ⟨MackeyDiagrams.LabelledDrawing.planarShape trunkMarked, ⟨G, K, _, _, trunkMarked, rfl, rfl⟩⟩
(∀ {U : Type u} [Group U],
  let T : Subgroup U := ⊤
  let embedding := MackeyDiagrams.ConjEmbedding.id T
  let wire := MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up embedding))
  let merge := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.mergeUp embedding embedding)
  let rightDot := MackeyDiagrams.DotLabel.upDrawing
    (MackeyDiagrams.DotLabel.identity (R := Complex) embedding)
  let trunkDot := MackeyDiagrams.DotLabel.upDrawing
    (MackeyDiagrams.DotLabel.identity (R := Complex)
      (MackeyDiagrams.ConjEmbedding.comp embedding embedding))
  let rightMarked := MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal wire rightDot) merge
  let trunkMarked := MackeyDiagrams.LabelledDrawing.vertical merge trunkDot
  let A : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary :=
    ⟨Subtype.val A₄, ⟨T, T, _, _, rightMarked, rfl, rfl⟩⟩
  let B : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary :=
    ⟨Subtype.val B₄, ⟨T, T, _, _, trunkMarked, rfl, rfl⟩⟩
  MackeyDiagrams.LabelledDrawing.ShapeReplaces A B) ∧
¬ MackeyDiagrams.LabelledDrawing.ShapeReplaces B₄ A₄) := by
  change (∀ {V : Type u} [Group V],
      LabelledDrawing.PlanarReplaces (U := V) Complex rightShape trunkShape) ∧
    ¬ LabelledDrawing.PlanarReplaces (U := S4) Complex trunkShape rightShape
  exact ⟨fun {_} _ => forward normal, reverse finiteNormal⟩

end DotSlidePreorderBridge

#print axioms DotSlidePreorderProof.fiber_code
#print axioms DotSlidePreorderProof.diagram_code_horiz
#print axioms DotSlidePreorderProof.drawing_code_horiz
#print axioms DotSlidePreorderBridge.proposition32

#print axioms DotSlidePreorderProof.singleton_merge_normal_form
#print axioms DotSlidePreorderProof.straightAt_of_eq
