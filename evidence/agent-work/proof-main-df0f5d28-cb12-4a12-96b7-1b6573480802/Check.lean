import MackeyDiagrams.PlanarShape
import MackeyDiagrams.DotSlideObstruction
import MackeyDiagrams.Identities
import Mathlib.Basic.Complex.Basic
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

namespace DotSlidePreorderProof

open MackeyDiagrams
open Biset.Hom

universe u
variable {U : Type u} [Group U] {A B C : Subgroup U}

private noncomputable def collectDot {a b : ConjEmbedding A B}
    (terms : List (Complex × Dot a b)) : DotLabel Complex a b :=
  (terms.map fun (c, d) => Finsupp.single d c).sum

private theorem eval_collectDot {a b : ConjEmbedding A B}
    (terms : List (Complex × Dot a b)) :
    (LabelledDrawing.upDot terms).interpret.eval =
      (DotLabel.upDrawing (collectDot terms)).interpret.eval := by
  rw [DotLabel.eval_upDrawing]
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (Diagram.finiteSum (terms.map fun (r, d) => Diagram.scale r (.upDot d))).eval.toLinearMap z =
    (Diagram.linearUpDot (collectDot terms)).eval.toLinearMap z
  rw [Diagram.eval_finiteSum, Diagram.eval_linearUpDot_apply, List.map_map]
  unfold collectDot
  induction terms with
  | nil => simp
  | cons t ts ih =>
    rcases t with ⟨r, d⟩
    simp only [List.map_cons, List.sum_cons, map_add, freeLift_single, ← ih]
    rfl

private theorem eval_collectSingleton {a b : ConjEmbedding A B} (d : Dot a b) :
    (Diagram.upDot (R := Complex) d).eval =
      (DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval := by
  rw [DotLabel.eval_upDrawing]
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  rw [Diagram.eval_linearUpDot_apply, freeLift_single, one_smul]


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
def EmptyCodeCoherence (U : Type u) [Group U] : Prop :=
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


private inductive ShortWord : {A B : Subgroup U} → Word A B → Type u
  | empty (A : Subgroup U) : ShortWord (.empty A)
  | up {A B : Subgroup U} (a : ConjEmbedding B A) : ShortWord (.up a)

private def UpWidth (l : List Bool) : Prop :=
  (∀ b ∈ l, b = true) ∧ l.length ≤ 2

private theorem UpWidth.left {l r : List Bool} (h : UpWidth (l ++ r)) : UpWidth l := by
  constructor
  · intro b hb
    exact h.1 _ (List.mem_append_left _ hb)
  · have hlen := h.2
    rw [List.length_append] at hlen
    omega

private theorem UpWidth.right {l r : List Bool} (h : UpWidth (l ++ r)) : UpWidth r := by
  constructor
  · intro b hb
    exact h.1 _ (List.mem_append_right _ hb)
  · have hlen := h.2
    rw [List.length_append] at hlen
    omega

private theorem shortBoundary (p : Boundary A B) (hw : UpWidth (boundaryDirections p))
    (h : (boundaryDirections p).length ≤ 1) :
    ∃ r : Word A B, Nonempty (ShortWord r) ∧ p = r.boundary := by
  cases p with
  | empty => exact ⟨.empty _, ⟨.empty _⟩, rfl⟩
  | cons s t =>
    cases s with
    | down a =>
      exact False.elim (Bool.false_ne_true (hw.1 false (by simp [boundaryDirections])))
    | up a =>
      cases t with
      | empty => exact ⟨.up a, ⟨.up a⟩, rfl⟩
      | cons s t => cases s <;> simp [boundaryDirections] at h

private inductive DotCore : {A B : Subgroup U} → Nat → Word A B → Word A B → Type u
  | single {A B : Subgroup U} {a b : ConjEmbedding B A} (label : DotLabel Complex a b) :
      DotCore 0 (.up a) (.up b)
  | left {A B C : Subgroup U} {a b : ConjEmbedding B A}
      (label : DotLabel Complex a b) (r : ConjEmbedding C B) :
      DotCore 0 ((Word.up a).tensor (.up r)) ((Word.up b).tensor (.up r))
  | right {A B C : Subgroup U} (l : ConjEmbedding B A)
      {a b : ConjEmbedding C B} (label : DotLabel Complex a b) :
      DotCore 1 ((Word.up l).tensor (.up a)) ((Word.up l).tensor (.up b))

private noncomputable def DotCore.drawing {n : Nat} {p q : Word A B} :
    DotCore n p q → LabelledDrawing Complex p q
  | .single label => label.upDrawing
  | .left label r => label.upDrawing.horizontal (.ordinary (.id (.up r)))
  | .right l label => (.ordinary (.id (.up l)) : LabelledDrawing Complex _ _).horizontal label.upDrawing

private theorem DotCore.positive {n : Nat} {p q : Word A B} (d : DotCore n p q) :
    0 < p.directions.length := by cases d <;> simp [Word.directions]

private def NormalDot {p q : Word A B} (n : Nat)
    (f : Biset.Hom Complex p.basis q.basis) : Prop :=
  ∃ (r s : Word A B) (d : DotCore n r s), Framed (p := p) (q := q) f d.drawing.interpret.eval

private theorem ShortWord.leftCore {n : Nat} {r s : Word A B} {p : Word B C}
    (d : DotCore n r s) (w : ShortWord p) (hw : (r.directions ++ p.directions).length ≤ 2) :
    NormalDot (p := r.tensor p) (q := s.tensor p) n
      (d.drawing.interpret.eval.horizontal (Biset.Hom.id p.basis)) := by
  cases w with
  | empty => exact ⟨_, _, d, stripRight _⟩
  | up a =>
    cases d with
    | single label => exact ⟨_, _, .left label a, Framed.self _⟩
    | left | right => simp [Word.directions] at hw

private theorem ShortWord.rightCore {n : Nat} {r s : Word B C} {p : Word A B}
    (w : ShortWord p) (d : DotCore n r s) (hw : (p.directions ++ r.directions).length ≤ 2) :
    NormalDot (p := p.tensor r) (q := p.tensor s) (p.directions.length + n)
      ((Biset.Hom.id p.basis).horizontal d.drawing.interpret.eval) := by
  cases w with
  | empty =>
    simp only [Word.directions, List.length_nil, Nat.zero_add]
    exact ⟨_, _, d, stripLeft _⟩
  | up a =>
    cases d with
    | single label => exact ⟨_, _, .right a label, Framed.self _⟩
    | left | right => simp [Word.directions] at hw

private theorem NormalDot.vertLeft {n : Nat} {p q r : Word A B}
    (d : Wire p q) {f : Biset.Hom Complex q.basis r.basis} (h : NormalDot (p := q) (q := r) n f) :
    NormalDot (p := p) (q := r) n (d.eval.vertical f) := by
  obtain ⟨s, t, c, hf⟩ := h
  exact ⟨s, t, c, hf.vertLeft d⟩

private theorem NormalDot.vertRight {n : Nat} {p q r : Word A B}
    (d : Wire q r) {f : Biset.Hom Complex p.basis q.basis} (h : NormalDot (p := p) (q := q) n f) :
    NormalDot (p := p) (q := r) n (f.vertical d.eval) := by
  obtain ⟨s, t, c, hf⟩ := h
  exact ⟨s, t, c, hf.vertRight d⟩

private theorem NormalDot.horizRight (hc : EmptyCodeCoherence U) {n : Nat}
    {p q : Word A B} {r s : Word B C} (d : Wire p q)
    {f : Biset.Hom Complex r.basis s.basis} (h : NormalDot (p := r) (q := s) n f)
    (hw : UpWidth (p.directions ++ r.directions)) :
    NormalDot (p := p.tensor r) (q := q.tensor s) (q.directions.length + n) (d.eval.horizontal f) := by
  obtain ⟨r', s', c, hf⟩ := h
  have hr : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (hf.boundaries hc).1
  have hp : p.directions.length ≤ 1 := by
    have hlen := hw.2
    rw [List.length_append, hr] at hlen
    have := c.positive
    omega
  obtain ⟨p', ⟨w⟩, hb⟩ := shortBoundary p.boundary
    (by simpa only [boundaryDirections_word] using hw.left)
    (by rwa [boundaryDirections_word])
  have hp' : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  have hlen := hw.2
  rw [hp', hr] at hlen
  obtain ⟨v, z, c', h'⟩ := w.rightCore c hlen
  rw [← d.directions hc, hp']
  have hi := frameStraight hc d hb
  exact ⟨v, z, c',
    (hi.horizontal hf).trans h'⟩

private theorem NormalDot.horizLeft (hc : EmptyCodeCoherence U) {n : Nat}
    {p q : Word A B} {r s : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} (h : NormalDot (p := p) (q := q) n f)
    (d : Wire r s) (hw : UpWidth (p.directions ++ r.directions)) :
    NormalDot (p := p.tensor r) (q := q.tensor s) n (f.horizontal d.eval) := by
  obtain ⟨p', q', c, hf⟩ := h
  have hp : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (hf.boundaries hc).1
  have hr : r.directions.length ≤ 1 := by
    have hlen := hw.2
    rw [List.length_append, hp] at hlen
    have := c.positive
    omega
  obtain ⟨r', ⟨w⟩, hb⟩ := shortBoundary r.boundary
    (by simpa only [boundaryDirections_word] using hw.right)
    (by rwa [boundaryDirections_word])
  have hr' : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  have hlen := hw.2
  rw [hp, hr'] at hlen
  obtain ⟨v, z, c', h'⟩ := ShortWord.leftCore c w hlen
  exact ⟨v, z, c', (hf.horizontal (frameStraight hc d hb)).trans h'⟩


private theorem splitSingleton {c d : PlanarCode.Code} {e : PlanarEvent}
    (h : c ++ d = [e]) : (c = [] ∧ d = [e]) ∨ (c = [e] ∧ d = []) := by
  cases c with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons x xs =>
    simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, rfl⟩

private theorem shiftSingleton {i n : Nat} {c : PlanarCode.Code}
    (h : PlanarCode.shift i c = [mark n]) :
    ∃ m : Nat, c = [mark m] ∧ i + m = n := by
  cases c with
  | nil => simp [PlanarCode.shift] at h
  | cons e es =>
    have ht := congrArg List.length h
    simp only [PlanarCode.shift, List.length_map, List.length_cons, List.length_nil] at ht
    have hz : es = [] := List.length_eq_zero_iff.mp (by omega)
    subst es
    cases e <;> simp [PlanarCode.shift, PlanarEvent.place, PlanarEvent.position] at h
    next m k =>
      obtain ⟨hm, rfl⟩ := h
      exact ⟨m, rfl, hm⟩

private theorem shiftEmpty {i : Nat} {c : PlanarCode.Code}
    (h : PlanarCode.shift i c = []) : c = [] := by
  simpa only [PlanarCode.shift, List.map_eq_nil_iff] using h

private theorem normalVertical (hc : EmptyCodeCoherence U) {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) {n : Nat}
    (h : code d.erase ++ code e.erase = [mark n]) (hw : UpWidth p.directions)
    (hd : ∀ m, code d.erase = [mark m] → UpWidth p.directions →
      NormalDot (p := p) (q := q) m d.interpret.eval)
    (he : ∀ m, code e.erase = [mark m] → UpWidth q.directions →
      NormalDot (p := q) (q := r) m e.interpret.eval) :
    NormalDot (p := p) (q := r) n (d.vertical e).interpret.eval := by
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · let w : Wire p q := ⟨d, hd0⟩
    have hwq : UpWidth q.directions := (w.directions hc) ▸ hw
    exact NormalDot.vertLeft w (he n he1 hwq)
  · exact NormalDot.vertRight ⟨e, he0⟩ (hd n hd1 hw)

private theorem normalHorizontal (hc : EmptyCodeCoherence U)
    {p q : Word A B} {r s : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex r s) {n : Nat}
    (h : code d.erase ++ PlanarCode.shift q.directions.length (code e.erase) = [mark n])
    (hw : UpWidth (p.directions ++ r.directions))
    (hd : ∀ m, code d.erase = [mark m] → UpWidth p.directions →
      NormalDot (p := p) (q := q) m d.interpret.eval)
    (he : ∀ m, code e.erase = [mark m] → UpWidth r.directions →
      NormalDot (p := r) (q := s) m e.interpret.eval) :
    NormalDot (p := p.tensor r) (q := q.tensor s) n (d.horizontal e).interpret.eval := by
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · obtain ⟨m, hm, rfl⟩ := shiftSingleton he1
    exact NormalDot.horizRight hc ⟨d, hd0⟩ (he m hm hw.right) hw
  · exact NormalDot.horizLeft hc (hd n hd1 hw.left) ⟨e, shiftEmpty he0⟩ hw

private theorem ordinarySingleton (hc : EmptyCodeCoherence U) {p q : Word A B}
    (d : Diagram Complex p q) :
    ∀ n, code d.drawing = [mark n] → UpWidth p.directions →
      NormalDot (p := p) (q := q) n d.eval := by
  induction d <;> intro n h hw
  case vertical d e hd he =>
    rw [diagram_code_vert] at h
    exact normalVertical hc (.ordinary d) (.ordinary e) h hw hd he
  case horizontal d e hd he =>
    rw [diagram_code_horiz] at h
    exact normalHorizontal hc (.ordinary d) (.ordinary e) h hw hd he
  case upDot d =>
    have h0 : n = 0 := (congrArg PlanarEvent.position (List.cons.inj h).1).symm
    subst n
    refine ⟨_, _, .single (Finsupp.single d 1), ?_⟩
    rw [eval_collectSingleton]
    exact Framed.self _
  all_goals
    simp [code, Diagram.drawing, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h

private theorem drawingSingleton (hc : EmptyCodeCoherence U) {p q : Word A B}
    (d : LabelledDrawing Complex p q) :
    ∀ n, code d.erase = [mark n] → UpWidth p.directions →
      NormalDot (p := p) (q := q) n d.interpret.eval := by
  induction d <;> intro n h hw
  case ordinary d => exact ordinarySingleton hc d n h hw
  case vertical d e hd he =>
    rw [drawing_code_vert] at h
    exact normalVertical hc d e h hw hd he
  case horizontal d e hd he =>
    rw [drawing_code_horiz] at h
    exact normalHorizontal hc d e h hw hd he
  case upDot ts =>
    have h0 : n = 0 := (congrArg PlanarEvent.position (List.cons.inj h).1).symm
    subst n
    refine ⟨_, _, .single (collectDot ts), ?_⟩
    rw [eval_collectDot]
    exact Framed.self _
  case trivalent v => cases v <;> simp [code, LabelledDrawing.erase, DrawingShape.geometry,
      PlanarCode.encode, VertexKind.canonical, TrivalentVertex.kind] at h
  case bentVertex v => cases v <;> simp [code, LabelledDrawing.erase, DrawingShape.geometry,
      PlanarCode.encode, VertexKind.canonical, BentVertex.kind] at h
  case parallelUpChain labels =>
    change PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack _) = _ at h
    rw [encode_stack] at h
    simp [PlanarCode.encode, VertexKind.canonical] at h
  case rightCurlUp =>
    simp [code, LabelledDrawing.erase, DrawingShape.geometry, DrawingShape.rightCurlGeometry,
      DrawingShape.stack, PlanarCode.encode, VertexKind.canonical, PlanarCode.shift,
      DrawingShape.outputs, PlanarEvent.place, PlanarEvent.position] at h
  case parallelDownChain | expandedProjection | expandedProjectionChain | expandedLinearDotProjection =>
    exact False.elim (Bool.false_ne_true (hw.1 false (by simp [Word.directions])))
  all_goals
    simp [code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h

private def singletonRightShape : PlanarShape :=
  ⟨[true,true], [true,true], Quotient.mk PlanarCode.setoid [mark 1]⟩

private theorem atBoundary_eval_heq {P Q : Boundary A B} {s : PlanarShape}
    (v : LabelledDrawing.PlanarAtBoundary Complex P Q s) :
    HEq v.interpret.eval (canon v.diagram.interpret.eval) := by
  rcases v with ⟨p, q, d, hp, hq, hs⟩
  subst P
  subst Q
  rfl

/-- Normalize the singleton right-input-dot stage at the exact ordered labelled boundaries. -/
theorem normalizeRightDot (hc : EmptyCodeCoherence U) {P Q : Boundary A B}
    {s : PlanarShape} (v : LabelledDrawing.PlanarAtBoundary Complex P Q s)
    (h : code v.diagram.erase = [mark 1]) (hw : v.bottom.directions = [true, true]) :
    ∃ (M : Subgroup U) (l : ConjEmbedding M A) (a b : ConjEmbedding B M)
      (label : DotLabel Complex a b)
      (hp : ((Word.up l).tensor (.up a)).boundary = P)
      (hq : ((Word.up l).tensor (.up b)).boundary = Q),
      v.interpret.eval =
        (show LabelledDrawing.PlanarAtBoundary Complex P Q singletonRightShape
          from ⟨_, _, (LabelledDrawing.ordinary (Diagram.id (.up l))).horizontal label.upDrawing,
            hp, hq, rfl⟩).interpret.eval := by
  have hwidth : UpWidth v.bottom.directions := by
    rw [hw]
    simp [UpWidth]
  obtain ⟨r, s', c, hf⟩ := drawingSingleton hc v.diagram 1 h hwidth
  cases c with
  | right l label =>
    obtain ⟨hb, ht⟩ := hf.boundaries hc
    let rep : LabelledDrawing.PlanarAtBoundary Complex P Q singletonRightShape :=
      ⟨_, _, (LabelledDrawing.ordinary (Diagram.id (.up l))).horizontal label.upDrawing,
        hb.symm.trans v.bottom_eq, ht.symm.trans v.top_eq, rfl⟩
    refine ⟨_, l, _, _, label, rep.bottom_eq, rep.top_eq, ?_⟩
    change v.interpret.eval = rep.interpret.eval
    exact eq_of_heq ((atBoundary_eval_heq v).trans ((hf.canonical hc).trans (atBoundary_eval_heq rep).symm))

end DotSlidePreorderProof

#print axioms DotSlidePreorderProof.normalizeRightDot
