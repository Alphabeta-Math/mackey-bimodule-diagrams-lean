import MackeyDiagrams
import Proofs.InductionMergeDotSlide
import Proofs.FixedBoundaryReplacementPreorder
import Proofs.RightInputDotSlideObstruction

set_option maxHeartbeats 2000000

/-
Ian Xiao, §3.3, Proposition 3.2 and Example 3.2, archived source PDF p. 10
(SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
and published 28 November revision p. 12
(SHA-256 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
The slide is equation (3.1) on archived p. 8 and published p. 10.
https://getcurious.cc/downloads/mackey-bimodules.pdf#page=12
The Alphabeta Math entry gives the two proof paragraphs of Proposition 3.2
and no separately numbered steps. The proof below follows its references
to (3.1) and Example 3.2.
https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:preorder-not-symmetric

The coordinator route uses the exact positioned event list of the right-input
fiber. The two events share a strand, so the disjoint exchange relation
cannot switch them. Associators and unitors have empty event code. Check
their evaluations on the balanced biset basis before removing them at the
ordered labelled boundary. The intermediate word in the typed cut carries
the same labels into the dot and merge normal forms. Recover its input
width from the fiber's shape equality, since the event list alone admits
extra stationary strands.

The working declarations integrate the local checked cut, structural
coherence, singleton-dot and singleton-merge helper proofs. The proof uses
Biset.Hom.horizontal_vertical for the cut, the boundary reordering
cancellation equations for the stage evaluations, and
ScopedDiagram.eval_atBoundary_eq_iff to transfer evaluation equalities.
The forward implication uses Diagram.mergeUp_slide_right, the arbitrary
eligible-dot lemma used by the registered InductionMergeDotSlide. The
registered statement specializes to dots formed from chosen representatives.
The reverse implication applies RightInputDotSlideObstruction with the
same fixed inclusions and the coefficient-one swap of the last two points.
Use the full-fiber witness definition of the relation throughout, which gives
the inclusion criterion proved in FixedBoundaryReplacementPreorder.
The checked Lean connection uses the current project declarations.
-/

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


private abbrev drawingCode {p q : Word A B} (d : LabelledDrawing Complex p q) :=
  code d.erase

private theorem drawingCode_vertical {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) :
    drawingCode (d.vertical e) = drawingCode d ++ drawingCode e :=
  drawing_code_vert d e

private theorem drawingCode_horizontal {p q : Word A B} {p' q' : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex p' q') :
    drawingCode (d.horizontal e) =
      drawingCode d ++ PlanarCode.shift q.directions.length (drawingCode e) :=
  drawing_code_horiz d e

private abbrev drawingId (p : Word A B) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private def Factorable {p q : Word A B} (d : LabelledDrawing Complex p q) : Prop :=
  ∀ l r, drawingCode d = l ++ r →
    ∃ (m : Word A B) (below : LabelledDrawing Complex p m)
      (above : LabelledDrawing Complex m q),
      drawingCode below = l ∧ drawingCode above = r ∧
        d.interpret.eval = below.interpret.eval.vertical above.interpret.eval

private theorem factor_atom {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : (drawingCode d).length ≤ 1) : Factorable d := by
  intro l r hc
  have hlen : l.length + r.length ≤ 1 := by simpa only [hc, List.length_append] using h
  have hempty : l = [] ∨ r = [] := by
    by_cases hl : l = []
    · exact .inl hl
    · exact .inr (List.length_eq_zero_iff.mp (by
        have := mt List.length_eq_zero_iff.mp hl
        omega))
  rcases hempty with rfl | rfl
  · exact ⟨p, drawingId p, d, rfl, hc, (Biset.Hom.id_vertical _).symm⟩
  · exact ⟨q, d, drawingId q, by simpa only [List.append_nil] using hc,
      rfl, (Biset.Hom.vertical_id _).symm⟩

private theorem factor_vertical {p q r : Word A B}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex q r}
    (hd : Factorable d) (he : Factorable e) : Factorable (d.vertical e) := by
  intro l t hc
  rw [drawingCode_vertical] at hc
  rcases List.append_eq_append_iff.mp hc with ⟨s, hl, hs⟩ | ⟨s, hs, ht⟩
  · obtain ⟨m, f, g, hf, hg, hev⟩ := he s t hs
    refine ⟨m, d.vertical f, g, ?_, hg, ?_⟩
    · rw [drawingCode_vertical, hf, hl]
    · change d.interpret.eval.vertical e.interpret.eval =
        (d.interpret.eval.vertical f.interpret.eval).vertical g.interpret.eval
      rw [hev, Biset.Hom.vertical_assoc]
  · obtain ⟨m, f, g, hf, hg, hdv⟩ := hd l s hs
    refine ⟨m, f, g.vertical e, hf, ?_, ?_⟩
    · rw [drawingCode_vertical, hg, ht]
    · change d.interpret.eval.vertical e.interpret.eval =
        f.interpret.eval.vertical (g.interpret.eval.vertical e.interpret.eval)
      rw [hdv, Biset.Hom.vertical_assoc]

private theorem factor_horizontal {p q : Word A B} {p' q' : Word B C}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex p' q'}
    (hd : Factorable d) (he : Factorable e) : Factorable (d.horizontal e) := by
  intro l t hc
  rw [drawingCode_horizontal] at hc
  rcases List.append_eq_append_iff.mp hc with ⟨s, hl, hs⟩ | ⟨s, hs, ht⟩
  · obtain ⟨s',t',hec,hs',ht'⟩ := List.map_eq_append_iff.mp hs
    change PlanarCode.shift q.directions.length s' = s at hs'
    change PlanarCode.shift q.directions.length t' = t at ht'
    obtain ⟨m,f,g,hf,hg,hev⟩ := he s' t' hec
    refine ⟨q.tensor m, d.horizontal f, (drawingId q).horizontal g, ?_, ?_, ?_⟩
    · rw [drawingCode_horizontal, hf, hs', hl]
    · rw [drawingCode_horizontal, hg, ht']
      rfl
    · change d.interpret.eval.horizontal e.interpret.eval =
        (d.interpret.eval.horizontal f.interpret.eval).vertical
          ((Biset.Hom.id q.basis).horizontal g.interpret.eval)
      rw [Biset.Hom.horizontal_vertical, Biset.Hom.vertical_id, hev]
  · obtain ⟨m,f,g,hf,hg,hdv⟩ := hd l s hs
    refine ⟨m.tensor p', f.horizontal (drawingId p'), g.horizontal e, ?_, ?_, ?_⟩
    · rw [drawingCode_horizontal, hf]
      exact List.append_nil _
    · rw [drawingCode_horizontal, hg, ht]
    · change d.interpret.eval.horizontal e.interpret.eval =
        (f.interpret.eval.horizontal (Biset.Hom.id p'.basis)).vertical
          (g.interpret.eval.horizontal e.interpret.eval)
      rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical, hdv]

private theorem factor_congr {p q : Word A B} {d e : LabelledDrawing Complex p q}
    (hc : drawingCode d = drawingCode e) (hv : d.interpret.eval = e.interpret.eval)
    (he : Factorable e) : Factorable d := by
  intro l r h
  obtain ⟨m,f,g,hf,hg,hev⟩ := he l r (hc.symm.trans h)
  exact ⟨m,f,g,hf,hg,hv.trans hev⟩

private def isMergeOrDot : PlanarEvent → Prop
  | .vertex _ .upDot | .vertex _ (.trivalent .mergeUp) => True
  | _ => False

private def goodCode (c : PlanarCode.Code) : Prop :=
  ∀ e ∈ c, isMergeOrDot e

private theorem good_left {l r : PlanarCode.Code} (h : goodCode (l ++ r)) :
    goodCode l := fun e he => h e (List.mem_append_left _ he)

private theorem good_right {l r : PlanarCode.Code} (h : goodCode (l ++ r)) :
    goodCode r := fun e he => h e (List.mem_append_right _ he)

private theorem good_unshift {n : Nat} {c : PlanarCode.Code}
    (h : goodCode (PlanarCode.shift n c)) : goodCode c := by
  intro e he
  have hp := h (e.place (n + e.position)) (List.mem_map_of_mem he)
  cases e with
  | vertex _ k =>
    cases k <;> try exact hp
    case trivalent t => cases t <;> exact hp
  | _ => exact hp

private theorem factor_ordinary {p q : Word A B} (d : Diagram Complex p q)
    (h : goodCode (drawingCode (.ordinary d))) : Factorable (.ordinary d) := by
  induction d with
  | vertical d e hd he =>
    change goodCode (code (d.vertical e).drawing) at h
    rw [diagram_code_vert] at h
    refine factor_congr (d := .ordinary (d.vertical e))
      (e := (LabelledDrawing.ordinary d).vertical (.ordinary e)) ?_ rfl
      (factor_vertical (hd (good_left h)) (he (good_right h)))
    exact (diagram_code_vert d e).trans (drawing_code_vert (.ordinary d) (.ordinary e)).symm
  | horizontal d e hd he =>
    change goodCode (code (d.horizontal e).drawing) at h
    rw [diagram_code_horiz] at h
    refine factor_congr (d := .ordinary (d.horizontal e))
      (e := (LabelledDrawing.ordinary d).horizontal (.ordinary e)) ?_ rfl
      (factor_horizontal (hd (good_left h)) (he (good_unshift (good_right h))))
    exact (diagram_code_horiz d e).trans (drawing_code_horiz (.ordinary d) (.ordinary e)).symm
  | zero p q =>
    exact False.elim (h (.zero 0 p.directions q.directions) List.mem_cons_self)
  | add d e _ _ =>
    let s := d.drawing.geometry
    exact False.elim (h (.add 0 s.inputs s.outputs (PlanarCode.encode s)
      (code e.drawing)) List.mem_cons_self)
  | scale _ d _ =>
    let s := d.drawing.geometry
    exact False.elim (h (.scale 0 s.inputs s.outputs (PlanarCode.encode s)) List.mem_cons_self)
  | _ => exact factor_atom _ (by first | exact Nat.le_refl 1 | exact Nat.zero_le 1)

private theorem no_parallelUpChain (n : Nat) :
    ¬ goodCode (code (.vertex (.parallelUpChain n))) := by
  intro h
  change goodCode (PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack
    ((DrawingShape.upwardDots n).stack (.vertex .splitUp)))) at h
  rw [encode_stack, encode_stack] at h
  exact (good_right (good_right h)) (.vertex 0 (.trivalent .splitUp)) List.mem_cons_self

private theorem no_parallelDownChain (n : Nat) :
    ¬ goodCode (code (.vertex (.parallelDownChain n))) := by
  intro h
  change goodCode (PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack
    ((DrawingShape.downwardDots n).stack (.vertex .splitDown)))) at h
  rw [encode_stack] at h
  exact (good_left h) (.vertex 0 (.trivalent .mergeDown)) List.mem_cons_self

private theorem no_expandedProjection (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    ¬ goodCode (PlanarCode.encode (DrawingShape.expandedProjectionGeometry n o c)) := by
  intro h
  unfold DrawingShape.expandedProjectionGeometry at h
  rw [encode_stack] at h
  have hs := good_left h
  cases o
  · exact hs (.vertex 1 (.trivalent .upToUpDown)) List.mem_cons_self
  · exact hs (.vertex 2 .reverseCup) List.mem_cons_self

private theorem factor_drawing {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : goodCode (drawingCode d)) : Factorable d := by
  induction d with
  | ordinary d => exact factor_ordinary d h
  | vertical d e hd he =>
    rw [drawingCode_vertical] at h
    exact factor_vertical (hd (good_left h)) (he (good_right h))
  | horizontal d e hd he =>
    rw [drawingCode_horizontal] at h
    exact factor_horizontal (hd (good_left h)) (he (good_unshift (good_right h)))
  | parallelUpChain _ _ _ _ labels => exact False.elim (no_parallelUpChain labels.length h)
  | parallelDownChain _ _ _ _ labels => exact False.elim (no_parallelDownChain labels.length h)
  | expandedProjection _ _ _ _ _ o c => exact False.elim (no_expandedProjection 1 o c h)
  | expandedProjectionChain _ _ _ _ labels _ o c =>
    exact False.elim (no_expandedProjection labels.length o c h)
  | expandedLinearDotProjection _ _ _ _ labels _ o c =>
    exact False.elim (no_expandedProjection labels.length o c h)
  | rightCurlUp =>
    exact False.elim (h (.vertex 0 (.trivalent .upToUpDown)) List.mem_cons_self)
  | add d e _ _ =>
    let s := d.erase.geometry
    exact False.elim (h (.add 0 s.inputs s.outputs (PlanarCode.encode s)
      (drawingCode e)) List.mem_cons_self)
  | scale _ d _ =>
    let s := d.erase.geometry
    exact False.elim (h (.scale 0 s.inputs s.outputs (PlanarCode.encode s)) List.mem_cons_self)
  | trivalent v => cases v <;> exact factor_atom _ (Nat.le_refl 1)
  | bentVertex v => cases v <;> exact factor_atom _ (Nat.le_refl 1)
  | _ => exact factor_atom _ (Nat.le_refl 1)

/-- Cut the right-input dot and the merge at a common typed word. -/
theorem factor_rightCode {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : PlanarCode.encode d.erase.geometry = [mark 1, join 0]) :
    ∃ (m : Word A B) (below : LabelledDrawing Complex p m)
      (above : LabelledDrawing Complex m q),
      PlanarCode.encode below.erase.geometry = [mark 1] ∧
      PlanarCode.encode above.erase.geometry = [join 0] ∧
      d.interpret.eval = below.interpret.eval.vertical above.interpret.eval := by
  change drawingCode d = [mark 1, join 0] at h
  have hg : goodCode (drawingCode d) := by
    rw [h]
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> trivial
  exact factor_drawing d hg [mark 1] [join 0] h

theorem factor_rightFiber {p q : Boundary A B}
    (v : LabelledDrawing.PlanarAtBoundary Complex p q
      ⟨[true,true], [true], Quotient.mk PlanarCode.setoid rightCode⟩) :
    ∃ (m : Word A B) (below : LabelledDrawing Complex v.bottom m)
      (above : LabelledDrawing Complex m v.top),
      PlanarCode.encode below.erase.geometry = [mark 1] ∧
      PlanarCode.encode above.erase.geometry = [join 0] ∧
      v.diagram.interpret.eval = below.interpret.eval.vertical above.interpret.eval :=
  factor_rightCode v.diagram (fiber_code v)

end DotSlidePreorderProof


namespace DotSlideStructuralCoherence

open MackeyDiagrams

universe u v

section Basis

variable {K H J F : Type u} [Group K] [Group H] [Group J] [Group F]
variable {R : Type v} [CommSemiring R]
variable {X X' X'' : Biset K H} {Y Y' : Biset H J}

/-- Equivariant maps taking each basis element to a basis element. -/
private structure BasisMap (X X' : Biset K H) where
  run : X.carrier → X'.carrier
  commute : ∀ g x, run (X.act g x) = X'.act g (run x)

namespace BasisMap

private noncomputable def linear (f : BasisMap X X') : Biset.Hom R X X' :=
  Biset.Hom.ofFunction f.run f.commute

private theorem linear_single (f : BasisMap X X') (x : X.carrier) (c : R) :
    (f.linear (R := R)).toLinearMap (Finsupp.single x c) = Finsupp.single (f.run x) c :=
  Biset.Hom.ofFunction_single _ _ _ _

private def ident (X : Biset K H) : BasisMap X X := ⟨id, fun _ _ => rfl⟩

private def vert (f : BasisMap X X') (g : BasisMap X' X'') : BasisMap X X'' :=
  ⟨g.run ∘ f.run, fun k x => by simp only [Function.comp_apply, f.commute, g.commute]⟩

private def hor (f : BasisMap X X') (g : BasisMap Y Y') :
    BasisMap (X.tensor Y) (X'.tensor Y') where
  run := Quotient.lift (fun z => X'.pair Y' (f.run z.1) (g.run z.2)) (by
    intro x y h
    obtain ⟨k, hk, hk'⟩ := h
    rw [← hk, ← hk', f.commute, g.commute, Biset.pair_orbit])
  commute := by
    intro k z
    refine Quotient.inductionOn z ?_
    rintro ⟨x,y⟩
    change X'.pair Y' (f.run (X.act (k.1,1) x)) (g.run (Y.act (1,k.2) y)) =
      X'.pair Y' (X'.act (k.1,1) (f.run x)) (Y'.act (1,k.2) (g.run y))
    rw [f.commute, g.commute]

private theorem linear_ident (X : Biset K H) : ((ident X).linear (R := R)) = Biset.Hom.id X := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  exact linear_single _ _ _

private theorem linear_vert (f : BasisMap X X') (g : BasisMap X' X'') :
    ((f.vert g).linear (R := R)) = f.linear.vertical g.linear := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  change ((f.vert g).linear (R := R)).toLinearMap (Finsupp.single x c) =
    g.linear.toLinearMap (f.linear.toLinearMap (Finsupp.single x c))
  rw [linear_single, linear_single, linear_single]
  rfl

private theorem linear_hor (f : BasisMap X X') (g : BasisMap Y Y') :
    ((f.hor g).linear (R := R)) = f.linear.horizontal g.linear := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z c
  refine Quotient.inductionOn z ?_
  rintro ⟨x,y⟩
  change ((f.hor g).linear (R := R)).toLinearMap (Finsupp.single (X.pair Y x y) c) =
    (f.linear.horizontal g.linear).toLinearMap (Finsupp.single (X.pair Y x y) c)
  rw [linear_single, Biset.Hom.horizontal_single, linear_single, linear_single,
    Biset.pairLinear_single, one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

private def assoc (X : Biset K H) (Y : Biset H J) (Z : Biset J F) :
    BasisMap ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z)) :=
  ⟨Biset.associateBasis X Y Z, by
    intro g w
    refine Quotient.inductionOn w (fun ⟨xy,z⟩ => ?_)
    exact Quotient.inductionOn xy (fun _ => rfl)⟩

private def left (X : Biset K H) : BasisMap ((Biset.regular K).tensor X) X :=
  ⟨Biset.leftUnitBasis X, by
    intro g z
    refine Quotient.inductionOn z ?_
    rintro ⟨k,x⟩
    change X.act (g.1 * k * (1 : K)⁻¹, 1) (X.act (1,g.2) x) =
      X.act g (X.act (k,1) x)
    rw [← X.mul_act, ← X.mul_act]
    rcases g with ⟨a,b⟩
    simp⟩

private def insRight (X : Biset K H) : BasisMap X (X.tensor (Biset.regular H)) :=
  ⟨fun x => X.pair (Biset.regular H) x 1, by
    intro g x
    change X.pair (Biset.regular H) (X.act g x) 1 =
      X.pair (Biset.regular H) (X.act (g.1,1) x) (1 * 1 * g.2⁻¹)
    have e := X.pair_balance (Biset.regular H) g.2⁻¹ (X.act (g.1,1) x) 1
    rw [← X.mul_act] at e
    rcases g with ⟨k,h⟩
    simpa [Biset.regular] using e⟩

end BasisMap

end Basis


section Words

variable {U : Type u} [Group U] {A B C D : Subgroup U}
variable {R : Type v} [CommSemiring R]

private def appendBasis : {A B C : Subgroup U} →
    (a : Boundary A B) → (b : Boundary B C) →
    BasisMap (a.word.basis.tensor b.word.basis) (a.append b).word.basis
  | _, _, _, .empty _, b => BasisMap.left b.word.basis
  | _, _, _, .cons s t, b => (BasisMap.assoc s.word.basis t.word.basis b.word.basis).vert
      ((BasisMap.ident s.word.basis).hor (appendBasis t b))

private def join (a : Boundary A B) (b : Boundary B C)
    (x : a.word.basis.carrier) (y : b.word.basis.carrier) :
    (a.append b).word.basis.carrier :=
  (appendBasis a b).run (a.word.basis.pair b.word.basis x y)

private theorem join_cons (s : Strand A B) (t : Boundary B C) (b : Boundary C D)
    (x : s.word.basis.carrier) (y : t.word.basis.carrier) (z : b.word.basis.carrier) :
    join (.cons s t) b (s.word.basis.pair t.word.basis x y) z =
      s.word.basis.pair (t.append b).word.basis x (join t b y z) := rfl

private theorem join_left_action (a : Boundary A B) (b : Boundary B C)
    (g : A) (x : a.word.basis.carrier) (y : b.word.basis.carrier) :
    join a b (a.word.basis.act (g,1) x) y =
      (a.append b).word.basis.act (g,1) (join a b x y) := by
  have h := (appendBasis a b).commute (g,1) (a.word.basis.pair b.word.basis x y)
  rw [Biset.act_pair] at h
  change (appendBasis a b).run
    (a.word.basis.pair b.word.basis (a.word.basis.act (g,1) x) (b.word.basis.act 1 y)) = _ at h
  rwa [Biset.one_act] at h

private def reindex {a b : Boundary A B} (h : a = b) :
    a.word.basis.carrier → b.word.basis.carrier :=
  fun x => h ▸ x

private theorem reindex_cons (s : Strand A B) {a b : Boundary B C}
    (h : a = b) (x : s.word.basis.carrier) (y : a.word.basis.carrier) :
    reindex (congrArg (Boundary.cons s) h) (s.word.basis.pair a.word.basis x y) =
      s.word.basis.pair b.word.basis x (reindex h y) := by
  cases h
  rfl

private theorem join_assoc (a : Boundary A B) (b : Boundary B C) (c : Boundary C D)
    (x : a.word.basis.carrier) (y : b.word.basis.carrier) (z : c.word.basis.carrier) :
    reindex (Boundary.append_assoc a b c) (join (a.append b) c (join a b x y) z) =
      join a (b.append c) x (join b c y z) := by
  induction a with
  | empty => exact join_left_action b c x y z
  | cons s t ih =>
    refine Quotient.inductionOn x ?_
    rintro ⟨x',x''⟩
    change reindex (congrArg (Boundary.cons s) (Boundary.append_assoc t b c))
      (join (.cons s (t.append b)) c (join (.cons s t) b (s.word.basis.pair t.word.basis x' x'') y) z) =
      join (.cons s t) (b.append c) (s.word.basis.pair t.word.basis x' x'') (join b c y z)
    simp only [join_cons, reindex_cons s (Boundary.append_assoc t b c), ih]
    rfl

private theorem join_empty (a : Boundary A B) (x : a.word.basis.carrier) (y : B) :
    reindex (Boundary.append_empty a) (join a (.empty B) x y) =
      a.word.basis.act (1,y⁻¹) x := by
  induction a with
  | @empty K =>
    change ↥K at x
    change x * y * (1 : K)⁻¹ = 1 * x * (y⁻¹)⁻¹
    simp
  | @cons K H J s t ih =>
    refine Quotient.inductionOn x ?_
    rintro ⟨x',x''⟩
    change reindex (congrArg (Boundary.cons s) (Boundary.append_empty t))
      (join (.cons s t) (.empty J) (s.word.basis.pair t.word.basis x' x'') y) =
      (s.word.basis.tensor t.word.basis).act (1,y⁻¹) (s.word.basis.pair t.word.basis x' x'')
    have step := congrArg (reindex (congrArg (Boundary.cons s) (Boundary.append_empty t)))
      (join_cons s t (.empty J) x' x'' y)
    refine step.trans ((reindex_cons s (Boundary.append_empty t) x' _).trans ?_)
    rw [ih, Biset.act_pair]
    change s.word.basis.pair t.word.basis x' _ =
      s.word.basis.pair t.word.basis (s.word.basis.act 1 x') _
    rw [Biset.one_act]

private theorem eval_appendBasis (a : Boundary A B) (b : Boundary B C) :
    ((appendBasis a b).linear (R := R)) = (a.appendDiagram b).eval := by
  induction a with
  | empty => rfl
  | cons s t ih =>
    change (((BasisMap.assoc s.word.basis t.word.basis b.word.basis).vert
      ((BasisMap.ident s.word.basis).hor (appendBasis t b))).linear (R := R)) =
      (Biset.associate _ _ _ R).vertical ((Biset.Hom.id _).horizontal (t.appendDiagram b).eval)
    rw [BasisMap.linear_vert, BasisMap.linear_hor, BasisMap.linear_ident, ih]
    rfl

private def normBasis : {A B : Subgroup U} →
    (p : Word A B) → BasisMap p.basis p.boundary.word.basis
  | _, _, .empty A => BasisMap.ident (Biset.regular A)
  | _, _, .up a => BasisMap.insRight (Biset.induction a)
  | _, _, .down a => BasisMap.insRight (Biset.restriction a)
  | _, _, .tensor p q => ((normBasis p).hor (normBasis q)).vert (appendBasis p.boundary q.boundary)

private theorem eval_normBasis (p : Word A B) :
    ((normBasis p).linear (R := R)) = (p.reorderToBoundary (R := R)).eval := by
  induction p with
  | empty => exact BasisMap.linear_ident (R := R) _
  | up => rfl
  | down => rfl
  | tensor p q ihp ihq =>
    change ((((normBasis p).hor (normBasis q)).vert
      (appendBasis p.boundary q.boundary)).linear (R := R)) =
      ((p.reorderToBoundary (R := R)).eval.horizontal (q.reorderToBoundary (R := R)).eval).vertical
        (p.boundary.appendDiagram q.boundary).eval
    rw [BasisMap.linear_vert, BasisMap.linear_hor, ihp, ihq, eval_appendBasis]


/-- Transport the target of a map across equality of ordered strand data. -/
def transport {X : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X a.word.basis) : Biset.Hom R X b.word.basis :=
  h ▸ f

private theorem transport_single {X : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X a.word.basis) (x : X.carrier) (y : a.word.basis.carrier) (c : R)
    (hf : f.toLinearMap (Finsupp.single x c) = Finsupp.single y c) :
    (transport h f).toLinearMap (Finsupp.single x c) = Finsupp.single (reindex h y) c := by
  cases h
  exact hf

private theorem transport_trans {X : Biset A B} {a b c : Boundary A B}
    (h : a = b) (k : b = c) (f : Biset.Hom R X a.word.basis) :
    transport (h.trans k) f = transport k (transport h f) := by
  cases h
  cases k
  rfl

private theorem transport_vertical {X Y : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X Y) (g : Biset.Hom R Y a.word.basis) :
    transport h (f.vertical g) = f.vertical (transport h g) := by
  cases h
  rfl

private theorem transport_append {X : Biset A B} {Y : Biset B C}
    {a a' : Boundary A B} {b b' : Boundary B C} (ha : a = a') (hb : b = b')
    (f : Biset.Hom R X a.word.basis) (g : Biset.Hom R Y b.word.basis) :
    transport (congrArg₂ Boundary.append ha hb) ((f.horizontal g).vertical (a.appendDiagram b).eval) =
      ((transport ha f).horizontal (transport hb g)).vertical (a'.appendDiagram b').eval := by
  cases ha
  cases hb
  rfl

private def Coherent {p q : Word A B} (f : Biset.Hom R p.basis q.basis) : Prop :=
  ∃ h : p.boundary = q.boundary, transport h (p.reorderToBoundary (R := R)).eval =
    f.vertical (q.reorderToBoundary (R := R)).eval

private theorem coherent_of_single {p q : Word A B} (f : Biset.Hom R p.basis q.basis)
    (h : p.boundary = q.boundary) (g : p.basis.carrier → q.basis.carrier)
    (hf : ∀ x c, f.toLinearMap (Finsupp.single x c) = Finsupp.single (g x) c)
    (hg : ∀ x, reindex h ((normBasis p).run x) = (normBasis q).run (g x)) :
    Coherent (p := p) (q := q) f := by
  refine ⟨h, ?_⟩
  rw [← eval_normBasis p, ← eval_normBasis q]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  change (transport h (normBasis p).linear).toLinearMap (Finsupp.single x c) =
    (normBasis q).linear.toLinearMap (f.toLinearMap (Finsupp.single x c))
  rw [transport_single h _ x _ c (BasisMap.linear_single _ _ _), hf, BasisMap.linear_single, hg]

private theorem coherent_id (p : Word A B) : Coherent (p := p) (q := p) (Biset.Hom.id (R := R) _) :=
  ⟨rfl, rfl⟩

private theorem coherent_vertical {p q t : Word A B}
    {f : Biset.Hom R p.basis q.basis} {g : Biset.Hom R q.basis t.basis}
    (hf : Coherent (p := p) (q := q) f) (hg : Coherent (p := q) (q := t) g) :
    Coherent (p := p) (q := t) (f.vertical g) := by
  obtain ⟨h, hf⟩ := hf
  obtain ⟨k, hg⟩ := hg
  exact ⟨h.trans k, by rw [transport_trans h k, hf, transport_vertical k, hg, Biset.Hom.vertical_assoc]⟩

private theorem coherent_horizontal {p p' : Word A B} {q q' : Word B C}
    {f : Biset.Hom R p.basis p'.basis} {g : Biset.Hom R q.basis q'.basis}
    (hf : Coherent (p := p) (q := p') f) (hg : Coherent (p := q) (q := q') g) :
    Coherent (p := p.tensor q) (q := p'.tensor q') (f.horizontal g) := by
  obtain ⟨h, hf⟩ := hf
  obtain ⟨k, hg⟩ := hg
  refine ⟨congrArg₂ Boundary.append h k, ?_⟩
  change transport (congrArg₂ Boundary.append h k)
    (((p.reorderToBoundary (R := R)).eval.horizontal (q.reorderToBoundary (R := R)).eval).vertical
      (p.boundary.appendDiagram q.boundary).eval) =
    (f.horizontal g).vertical
      (((p'.reorderToBoundary (R := R)).eval.horizontal (q'.reorderToBoundary (R := R)).eval).vertical
        (p'.boundary.appendDiagram q'.boundary).eval)
  rw [transport_append h k, hf, hg, ← Biset.Hom.horizontal_vertical, Biset.Hom.vertical_assoc]

private theorem coherent_inverse {p q : Word A B}
    {f : Biset.Hom R p.basis q.basis} {g : Biset.Hom R q.basis p.basis}
    (hf : Coherent (p := p) (q := q) f) (hg : g.vertical f = Biset.Hom.id _) :
    Coherent (p := q) (q := p) g := by
  obtain ⟨h, hf⟩ := hf
  have hc := congrArg (transport h.symm) hf
  rw [← transport_trans h h.symm] at hc
  change (p.reorderToBoundary (R := R)).eval = transport h.symm
    (f.vertical (q.reorderToBoundary (R := R)).eval) at hc
  refine ⟨h.symm, ?_⟩
  rw [hc, transport_vertical h.symm, ← Biset.Hom.vertical_assoc, hg, Biset.Hom.id_vertical]

private theorem coherent_associate (p : Word A B) (q : Word B C) (t : Word C D) :
    Coherent (p := (p.tensor q).tensor t) (q := p.tensor (q.tensor t))
      (Diagram.associate (R := R) p q t).eval := by
  refine coherent_of_single _ (Word.boundary_associate p q t)
    (Biset.associateBasis p.basis q.basis t.basis) ?_ ?_
  · intro x c
    change (Biset.associate p.basis q.basis t.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.associate, Biset.Hom.ofFunction_single]
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨xy,z⟩
    refine Quotient.inductionOn xy ?_
    rintro ⟨x,y⟩
    change reindex (Boundary.append_assoc p.boundary q.boundary t.boundary)
      ((normBasis ((p.tensor q).tensor t)).run ((p.basis.tensor q.basis).pair t.basis (p.basis.pair q.basis x y) z)) =
      (normBasis (p.tensor (q.tensor t))).run (p.basis.pair (q.basis.tensor t.basis) x (q.basis.pair t.basis y z))
    exact join_assoc p.boundary q.boundary t.boundary _ _ _

private theorem coherent_leftUnit (p : Word A B) :
    Coherent (p := (Word.empty A).tensor p) (q := p) (Diagram.leftUnit (R := R) p).eval := by
  refine coherent_of_single _ (Word.boundary_leftUnit p) (Biset.leftUnitBasis p.basis) ?_ ?_
  · intro x c
    change (Biset.leftUnit p.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.leftUnit, Biset.Hom.ofFunction_single]
  · intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨k,x⟩
    change p.boundary.word.basis.act (k,1) ((normBasis p).run x) =
      (normBasis p).run (p.basis.act (k,1) x)
    exact ((normBasis p).commute _ _).symm

private theorem coherent_rightUnit (p : Word A B) :
    Coherent (p := p.tensor (.empty B)) (q := p) (Diagram.rightUnit (R := R) p).eval := by
  refine coherent_of_single _ (Word.boundary_rightUnit p) (Biset.rightUnitBasis p.basis) ?_ ?_
  · intro x c
    change (Biset.rightUnit p.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.rightUnit, Biset.Hom.ofFunction_single]
  · intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨x,k⟩
    change reindex (Boundary.append_empty p.boundary) (join p.boundary (.empty B) ((normBasis p).run x) k) =
      (normBasis p).run (p.basis.act (1,k⁻¹) x)
    exact (join_empty p.boundary _ k).trans ((normBasis p).commute _ _).symm

end Words

end DotSlideStructuralCoherence

namespace DotSlidePreorderProof

open MackeyDiagrams DotSlideStructuralCoherence

universe u
variable {U : Type u} [Group U] {A B : Subgroup U}

private theorem expanded_code_ne_nil (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry n o c) ≠ [] := by
  cases o <;> cases c <;>
    simp [DrawingShape.expandedProjectionGeometry, encode_stack, PlanarCode.encode, PlanarCode.shift]

private theorem vertex_code_ne_nil (k : VertexKind) : code (.vertex k) ≠ [] := by
  cases k <;> try (exact List.cons_ne_nil _ _)
  case parallelUpChain n =>
    simp [code, DrawingShape.geometry, encode_stack, PlanarCode.encode]
  case parallelDownChain n =>
    simp [code, DrawingShape.geometry, encode_stack, PlanarCode.encode]
  case expandedMixedProjection o c => exact expanded_code_ne_nil 1 o c
  case expandedProjectionChain n o c => exact expanded_code_ne_nil n o c

private theorem code_split_horizontal {a b : PlanarCode.Code} {n : Nat}
    (h : a ++ PlanarCode.shift n b = []) : a = [] ∧ b = [] := by
  obtain ⟨ha, hb⟩ := List.append_eq_nil_iff.mp h
  exact ⟨ha, List.map_eq_nil_iff.mp hb⟩

private theorem emptyDiagram_coherent {p q : Word A B} (d : Diagram Complex p q)
    (h : code d.drawing = []) : Coherent (p := p) (q := q) d.eval := by
  induction d <;> try (exact (List.cons_ne_nil _ _ h).elim)
  case id p => exact coherent_id p
  case associate p q r => exact coherent_associate p q r
  case unassociate p q r =>
    exact coherent_inverse (coherent_associate p q r) Biset.unassociate_associate
  case leftUnit p => exact coherent_leftUnit p
  case rightUnit p => exact coherent_rightUnit p
  case insertLeftUnit p =>
    exact coherent_inverse (coherent_leftUnit p) Biset.insertLeftUnit_leftUnit
  case insertRightUnit p =>
    exact coherent_inverse (coherent_rightUnit p) Biset.insertRightUnit_rightUnit
  case vertical d e ihd ihe =>
    have ⟨hd, he⟩ := List.append_eq_nil_iff.mp ((diagram_code_vert d e).symm.trans h)
    exact coherent_vertical (ihd hd) (ihe he)
  case horizontal d e ihd ihe =>
    have ⟨hd, he⟩ := code_split_horizontal ((diagram_code_horiz d e).symm.trans h)
    exact coherent_horizontal (ihd hd) (ihe he)

private theorem emptyDrawing_coherent {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : code d.erase = []) : Coherent (p := p) (q := q) d.interpret.eval := by
  induction d <;> try (exact (vertex_code_ne_nil _ h).elim)
  case ordinary d => exact emptyDiagram_coherent d h
  case add | scale =>
    simp only [code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, List.cons_ne_nil] at h
  case vertical d e ihd ihe =>
    have ⟨hd, he⟩ := List.append_eq_nil_iff.mp ((drawing_code_vert d e).symm.trans h)
    exact coherent_vertical (ihd hd) (ihe he)
  case horizontal d e ihd ihe =>
    have ⟨hd, he⟩ := code_split_horizontal ((drawing_code_horiz d e).symm.trans h)
    exact coherent_horizontal (ihd hd) (ihe he)

/-- At the canonical boundary the evaluated map is the transported identity. -/
theorem empty_geometry_atBoundary {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : PlanarCode.encode d.erase.geometry = []) :
    ∃ he : p.boundary = q.boundary,
      d.interpret.atBoundary.eval = transport he (Biset.Hom.id (R := Complex) p.boundary.word.basis) := by
  obtain ⟨he, hc⟩ := emptyDrawing_coherent d h
  refine ⟨he, ?_⟩
  change (p.reorderFromBoundary (R := Complex)).eval.vertical
    (d.interpret.eval.vertical (q.reorderToBoundary (R := Complex)).eval) = _
  rw [← hc, ← transport_vertical he]
  have hp : (p.reorderFromBoundary (R := Complex)).eval.vertical
      (p.reorderToBoundary (R := Complex)).eval = Biset.Hom.id p.boundary.word.basis :=
    Word.eval_reorderFromTo p
  rw [hp]

end DotSlidePreorderProof



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


namespace DotSlidePreorderProof

open MackeyDiagrams

universe u
variable {U : Type u} [Group U]
variable {G H K : Subgroup U}

private abbrev MergeBoundaryMap (p q : Boundary G K) :=
  Biset.Hom Complex p.word.basis q.word.basis

private noncomputable abbrev normalize {p q : Word G K} (d : ScopedDiagram Complex p q) :
    MergeBoundaryMap p.boundary q.boundary := d.atBoundary.eval

private abbrev upPair (l : ConjEmbedding H G) (a : ConjEmbedding K H) :=
  (Word.up l).tensor (.up a)

private inductive StraightAt : (p q : Boundary G K) → MergeBoundaryMap p q → Prop
  | id (p : Boundary G K) : StraightAt p p (Biset.Hom.id _)

private inductive MergeAt : (p q : Boundary G K) → MergeBoundaryMap p q → Prop
  | vertex (H : Subgroup U) (l : ConjEmbedding H G) (a : ConjEmbedding K H) :
    MergeAt (upPair l a).boundary (Word.up (l.comp a)).boundary
      (normalize (.ordinary (.mergeUp l a)))

/-- The only coherence input. Empty code evaluates to the identity at the
common ordered labelled boundary. -/
private def EmptyCodeStraight (U : Type u) [Group U] : Prop :=
  ∀ {G K : Subgroup U} {p q : Word G K} (d : LabelledDrawing Complex p q),
    code d.erase = [] → StraightAt p.boundary q.boundary (normalize d.interpret)

private noncomputable def juxtaposeMap
    {p q : Boundary G H} {r s : Boundary H K}
    (f : MergeBoundaryMap p q) (g : MergeBoundaryMap r s) : MergeBoundaryMap (p.append r) (q.append s) :=
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

private theorem straight_boundary_eq {p q : Boundary G K} {f : MergeBoundaryMap p q}
    (h : StraightAt p q f) : p = q := by
  cases h
  rfl

private theorem vertical_straight_left
    {p q r : Boundary G K} {f : MergeBoundaryMap p q} {g : MergeBoundaryMap q r}
    (hf : StraightAt p q f) (hg : MergeAt q r g) :
    MergeAt p r (f.vertical g) := by
  cases hf
  simpa only [Biset.Hom.id_vertical] using hg

private theorem vertical_straight_right
    {p q r : Boundary G K} {f : MergeBoundaryMap p q} {g : MergeBoundaryMap q r}
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
    {p q p' q' : Boundary G K} {f : MergeBoundaryMap p p'} {g : MergeBoundaryMap p' q'}
    {h : MergeBoundaryMap q' q} (hf : StraightAt p p' f) (hh : StraightAt q' q h)
    (hm : MergeAt p q ((f.vertical g).vertical h)) : MergeAt p' q' g := by
  cases hf
  cases hh
  simpa only [Biset.Hom.id_vertical, Biset.Hom.vertical_id] using hm

private theorem merge_pad_left (empty : EmptyCodeStraight U)
    {p q : Boundary G K} {f : MergeBoundaryMap p q} (h : MergeAt p q f) :
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

private theorem merge_pad_right (empty : EmptyCodeStraight U)
    {p q : Boundary G K} {f : MergeBoundaryMap p q} (h : MergeAt p q f) :
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

private theorem merge_input_dirs {p q : Boundary G K} {f : MergeBoundaryMap p q}
    (h : MergeAt p q f) : boundaryDirs p = [true, true] := by
  cases h
  rfl

private theorem merge_horizontal_left
    (empty : EmptyCodeStraight U)
    {p q : Boundary G H} {r s : Boundary H K}
    {f : MergeBoundaryMap p q} {g : MergeBoundaryMap r s}
    (hf : MergeAt p q f) (hg : StraightAt r s g) (hr : boundaryDirs r = []) :
    MergeAt (p.append r) (q.append s) (juxtaposeMap f g) := by
  cases hg
  rename_i r
  cases r with
  | empty => exact merge_pad_right empty hf
  | cons t tail => cases t <;> cases hr

private theorem merge_horizontal_right
    (empty : EmptyCodeStraight U)
    {p q : Boundary G H} {r s : Boundary H K}
    {f : MergeBoundaryMap p q} {g : MergeBoundaryMap r s}
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

private theorem merge_vertical_step (empty : EmptyCodeStraight U)
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

private theorem merge_horizontal_step (empty : EmptyCodeStraight U)
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

private theorem diagram_merge (empty : EmptyCodeStraight U) {p q : Word G K}
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

private theorem drawing_merge (empty : EmptyCodeStraight U) {p q : Word G K}
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

private theorem mergeAt_witness {p q : Boundary G K} {f : MergeBoundaryMap p q}
    (h : MergeAt p q f) :
    ∃ (M : Subgroup U) (l : ConjEmbedding M G) (a : ConjEmbedding K M)
      (hp : p = (upPair l a).boundary) (hq : q = (Word.up (l.comp a)).boundary),
      cast (congrArg₂ (fun b c : Boundary G K => MergeBoundaryMap b c) hp hq) f =
        normalize (ScopedDiagram.ordinary (Diagram.mergeUp l a)) := by
  cases h with
  | vertex M l a => exact ⟨M, l, a, rfl, rfl, rfl⟩

/-- Normalize a singleton merge at any parenthesization of its ordered inputs
and output. The stronger width-bound hypothesis suffices. -/
private theorem singleton_merge_normal_form (empty : EmptyCodeStraight U)
    {p q : Word G K} (d : LabelledDrawing Complex p q)
    (hc : code d.erase = [join 0]) (hw : p.directions.length ≤ 2) :
    ∃ (M : Subgroup U) (l : ConjEmbedding M G) (a : ConjEmbedding K M)
      (hp : p.boundary = (upPair l a).boundary)
      (hq : q.boundary = (Word.up (l.comp a)).boundary),
      cast (congrArg₂ (fun b c : Boundary G K => MergeBoundaryMap b c) hp hq)
          d.interpret.atBoundary.eval =
        (LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.mergeUp l a)).interpret.atBoundary.eval :=
  mergeAt_witness (drawing_merge empty d hc hw)

private theorem straightAt_of_eq {p q : Boundary G K} {f : MergeBoundaryMap p q}
    (h : p = q)
    (he : cast (congrArg (fun b => MergeBoundaryMap p b) h.symm) f = Biset.Hom.id _) :
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


/-- Remaining normal form, for two stages with a common typed word. -/
def StagedNormalForm (U : Type u) [Group U] : Prop :=
  ∀ (G K : Subgroup U) {p m q : Word G K}
    (below : LabelledDrawing Complex p m) (above : LabelledDrawing Complex m q),
    p.directions = [true, true] →
    PlanarCode.encode below.erase.geometry = [.vertex 1 .upDot] →
    PlanarCode.encode above.erase.geometry = [.vertex 0 (.trivalent .mergeUp)] →
    ∃ (H : Subgroup U) (l : ConjEmbedding H G) (a b : ConjEmbedding K H)
      (label : DotLabel Complex a b) (hp : (pair l a).boundary = p.boundary)
      (hq : (Word.up (l.comp b)).boundary = q.boundary),
      (below.vertical above).interpret.atBoundary.eval =
        (show LabelledDrawing.PlanarAtBoundary Complex p.boundary q.boundary rightShape
          from ⟨_, _, branch l label, hp, hq, branch_shape l label⟩).interpret.eval

theorem normalForm_of_staged (normal : StagedNormalForm U) : NormalForm U := by
  rintro G K _ _ ⟨p, q, d, rfl, rfl, hs⟩
  let v : LabelledDrawing.PlanarAtBoundary Complex p.boundary q.boundary rightShape :=
    ⟨p, q, d, rfl, rfl, hs⟩
  obtain ⟨m, below, above, hb, ha, he⟩ := DotSlidePreorderProof.factor_rightFiber v
  have hw : p.directions = [true, true] := congrArg PlanarShape.bottom hs
  obtain ⟨H, l, a, b, label, hp, hq, hn⟩ := normal G K below above hw hb ha
  refine ⟨H, l, a, b, label, hp, hq, ?_⟩
  have hh := (ScopedDiagram.eval_atBoundary_eq_iff
    d.interpret (below.vertical above).interpret).2 he
  exact hh.trans hn

end DotSlidePreorderBridge

namespace DotSlidePreorderProof

open MackeyDiagrams

universe u
variable {U : Type u} [Group U]

private theorem transport_id_eq_boundaryId {G K : Subgroup U}
    {P Q : Boundary G K} (h : P = Q) :
    DotSlideStructuralCoherence.transport h
      (Biset.Hom.id (R := Complex) P.word.basis) = boundaryId h := by
  subst Q
  rfl

private theorem cast_boundaryId {G K : Subgroup U} {P Q : Boundary G K} (h : P = Q) :
    cast (congrArg (fun b => BoundaryMap P b) h.symm) (boundaryId h) =
      Biset.Hom.id (R := Complex) P.word.basis := by
  subst Q
  rfl

private theorem dot_empty_coherence : EmptyCodeCoherence U := by
  intro G K p q d h
  obtain ⟨he, hev⟩ := empty_geometry_atBoundary d h
  exact ⟨he, hev.trans (transport_id_eq_boundaryId he)⟩

private theorem merge_empty_coherence : EmptyCodeStraight U := by
  intro G K p q d h
  obtain ⟨he, hev⟩ := dot_empty_coherence (U := U) d h
  apply straightAt_of_eq he
  change cast _ (canon d.interpret.eval) = _
  rw [hev]
  exact cast_boundaryId he

end DotSlidePreorderProof

namespace DotSlidePreorderBridge

open MackeyDiagrams DotSlidePreorderProof

universe u
variable {U : Type u} [Group U] {G K : Subgroup U}

private abbrev BoundaryHom (p q : Boundary G K) :=
  Biset.Hom Complex p.word.basis q.word.basis

private theorem heq_of_hom_cast {p q p' q' : Boundary G K}
    (hp : p = p') (hq : q = q') {f : BoundaryHom p q} {g : BoundaryHom p' q'}
    (h : cast (congrArg₂ (fun b c : Boundary G K => BoundaryHom b c) hp hq) f = g) :
    HEq f g := by
  subst p'
  subst q'
  exact heq_of_eq h

private theorem vertical_heq {p m q p' m' q' : Boundary G K}
    (hp : p = p') (hm : m = m') (hq : q = q')
    {f : BoundaryHom p m} {f' : BoundaryHom p' m'}
    {g : BoundaryHom m q} {g' : BoundaryHom m' q'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (f.vertical g) (f'.vertical g') := by
  subst p'
  subst m'
  subst q'
  rw [eq_of_heq hf, eq_of_heq hg]

/- Proposition 3.2 uses (3.1) on the displayed right-input drawing.
   For the full planar fiber, first cut its rigid event list and normalize the
   two typed stages. The source shape provides the width-two hypothesis.
   On the shared middle word the two normalized ordered boundaries agree,
   including both embedding labels. Transport both evaluations through that
   common boundary before composing. -/
private theorem stagedNormalForm : StagedNormalForm U := by
  intro G K p m q below above hw hb ha
  let v : LabelledDrawing.PlanarAtBoundary Complex p.boundary m.boundary below.planarShape :=
    ⟨p, m, below, rfl, rfl, rfl⟩
  obtain ⟨H, l, a, b, label, hp, hm, hd⟩ :=
    normalizeRightDot (dot_empty_coherence (U := U)) v hb hw
  have hmw : m.directions.length ≤ 2 := by
    have h := congrArg boundaryDirections hm
    rw [boundaryDirections_word, boundaryDirections_word] at h
    rw [← h]
    change 2 ≤ 2
    exact le_rfl
  obtain ⟨J, l', b', hm', hq, he⟩ :=
    singleton_merge_normal_form (merge_empty_coherence (U := U)) above ha hmw
  obtain ⟨hJ, hl, hb'⟩ := branchBoundary_inj l b l' b' (hm'.symm.trans hm.symm)
  subst J
  have hl' := eq_of_heq hl
  have hb'' := eq_of_heq hb'
  subst l'
  subst b'
  let dotStage : LabelledDrawing Complex (pair l a) (pair l b) :=
    (LabelledDrawing.ordinary (Diagram.id (.up l))).horizontal label.upDrawing
  let mergeStage : LabelledDrawing Complex (pair l b) (.up (l.comp b)) :=
    .trivalent (.mergeUp l b)
  let dotRep : LabelledDrawing.PlanarAtBoundary Complex p.boundary m.boundary singletonRightShape :=
    ⟨_, _, dotStage, hp, hm, rfl⟩
  have hd' : HEq below.interpret.atBoundary.eval dotStage.interpret.atBoundary.eval :=
    (heq_of_eq (show below.interpret.atBoundary.eval = dotRep.interpret.eval from hd)).trans
      (atBoundary_eval_heq dotRep)
  have he' : HEq above.interpret.atBoundary.eval mergeStage.interpret.atBoundary.eval :=
    heq_of_hom_cast hm' hq he
  let rep : LabelledDrawing.PlanarAtBoundary Complex p.boundary q.boundary rightShape :=
    ⟨_, _, branch l label, hp, hq.symm, branch_shape l label⟩
  refine ⟨H, l, a, b, label, hp, hq.symm, ?_⟩
  have hv := vertical_heq hp.symm hm.symm hq hd' he'
  rw [← normalize_vertical below.interpret above.interpret,
    ← normalize_vertical dotStage.interpret mergeStage.interpret] at hv
  exact eq_of_heq (hv.trans (atBoundary_eval_heq rep).symm)

private theorem wholeFiber : NormalForm U := normalForm_of_staged stagedNormalForm

end DotSlidePreorderBridge


theorem DotSlidePreorderNotSymmetric : (
let boundary : List Bool × List Bool := ([true, true], [true])
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
(∀ {U : Type*} [Group U],
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
¬ MackeyDiagrams.LabelledDrawing.ShapeReplaces B₄ A₄
) :=
(by
  exact DotSlidePreorderBridge.proposition32
    (fun {_} _ => DotSlidePreorderBridge.wholeFiber) DotSlidePreorderBridge.wholeFiber)
