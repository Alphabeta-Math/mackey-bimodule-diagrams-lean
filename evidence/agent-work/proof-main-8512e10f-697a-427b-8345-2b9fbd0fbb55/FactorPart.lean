import ShapePart

set_option maxHeartbeats 2000000
namespace CaseTwoFactor
open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {A B C D : Subgroup U}

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

private def isCompactCrossing : PlanarEvent → Prop
  | .vertex _ .mixedProjection | .vertex _ .parallelUp => True
  | _ => False

private def goodCode (c : PlanarCode.Code) : Prop :=
  ∀ e ∈ c, isCompactCrossing e

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


/-- Split the exact left code into the three typed crossing stages.
Use the cut proof from the registered DotSlidePreorderNotSymmetric, replacing
its admitted event kinds by the two compact crossing kinds of Example 6.3. -/
theorem factor_left {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : PlanarCode.encode d.erase.geometry =
      [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp]) :
    ∃ (m n : Word A B) (d₁ : LabelledDrawing Complex p m)
      (d₂ : LabelledDrawing Complex m n) (d₃ : LabelledDrawing Complex n q),
      PlanarCode.encode d₁.erase.geometry = [.vertex 0 .mixedProjection] ∧
      PlanarCode.encode d₂.erase.geometry = [.vertex 1 .mixedProjection] ∧
      PlanarCode.encode d₃.erase.geometry = [.vertex 0 .parallelUp] ∧
      d.interpret.eval = d₁.interpret.eval.vertical
        (d₂.interpret.eval.vertical d₃.interpret.eval) := by
  let a : PlanarEvent := .vertex 0 .mixedProjection
  let b : PlanarEvent := .vertex 1 .mixedProjection
  let c : PlanarEvent := .vertex 0 .parallelUp
  change drawingCode d = [a,b,c] at h
  have hg : goodCode (drawingCode d) := by
    rw [h]
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> trivial
  obtain ⟨m,d₁,tail,h₁,ht,he⟩ := factor_drawing d hg [a] [b,c] h
  have htgood : goodCode (drawingCode tail) := by
    rw [ht]
    intro e hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> trivial
  obtain ⟨n,d₂,d₃,h₂,h₃,he'⟩ := factor_drawing tail htgood [b] [c] ht
  exact ⟨m,n,d₁,d₂,d₃,h₁,h₂,h₃,he.trans (congrArg (d₁.interpret.eval.vertical ·) he')⟩

end CaseTwoFactor

#print axioms CaseTwoFactor.factor_left
