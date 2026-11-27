import MackeyDiagrams.PlanarShape

namespace MackeyDiagrams.CaseOneTrace

universe u v

variable {U : Type u} [Group U]
variable {K H J : Subgroup U}

def width : {K H : Subgroup U} → Boundary K H → Nat
  | _, _, .empty _ => 0
  | _, _, .cons _ rest => 1 + width rest

theorem width_append (a : Boundary K H) (b : Boundary H J) :
    width (a.append b) = width a + width b := by
  induction a with
  | empty => simp [width, Boundary.append]
  | cons _ rest ih => simp [width, Boundary.append, Nat.add_assoc, ih]

theorem width_boundary (p : Word K H) : width p.boundary = p.directions.length := by
  induction p with
  | empty => rfl
  | up => rfl
  | down => rfl
  | tensor p q ihp ihq => simp [Word.boundary, Word.directions, width_append, ihp, ihq]

inductive Crossing : {K H : Subgroup U} →
    Boundary K H → Boundary K H → VertexKind → Type u
  | parallelUp {K H B B' : Subgroup U}
      (a : ConjEmbedding B K) (b : ConjEmbedding H B)
      (a' : ConjEmbedding B' K) (b' : ConjEmbedding H B') :
      Crossing ((Word.up a).tensor (.up b)).boundary
        ((Word.up a').tensor (.up b')).boundary .parallelUp
  | mixedProjection {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G)
      (l : ConjEmbedding L K) (r : ConjEmbedding L H)
      (label : ProjectionDot.Mixed a b l r) :
      Crossing ((Word.down a).tensor (.up b)).boundary
        ((Word.up l).tensor (.down r)).boundary .mixedProjection

inductive Edge {K H : Subgroup U} :
    Boundary K H → Boundary K H → PlanarEvent → Type u
  | pad {A B : Subgroup U} {p q : Boundary A B} {kind : VertexKind}
      (pre : Boundary K A) (suffix : Boundary B H) (crossing : Crossing p q kind) :
      Edge (pre.append (p.append suffix)) (pre.append (q.append suffix))
        (.vertex (width pre) kind)

def Crossing.edge {p q : Boundary K H} {kind : VertexKind} (c : Crossing p q kind) :
    Edge p q (.vertex 0 kind) := by
  simpa only [Boundary.append, Boundary.append_empty, width] using
    (Edge.pad (.empty K) (.empty H) c)

inductive Path {K H : Subgroup U} : Boundary K H → Boundary K H → PlanarCode.Code → Type u
  | nil (p : Boundary K H) : Path p p []
  | cons {p q r : Boundary K H} {e : PlanarEvent} {es : PlanarCode.Code}
      (head : Edge p q e) (tail : Path q r es) : Path p r (e :: es)

def Path.empty {p q : Boundary K H} (h : p = q) : Path p q [] := h ▸ .nil p

def Path.append {p q r : Boundary K H} {a b : PlanarCode.Code}
    (x : Path p q a) (y : Path q r b) : Path p r (a ++ b) :=
  match x with
  | .nil _ => y
  | .cons e tail => .cons e (tail.append y)

def Edge.suffix {p q : Boundary K H} {e : PlanarEvent}
    (x : Edge p q e) (b : Boundary H J) : Edge (p.append b) (q.append b) e := by
  cases x with
  | pad pre suffix c =>
    simpa only [Boundary.append_assoc] using Edge.pad pre (suffix.append b) c

def Edge.withPrefix {p q : Boundary H J} {e : PlanarEvent}
    (x : Edge p q e) (a : Boundary K H) :
    Edge (a.append p) (a.append q) (e.place (width a + e.position)) := by
  cases x with
  | pad pre suffix c =>
    simpa only [Boundary.append_assoc, width_append, PlanarEvent.place, PlanarEvent.position]
      using Edge.pad (a.append pre) suffix c

def Path.suffix {p q : Boundary K H} {es : PlanarCode.Code}
    (x : Path p q es) (b : Boundary H J) : Path (p.append b) (q.append b) es :=
  match x with
  | .nil p => .nil (p.append b)
  | .cons e tail => .cons (e.suffix b) (tail.suffix b)

def Path.withPrefix {p q : Boundary H J} {es : PlanarCode.Code}
    (x : Path p q es) (a : Boundary K H) :
    Path (a.append p) (a.append q) (PlanarCode.shift (width a) es) :=
  match x with
  | .nil p => .nil (a.append p)
  | .cons e tail => .cons (e.withPrefix a) (tail.withPrefix a)

def Path.horizontal {p p' : Boundary K H} {q q' : Boundary H J}
    {es fs : PlanarCode.Code} (left : Path p p' es) (right : Path q q' fs) :
    Path (p.append q) (p'.append q') (es ++ PlanarCode.shift (width p') fs) :=
  (left.suffix q).append (right.withPrefix p')


section Codes

theorem event_place_place (e : PlanarEvent) (j i : Nat) :
    (e.place j).place i = e.place i := by
  cases e <;> rfl

theorem event_position_place (e : PlanarEvent) (i : Nat) : (e.place i).position = i := by
  cases e <;> rfl

theorem shift_zero (es : PlanarCode.Code) : PlanarCode.shift 0 es = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.place (0 + e.position) :: PlanarCode.shift 0 es = e :: es
    rw [Nat.zero_add, ih]
    cases e <;> rfl

theorem shift_nil (n : Nat) : PlanarCode.shift n [] = [] := rfl

theorem shift_append (n : Nat) (es fs : PlanarCode.Code) :
    PlanarCode.shift n (es ++ fs) = PlanarCode.shift n es ++ PlanarCode.shift n fs :=
  List.map_append

theorem shift_shift (n m : Nat) (es : PlanarCode.Code) :
    PlanarCode.shift n (PlanarCode.shift m es) = PlanarCode.shift (n + m) es := by
  simp only [PlanarCode.shift, List.map_map, Function.comp_def,
    event_position_place, event_place_place, Nat.add_assoc]

theorem encode_stack (a b : DrawingShape) :
    PlanarCode.encode (a.stack b) = PlanarCode.encode a ++ PlanarCode.encode b := by
  fun_induction DrawingShape.stack a b <;>
    simp_all [PlanarCode.encode, List.append_assoc]

theorem encode_juxtapose (a b : DrawingShape) :
    PlanarCode.encode (a.juxtapose b) =
      PlanarCode.encode a ++ PlanarCode.shift a.outputs.length (PlanarCode.encode b) := by
  fun_induction DrawingShape.juxtapose a b <;>
    simp_all [DrawingShape.outputs, PlanarCode.encode, shift_nil, shift_zero, shift_append, shift_shift,
      List.append_assoc]

end Codes


section OrdinaryCode

/-- A shape made of ordinary vertices with matching interfaces. -/
inductive OrdinaryForm : DrawingShape → List Bool → List Bool → Prop
  | straight (dirs : List Bool) : OrdinaryForm (.straight dirs) dirs dirs
  | vertex (k : VertexKind) (h : (DrawingShape.vertex k).geometry = .vertex k) :
      OrdinaryForm (.vertex k) k.inputs k.outputs
  | vertical {a b : DrawingShape} {i m o : List Bool} :
      OrdinaryForm a i m → OrdinaryForm b m o → OrdinaryForm (.vertical a b) i o
  | horizontal {a b : DrawingShape} {i j m o : List Bool} :
      OrdinaryForm a i j → OrdinaryForm b m o → OrdinaryForm (.horizontal a b) (i ++ m) (j ++ o)
  | zero (i o : List Bool) : OrdinaryForm (.zero i o) i o
  | add {a b : DrawingShape} {i o : List Bool} :
      OrdinaryForm a i o → OrdinaryForm b i o → OrdinaryForm (.add a b) i o
  | scale {a : DrawingShape} {i o : List Bool} :
      OrdinaryForm a i o → OrdinaryForm (.scale a) i o

theorem OrdinaryForm.inputs {s : DrawingShape} {i o : List Bool} (f : OrdinaryForm s i o) :
    s.inputs = i := by
  induction f <;> simp_all [DrawingShape.inputs]

theorem OrdinaryForm.outputs {s : DrawingShape} {i o : List Bool} (f : OrdinaryForm s i o) :
    s.outputs = o := by
  induction f <;> simp_all [DrawingShape.outputs]

theorem OrdinaryForm.stack {a b : DrawingShape} {i m o : List Bool}
    (x : OrdinaryForm a i m) (y : OrdinaryForm b m o) : OrdinaryForm (a.stack b) i o := by
  fun_induction DrawingShape.stack a b generalizing i m o
  · cases x
    exact y
  · cases y
    exact x
  · rename_i first rest above h ih
    cases x with
    | vertical x₁ x₂ => exact .vertical x₁ (ih x₂ y)
  · exact .vertical x y

theorem OrdinaryForm.juxtapose {a b : DrawingShape} {i j m o : List Bool}
    (x : OrdinaryForm a i j) (y : OrdinaryForm b m o) :
    OrdinaryForm (a.juxtapose b) (i ++ m) (j ++ o) := by
  fun_induction DrawingShape.juxtapose a b generalizing i j m o
  · cases x
    exact y
  · cases y
    simpa only [List.append_nil] using x
  · cases x
    cases y
    exact .straight _
  · rename_i first rest right h ih
    cases x with
    | horizontal x₁ x₂ =>
      simpa only [List.append_assoc] using OrdinaryForm.horizontal x₁ (ih x₂ y)
  · exact .horizontal x y

theorem OrdinaryForm.geometry {s : DrawingShape} {i o : List Bool}
    (f : OrdinaryForm s i o) : OrdinaryForm s.geometry i o := by
  induction f with
  | straight => exact .straight _
  | vertex k h =>
    rw [h]
    exact .vertex k h
  | vertical _ _ ia ib => exact ia.stack ib
  | horizontal _ _ ia ib => exact ia.juxtapose ib
  | zero => exact .zero _ _
  | add _ _ ia ib => exact .add ia ib
  | scale _ ia => exact .scale ia

theorem OrdinaryForm.encode_geometry {s : DrawingShape} {i o : List Bool}
    (f : OrdinaryForm s i o) : PlanarCode.encode s.geometry = PlanarCode.encode s := by
  induction f with
  | straight => rfl
  | vertex _ h => rw [h]
  | vertical _ _ ia ib => simp only [DrawingShape.geometry, encode_stack, PlanarCode.encode, ia, ib]
  | horizontal x _ ia ib =>
    simp only [DrawingShape.geometry, encode_juxtapose, PlanarCode.encode,
      x.geometry.outputs, x.outputs, ia, ib]
  | zero => rfl
  | add x _ ia ib =>
    simp only [DrawingShape.geometry, PlanarCode.encode, x.geometry.inputs, x.inputs,
      x.geometry.outputs, x.outputs, ia, ib]
  | scale x ia =>
    simp only [DrawingShape.geometry, PlanarCode.encode, x.geometry.inputs, x.inputs,
      x.geometry.outputs, x.outputs, ia]

theorem ordinaryForm {R : Type v} {K H : Subgroup U} {p q : Word K H} (d : Diagram R p q) :
    OrdinaryForm d.drawing p.directions q.directions := by
  induction d with
  | id => exact .straight _
  | leftUnit => exact .straight _
  | rightUnit => simpa only [Diagram.drawing, Word.directions, List.append_nil] using OrdinaryForm.straight _
  | insertLeftUnit => exact .straight _
  | insertRightUnit => simpa only [Diagram.drawing, Word.directions, List.append_nil] using OrdinaryForm.straight _
  | associate => simpa only [Diagram.drawing, Word.directions, List.append_assoc] using OrdinaryForm.straight _
  | unassociate => simpa only [Diagram.drawing, Word.directions, List.append_assoc] using OrdinaryForm.straight _
  | vertical _ _ ix iy => exact ix.stack iy
  | horizontal _ _ ix iy => exact ix.juxtapose iy
  | zero => exact .zero _ _
  | add _ _ ix iy => exact .add ix iy
  | scale _ _ ix => exact .scale ix
  | _ => exact .vertex _ rfl

theorem encode_ordinary_geometry {R : Type v} {K H : Subgroup U} {p q : Word K H}
    (d : Diagram R p q) : PlanarCode.encode d.drawing.geometry = PlanarCode.encode d.drawing :=
  (ordinaryForm d).encode_geometry

end OrdinaryCode


def allowedEvent : PlanarEvent → Prop
  | .vertex _ kind => kind = .parallelUp ∨ kind = .mixedProjection
  | _ => False

def Allowed (code : PlanarCode.Code) : Prop :=
  ∀ e ∈ code, allowedEvent e

theorem allowedEvent_place (e : PlanarEvent) (n : Nat) :
    allowedEvent (e.place n) ↔ allowedEvent e := by
  cases e <;> rfl

theorem allowed_append {a b : PlanarCode.Code} :
    Allowed (a ++ b) ↔ Allowed a ∧ Allowed b := by
  simp only [Allowed, List.mem_append]
  constructor
  · intro h
    exact ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩
  · rintro ⟨ha, hb⟩ e (he | he)
    · exact ha e he
    · exact hb e he

theorem allowed_shift (n : Nat) {code : PlanarCode.Code} :
    Allowed (PlanarCode.shift n code) ↔ Allowed code := by
  constructor
  · intro h e he
    exact (allowedEvent_place _ _).mp (h _ (List.mem_map_of_mem he))
  · intro h e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact (allowedEvent_place _ _).mpr (h f hf)

theorem allowed_singleton (e : PlanarEvent) : Allowed [e] ↔ allowedEvent e := by
  simp [Allowed]

theorem Path.nil_iff {p q : Boundary K H} : Nonempty (Path p q []) ↔ p = q := by
  constructor
  · rintro ⟨path⟩
    cases path
    rfl
  · exact fun h => ⟨Path.empty h⟩

theorem ordinaryRaw {R : Type v} {K H : Subgroup U} {p q : Word K H} (d : Diagram R p q) :
    Allowed (PlanarCode.encode d.drawing) →
      Nonempty (Path p.boundary q.boundary (PlanarCode.encode d.drawing)) := by
  induction d with
  | id => exact fun _ => ⟨.nil _⟩
  | leftUnit p => exact fun _ => ⟨Path.empty (Word.boundary_leftUnit p)⟩
  | rightUnit p => exact fun _ => ⟨Path.empty (Word.boundary_rightUnit p)⟩
  | insertLeftUnit p => exact fun _ => ⟨Path.empty (Word.boundary_leftUnit p).symm⟩
  | insertRightUnit p => exact fun _ => ⟨Path.empty (Word.boundary_rightUnit p).symm⟩
  | associate p q r => exact fun _ => ⟨Path.empty (Word.boundary_associate p q r)⟩
  | unassociate p q r => exact fun _ => ⟨Path.empty (Word.boundary_associate p q r).symm⟩
  | mixedProjection a b l r dot finite =>
    exact fun _ => ⟨.cons (Crossing.edge (.mixedProjection a b l r ⟨dot, finite⟩)) (.nil _)⟩
  | vertical d e ihd ihe =>
    simp only [Diagram.drawing, encode_stack, allowed_append]
    rintro ⟨hd, he⟩
    obtain ⟨p⟩ := ihd hd
    obtain ⟨q⟩ := ihe he
    exact ⟨p.append q⟩
  | horizontal d e ihd ihe =>
    simp only [Diagram.drawing, encode_juxtapose, allowed_append, allowed_shift]
    rintro ⟨hd, he⟩
    obtain ⟨p⟩ := ihd hd
    obtain ⟨q⟩ := ihe he
    simpa only [Word.boundary, width_boundary, (ordinaryForm d).outputs] using Nonempty.intro (p.horizontal q)
  | _ =>
    simp [Diagram.drawing, PlanarCode.encode, VertexKind.canonical, allowed_singleton, allowedEvent]

/-- Extract a typed path through the actual geometric code of an ordinary diagram. -/
theorem ordinary {R : Type v} {K H : Subgroup U} {p q : Word K H} (d : Diagram R p q)
    (h : Allowed (PlanarCode.encode d.drawing.geometry)) :
    Nonempty (Path p.boundary q.boundary (PlanarCode.encode d.drawing.geometry)) := by
  rw [encode_ordinary_geometry] at h ⊢
  exact ordinaryRaw d h

/-- An empty compact label still contributes a visible mixed projection. -/
theorem emptyCompact_code {R : Type v} [CommSemiring R] {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) :
    PlanarCode.encode (LabelledDrawing.compactProjection (R := R) a b l r []).erase.geometry =
      [.vertex 0 .mixedProjection] := rfl

theorem emptyCompact_eval {R : Type v} [CommSemiring R] {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) :
    (LabelledDrawing.compactProjection (R := R) a b l r []).interpret.eval.toLinearMap = 0 := by
  apply LinearMap.ext
  intro x
  rfl

end MackeyDiagrams.CaseOneTrace

#print axioms MackeyDiagrams.CaseOneTrace.Path.horizontal
#print axioms MackeyDiagrams.CaseOneTrace.ordinary
#print axioms MackeyDiagrams.CaseOneTrace.emptyCompact_eval
