import MackeyDiagrams.PlanarShape
import MackeyDiagrams.HorizontalComposition

namespace MackeyDiagrams.CaseOneLocal
universe u v
variable {U : Type u} [Group U]
variable {R : Type v} [CommSemiring R]
variable {K H J : Subgroup U}

open DrawingShape PlanarCode

private theorem shift_append (n : Nat) (a b : Code) :
    shift n (a ++ b) = shift n a ++ shift n b := by simp [shift]

private theorem shift_shift (n m : Nat) (a : Code) :
    shift n (shift m a) = shift (n + m) a := by
  induction a with
  | nil => rfl
  | cons e es ih =>
    change (e.place (m + e.position)).place
      (n + (e.place (m + e.position)).position) ::
        shift n (shift m es) = e.place (n + m + e.position) :: shift (n + m) es
    rw [ih]
    cases e <;> simp [PlanarEvent.place, PlanarEvent.position, Nat.add_assoc]

private theorem encode_stack (a b : DrawingShape) :
    encode (a.stack b) = encode a ++ encode b := by
  induction a generalizing b <;> cases b <;>
    simp [stack, encode, *, List.append_assoc]

private theorem outputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).outputs = a.outputs ++ b.outputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.outputs, List.nil_append, List.append_nil, *, List.append_assoc]

@[simp] private theorem shift_nil (n : Nat) : shift n [] = [] := rfl

@[simp] private theorem shift_zero (xs : Code) : shift 0 xs = xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    change e.place (0 + e.position) :: shift 0 es = e :: es
    rw [Nat.zero_add, ih]
    cases e <;> rfl

private theorem encode_juxtapose (a b : DrawingShape) :
    encode (a.juxtapose b) = encode a ++ shift a.outputs.length (encode b) := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [encode, DrawingShape.outputs, List.length_nil, List.length_append,
      List.nil_append, List.append_nil, shift_nil, shift_zero, shift_append, shift_shift, List.append_assoc, *]

private def geomCode (s : DrawingShape) := encode s.geometry

private theorem geomCode_stack (a b : DrawingShape) :
    geomCode (a.stack b) = geomCode a ++ geomCode b := by
  fun_induction DrawingShape.stack <;>
    simp only [geomCode, DrawingShape.geometry, encode, encode_stack, List.nil_append,
      List.append_nil, List.append_assoc] at *
  simp only [*]

private theorem geomOutputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).geometry.outputs = a.geometry.outputs ++ b.geometry.outputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.geometry, outputs_juxtapose, DrawingShape.outputs,
      List.nil_append, List.append_nil, List.append_assoc] at *
  simp only [*]

private theorem geomCode_juxtapose (a b : DrawingShape) :
    geomCode (a.juxtapose b) = geomCode a ++ shift a.geometry.outputs.length (geomCode b) := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [geomCode, DrawingShape.geometry, encode_juxtapose, outputs_juxtapose, encode,
      DrawingShape.outputs, List.length_nil, List.length_append,
      shift_zero, shift_nil, List.nil_append, List.append_nil,
      List.append_assoc] at *
  rename_i ih
  rw [ih, shift_append, shift_shift]

private theorem stack_assoc (a b c : DrawingShape) :
    (a.stack b).stack c = a.stack (b.stack c) := by
  induction a generalizing b c <;> cases b <;> cases c <;> simp [stack, *]

private theorem inputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).inputs = a.inputs ++ b.inputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.inputs, List.nil_append, List.append_nil, *, List.append_assoc]

private theorem geomInputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).geometry.inputs = a.geometry.inputs ++ b.geometry.inputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.geometry, inputs_juxtapose, DrawingShape.inputs,
      List.nil_append, List.append_nil, List.append_assoc] at *
  simp only [*]

private theorem inputs_stack (a b : DrawingShape) (h : a.outputs = b.inputs) :
    (a.stack b).inputs = a.inputs := by
  fun_induction DrawingShape.stack <;> simp_all [DrawingShape.inputs, DrawingShape.outputs]

private theorem outputs_stack (a b : DrawingShape) (h : a.outputs = b.inputs) :
    (a.stack b).outputs = b.outputs := by
  fun_induction DrawingShape.stack <;> simp_all [DrawingShape.inputs, DrawingShape.outputs]

private def VFit : DrawingShape → Prop
  | .vertical first rest => VFit rest ∧ first.geometry.outputs = rest.geometry.inputs
  | _ => True

private theorem geom_stack (a b : DrawingShape) (ha : VFit a)
    (h : a.geometry.outputs = b.geometry.inputs) :
    (a.stack b).geometry = a.geometry.stack b.geometry := by
  fun_induction DrawingShape.stack
  · simp [geometry, stack]
  · rename_i below ds _
    simp only [geometry, DrawingShape.inputs] at h ⊢
    cases hg : below.geometry <;> try rfl
    exact congrArg DrawingShape.straight (by simpa only [hg, DrawingShape.outputs] using h)
  · rename_i first rest above _ ih
    change VFit rest ∧ first.geometry.outputs = rest.geometry.inputs at ha
    simp only [DrawingShape.geometry, outputs_stack _ _ ha.2] at h
    simp only [DrawingShape.geometry, ih ha.1 h, stack_assoc]
  · rfl

private theorem vfit_stack (a b : DrawingShape) (ha : VFit a) (hb : VFit b)
    (h : a.geometry.outputs = b.geometry.inputs) : VFit (a.stack b) := by
  fun_induction DrawingShape.stack
  · exact hb
  · exact ha
  · rename_i first rest above _ ih
    change VFit rest ∧ first.geometry.outputs = rest.geometry.inputs at ha
    simp only [DrawingShape.geometry, outputs_stack _ _ ha.2] at h
    exact ⟨ih ha.1 hb h, by rw [geom_stack _ _ ha.1 h, inputs_stack _ _ h]; exact ha.2⟩
  · exact ⟨hb, h⟩

private theorem vfit_juxtapose (a b : DrawingShape) (ha : VFit a) (hb : VFit b) :
    VFit (a.juxtapose b) := by
  fun_induction DrawingShape.juxtapose <;> first | exact ha | exact hb | trivial

private def Boundary.strands : {A B : Subgroup U} → Boundary A B → Nat
  | _, _, .empty _ => 0
  | _, _, .cons _ p => 1 + Boundary.strands p

private theorem strands_append {A B C : Subgroup U} (p : Boundary A B) (q : Boundary B C) :
    Boundary.strands (p.append q) = Boundary.strands p + Boundary.strands q := by
  induction p with
  | empty => simp [Boundary.strands, Boundary.append]
  | cons s p ih => simp [Boundary.strands, Boundary.append, ih, Nat.add_assoc]

private theorem strands_boundary {A B : Subgroup U} (p : Word A B) :
    Boundary.strands p.boundary = p.directions.length := by
  induction p with
  | empty | up | down => rfl
  | tensor p q ih₁ ih₂ => simp [Word.boundary, Word.directions, strands_append, ih₁, ih₂]

private inductive Crossing : {A B : Subgroup U} → VertexKind → Boundary A B → Boundary A B → Prop
  | parallelUp {A B C D : Subgroup U}
      (b : ConjEmbedding C A) (a : ConjEmbedding B C)
      (b' : ConjEmbedding D A) (a' : ConjEmbedding B D) :
      Crossing .parallelUp (Word.tensor (.up b) (.up a)).boundary
        (Word.tensor (.up b') (.up a')).boundary
  | mixedProjection {A B C D : Subgroup U}
      (a : ConjEmbedding A C) (b : ConjEmbedding B C)
      (l : ConjEmbedding D A) (r : ConjEmbedding D B)
      (term : ProjectionDot.Mixed a b l r) :
      Crossing .mixedProjection (Word.tensor (.down a) (.up b)).boundary
        (Word.tensor (.up l) (.down r)).boundary

private inductive Edge : PlanarEvent → Boundary K H → Boundary K H → Prop
  | padded {A B : Subgroup U} {p q : Boundary A B} {kind : VertexKind}
      (pre : Boundary K A) (suffix : Boundary B H) (c : Crossing kind p q) :
      Edge (.vertex (Boundary.strands pre) kind)
        (pre.append (p.append suffix)) (pre.append (q.append suffix))

private inductive Trace : Code → Boundary K H → Boundary K H → Prop
  | nil (p : Boundary K H) : Trace [] p p
  | cons {e : PlanarEvent} {es : Code} {p q r : Boundary K H}
      (edge : Edge e p q) (tail : Trace es q r) : Trace (e :: es) p r

private theorem Trace.append {p q r : Boundary K H} {xs ys : Code}
    (hx : Trace xs p q) (hy : Trace ys q r) : Trace (xs ++ ys) p r := by
  induction hx with
  | nil => exact hy
  | cons edge _ ih => exact .cons edge (ih hy)

private theorem Edge.padLeft {e : PlanarEvent} {p q : Boundary H J}
    (h : Edge e p q) (pre : Boundary K H) :
    Edge (e.place (Boundary.strands pre + e.position)) (pre.append p) (pre.append q) := by
  cases h with
  | padded inner suffix c =>
    simpa only [strands_append, Boundary.append_assoc, PlanarEvent.place, PlanarEvent.position]
      using (Edge.padded (pre.append inner) suffix c)

private theorem Edge.padRight {e : PlanarEvent} {p q : Boundary K H}
    (h : Edge e p q) (suffix : Boundary H J) :
    Edge e (p.append suffix) (q.append suffix) := by
  cases h with
  | padded pre inner c =>
    simpa only [Boundary.append_assoc] using (Edge.padded pre (inner.append suffix) c)

private theorem Trace.padLeft {p q : Boundary H J} {xs : Code}
    (h : Trace xs p q) (pre : Boundary K H) :
    Trace (shift (Boundary.strands pre) xs) (pre.append p) (pre.append q) := by
  induction h with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (edge.padLeft pre) ih

private theorem Trace.padRight {p q : Boundary K H} {xs : Code}
    (h : Trace xs p q) (suffix : Boundary H J) :
    Trace xs (p.append suffix) (q.append suffix) := by
  induction h with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (edge.padRight suffix) ih

private theorem Trace.one {p q : Boundary K H} {kind : VertexKind} (c : Crossing kind p q) :
    Trace [.vertex 0 kind] p q := by
  have h := Edge.padded (.empty K) (.empty H) c
  rw [Boundary.append, Boundary.append_empty, Boundary.append, Boundary.append_empty] at h
  exact .cons h (.nil _)

private def AllowedEvent : PlanarEvent → Prop
  | .vertex _ k => k = .parallelUp ∨ k = .mixedProjection
  | _ => False

private def Allowed (xs : Code) : Prop := ∀ e ∈ xs, AllowedEvent e

private theorem allowed_append (a b : Code) : Allowed (a ++ b) ↔ Allowed a ∧ Allowed b := by
  simp only [Allowed, List.mem_append, or_imp, forall_and]

private theorem allowed_shift (n : Nat) (xs : Code) : Allowed (shift n xs) ↔ Allowed xs := by
  constructor
  · intro h e he
    have hh := h (e.place (n + e.position)) (List.mem_map_of_mem he)
    cases e <;> exact hh
  · intro h e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    have hh := h f hf
    cases f <;> exact hh

private theorem allowed_single (e : PlanarEvent) : Allowed [e] ↔ AllowedEvent e := by
  simp [Allowed]

private theorem allowed_cons (e : PlanarEvent) (es : Code) :
    Allowed (e :: es) ↔ AllowedEvent e ∧ Allowed es := by
  simp only [Allowed, List.mem_cons, or_imp, forall_and, forall_eq]

private theorem allowed_equivalent {xs ys : Code} (h : Equivalent xs ys) :
    Allowed xs ↔ Allowed ys := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | context _ _ _ ih => simp only [allowed_append, ih]
  | exchange before after i gap l r =>
    have hp (e : PlanarEvent) (n : Nat) : AllowedEvent (e.place n) ↔ AllowedEvent e := by
      cases e <;> rfl
    simp only [allowed_append, allowed_cons, hp]
    tauto
  | add | scale => simp [allowed_single, AllowedEvent]

private theorem horizontal_zero_left {X X' : Biset K H} {Y Y' : Biset H J}
    (f : Biset.Hom R X X') (g : Biset.Hom R Y Y') (hf : f.toLinearMap = 0) :
    (f.horizontal g).toLinearMap = 0 := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change (f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r) = _
  simp [Biset.Hom.horizontal_single, hf]

private theorem horizontal_zero_right {X X' : Biset K H} {Y Y' : Biset H J}
    (f : Biset.Hom R X X') (g : Biset.Hom R Y Y') (hg : g.toLinearMap = 0) :
    (f.horizontal g).toLinearMap = 0 := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change (f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r) = _
  simp [Biset.Hom.horizontal_single, hg]

private theorem compact_empty {A B C D : Subgroup U}
    (a : ConjEmbedding A C) (b : ConjEmbedding B C)
    (l : ConjEmbedding D A) (r : ConjEmbedding D B) :
    (LabelledDrawing.compactProjection (R := R) a b l r []).interpret.eval.toLinearMap = 0 :=
  rfl

private theorem vertical_nonzero {X Y Z : Biset K H}
    (f : Biset.Hom R X Y) (g : Biset.Hom R Y Z)
    (h : (f.vertical g).toLinearMap ≠ 0) : f.toLinearMap ≠ 0 ∧ g.toLinearMap ≠ 0 := by
  change g.toLinearMap.comp f.toLinearMap ≠ 0 at h
  exact ⟨fun hf => h (by simp only [hf, LinearMap.comp_zero]),
    fun hg => h (by simp only [hg, LinearMap.zero_comp])⟩

private def Traced (s : DrawingShape) (p q : Word K H) : Prop :=
  VFit s ∧ s.geometry.inputs = p.directions ∧ s.geometry.outputs = q.directions ∧
    Trace (geomCode s) p.boundary q.boundary

private theorem traced_straight {p q : Word K H} {ds : List Bool}
    (hi : ds = p.directions) (ho : ds = q.directions) (hpq : p.boundary = q.boundary) :
    Traced (.straight ds) p q := by
  refine ⟨trivial, hi, ho, ?_⟩
  change Trace [] p.boundary q.boundary
  rw [hpq]
  exact .nil _

private theorem traced_stack {a b : DrawingShape} {p q r : Word K H}
    (ha : Traced a p q) (hb : Traced b q r) : Traced (a.stack b) p r := by
  obtain ⟨av, ai, ao, ap⟩ := ha
  obtain ⟨bv, bi, bo, bp⟩ := hb
  have link := ao.trans bi.symm
  exact ⟨vfit_stack _ _ av bv link, by rw [geom_stack _ _ av link, inputs_stack _ _ link, ai],
    by rw [geom_stack _ _ av link, outputs_stack _ _ link, bo],
    by rw [geomCode_stack]; exact ap.append bp⟩

private theorem traced_juxtapose {a b : DrawingShape} {p p' : Word K H} {q q' : Word H J}
    (ha : Traced a p p') (hb : Traced b q q') : Traced (a.juxtapose b) (p.tensor q) (p'.tensor q') := by
  obtain ⟨av, ai, ao, ap⟩ := ha
  obtain ⟨bv, bi, bo, bp⟩ := hb
  refine ⟨vfit_juxtapose _ _ av bv, by rw [geomInputs_juxtapose, ai, bi]; rfl,
    by rw [geomOutputs_juxtapose, ao, bo]; rfl, ?_⟩
  rw [geomCode_juxtapose, ao, ← strands_boundary]
  exact (ap.padRight q.boundary).append (bp.padLeft p'.boundary)

private theorem ordinary_trace {p q : Word K H} (d : Diagram R p q)
    (hc : Allowed (geomCode d.drawing)) (hn : d.eval.toLinearMap ≠ 0) :
    Traced d.drawing p q := by
  induction d with
  | id p => exact traced_straight rfl rfl rfl
  | leftUnit p => exact traced_straight rfl rfl rfl
  | insertLeftUnit p => exact traced_straight rfl rfl rfl
  | rightUnit p => exact traced_straight (List.append_nil _).symm rfl (Word.boundary_rightUnit p)
  | insertRightUnit p => exact traced_straight rfl (List.append_nil _).symm (Word.boundary_rightUnit p).symm
  | associate p q r =>
    exact traced_straight rfl (List.append_assoc _ _ _) (Word.boundary_associate p q r)
  | unassociate p q r =>
    exact traced_straight (List.append_assoc _ _ _) rfl (Word.boundary_associate p q r).symm
  | mixedProjection a b l r d fin =>
    exact ⟨trivial, rfl, rfl, Trace.one (.mixedProjection a b l r ⟨d, fin⟩)⟩
  | vertical a b ia ib =>
    have hz := vertical_nonzero a.eval b.eval hn
    have hab : Allowed (geomCode a.drawing ++ geomCode b.drawing) := by
      simpa only [Diagram.drawing, geomCode_stack] using hc
    have ⟨ha, hb⟩ := (allowed_append _ _).mp hab
    exact traced_stack (ia ha hz.1) (ib hb hz.2)
  | horizontal a b ia ib =>
    have hab := hc
    simp only [Diagram.drawing, geomCode_juxtapose, allowed_append, allowed_shift] at hab
    exact traced_juxtapose (ia hab.1 (fun hf => hn (horizontal_zero_left a.eval b.eval hf)))
      (ib hab.2 (fun hg => hn (horizontal_zero_right a.eval b.eval hg)))
  | _ =>
    exfalso
    simp only [Diagram.drawing, geomCode, geometry, encode, allowed_single, AllowedEvent,
      VertexKind.canonical, reduceCtorEq, or_self] at hc

private theorem projectionGeometry_forbidden (n : Nat)
    (opening : ProjectionOpening) (closing : ProjectionClosing) :
    ¬ Allowed (encode (expandedProjectionGeometry n opening closing)) := by
  unfold expandedProjectionGeometry
  cases opening <;>
    simp [encode_stack, allowed_append, allowed_shift, encode,
      allowed_single, AllowedEvent, VertexKind.canonical]

private theorem labelled_trace {p q : Word K H} (d : LabelledDrawing R p q)
    (hc : Allowed (geomCode d.erase)) (hn : d.interpret.eval.toLinearMap ≠ 0) :
    Traced d.erase p q := by
  induction d with
  | ordinary d => exact ordinary_trace d hc hn
  | parallelUp b a b' a' labels =>
    exact ⟨trivial, rfl, rfl, Trace.one (.parallelUp b a b' a')⟩
  | compactProjection a b l r labels =>
    cases labels with
    | nil => exact (hn (compact_empty a b l r)).elim
    | cons term rest =>
      exact ⟨trivial, rfl, rfl, Trace.one (.mixedProjection a b l r term.2)⟩
  | vertical a b ia ib =>
    have hz := vertical_nonzero a.interpret.eval b.interpret.eval hn
    have hab := hc
    simp only [LabelledDrawing.erase, geomCode_stack, allowed_append] at hab
    exact traced_stack (ia hab.1 hz.1) (ib hab.2 hz.2)
  | horizontal a b ia ib =>
    have hab := hc
    simp only [LabelledDrawing.erase, geomCode_juxtapose, allowed_append, allowed_shift] at hab
    exact traced_juxtapose
      (ia hab.1 (fun hf => hn (horizontal_zero_left a.interpret.eval b.interpret.eval hf)))
      (ib hab.2 (fun hg => hn (horizontal_zero_right a.interpret.eval b.interpret.eval hg)))
  | expandedProjection a b l r marks opening closing =>
    exact (projectionGeometry_forbidden 1 opening closing hc).elim
  | expandedProjectionChain a b l r chain fin opening closing =>
    exact (projectionGeometry_forbidden chain.length opening closing hc).elim
  | expandedLinearDotProjection a b l r chain fin opening closing =>
    exact (projectionGeometry_forbidden chain.length opening closing hc).elim
  | bentVertex b =>
    exfalso
    cases b <;> simp [LabelledDrawing.erase, BentVertex.kind, geomCode, geometry, encode,
      allowed_single, AllowedEvent, VertexKind.canonical] at hc
  | _ =>
    exfalso
    simp [LabelledDrawing.erase, geomCode, geometry, rightCurlGeometry, encode_stack,
      encode, allowed_append, allowed_cons, AllowedEvent,
      VertexKind.canonical] at hc

private theorem atBoundary_zero {p q : Word K H} (d : ScopedDiagram R p q)
    (h : d.eval.toLinearMap = 0) : d.atBoundary.eval.toLinearMap = 0 := by
  unfold ScopedDiagram.atBoundary
  change (q.reorderToBoundary.eval.toLinearMap.comp
    (d.eval.toLinearMap.comp p.reorderFromBoundary.eval.toLinearMap)) = 0
  simp only [h, LinearMap.zero_comp, LinearMap.comp_zero]

private theorem planarAtBoundary_trace {p q : Boundary K H} {s : PlanarShape} {template : Code}
    (d : LabelledDrawing.PlanarAtBoundary R p q s)
    (hcode : s.wiring = Quotient.mk PlanarCode.setoid template)
    (hc : Allowed template) (hn : d.interpret.eval.toLinearMap ≠ 0) :
    ∃ xs : Code, Equivalent xs template ∧ Trace xs p q := by
  rcases d with ⟨bottom, top, diagram, rfl, rfl, shape_eq⟩
  have he : Equivalent (geomCode diagram.erase) template :=
    Quotient.exact ((congrArg PlanarShape.wiring shape_eq).trans hcode)
  have ha := (allowed_equivalent he).mpr hc
  have ht := labelled_trace diagram ha (fun h => hn (atBoundary_zero diagram.interpret h))
  exact ⟨_, he, ht.2.2.2⟩


/-- At most three wires are live, so two allowed crossings cannot be disjoint. -/
private def OnThree (xs : Code) : Prop :=
  ∀ e ∈ xs, AllowedEvent e ∧ e.position < 2

private theorem place_allowedEvent (e : PlanarEvent) (i : Nat) :
    AllowedEvent (e.place i) ↔ AllowedEvent e := by cases e <;> rfl

private theorem place_position (e : PlanarEvent) (i : Nat) : (e.place i).position = i := by
  cases e <;> rfl

private theorem allowed_widths (e : PlanarEvent) (h : AllowedEvent e) :
    e.inputs.length = 2 ∧ e.outputs.length = 2 := by
  cases e with
  | vertex i k =>
    rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩
  | zero | add | scale => exact h.elim

private theorem onThree_forbidden (pre post : Code) (e : PlanarEvent)
    (hf : ¬ AllowedEvent e) : ¬ OnThree (pre ++ [e] ++ post) :=
  fun h => hf (h e (by simp)).1

private theorem equivalent_eq_onThree {xs ys : Code} (h : Equivalent xs ys) :
    ∀ pre post : Code,
      (OnThree (pre ++ xs ++ post) → (pre ++ xs ++ post) = (pre ++ ys ++ post)) ∧
      (OnThree (pre ++ ys ++ post) → (pre ++ ys ++ post) = (pre ++ xs ++ post)) := by
  induction h with
  | refl => exact fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact fun pre post => ⟨(ih pre post).2, (ih pre post).1⟩
  | trans _ _ ih₁ ih₂ =>
    intro pre post
    constructor
    · intro ha
      have h₁ := (ih₁ pre post).1 ha
      exact h₁.trans ((ih₂ pre post).1 (h₁ ▸ ha))
    · intro hc
      have h₂ := (ih₂ pre post).2 hc
      exact h₂.trans ((ih₁ pre post).2 (h₂ ▸ hc))
  | context bef aft _ ih =>
    intro pre post
    simpa only [List.append_assoc] using ih (pre ++ bef) (aft ++ post)
  | exchange bef aft i gap l r =>
    intro pre post
    constructor
    · intro h
      have hl := (h (l.place i) (by simp)).1
      have hr := (h (r.place (i + l.outputs.length + gap)) (by simp)).2
      rw [place_position, (allowed_widths l ((place_allowedEvent l i).1 hl)).2] at hr
      omega
    · intro h
      have hl := (h (l.place i) (by simp)).1
      have hr := (h (r.place (i + l.inputs.length + gap)) (by simp)).2
      rw [place_position, (allowed_widths l ((place_allowedEvent l i).1 hl)).1] at hr
      omega
  | @scale i below above a b _ _ =>
    intro pre post
    exact ⟨fun h => (onThree_forbidden pre post (.scale i below above a) (fun he => he) h).elim,
      fun h => (onThree_forbidden pre post (.scale i below above b) (fun he => he) h).elim⟩
  | @add i below above a b c d _ _ _ _ =>
    intro pre post
    exact ⟨fun h => (onThree_forbidden pre post (.add i below above a c) (fun he => he) h).elim,
      fun h => (onThree_forbidden pre post (.add i below above b d) (fun he => he) h).elim⟩

private def rightCode : Code :=
  [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]

private theorem rightCode_onThree : OnThree rightCode := by
  intro e h
  simp only [rightCode, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [AllowedEvent, PlanarEvent.position]

private theorem rightFiber_trace {p q : Boundary K H} {s : PlanarShape}
    (d : LabelledDrawing.PlanarAtBoundary R p q s)
    (hcode : s.wiring = Quotient.mk PlanarCode.setoid rightCode)
    (hn : d.interpret.eval.toLinearMap ≠ 0) : Trace rightCode p q := by
  obtain ⟨xs, he, ht⟩ := planarAtBoundary_trace d hcode (fun e he => (rightCode_onThree e he).1) hn
  have hh := (equivalent_eq_onThree he [] []).2
  simp only [List.nil_append, List.append_nil] at hh
  rw [hh rightCode_onThree]
  exact ht

private theorem rightTemplate_code {A C D E F G : Subgroup U}
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F) :
    let bc := b.comp c
    let ad := a.comp d
    let j := ConjEmbedding.id A
    let drawId := fun {K H : Subgroup U} (p : Word K H) =>
      LabelledDrawing.ordinary (Diagram.id (R := R) p)
    let atRight := fun {K H J L J' : Subgroup U} (p : Word K H)
        {q : Word H J} {r : Word J L} {q' : Word H J'} {r' : Word J' L}
        (crossing : LabelledDrawing R (q.tensor r) (q'.tensor r')) =>
      LabelledDrawing.vertical (LabelledDrawing.ordinary (Diagram.associate p q r))
        (LabelledDrawing.vertical (LabelledDrawing.horizontal (drawId p) crossing)
          (LabelledDrawing.ordinary (Diagram.unassociate p q' r')))
    let rightTemplate :=
      LabelledDrawing.vertical
        (atRight (Word.down a) (LabelledDrawing.parallelUp b c j bc []))
        (LabelledDrawing.vertical
          (LabelledDrawing.horizontal
            (LabelledDrawing.compactProjection a j d ad []) (drawId (Word.up bc)))
          (atRight (Word.up d) (LabelledDrawing.compactProjection ad bc e f [])))
    rightTemplate.planarShape.wiring = Quotient.mk PlanarCode.setoid rightCode := rfl

#print axioms planarAtBoundary_trace
#print axioms rightFiber_trace
#print axioms rightTemplate_code

end MackeyDiagrams.CaseOneLocal
