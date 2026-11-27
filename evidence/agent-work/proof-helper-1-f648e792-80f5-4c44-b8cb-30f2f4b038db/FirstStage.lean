import Proofs.DotSlidePreorderNotSymmetric
import Batteries.Tactic.OpenPrivate

namespace CaseTwoFirstStage

open MackeyDiagrams Biset.Hom
set_option linter.unusedSimpArgs false
open private DotSlidePreorderProof.code diagram_code_vert diagram_code_horiz drawing_code_vert
  drawing_code_horiz boundaryDirections boundaryDirections_word
  Wire Wire.eval Wire.directions
  Framed Framed.self Framed.boundaries Framed.canonical Framed.vertLeft
  Framed.vertRight Framed.horizontal Framed.trans frameStraight stripLeft stripRight
  splitSingleton shiftEmpty shift_zero encode_stack from Proofs.DotSlidePreorderNotSymmetric

universe u
variable {U : Type u} [Group U] {K H J P : Subgroup U}

private theorem coherence : DotSlidePreorderProof.EmptyCodeCoherence U :=
  fun d h => DotSlidePreorderProof.empty_geometry_atBoundary d h

private abbrev inputPair (a : ConjEmbedding K P) (b : ConjEmbedding H P) :=
  (Word.down a).tensor (.up b)

private abbrev outputPair (r : ConjEmbedding P K) (s : ConjEmbedding P H) :=
  (Word.up r).tensor (.down s)

private def cross (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    {B : Subgroup U} (r : ConjEmbedding B K) (s : ConjEmbedding B H)
    (ts : List (Complex × ProjectionDot.Mixed a b r s)) :=
  LabelledDrawing.compactProjection a b r s ts

private def straight (p : Word K H) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private inductive Core : {K H : Subgroup U} → Word K H → Word K H → Type u
  | atom {K H P B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P) (r : ConjEmbedding B K) (s : ConjEmbedding B H)
      (ts : List (Complex × ProjectionDot.Mixed a b r s)) :
      Core (inputPair a b) (outputPair r s)
  | tail {K H J P B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P) (r : ConjEmbedding B K) (s : ConjEmbedding B H)
      (ts : List (Complex × ProjectionDot.Mixed a b r s)) (t : Strand H J) :
      Core ((inputPair a b).tensor t.word) ((outputPair r s).tensor t.word)

private def Core.drawing {p q : Word K H} : Core p q → LabelledDrawing Complex p q
  | .atom a b r s ts => cross a b r s ts
  | .tail a b r s ts t => (cross a b r s ts).horizontal (straight t.word)

private theorem Core.width {p q : Word K H} (d : Core p q) :
    2 ≤ p.directions.length := by
  cases d with
  | atom => exact Nat.le_refl 2
  | tail _ _ _ _ _ t => cases t <;> exact Nat.le_succ 2

private inductive Short : {K H : Subgroup U} → Word K H → Type u
  | empty (K : Subgroup U) : Short (.empty K)
  | one {K H : Subgroup U} (s : Strand K H) : Short s.word

private theorem shortBoundary (p : Boundary K H) (h : (boundaryDirections p).length ≤ 1) :
    ∃ q : Word K H, Nonempty (Short q) ∧ p = q.boundary := by
  cases p with
  | empty => exact ⟨_, ⟨.empty _⟩, rfl⟩
  | cons s t =>
    cases t with
    | empty =>
      cases s with
      | up a => exact ⟨.up a, ⟨.one (.up a)⟩, rfl⟩
      | down a => exact ⟨.down a, ⟨.one (.down a)⟩, rfl⟩
    | cons s' t => cases s <;> cases s' <;> simp [boundaryDirections] at h

private theorem emptyBoundary (p : Boundary K H) (h : (boundaryDirections p).length = 0) :
    ∃ e : K = H, p = e ▸ Boundary.empty K := by
  cases p with
  | empty => exact ⟨rfl, rfl⟩
  | cons s t => cases s <;> simp [boundaryDirections] at h

private def Normal {p q : Word K H} (f : Biset.Hom Complex p.basis q.basis) : Prop :=
  ∃ (p' q' : Word K H) (x : Core p' q'),
    Framed (p := p) (q := q) f x.drawing.interpret.eval

private theorem Core.withTail {p q : Word K H} (d : Core p q) {t : Word H J}
    (s : Short t) (hw : (p.directions ++ t.directions).length ≤ 3) :
    Normal (p := p.tensor t) (q := q.tensor t)
      (d.drawing.interpret.eval.horizontal (Biset.Hom.id t.basis)) := by
  cases s with
  | empty => exact ⟨_, _, d, stripRight _⟩
  | one t =>
    cases d with
    | atom a b r s ts => exact ⟨_, _, .tail a b r s ts t, Framed.self _⟩
    | tail a b r s ts z => cases z <;> cases t <;> simp [Strand.word, Word.directions] at hw

private theorem normalTail {p q : Word K H} {r s : Word H J}
    {f : Biset.Hom Complex p.basis q.basis} (hn : Normal (p := p) (q := q) f)
    (w : Wire r s) (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor s) (f.horizontal (Wire.eval w)) := by
  obtain ⟨p', q', d, hd⟩ := hn
  have hp : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using
      congrArg boundaryDirections (Framed.boundaries coherence hd).1
  rw [hp, List.length_append] at hw
  have hr : r.directions.length ≤ 1 := by have := d.width; omega
  obtain ⟨t, ⟨st⟩, ht⟩ := shortBoundary r.boundary (by rwa [boundaryDirections_word])
  have ht' : r.directions = t.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections ht
  obtain ⟨x, y, z, hz⟩ := d.withTail st (by rw [List.length_append, ← ht']; exact hw)
  exact ⟨x, y, z, Framed.trans (Framed.horizontal hd (frameStraight coherence w ht)) hz⟩

private theorem normalPrefix {p q : Word K H} {r s : Word H J}
    (w : Wire p q) (hw : q.directions.length = 0)
    {f : Biset.Hom Complex r.basis s.basis} (hn : Normal (p := r) (q := s) f) :
    Normal (p := p.tensor r) (q := q.tensor s) ((Wire.eval w).horizontal f) := by
  have hp : p.directions.length = 0 := by rwa [Wire.directions coherence w]
  obtain ⟨e, he⟩ := emptyBoundary p.boundary (by rwa [boundaryDirections_word])
  subst H
  obtain ⟨x, y, z, hz⟩ := hn
  have hi := frameStraight coherence (r := Word.empty K) w he
  exact ⟨x, y, z, Framed.trans (Framed.horizontal hi hz) (stripLeft _)⟩

private abbrev mark : PlanarEvent := .vertex 0 .mixedProjection

private theorem splitShift {n : Nat} {c : PlanarCode.Code} (h : PlanarCode.shift n c = [mark]) :
    n = 0 ∧ c = [mark] := by
  cases c with
  | nil => simp [PlanarCode.shift] at h
  | cons e es =>
    have hpos := congrArg PlanarEvent.position (List.cons.inj h).1
    have placePos : (e.place (n + e.position)).position = n + e.position := by
      cases e <;> rfl
    change (e.place (n + e.position)).position = 0 at hpos
    rw [placePos] at hpos
    have hn : n = 0 := by omega
    subst n
    exact ⟨rfl, (shift_zero _).symm.trans h⟩

private theorem verticalStep {p q t : Word K H}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q t)
    (h : DotSlidePreorderProof.code d.erase ++ DotSlidePreorderProof.code e.erase = [mark]) (hw : p.directions.length ≤ 3)
    (hd : DotSlidePreorderProof.code d.erase = [mark] → p.directions.length ≤ 3 → Normal (p := p) (q := q) d.interpret.eval)
    (he : DotSlidePreorderProof.code e.erase = [mark] → q.directions.length ≤ 3 → Normal (p := q) (q := t) e.interpret.eval) :
    Normal (p := p) (q := t) (d.vertical e).interpret.eval := by
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · let w : Wire p q := ⟨d, hd0⟩
    obtain ⟨x, y, z, hz⟩ := he he1 (by rwa [← Wire.directions coherence w])
    exact ⟨x, y, z, Framed.vertLeft w hz⟩
  · obtain ⟨x, y, z, hz⟩ := hd hd1 hw
    exact ⟨x, y, z, Framed.vertRight ⟨e, he0⟩ hz⟩

private theorem horizontalStep {p q : Word K H} {r s : Word H J}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex r s)
    (h : DotSlidePreorderProof.code d.erase ++ PlanarCode.shift q.directions.length (DotSlidePreorderProof.code e.erase) = [mark])
    (hw : (p.directions ++ r.directions).length ≤ 3)
    (hd : DotSlidePreorderProof.code d.erase = [mark] → p.directions.length ≤ 3 → Normal (p := p) (q := q) d.interpret.eval)
    (he : DotSlidePreorderProof.code e.erase = [mark] → r.directions.length ≤ 3 → Normal (p := r) (q := s) e.interpret.eval) :
    Normal (p := p.tensor r) (q := q.tensor s) (d.horizontal e).interpret.eval := by
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · obtain ⟨hz, he1⟩ := splitShift he1
    exact normalPrefix ⟨d, hd0⟩ hz (he he1 (by rw [List.length_append] at hw; omega))
  · exact normalTail (hd hd1 (by rw [List.length_append] at hw; omega)) ⟨e, shiftEmpty he0⟩ hw

private theorem eval_atom {B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (r : ConjEmbedding B K) (s : ConjEmbedding B H)
    (d : Dot (a.comp r) (b.comp s))
    (hf : ∀ y, Set.Finite {x | Generator.mixedMultiplicationBasis a b r s d x = y}) :
    (Diagram.mixedProjection (R := Complex) a b r s d hf).eval =
      (cross a b r s [(1, ⟨d, hf⟩)]).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change _ = (ScopedDiagram.linearCombination
    [(1, .ordinary (.mixedProjection a b r s d hf))]).eval.toLinearMap z
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval]

private theorem ordinaryNormal {p q : Word K H} (d : Diagram Complex p q) :
    DotSlidePreorderProof.code d.drawing = [mark] → p.directions.length ≤ 3 →
      Normal (p := p) (q := q) d.eval := by
  induction d <;> intro h hw
  case vertical d e hd he =>
    rw [diagram_code_vert] at h
    exact verticalStep (.ordinary d) (.ordinary e) h hw hd he
  case horizontal d e hd he =>
    rw [diagram_code_horiz] at h
    exact horizontalStep (.ordinary d) (.ordinary e) h hw hd he
  case mixedProjection a b r s d hf =>
    refine ⟨_, _, .atom a b r s [(1, ⟨d, hf⟩)], ?_⟩
    rw [eval_atom]
    exact Framed.self (cross a b r s [(1, ⟨d, hf⟩)]).interpret.eval
  all_goals
    simp [DotSlidePreorderProof.code, mark, Diagram.drawing, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h

private theorem expandedNotMark (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry n o c) ≠ [mark] := by
  unfold DrawingShape.expandedProjectionGeometry
  rw [encode_stack]
  cases o <;> simp [DrawingShape.stack, PlanarCode.encode, PlanarCode.shift,
    DrawingShape.outputs, VertexKind.outputs, VertexKind.canonical, PlanarEvent.place,
    PlanarEvent.position, mark]

private theorem drawingNormal {p q : Word K H} (d : LabelledDrawing Complex p q) :
    DotSlidePreorderProof.code d.erase = [mark] → p.directions.length ≤ 3 →
      Normal (p := p) (q := q) d.interpret.eval := by
  induction d <;> intro h hw
  case ordinary d => exact ordinaryNormal d h hw
  case vertical d e hd he =>
    rw [drawing_code_vert] at h
    exact verticalStep d e h hw hd he
  case horizontal d e hd he =>
    rw [drawing_code_horiz] at h
    exact horizontalStep d e h hw hd he
  case compactProjection a b r s ts =>
    exact ⟨_, _, .atom a b r s ts, Framed.self (cross a b r s ts).interpret.eval⟩
  case trivalent v => cases v <;> simp [DotSlidePreorderProof.code, LabelledDrawing.erase, DrawingShape.geometry,
    PlanarCode.encode, VertexKind.canonical, TrivalentVertex.kind, mark] at h
  case bentVertex v => cases v <;> simp [DotSlidePreorderProof.code, LabelledDrawing.erase, DrawingShape.geometry,
    PlanarCode.encode, VertexKind.canonical, BentVertex.kind, mark] at h
  case parallelUpChain labels =>
    change PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack _) = _ at h
    rw [encode_stack] at h
    simp [mark, PlanarCode.encode, VertexKind.canonical] at h
  case parallelDownChain labels =>
    change PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack _) = _ at h
    rw [encode_stack] at h
    simp [mark, PlanarCode.encode, VertexKind.canonical] at h
  case expandedProjection _ _ _ _ _ o c => exact False.elim (expandedNotMark 1 o c h)
  case expandedProjectionChain _ _ _ _ labels _ o c =>
    exact False.elim (expandedNotMark labels.length o c h)
  case expandedLinearDotProjection _ _ _ _ labels _ o c =>
    exact False.elim (expandedNotMark labels.length o c h)
  case rightCurlUp =>
    simp [DotSlidePreorderProof.code, LabelledDrawing.erase, DrawingShape.geometry, DrawingShape.rightCurlGeometry,
      DrawingShape.stack, PlanarCode.encode, VertexKind.canonical, PlanarCode.shift,
      DrawingShape.outputs, PlanarEvent.place, PlanarEvent.position, mark] at h
  all_goals
    simp [DotSlidePreorderProof.code, mark, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h

private theorem sameInput {M M' N N' : Subgroup U}
    (a : ConjEmbedding K M) (b : ConjEmbedding N M) (c : Strand N H)
    (a' : ConjEmbedding K M') (b' : ConjEmbedding N' M') (c' : ConjEmbedding H N')
    (h : ((inputPair a b).tensor c.word).boundary =
      ((inputPair a' b').tensor (.up c')).boundary) :
    ∃ _e : M = M', ∃ _e' : N = N',
      HEq a a' ∧ HEq b b' ∧ HEq c (.up c' : Strand N' H) := by
  cases c with
  | up c =>
    change Boundary.cons (.down a) (.cons (.up b) (.cons (.up c) (.empty H))) =
      Boundary.cons (.down a') (.cons (.up b') (.cons (.up c') (.empty H))) at h
    injection h with _ hm _ ha ht
    subst M'
    have haa : a = a' := by injection ha
    have ht' := eq_of_heq ht
    injection ht' with _ hn _ hb hu
    subst N'
    have hbb : b = b' := by injection hb
    have hu' := eq_of_heq hu
    injection hu' with _ _ _ hc _
    exact ⟨rfl, rfl, heq_of_eq haa, heq_of_eq hbb, heq_of_eq hc⟩
  | down c =>
    change Boundary.cons (.down a) (.cons (.up b) (.cons (.down c) (.empty H))) =
      Boundary.cons (.down a') (.cons (.up b') (.cons (.up c') (.empty H))) at h
    injection h with _ hm _ _ ht
    subst M'
    have ht' := eq_of_heq ht
    injection ht' with _ hn _ _ hu
    subst N'
    have hu' := eq_of_heq hu
    injection hu' with _ _ _ hc _
    injection hc

private abbrev BMap (p q : Boundary K H) :=
  Biset.Hom Complex p.word.basis q.word.basis

/-- Transport along the recovered equality of the ordered source and target. -/
def castBoundary {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (f : BMap p q) : BMap p' q' := by
  cases hp
  cases hq
  exact f

private theorem castBoundary_eq {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (f : BMap p q) (g : BMap p' q') (h : HEq f g) : castBoundary hp hq f = g := by
  cases hp
  cases hq
  exact eq_of_heq h

set_option maxHeartbeats 800000 in
/-- The exact leftmost projection stage, with the third strand fixed by the input boundary. -/
theorem normalizeFirst {M N : Subgroup U} (a : ConjEmbedding K M) (b : ConjEmbedding N M)
    (c : ConjEmbedding H N) {p q : Word K H} (d : LabelledDrawing Complex p q)
    (hc : PlanarCode.encode d.erase.geometry = [.vertex 0 .mixedProjection])
    (hp : p.boundary = ((inputPair a b).tensor (.up c)).boundary) :
    ∃ (B : Subgroup U) (r : ConjEmbedding B K) (s : ConjEmbedding B N)
      (ts : List (Complex × ProjectionDot.Mixed a b r s))
      (hq : q.boundary = ((outputPair r s).tensor (.up c)).boundary),
      castBoundary hp hq d.interpret.atBoundary.eval =
        ((LabelledDrawing.compactProjection a b r s ts).horizontal
          (.ordinary (.id (.up c)))).interpret.atBoundary.eval := by
  have hw : p.directions.length = 3 := by
    have hd := congrArg boundaryDirections hp
    simpa [boundaryDirections_word, Word.directions] using congrArg List.length hd
  obtain ⟨v, w, x, hx⟩ := drawingNormal d hc (Nat.le_of_eq hw)
  obtain ⟨hv, hq⟩ := Framed.boundaries coherence hx
  have hcanon := Framed.canonical coherence hx
  have hd := hv.symm.trans hp
  cases x with
  | atom a₀ b₀ r s ts =>
    have bad := congrArg (List.length ∘ boundaryDirections) hd
    simp [Function.comp_apply, boundaryDirections_word, Word.directions] at bad
  | tail a₀ b₀ r s ts t =>
    obtain ⟨hM, hN, ha, hb, ht⟩ := sameInput a₀ b₀ t a b c hd
    cases hM
    cases hN
    cases eq_of_heq ha
    cases eq_of_heq hb
    cases eq_of_heq ht
    refine ⟨_, r, s, ts, hq, ?_⟩
    apply castBoundary_eq
    exact hcanon

/-- Combine repeated projection entries by adding their complex coefficients. -/
noncomputable def collectProjection {X : Type u} (ts : List (Complex × X)) : X →₀ Complex :=
  (ts.map fun (z, x) => Finsupp.single x z).sum

private theorem eval_collect {X : Type u} {Y : Type*} [AddCommMonoid Y] [Module Complex Y]
    (f : X → Y) (ts : List (Complex × X)) :
    freeLift Complex f (collectProjection ts) = (ts.map fun t => t.1 • f t.2).sum := by
  induction ts with
  | nil => simp [collectProjection]
  | cons t ts ih =>
    rcases t with ⟨z, x⟩
    change freeLift Complex f (Finsupp.single x z + collectProjection ts) = _
    rw [map_add, freeLift_single, ih]
    rfl

/-- Evaluation factors through the collected coefficients, including repeated and cancelling terms. -/
theorem eval_collectProjection {B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (r : ConjEmbedding B K) (s : ConjEmbedding B H)
    (ts : List (Complex × ProjectionDot.Mixed a b r s))
    (z : (inputPair a b).basis.carrier →₀ Complex) :
    (LabelledDrawing.compactProjection a b r s ts).interpret.eval.toLinearMap z =
      freeLift Complex
        (fun x : ProjectionDot.Mixed a b r s =>
          (Diagram.mixedProjection (R := Complex) a b r s x.dot x.finite).eval.toLinearMap z)
        (collectProjection ts) := by
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply, eval_collect, List.map_map]
  rfl

end CaseTwoFirstStage
