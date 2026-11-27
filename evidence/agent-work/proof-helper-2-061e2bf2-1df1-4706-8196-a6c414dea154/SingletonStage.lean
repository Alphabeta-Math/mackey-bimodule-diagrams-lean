import FactorPart
import Proofs.DotSlidePreorderNotSymmetric
import Batteries.Tactic.OpenPrivate

set_option maxHeartbeats 2000000

open private CaseTwoFactor.code drawing_code_vert drawing_code_horiz diagram_code_vert diagram_code_horiz
  encode_stack no_expandedProjection goodCode isCompactCrossing from FactorPart
open private Wire Wire.eval Wire.boundary Wire.directions Framed Framed.self Framed.vertLeft
  Framed.vertRight Framed.horizontal Framed.trans Framed.boundaries Framed.canonical
  canon canon_vertical frameStraight stripLeft stripRight dot_empty_coherence boundaryDirections
  boundaryDirections_word splitSingleton shiftEmpty
  from Proofs.DotSlidePreorderNotSymmetric

namespace CaseTwoStage
open MackeyDiagrams Biset.Hom
universe u
variable {U : Type u} [Group U] {A B C D : Subgroup U}

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
      ((Wire.eval d).horizontal f) := by
  let hc : DotSlidePreorderProof.EmptyCodeCoherence U := dot_empty_coherence
  obtain ⟨r', s', c, hf⟩ := h
  have hr : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (Framed.boundaries hc hf).1
  have hp : p.directions.length ≤ 1 := by
    rw [List.length_append, hr] at hw
    have := c.width
    omega
  obtain ⟨p', ⟨w⟩, hb⟩ := shortBoundary p.boundary (by rwa [boundaryDirections_word])
  have hp' : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  rw [← Wire.directions hc d, hp']
  rw [hp', hr] at hw
  obtain ⟨v, z, c', h'⟩ := w.padLeft c hw
  exact ⟨v, z, c', Framed.trans (Framed.horizontal (frameStraight hc d hb) hf) h'⟩

private theorem padRight {k : VertexKind} {n : Nat}
    {p q : Word A B} {r s : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} (h : Normal (p := p) (q := q) k n f)
    (d : Wire r s) (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor s) k n (f.horizontal (Wire.eval d)) := by
  let hc : DotSlidePreorderProof.EmptyCodeCoherence U := dot_empty_coherence
  obtain ⟨p', q', c, hf⟩ := h
  have hp : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (Framed.boundaries hc hf).1
  have hr : r.directions.length ≤ 1 := by
    rw [List.length_append, hp] at hw
    have := c.width
    omega
  obtain ⟨r', ⟨w⟩, hb⟩ := shortBoundary r.boundary (by rwa [boundaryDirections_word])
  have hr' : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  rw [hp, hr'] at hw
  obtain ⟨v, z, c', h'⟩ := w.padRight c hw
  exact ⟨v, z, c', Framed.trans (Framed.horizontal hf (frameStraight hc d hb)) h'⟩

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
  ∀ n, CaseTwoFactor.code d.erase = [.vertex n k] → p.directions.length ≤ 3 →
    Normal (p := p) (q := q) k n d.interpret.eval

private theorem normalVertical {k : VertexKind} {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r)
    (hd : Normalizes d k) (he : Normalizes e k) : Normalizes (d.vertical e) k := by
  intro n h hw
  rw [drawing_code_vert] at h
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · let w : Wire p q := ⟨d, hd0⟩
    have hew : q.directions.length ≤ 3 := by rw [← Wire.directions dot_empty_coherence w]; exact hw
    obtain ⟨s, t, c, hf⟩ := he n he1 hew
    exact ⟨s, t, c, Framed.vertLeft w hf⟩
  · obtain ⟨s, t, c, hf⟩ := hd n hd1 hw
    exact ⟨s, t, c, Framed.vertRight ⟨e, he0⟩ hf⟩

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
      simp [CaseTwoFactor.code, LabelledDrawing.erase, Diagram.drawing, DrawingShape.geometry,
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
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode,
        VertexKind.canonical, TrivalentVertex.kind] at h
  case bentVertex v =>
    intro n h _
    cases v <;> rcases hk with rfl | rfl <;>
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode,
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
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, DrawingShape.rightCurlGeometry,
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
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h


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

/-- Canonical evaluation composes at a shared labelled intermediate boundary. -/
theorem evalAt_vertical {p q v : Word A B} {P Q V : Boundary A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q v)
    (hp : p.boundary = P) (hq : q.boundary = Q) (hv : v.boundary = V) :
    evalAt (d.vertical e) hp hv = (evalAt d hp hq).vertical (evalAt e hq hv) := by
  cases hp
  cases hq
  cases hv
  exact canon_vertical d.interpret.eval e.interpret.eval

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
  exact Framed.canonical dot_empty_coherence h

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
    obtain ⟨hb, ht⟩ := Framed.boundaries dot_empty_coherence hf
    cases atom with
    | project s' c' t j ys =>
      have hb' := hb.symm.trans hin
      cases head with
      | down r' =>
        have bad := congrArg boundaryDirections hb'
        change [false, false, true] = [true, false, true] at bad
        contradiction
      | up r' =>
        rename_i B' D' L
        obtain ⟨eB, eD, er, es, ec⟩ :=
          upDownUp_inj (r := r) (s := s) (c := c)
            (r' := r') (s' := s') (c' := c') hb'
        subst B'
        subst D'
        have er' := eq_of_heq er
        have es' := eq_of_heq es
        have ec' := eq_of_heq ec
        subst r'
        subst s'
        subst c'
        have hout : (upUpDown r t j).boundary = q.boundary := ht.symm
        refine ⟨_, t, j, ys, hout, ?_⟩
        exact eq_of_heq ((evalAt_heq draw hin rfl).trans
          ((Framed.canonical dot_empty_coherence hf).trans
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
  obtain ⟨hb, ht⟩ := Framed.boundaries dot_empty_coherence hf
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
    rw [boundaryDirections_word] at h
    exact h
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

-- Verify the framed drawing is the endpoint's actual atRight expression.
example {B : Subgroup CaseTwoAudit.U} (r : MackeyDiagrams.ConjEmbedding B CaseTwoAudit.G)
    (s : MackeyDiagrams.ConjEmbedding B CaseTwoAudit.D)
    (t : MackeyDiagrams.ConjEmbedding CaseTwoAudit.T B)
    (ys : List (Complex × MackeyDiagrams.ProjectionDot.Mixed s CaseTwoAudit.c t CaseTwoAudit.f)) :
    CaseTwoStage.rightProjection r s CaseTwoAudit.c t CaseTwoAudit.f ys =
      CaseTwoAudit.atRight (.up r) (.compactProjection s CaseTwoAudit.c t CaseTwoAudit.f ys) := rfl
