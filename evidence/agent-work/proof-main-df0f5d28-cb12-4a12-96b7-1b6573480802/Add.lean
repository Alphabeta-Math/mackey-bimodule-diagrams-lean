
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
