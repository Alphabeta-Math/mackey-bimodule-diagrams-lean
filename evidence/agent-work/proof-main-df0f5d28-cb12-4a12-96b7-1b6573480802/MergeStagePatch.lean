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

