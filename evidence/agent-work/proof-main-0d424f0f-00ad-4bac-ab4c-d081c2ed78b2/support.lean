open MackeyDiagrams

namespace CaseSixStrictAux

universe u

-- A weighted mark, framed on either side by a fixed diagram, evaluates
-- termwise. These two identities work on all balanced basis classes.
private theorem frameRight {U : Type u} [Group U] {K H J : Subgroup U}
    {p q : Word K H} {v w : Word H J}
    (right : Biset.Hom Complex v.basis w.basis)
    (terms : List (Complex × ScopedDiagram Complex p q)) :
    ((ScopedDiagram.linearCombination terms).eval.horizontal right).toLinearMap =
      (terms.map fun (c, d) => c • (d.eval.horizontal right).toLinearMap).sum := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z fun ⟨x, y⟩ => ?_
  change ((ScopedDiagram.linearCombination terms).eval.horizontal right).toLinearMap
    (Finsupp.single (p.basis.pair v.basis x y) r) = _
  rw [Biset.Hom.horizontal_single, ScopedDiagram.eval_linearCombination_apply]
  let frame := (Biset.pairLinear Complex q.basis w.basis).flip
    (right.toLinearMap (Finsupp.single y 1))
  change r • frame ((terms.map fun term => term.1 • term.2.eval.toLinearMap
      (Finsupp.single x 1)).sum) =
    (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))
      ((terms.map fun (c, d) => c • (d.eval.horizontal right).toLinearMap).sum)
  rw [map_list_sum frame, List.smul_sum,
    map_list_sum (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c, d⟩ _
  change r • frame (c • d.eval.toLinearMap (Finsupp.single x 1)) =
    c • (d.eval.horizontal right).toLinearMap (Finsupp.single (p.basis.pair v.basis x y) r)
  rw [map_smul, Biset.Hom.horizontal_single]
  exact smul_comm r c _

private theorem frameLeft {U : Type u} [Group U] {K H J : Subgroup U}
    {p q : Word K H} {v w : Word H J}
    (left : Biset.Hom Complex p.basis q.basis)
    (terms : List (Complex × ScopedDiagram Complex v w)) :
    (left.horizontal (ScopedDiagram.linearCombination terms).eval).toLinearMap =
      (terms.map fun (c, d) => c • (left.horizontal d.eval).toLinearMap).sum := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z fun ⟨x, y⟩ => ?_
  change (left.horizontal (ScopedDiagram.linearCombination terms).eval).toLinearMap
    (Finsupp.single (p.basis.pair v.basis x y) r) = _
  rw [Biset.Hom.horizontal_single, ScopedDiagram.eval_linearCombination_apply]
  let frame := Biset.pairLinear Complex q.basis w.basis (left.toLinearMap (Finsupp.single x 1))
  change r • frame ((terms.map fun term => term.1 • term.2.eval.toLinearMap
      (Finsupp.single y 1)).sum) =
    (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))
      ((terms.map fun (c, d) => c • (left.horizontal d.eval).toLinearMap).sum)
  rw [map_list_sum frame, List.smul_sum,
    map_list_sum (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c, d⟩ _
  change r • frame (c • d.eval.toLinearMap (Finsupp.single y 1)) =
    c • (left.horizontal d.eval).toLinearMap (Finsupp.single (p.basis.pair v.basis x y) r)
  rw [map_smul, Biset.Hom.horizontal_single]
  exact smul_comm r c _

-- Apply linearity to a weighted list of linear maps with a fixed input and
-- an arbitrary downstream linear functional. This also covers the empty list.
private theorem list_apply_zero {D M N : Type*}
    [AddCommMonoid M] [Module Complex M] [AddCommMonoid N] [Module Complex N]
    (terms : List (Complex × D)) (eval : D → M →ₗ[Complex] N)
    (x : M) (measure : N →ₗ[Complex] Complex)
    (zero : ∀ d : D, measure (eval d x) = 0) :
    measure (((terms.map fun term => term.1 • eval term.2).sum) x) = 0 := by
  induction terms with
  | nil => simp
  | cons d terms ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, zero, ih, smul_zero, add_zero]

private theorem stack_apply_zero {L M N V W X Y : Type*}
    [AddCommMonoid V] [Module Complex V] [AddCommMonoid W] [Module Complex W]
    [AddCommMonoid X] [Module Complex X] [AddCommMonoid Y] [Module Complex Y]
    (rs : List (Complex × L)) (ts : List (Complex × M)) (ss : List (Complex × N))
    (lower : L → V →ₗ[Complex] W) (middle : M → W →ₗ[Complex] X)
    (upper : N → X →ₗ[Complex] Y) (input : V) (measure : Y →ₗ[Complex] Complex)
    (zero : ∀ r t s, measure (upper s (middle t (lower r input))) = 0) :
    measure ((ss.map fun term => term.1 • upper term.2).sum
      ((ts.map fun term => term.1 • middle term.2).sum
        ((rs.map fun term => term.1 • lower term.2).sum input))) = 0 := by
  let mid := (ts.map fun term => term.1 • middle term.2).sum
  let top := (ss.map fun term => term.1 • upper term.2).sum
  change ((measure.comp top).comp mid) ((rs.map fun term => term.1 • lower term.2).sum input) = 0
  apply list_apply_zero rs lower input
  intro r
  change (measure.comp top) (mid (lower r input)) = 0
  apply list_apply_zero ts middle (lower r input)
  intro t
  change measure (top (middle t (lower r input))) = 0
  exact list_apply_zero ss upper _ measure (zero r t)

private theorem compose_weighted_list {V W X : Type*} [AddCommMonoid V] [Module Complex V]
    [AddCommMonoid W] [Module Complex W] [AddCommMonoid X] [Module Complex X]
    {D : Type*} (terms : List (Complex × D)) (after : W →ₗ[Complex] X)
    (stage : D → V →ₗ[Complex] W) (col : V) :
    after ((terms.map fun d => d.1 • stage d.2).sum col) =
      (terms.map fun d => d.1 • after.comp (stage d.2)).sum col := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, LinearMap.comp_apply, ih]

section LeftDrawing

variable {U : Type u} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (u : ConjEmbedding G B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)

private abbrev leftDrawing (rs : List (Complex × Dot (u.comp a) (v.comp b)))
    (ts : List (Complex × Dot (v.comp d) (w.comp f)))
    (ss : List (Complex × ProjectionDot.Mixed u w c e)) :
    LabelledDrawing Complex ((Word.up a).tensor ((Word.down b).tensor (.up d)))
      ((Word.up c).tensor ((Word.down e).tensor (.up f))) :=
  .vertical (.ordinary (.unassociate (.up a) (.down b) (.up d)))
    (.vertical (.horizontal (.mixedMultiplication u v a b rs) (.ordinary (.id (.up d))))
      (.vertical (.ordinary (.associate (.down u) (.up v) (.up d)))
        (.vertical (.horizontal (.ordinary (.id (.down u))) (.parallelUp v d w f ts))
          (.vertical (.ordinary (.unassociate (.down u) (.up w) (.up f)))
            (.vertical (.horizontal (.compactProjection u w c e ss) (.ordinary (.id (.up f))))
              (.ordinary (.associate (.up c) (.down e) (.up f))))))))

private noncomputable abbrev evaluate {K H : Subgroup U} {p q : Word K H}
    (drawing : LabelledDrawing Complex p q) := drawing.interpret.eval.toLinearMap

private theorem left_apply_zero
    (rs : List (Complex × Dot (u.comp a) (v.comp b)))
    (ts : List (Complex × Dot (v.comp d) (w.comp f)))
    (ss : List (Complex × ProjectionDot.Mixed u w c e))
    (x : ((Word.up a).tensor ((Word.down b).tensor (.up d))).basis.carrier →₀ Complex)
    (y : ((Word.up c).tensor ((Word.down e).tensor (.up f))).basis.carrier)
    (zero : ∀ r t s, evaluate (leftDrawing a b d c e f u v w [(1, r)] [(1, t)] [(1, s)]) x y = 0) :
    evaluate (leftDrawing a b d c e f u v w rs ts ss) x y = 0 := by
  let pre := (Diagram.unassociate (R := Complex) (.up a) (.down b) (.up d)).eval.toLinearMap
  let reassoc := (Diagram.associate (R := Complex) (.down u) (.up v) (.up d)).eval.toLinearMap
  let unassoc := (Diagram.unassociate (R := Complex) (.down u) (.up w) (.up f)).eval.toLinearMap
  let post := (Finsupp.lapply (R := Complex) y).comp
    (Diagram.associate (R := Complex) (.up c) (.down e) (.up f)).eval.toLinearMap
  let idD := (Diagram.id (R := Complex) (.up d)).eval
  let idU := (Diagram.id (R := Complex) (.down u)).eval
  let idF := (Diagram.id (R := Complex) (.up f)).eval
  let lower (r : Dot (u.comp a) (v.comp b)) : ScopedDiagram Complex _ _ :=
    .ordinary (.mixedMultiplication u v a b r)
  let middle (t : Dot (v.comp d) (w.comp f)) : ScopedDiagram Complex _ _ :=
    .ordinary (.parallelUp v d w f t)
  let upper (s : ProjectionDot.Mixed u w c e) : ScopedDiagram Complex _ _ :=
    .ordinary (.mixedProjection u w c e s.dot s.finite)
  have expansion (rs : List (Complex × Dot (u.comp a) (v.comp b)))
      (ts : List (Complex × Dot (v.comp d) (w.comp f)))
      (ss : List (Complex × ProjectionDot.Mixed u w c e)) :
      evaluate (leftDrawing a b d c e f u v w rs ts ss) x y =
        post ((ss.map fun s => s.1 • ((upper s.2).eval.horizontal idF).toLinearMap).sum
          ((ts.map fun t => t.1 • unassoc.comp (idU.horizontal (middle t.2).eval).toLinearMap).sum
            ((rs.map fun r => r.1 • reassoc.comp ((lower r.2).eval.horizontal idD).toLinearMap).sum
              (pre x)))) := by
    change post (((ScopedDiagram.linearCombination (ss.map fun s => (s.1, upper s.2))).eval.horizontal
      idF).toLinearMap (unassoc ((idU.horizontal
        (ScopedDiagram.linearCombination (ts.map fun t => (t.1, middle t.2))).eval).toLinearMap
        (reassoc (((ScopedDiagram.linearCombination (rs.map fun r => (r.1, lower r.2))).eval.horizontal
          idD).toLinearMap (pre x)))))) = _
    rw [frameRight, frameLeft, frameRight]
    simp only [List.map_map]
    change post ((ss.map fun s => s.1 • ((upper s.2).eval.horizontal idF).toLinearMap).sum
      (unassoc ((ts.map fun t => t.1 • (idU.horizontal (middle t.2).eval).toLinearMap).sum
        (reassoc ((rs.map fun r => r.1 • ((lower r.2).eval.horizontal idD).toLinearMap).sum
          (pre x)))))) = _
    rw [compose_weighted_list rs reassoc (fun r => ((lower r).eval.horizontal idD).toLinearMap) (pre x),
      compose_weighted_list ts unassoc (fun t => (idU.horizontal (middle t).eval).toLinearMap)]
  rw [expansion]
  refine stack_apply_zero rs ts ss
    (fun r => reassoc.comp ((lower r).eval.horizontal idD).toLinearMap)
    (fun t => unassoc.comp (idU.horizontal (middle t).eval).toLinearMap)
    (fun s => ((upper s).eval.horizontal idF).toLinearMap) (pre x) post ?_
  intro r t s
  simpa only [expansion, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_smul, add_zero] using zero r t s

end LeftDrawing

end CaseSixStrictAux
