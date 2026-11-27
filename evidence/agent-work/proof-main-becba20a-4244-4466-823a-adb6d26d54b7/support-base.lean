namespace ReplacementForTwoProjectionsAux

open MackeyDiagrams

universe u
noncomputable section

variable {U : Type u} [Group U] {K H : Subgroup U}

private abbrev ev {p q : Word K H} (d : LabelledDrawing Complex p q) :=
  d.interpret.eval.toLinearMap

private theorem cancelFrame {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (preInv : Biset.Hom Complex p.basis p₀.basis)
    (postInv : Biset.Hom Complex q₀.basis q.basis)
    (hp : preInv.vertical pre.interpret.eval = Biset.Hom.id p.basis)
    (hq : post.interpret.eval.vertical postInv = Biset.Hom.id q.basis)
    (x y : LabelledDrawing Complex p q) :
    ev (.vertical pre (.vertical x post)) = ev (.vertical pre (.vertical y post)) ↔
      x.interpret.eval = y.interpret.eval := by
  constructor
  · intro h
    have he : pre.interpret.eval.vertical (x.interpret.eval.vertical post.interpret.eval) =
        pre.interpret.eval.vertical (y.interpret.eval.vertical post.interpret.eval) :=
      Biset.Hom.ext h
    have undo (z : LabelledDrawing Complex p q) :
        (preInv.vertical (pre.interpret.eval.vertical
          (z.interpret.eval.vertical post.interpret.eval))).vertical postInv = z.interpret.eval := by
      rw [← Biset.Hom.vertical_assoc preInv, hp, Biset.Hom.id_vertical,
        Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]
    have h' := congrArg (fun z => (preInv.vertical z).vertical postInv) he
    exact (undo x).symm.trans (h'.trans (undo y))
  · intro h
    exact congrArg (fun z : Biset.Hom Complex p.basis q.basis =>
      (pre.interpret.eval.vertical (z.vertical post.interpret.eval)).toLinearMap) h

private abbrev drawId (p : Word K H) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

section Boundary
variable {G A D F C E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev bottom := ((Word.down a).tensor (.up b)).tensor (.up c)
private abbrev top := ((Word.up d).tensor (.up e)).tensor (.down f)
private abbrev mergedBottom := (Word.down a).tensor (.up (b.comp c))
private abbrev mergedTop := (Word.up (d.comp e)).tensor (.down f)

private abbrev splitBottom : LabelledDrawing Complex (mergedBottom a b c) (bottom a b c) :=
  .vertical (.horizontal (drawId (.down a)) (.trivalent (.splitUp b c)))
    (.ordinary (.unassociate (.down a) (.up b) (.up c)))

private abbrev mergeTop : LabelledDrawing Complex (top d e f) (mergedTop d e f) :=
  .horizontal (.trivalent (.mergeUp d e)) (drawId (.down f))

private theorem splitBottom_leftCancel :
    ((Diagram.associate (R := Complex) (.down a) (.up b) (.up c)).eval.vertical
      ((Diagram.id (.down a)).eval.horizontal (Diagram.mergeUp b c).eval)).vertical
      (splitBottom a b c).interpret.eval = Biset.Hom.id (bottom a b c).basis := by
  change ((Biset.associate (Word.down a).basis (Word.up b).basis (Word.up c).basis
      Complex).vertical
      ((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.mergeUp b c).eval)).vertical
    (((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.splitUp b c).eval).vertical
      (Biset.unassociate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex)) = _
  refine Biset.Hom.cancel_middle _ _ _ _ ?_ Biset.associate_unassociate
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id (Word.down a).basis).horizontal
    ((Diagram.mergeUp (R := Complex) b c).vertical (Diagram.splitUp b c)).eval = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem mergeTop_rightCancel :
    (mergeTop d e f).interpret.eval.vertical
      ((Diagram.splitUp d e).eval.horizontal (Diagram.id (.down f)).eval) =
      Biset.Hom.id (top d e f).basis := by
  change ((Diagram.mergeUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)).vertical
      ((Diagram.splitUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.mergeUp (R := Complex) d e).vertical (Diagram.splitUp d e)).eval.horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem merged_eq_iff (x y : LabelledDrawing Complex (bottom a b c) (top d e f)) :
    ev (.vertical (splitBottom a b c) (.vertical x (mergeTop d e f))) =
      ev (.vertical (splitBottom a b c) (.vertical y (mergeTop d e f))) ↔
      x.interpret.eval = y.interpret.eval :=
  cancelFrame _ _ _ _ (splitBottom_leftCancel a b c) (mergeTop_rightCancel d e f) x y

end Boundary

private theorem terms_single {I : Type*} (x : I) {w : Complex} (hw : w ≠ 0) :
    ((Finsupp.single x w).support.toList.map fun y => ((Finsupp.single x w) y, y)) = [(w, x)] := by
  classical
  simp [Finsupp.support_single _ hw]

private abbrev drawSum {p q : Word K H} (ds : List (LabelledDrawing Complex p q)) :=
  match ds with
  | [] => LabelledDrawing.ordinary (Diagram.zero p q)
  | first :: rest => rest.foldl LabelledDrawing.add first

private theorem framed_add {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (x y : LabelledDrawing Complex p q) :
    ev (.vertical pre (.vertical (.add x y) post)) =
      ev (.vertical pre (.vertical x post)) + ev (.vertical pre (.vertical y post)) := by
  apply LinearMap.ext
  intro v
  change ev post ((ev x + ev y) (ev pre v)) =
    ev post (ev x (ev pre v)) + ev post (ev y (ev pre v))
  exact map_add (ev post) _ _

private theorem framed_sum {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (ds : List (LabelledDrawing Complex p q)) :
    ev (.vertical pre (.vertical (drawSum ds) post)) =
      (ds.map (fun z => ev (.vertical pre (.vertical z post)))).sum := by
  let value := fun z : LabelledDrawing Complex p q => ev (.vertical pre (.vertical z post))
  have hfold (rest : List (LabelledDrawing Complex p q)) (first : LabelledDrawing Complex p q) :
      value (rest.foldl LabelledDrawing.add first) = value first + (rest.map value).sum := by
    induction rest generalizing first with
    | nil => simp
    | cons next rest ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
      exact congrArg (· + (rest.map value).sum) (framed_add pre post first next)
  cases ds with
  | nil =>
    apply LinearMap.ext
    intro v
    change ev post 0 = 0
    exact map_zero _
  | cons first rest => exact hfold rest first

private def weighted {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (v : I → M) (xs : List (Complex × I)) : M :=
  (xs.map fun term => term.1 • v term.2).sum

private theorem map_weighted {I M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (f : M →ₗ[Complex] N)
    (v : I → M) (xs : List (Complex × I)) :
    f (weighted v xs) = weighted (fun x => f (v x)) xs := by
  unfold weighted
  rw [map_list_sum, List.map_map]
  simp only [Function.comp_def, map_smul]

private abbrev labelTerms {I : Type*} (coeff : I →₀ Complex) :=
  coeff.support.toList.map fun x => (coeff x, x)

private theorem weighted_labelTerms {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (v : I → M) (coeff : I →₀ Complex) :
    weighted v (labelTerms coeff) = Finsupp.linearCombination Complex v coeff := by
  classical
  rw [weighted, List.map_map, Finsupp.linearCombination_apply]
  exact Finset.sum_map_toList _ _

private def applyAt {M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (x : M) : (M →ₗ[Complex] N) →ₗ[Complex] N where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem compactWeighted {L P : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (r : ConjEmbedding L K) (s : ConjEmbedding L H)
    (xs : List (Complex × ProjectionDot.Mixed a b r s)) :
    ev (.compactProjection a b r s xs) =
      weighted (fun x => ev (.compactProjection a b r s [(1, x)])) xs := by
  apply LinearMap.ext
  intro v
  change (ScopedDiagram.linearCombination (xs.map fun x =>
    (x.1, ScopedDiagram.ordinary (.mixedProjection a b r s x.2.dot x.2.finite)))).eval.toLinearMap v =
    applyAt v (weighted (fun x => ev (.compactProjection a b r s [(1, x)])) xs)
  rw [ScopedDiagram.eval_linearCombination_apply, map_weighted]
  unfold weighted
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  let d : ScopedDiagram Complex ((Word.down a).tensor (.up b)) ((Word.up r).tensor (.down s)) :=
    .ordinary (.mixedProjection a b r s x.2.dot x.2.finite)
  have hs : ev (.compactProjection a b r s [(1, x.2)]) v = d.eval.toLinearMap v := by
    change (ScopedDiagram.linearCombination [(1, d)]).eval.toLinearMap v = _
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
      using ScopedDiagram.eval_linearCombination_apply [(1, d)] v
  exact congrArg (x.1 • ·) hs.symm

private theorem horizontalWeighted {I : Type*} {J : Subgroup U}
    {p q : Word K H} {r s : Word H J}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex r s)
    (terms : I → LabelledDrawing Complex p q) (xs : List (Complex × I))
    (he : ev d = weighted (fun x => ev (terms x)) xs) :
    ev (.horizontal d e) = weighted (fun x => ev (.horizontal (terms x) e)) xs := by
  apply Finsupp.lhom_ext
  intro z w
  refine Quotient.inductionOn z (fun ⟨x,y⟩ => ?_)
  let v := Finsupp.single (p.basis.pair r.basis x y) w
  let tensorAt := w • (((Biset.pairLinear Complex q.basis s.basis).flip
    (ev e (Finsupp.single y 1))).comp (applyAt (Finsupp.single x (1 : Complex))))
  have h (g : LabelledDrawing Complex p q) : ev (.horizontal g e) v = tensorAt (ev g) :=
    Biset.Hom.horizontal_single g.interpret.eval e.interpret.eval x y w
  change ev (.horizontal d e) v =
    applyAt v (weighted (fun i => ev (.horizontal (terms i) e)) xs)
  rw [h, he, map_weighted, map_weighted]
  exact congrArg (fun f => weighted f xs) (funext fun i => (h (terms i)).symm)

private theorem stackWeighted {I : Type*} {p₀ p q q' q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (next : LabelledDrawing Complex q q')
    (post : LabelledDrawing Complex q' q₀)
    (d : LabelledDrawing Complex p q) (terms : I → LabelledDrawing Complex p q)
    (xs : List (Complex × I)) (he : ev d = weighted (fun x => ev (terms x)) xs) :
    ev (.vertical pre (.vertical (.vertical d next) post)) =
      weighted (fun x => ev (.vertical pre (.vertical (.vertical (terms x) next) post))) xs := by
  apply LinearMap.ext
  intro v
  let push := ((ev post).comp (ev next)).comp (applyAt (ev pre v))
  change push (ev d) =
    applyAt v (weighted (fun x => ev (.vertical pre (.vertical (.vertical (terms x) next) post))) xs)
  rw [he, map_weighted, map_weighted]
  rfl

private theorem firstProjectionWeighted {J L P : Subgroup U}
    {r' : Word H J} {q' : Word H J}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (r : ConjEmbedding L K) (s : ConjEmbedding L H)
    (other : LabelledDrawing Complex r' q')
    {p₀ q'₁ q₀ : Word K J}
    (pre : LabelledDrawing Complex p₀ (((Word.down a).tensor (.up b)).tensor r'))
    (next : LabelledDrawing Complex (((Word.up r).tensor (.down s)).tensor q') q'₁)
    (post : LabelledDrawing Complex q'₁ q₀)
    (xs : List (Complex × ProjectionDot.Mixed a b r s)) :
    let value := fun ts => ev (.vertical pre (.vertical
      (.vertical (.horizontal (.compactProjection a b r s ts) other) next) post))
    value xs = weighted (fun x => value [(1, x)]) xs := by
  exact stackWeighted pre next post _ _ xs
    (horizontalWeighted _ other _ xs (compactWeighted a b r s xs))

private theorem quotientReplacement {L R M : Type*} (lEval : L → M) (rEval : R → M)
    (hL : ∀ l, ∃ r, rEval r = lEval l) (hR : ∀ r, ∃ l, lEval l = rEval r) :
    ∃ (lr : L → R) (rl : R → L) (q : Quotient (Setoid.ker lEval) ≃ Quotient (Setoid.ker rEval)),
      (∀ l, rEval (lr l) = lEval l ∧
        q (Quotient.mk (Setoid.ker lEval) l) = Quotient.mk (Setoid.ker rEval) (lr l)) ∧
      (∀ r, lEval (rl r) = rEval r ∧
        q.symm (Quotient.mk (Setoid.ker rEval) r) = Quotient.mk (Setoid.ker lEval) (rl r)) := by
  choose lr hlr using hL
  choose rl hrl using hR
  let q : Quotient (Setoid.ker lEval) ≃ Quotient (Setoid.ker rEval) :=
    { toFun := Quotient.map lr (fun {_ _} h => (hlr _).trans (h.trans (hlr _).symm))
      invFun := Quotient.map rl (fun {_ _} h => (hrl _).trans (h.trans (hrl _).symm))
      left_inv := by
        intro x
        refine Quotient.inductionOn x (fun l => Quotient.sound ?_)
        exact (hrl (lr l)).trans (hlr l)
      right_inv := by
        intro x
        refine Quotient.inductionOn x (fun r => Quotient.sound ?_)
        exact (hlr (rl r)).trans (hrl r) }
  exact ⟨lr, rl, q, fun l => ⟨hlr l, rfl⟩, fun r => ⟨hrl r, rfl⟩⟩

end
end ReplacementForTwoProjectionsAux
