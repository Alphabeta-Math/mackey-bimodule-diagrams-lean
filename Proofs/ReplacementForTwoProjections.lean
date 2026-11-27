import MackeyDiagrams
import Proofs.CaseOneRightProjectionConstruction
import Proofs.CaseTwoLeftProjectionConstruction

set_option maxHeartbeats 2000000

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
namespace ReplacementForTwoProjectionsAux

open MackeyDiagrams

universe u
noncomputable section

variable {U : Type u} [Group U] {G A D F C E B B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev atRight {K H J L J' : Subgroup U} (p : Word K H)
    {q : Word H J} {r : Word J L} {q' : Word H J'} {r' : Word J' L}
    (x : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :=
  LabelledDrawing.vertical (.ordinary (.associate p q r))
    (.vertical (.horizontal (drawId p) x) (.ordinary (.unassociate p q' r')))

local notation "bc'" => b.comp c
local notation "ad'" => a.comp d
local notation "de'" => d.comp e

private abbrev Parameter := ProjectionDot.Mixed a bc' de' f

private abbrev transfer (p : Parameter a b c d e f) :=
  (Diagram.mixedProjection (R := Complex) a bc' de' f p.dot p.finite).eval.toLinearMap

private abbrev expansion (coeff : Parameter a b c d e f →₀ Complex) :=
  coeff.sum (fun p weight => weight • transfer a b c d e f p)

private abbrev Drawing := LabelledDrawing Complex (bottom a b c) (top d e f)

private abbrev merged (x : Drawing a b c d e f) :=
  ev (.vertical (splitBottom a b c) (.vertical x (mergeTop d e f)))

private abbrev leftTerm (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B) (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × Dot (r.comp t) de')) : Drawing a b c d e f :=
  .vertical (.horizontal (.compactProjection a b r s xs) (drawId (.up c)))
    (.vertical (atRight (.up r) (.compactProjection s c t f ys))
      (.horizontal (.parallelUp r t d e zs) (drawId (.down f))))

private abbrev rightTerm (j : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B') (ells : List (Complex × Dot bc' (j.comp w)))
    (ms : List (Complex × ProjectionDot.Mixed a j d v))
    (ns : List (Complex × ProjectionDot.Mixed v w e f)) : Drawing a b c d e f :=
  .vertical (atRight (.down a) (.parallelUp b c j w ells))
    (.vertical (.horizontal (.compactProjection a j d v ms) (drawId (.up w)))
      (atRight (.up d) (.compactProjection v w e f ns)))

private abbrev LeftLabels :=
  Σ B : Subgroup U, Σ r : ConjEmbedding B G, Σ s : ConjEmbedding B D, Σ t : ConjEmbedding E B,
    Finsupp (ProjectionDot.Mixed a b r s) Complex × Finsupp (ProjectionDot.Mixed s c t f) Complex ×
      DotLabel Complex (r.comp t) de'

private abbrev RightLabels :=
  Σ B' : Subgroup U, Σ j : ConjEmbedding B' A, Σ v : ConjEmbedding C B', Σ w : ConjEmbedding F B',
    DotLabel Complex bc' (j.comp w) × Finsupp (ProjectionDot.Mixed a j d v) Complex ×
      Finsupp (ProjectionDot.Mixed v w e f) Complex

private abbrev leftDraw : LeftLabels a b c d e f → Drawing a b c d e f :=
  fun ⟨_, r, s, t, xs, ys, zs⟩ => leftTerm a b c d e f r s t (labelTerms xs) (labelTerms ys) zs.terms

private abbrev rightDraw : RightLabels a b c d e f → Drawing a b c d e f :=
  fun ⟨_, j, v, w, ells, ms, ns⟩ => rightTerm a b c d e f j v w ells.terms (labelTerms ms) (labelTerms ns)

private abbrev middleFinite (p : Parameter a b c d e f) :=
  let conjugated := (bc').toHom.range.map (MulAut.conj p.dot.element).toMonoidHom
  ((ad').toHom.range.subgroupOf (a.toHom.range ⊓ ((ad').toHom.range ⊔ conjugated))).FiniteIndex

private abbrev evalLeft (l : LeftLabels a b c d e f) := (leftDraw a b c d e f l).interpret.eval
private abbrev evalRight (r : RightLabels a b c d e f) := (rightDraw a b c d e f r).interpret.eval

local notation "LD" => LeftLabels a b c d e f
local notation "RD" => RightLabels a b c d e f
local notation "Draw" => Drawing a b c d e f
local notation "Param" => Parameter a b c d e f
local notation "qstar" => transfer a b c d e f
local notation "expand" => expansion a b c d e f
local notation "mergedEval'" => merged a b c d e f
local notation "leftTerm'" => leftTerm a b c d e f
local notation "leftDraw'" => leftDraw a b c d e f
local notation "rightDraw'" => rightDraw a b c d e f
local notation "leftEval'" => evalLeft a b c d e f
local notation "rightEval'" => evalRight a b c d e f
local notation "middleOK" => middleFinite a b c d e f

-- Lemma 6.3 supplies uniqueness of the transfer expansion for these exact
-- coefficient labels, with finite fibers carried by ProjectionDot.Mixed.
private theorem leftCoefficients (l : LD) :
    ∃! coeff : Param →₀ Complex, mergedEval' (leftDraw' l) = expand coeff := by
  rcases l with ⟨B, r, s, t, xs, ys, zs⟩
  exact ((EvaluationForTwoProjections a b c d e f).2.2.1 r s t).2 xs ys zs

private theorem rightCoefficients (r : RD) :
    ∃! coeff : Param →₀ Complex, mergedEval' (rightDraw' r) = expand coeff := by
  rcases r with ⟨B', j, v, w, ells, ms, ns⟩
  exact ((EvaluationForTwoProjections a b c d e f).2.2.2 j v w).2 ells ms ns

-- Theorem 6.4(1). Apply the registered join construction and middle-index test.
private theorem singleRight (p : Param) (hp : middleOK p) :
    ∃ r : RD, mergedEval' (rightDraw' r) = qstar p := by
  obtain ⟨j, v, w, ell, m, n, _, _, _, _, _, _, _, he⟩ :=
    (CaseOneRightProjectionConstruction a b c d e f).1 p hp
  exact ⟨⟨_, j, v, w, Finsupp.single ell 1, Finsupp.single m 1, Finsupp.single n 1⟩, he⟩


private theorem caseOneMerged (l : LD) (coeff : Param →₀ Complex)
    (hc : mergedEval' (leftDraw' l) = expand coeff) :
    (∃ ds : List Draw,
      (∀ x ∈ ds, ∃ r : RD, x = rightDraw' r) ∧
      mergedEval' (drawSum ds) = mergedEval' (leftDraw' l)) ↔
    ∀ p ∈ coeff.support, middleOK p := by
  rcases l with ⟨B, r, s, t, xs, ys, zs⟩
  have criterion := (CaseOneRightProjectionConstruction a b c d e f).2.2 r s t xs ys zs coeff hc
  constructor
  · rintro ⟨ds, hds, he⟩
    apply criterion.mp
    refine ⟨ds, ?_, ?_⟩
    · intro x hx
      obtain ⟨⟨B', j, v, w, ells, ms, ns⟩, hdraw⟩ := hds x hx
      exact ⟨B', j, v, w, ells, ms, ns, hdraw⟩
    · cases ds <;> exact he
  · intro hs
    obtain ⟨ds, hds, he⟩ := criterion.mpr hs
    refine ⟨ds, ?_, ?_⟩
    · intro x hx
      obtain ⟨B', j, v, w, ells, ms, ns, hdraw⟩ := hds x hx
      exact ⟨⟨B', j, v, w, ells, ms, ns⟩, hdraw⟩
    · cases ds <;> exact he

private theorem caseOne (l : LD) (coeff : Param →₀ Complex)
    (hc : mergedEval' (leftDraw' l) = expand coeff) :
    (∃ ds : List RD, (drawSum (ds.map rightDraw')).interpret.eval = leftEval' l) ↔
      ∀ p ∈ coeff.support, middleOK p := by
  refine Iff.trans ?_ (caseOneMerged a b c d e f l coeff hc)
  constructor
  · rintro ⟨ds, he⟩
    refine ⟨ds.map rightDraw', ?_, (merged_eq_iff a b c d e f _ _).2 he⟩
    intro x hx
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hx
    exact ⟨r, hr.symm⟩
  · rintro ⟨ds, hds, he⟩
    have lift (xs : List Draw) (hs : ∀ x ∈ xs, ∃ r : RD, x = rightDraw' r) :
        ∃ rs : List RD, rs.map rightDraw' = xs := by
      induction xs with
      | nil => exact ⟨[], rfl⟩
      | cons x xs ih =>
        obtain ⟨r, hr⟩ := hs x (List.mem_cons_self ..)
        obtain ⟨rs, hrs⟩ := ih (fun z hz => hs z (List.mem_cons_of_mem x hz))
        exact ⟨r :: rs, by rw [List.map_cons, ← hr, hrs]⟩
    obtain ⟨rs, rfl⟩ := lift ds hds
    exact ⟨rs, (merged_eq_iff a b c d e f _ _).1 he⟩

private theorem singleCaseOne (hd : Subgroup.FiniteIndex d.toHom.range) :
    ∀ l : LD, ∃ r : RD, rightEval' r = leftEval' l := by
  obtain ⟨ell, m, n, _, _, _, _, he⟩ := (CaseOneRightProjectionConstruction a b c d e f).2.1 hd
  intro l
  obtain ⟨coeff, hc, _⟩ := leftCoefficients a b c d e f l
  let r : RD := ⟨A, MackeyDiagrams.ConjEmbedding.id A, ad', bc',
    Finsupp.single ell 1, Finsupp.single m 1, Finsupp.mapDomain n coeff⟩
  exact ⟨r, (merged_eq_iff a b c d e f _ _).1 ((he coeff).trans hc.symm)⟩

-- Theorem 6.4(2). Put each coefficient in the marked lower projection.
-- Balanced horizontal evaluation and stacking are linear in that mark.
private theorem leftWeighted {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
    (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
    (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × MackeyDiagrams.Dot (r.comp t) de')) :
    mergedEval' (leftTerm' r s t xs ys zs) =
      weighted
        (fun x => mergedEval' (leftTerm' r s t [(1, x)] ys zs)) xs :=
  firstProjectionWeighted a b r s (drawId (.up c)) (splitBottom a b c)
    (MackeyDiagrams.LabelledDrawing.vertical
      (atRight (.up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (.down f))))
    (mergeTop d e f) xs

private theorem leftWeight (p : Param) (weight : Complex) (hw : weight ≠ 0) :
    ∃ l : LD, mergedEval' (leftDraw' l) = weight • qstar p := by
  obtain ⟨drawing, hshape, he⟩ := (CaseTwoLeftProjectionConstruction a b c d e f).1 p
  obtain ⟨r, s, t, _, _, _, _, x, y, z, _, _, _, _, _, rfl⟩ := hshape
  refine ⟨⟨_, r, s, t, Finsupp.single x weight, Finsupp.single y 1, Finsupp.single z 1⟩, ?_⟩
  change mergedEval' (leftTerm' r s t (labelTerms (Finsupp.single x weight)) (labelTerms (Finsupp.single y 1))
    (MackeyDiagrams.DotLabel.terms (Finsupp.single z 1))) = _
  rw [show labelTerms (Finsupp.single x weight) = [(weight, x)] from
    terms_single x hw,
    show labelTerms (Finsupp.single y (1 : Complex)) = [(1, y)] from
      terms_single y one_ne_zero,
    show MackeyDiagrams.DotLabel.terms (Finsupp.single z (1 : Complex)) = [(1, z)] from
      terms_single z one_ne_zero,
    leftWeighted a b c d e f]
  change weight • mergedEval' (leftTerm' r s t [(1, x)] [(1, y)] [(1, z)]) + 0 = _
  rw [add_zero]
  exact congrArg (weight • ·) he

-- The endpoint presents its finite sum as a list of whole drawings.
-- Evaluate its additive fold and match it with the coefficient support.
private theorem caseTwo (r : RD) :
    ∃ ds : List LD, (drawSum (ds.map leftDraw')).interpret.eval = rightEval' r := by
  obtain ⟨coeff, hc, _⟩ := rightCoefficients a b c d e f r
  have hex (p : {p // p ∈ coeff.support}) :
      ∃ l : LD, mergedEval' (leftDraw' l) = coeff p.1 • qstar p.1 :=
    leftWeight a b c d e f p.1 (coeff p.1) (Finsupp.mem_support_iff.mp p.2)
  choose build hbuild using hex
  refine ⟨coeff.support.attach.toList.map build, (merged_eq_iff a b c d e f _ _).1 ?_⟩
  change mergedEval' (drawSum ((coeff.support.attach.toList.map build).map leftDraw')) =
    mergedEval' (rightDraw' r)
  refine Eq.trans ?_ hc.symm
  refine (framed_sum (splitBottom a b c) (mergeTop d e f) _).trans ?_
  rw [List.map_map, List.map_map]
  have hmap : coeff.support.attach.toList.map (mergedEval' ∘ leftDraw' ∘ build) =
      coeff.support.attach.toList.map (fun p => coeff p.1 • qstar p.1) :=
    List.map_congr_left (fun p _ => hbuild p)
  change (coeff.support.attach.toList.map (mergedEval' ∘ leftDraw' ∘ build)).sum = _
  rw [hmap, Finset.sum_map_toList]
  exact Finset.sum_attach coeff.support (fun p => coeff p • qstar p)

-- Collect coincident lower parameters inside the one marked projection.
-- Linearity identifies the collected label with the supplier's termwise list.
private theorem singleCaseTwo (hd : Subgroup.FiniteIndex ((de').toHom.range)) :
    ∀ r : RD, ∃ l : LD, leftEval' l = rightEval' r := by
  intro r
  obtain ⟨coeff, hc, _⟩ := rightCoefficients a b c d e f r
  obtain ⟨drawing, hshape, he⟩ := (CaseTwoLeftProjectionConstruction a b c d e f).2.1 hd coeff
  obtain ⟨x, y, z, _, _, _, _, rfl⟩ := hshape
  let cf := c.comp f
  let t := MackeyDiagrams.ConjEmbedding.id E
  let l : LD := ⟨E, de', cf, t, Finsupp.mapDomain x coeff, Finsupp.single y 1, Finsupp.single z 1⟩
  let value := fun xs => mergedEval' (leftTerm' de' cf t xs [(1, y)] [(1, z)])
  let unitValue := fun p => value [(1, p)]
  have heval : mergedEval' (leftDraw' l) = value (labelTerms (Finsupp.mapDomain x coeff)) := by
    change mergedEval' (leftTerm' de' cf t _ (labelTerms (Finsupp.single y 1))
      (MackeyDiagrams.DotLabel.terms (Finsupp.single z 1))) = _
    rw [show labelTerms (Finsupp.single y (1 : Complex)) = [(1, y)] from
      terms_single y one_ne_zero,
      show MackeyDiagrams.DotLabel.terms (Finsupp.single z (1 : Complex)) = [(1, z)] from
        terms_single z one_ne_zero]
  have hcollect : value (labelTerms (Finsupp.mapDomain x coeff)) =
      value ((labelTerms coeff).map (fun term => (term.1, x term.2))) := by
    calc
      _ = weighted unitValue (labelTerms (Finsupp.mapDomain x coeff)) :=
        leftWeighted a b c d e f de' cf t _ _ _
      _ = Finsupp.linearCombination Complex (unitValue ∘ x) coeff := by
        rw [weighted_labelTerms, Finsupp.linearCombination_mapDomain]
      _ = weighted (unitValue ∘ x) (labelTerms coeff) :=
        (weighted_labelTerms _ _).symm
      _ = weighted unitValue ((labelTerms coeff).map (fun term => (term.1, x term.2))) := by
        simp only [weighted, List.map_map, Function.comp_def]
      _ = _ := (leftWeighted a b c d e f de' cf t _ _ _).symm
  exact ⟨l, (merged_eq_iff a b c d e f _ _).1 (heval.trans (hcollect.trans (he.trans hc.symm)))⟩
private theorem evaluationClasses (h : ((de').toHom.range).FiniteIndex ∨ Finite G) :
    ∃ (lr : LD → RD) (rl : RD → LD)
      (q : Quotient (Setoid.ker leftEval') ≃ Quotient (Setoid.ker rightEval')),
      (∀ l, rightEval' (lr l) = leftEval' l ∧ q (Quotient.mk _ l) = Quotient.mk _ (lr l)) ∧
      (∀ r, leftEval' (rl r) = rightEval' r ∧ q.symm (Quotient.mk _ r) = Quotient.mk _ (rl r)) := by
  have hd : ((de').toHom.range).FiniteIndex := by
    rcases h with h | h
    · exact h
    · exact @Subgroup.finiteIndex_of_finite G _ _ h
  have hle : (de').toHom.range ≤ d.toHom.range := by
    rintro g ⟨v, hv⟩
    exact ⟨e.toHom v, hv⟩
  exact quotientReplacement leftEval' rightEval'
    (singleCaseOne a b c d e f (@Subgroup.finiteIndex_of_le G _ _ _ hd hle))
    (singleCaseTwo a b c d e f hd)

end
end ReplacementForTwoProjectionsAux

theorem ReplacementForTwoProjections : (
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let ade := comp a de
  let bcf := comp bc f
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : Drawing) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let mergedEval := fun (drawing : Drawing) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let Parameter := ProjectionLabel a bc de f
  let Q := fun (p : MackeyDiagrams.Dot ade bcf) (w : (MackeyDiagrams.Word.basis mergedTop).carrier) =>
    MackeyDiagrams.Generator.mixedProduct a bc
      (MackeyDiagrams.Generator.mixedMultiplicationBasis a bc de f p w)
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let intersection := fun (p : MackeyDiagrams.Dot ade bcf) =>
    MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a) ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (MackeyDiagrams.Dot.element p)))
        (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom bc))
  let lower := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom ade)
  let terms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let finiteFibers := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.Dot (comp α η) (comp β θ)) =>
    ∀ z, Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ x w = z}
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : List (Complex × ProjectionLabel a b r s))
      (ys : List (Complex × ProjectionLabel s c t f))
      (zs : List (Complex × MackeyDiagrams.Dot (comp r t) de)) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s xs) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (down f))))
  let right := fun {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : List (Complex × MackeyDiagrams.Dot bc (comp j w)))
      (ms : List (Complex × ProjectionLabel a j d v))
      (ns : List (Complex × ProjectionLabel v w e f)) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c j w ells))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d v ms) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f ns)))
  let Left := Σ B : Subgroup U,
    Σ r : MackeyDiagrams.ConjEmbedding B G,
    Σ s : MackeyDiagrams.ConjEmbedding B D,
    Σ t : MackeyDiagrams.ConjEmbedding E B,
      Finsupp (ProjectionLabel a b r s) Complex ×
      Finsupp (ProjectionLabel s c t f) Complex ×
      MackeyDiagrams.DotLabel Complex (comp r t) de
  let Right := Σ B' : Subgroup U,
    Σ j : MackeyDiagrams.ConjEmbedding B' A,
    Σ v : MackeyDiagrams.ConjEmbedding C B',
    Σ w : MackeyDiagrams.ConjEmbedding F B',
      MackeyDiagrams.DotLabel Complex bc (comp j w) ×
      Finsupp (ProjectionLabel a j d v) Complex ×
      Finsupp (ProjectionLabel v w e f) Complex
  let leftDrawing : Left → Drawing :=
    fun ⟨_, r, s, t, xs, ys, zs⟩ =>
      left r s t (terms xs) (terms ys) (MackeyDiagrams.DotLabel.terms zs)
  let rightDrawing : Right → Drawing :=
    fun ⟨_, j, v, w, ells, ms, ns⟩ =>
      right j v w (MackeyDiagrams.DotLabel.terms ells) (terms ms) (terms ns)
  let sumDrawings := fun (ds : List Drawing) =>
    match ds with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let conjugatedImage := fun (p : Parameter) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj
      (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p))))
      (MonoidHom.range (hom bc))
  let join := fun (p : Parameter) => MonoidHom.range (hom ad) ⊔ conjugatedImage p
  let middleFinite := fun (p : Parameter) =>
    Subgroup.FiniteIndex (Subgroup.subgroupOf (MonoidHom.range (hom ad))
      (MonoidHom.range (hom a) ⊓ join p))
  let expansion := fun (coeff : Finsupp Parameter Complex) =>
    Finsupp.sum coeff (fun p weight => weight • Qstar p)
  let leftEval := fun l : Left => eval (leftDrawing l)
  let rightEval := fun r : Right => eval (rightDrawing r)
  let leftClasses := Setoid.ker leftEval
  let rightClasses := Setoid.ker rightEval
  (∀ p : MackeyDiagrams.Dot ade bcf,
    lower ≤ intersection p ∧
    (finiteFibers a bc de f p ↔ Subgroup.FiniteIndex (Subgroup.subgroupOf lower (intersection p))) ∧
    (∀ (g : G) (h : F),
      Q p (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction de)
          (MackeyDiagrams.Biset.restriction f) g h) =
        MackeyDiagrams.ConjEmbedding.toHom a g * MackeyDiagrams.Dot.element p *
          MackeyDiagrams.ConjEmbedding.toHom bc h)) ∧
  (∀ (p : Parameter) (z : A),
    Qstar p (Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc z) 1) =
      Finset.sum (Set.Finite.toFinset (MackeyDiagrams.ProjectionDot.finite p (MackeyDiagrams.Generator.mixedPair a bc z)))
        (fun w => Finsupp.single w 1) ∧
    (z ∈ Set.range (Q (MackeyDiagrams.ProjectionDot.dot p)) →
      Nat.card {w : (MackeyDiagrams.Word.basis mergedTop).carrier // Q (MackeyDiagrams.ProjectionDot.dot p) w = z} =
        Subgroup.relIndex lower (intersection (MackeyDiagrams.ProjectionDot.dot p)))) ∧
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (x : ProjectionLabel a b r s) (y : ProjectionLabel s c t f)
      (z : MackeyDiagrams.Dot (comp r t) de),
    ∃! p : Parameter, mergedEval (left r s t [(1, x)] [(1, y)] [(1, z)]) = Qstar p) ∧
  (∀ {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ell : MackeyDiagrams.Dot bc (comp j w)) (m : ProjectionLabel a j d v)
      (n : ProjectionLabel v w e f),
    ∃! p : Parameter, mergedEval (right j v w [(1, ell)] [(1, m)] [(1, n)]) = Qstar p) ∧
  (∀ l : Left, ∃ coeff : Finsupp Parameter Complex,
    mergedEval (leftDrawing l) = expansion coeff ∧
    (∀ other : Finsupp Parameter Complex,
      mergedEval (leftDrawing l) = expansion other → other = coeff) ∧
    ((∃ ds : List Right, eval (sumDrawings (List.map rightDrawing ds)) = leftEval l) ↔
      ∀ p ∈ Finsupp.support coeff, middleFinite p)) ∧
  (∀ r : Right, ∃! coeff : Finsupp Parameter Complex,
    mergedEval (rightDrawing r) = expansion coeff) ∧
  (∀ p : Parameter, middleFinite p →
    ∃ r : Right, mergedEval (rightDrawing r) = Qstar p) ∧
  (Subgroup.FiniteIndex (MonoidHom.range (hom d)) →
    ∀ l : Left, ∃ r : Right, rightEval r = leftEval l) ∧
  (∀ r : Right, ∃ ds : List Left, eval (sumDrawings (List.map leftDrawing ds)) = rightEval r) ∧
  (Subgroup.FiniteIndex (MonoidHom.range (hom de)) →
    ∀ r : Right, ∃ l : Left, leftEval l = rightEval r) ∧
  (Subgroup.FiniteIndex (MonoidHom.range (hom de)) ∨ Finite G →
    ∃ (replaceCase1 : Left → Right) (replaceCase2 : Right → Left)
      (replacement : Quotient leftClasses ≃ Quotient rightClasses),
      (∀ l : Left, rightEval (replaceCase1 l) = leftEval l ∧
        replacement (Quotient.mk leftClasses l) = Quotient.mk rightClasses (replaceCase1 l)) ∧
      (∀ r : Right, leftEval (replaceCase2 r) = rightEval r ∧
        Equiv.symm replacement (Quotient.mk rightClasses r) =
          Quotient.mk leftClasses (replaceCase2 r)))
) :=
(by
  classical
  intro U inst G A D F C E a b c d e f up down tensor comp hom bc ad de ade bcf
    bottom top mergedBottom mergedTop Drawing drawId splitBottom mergeTop eval mergedEval
    atRight ProjectionLabel Parameter Q Qstar intersection lower terms finiteFibers left right
    Left Right leftDrawing rightDrawing sumDrawings conjugatedImage join middleFinite expansion
    leftEval rightEval leftClasses rightClasses
  -- Xiao, §6.2.1, Lemma 6.3 and Theorem 6.4, archived original pp. 22–23
  -- (bc57d137…) and revised published PDF pp. 24–25 (6d7e8859…).
  -- Alphabeta Math numbers the replacement directions as Theorem 6.4(1)
  -- and (2), with the constructions and the quotient argument in prose.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#thm:three-projections
  obtain ⟨hindex, hfibers, hleft, hright⟩ := EvaluationForTwoProjections a b c d e f
  have sum_eq (ds : List Drawing) : sumDrawings ds = ReplacementForTwoProjectionsAux.drawSum ds := by
    cases ds <;> rfl
  refine ⟨hindex, hfibers, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B r s t x y z
    exact (hleft r s t).1 x y z
  · intro B' j v w ell m n
    exact (hright j v w).1 ell m n
  -- Step 1 (Theorem 6.4(1)). The join construction and finite-sum
  -- criterion use their original middle-index hypothesis. The merge
  -- and split inverses transport equality to the fixed boundary.
  · intro l
    obtain ⟨coeff, hc, hu⟩ := ReplacementForTwoProjectionsAux.leftCoefficients a b c d e f l
    refine ⟨coeff, hc, hu, ?_⟩
    refine Iff.trans ?_ (ReplacementForTwoProjectionsAux.caseOne a b c d e f l coeff hc)
    constructor
    · rintro ⟨ds, he⟩
      exact ⟨ds, (congrArg eval (sum_eq (ds.map rightDrawing))).symm.trans he⟩
    · rintro ⟨ds, he⟩
      exact ⟨ds, (congrArg eval (sum_eq (ds.map rightDrawing))).trans he⟩
  · exact ReplacementForTwoProjectionsAux.rightCoefficients a b c d e f
  · exact ReplacementForTwoProjectionsAux.singleRight a b c d e f
  · exact ReplacementForTwoProjectionsAux.singleCaseOne a b c d e f
  -- Step 2 (Theorem 6.4(2)). The full intersection gives one left term
  -- per supported parameter. The common group under finite index lets
  -- those coefficients share one lower mark.
  · intro r
    obtain ⟨ds, he⟩ := ReplacementForTwoProjectionsAux.caseTwo a b c d e f r
    exact ⟨ds, (congrArg eval (sum_eq (ds.map leftDrawing))).trans he⟩
  · exact ReplacementForTwoProjectionsAux.singleCaseTwo a b c d e f
  -- Step 3 (Theorem 6.4, final paragraph). Apply both single replacements
  -- and descend them to the quotient by evaluation. The index of the
  -- image of de supplies finite index for the larger image of d.
  · exact ReplacementForTwoProjectionsAux.evaluationClasses a b c d e f)
