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
  let conjugated := bc'.toHom.range.map (MulAut.conj p.dot.element).toMonoidHom
  (ad'.toHom.range.subgroupOf (a.toHom.range ⊓ (ad'.toHom.range ⊔ conjugated))).FiniteIndex

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
