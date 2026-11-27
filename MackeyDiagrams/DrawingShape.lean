import MackeyDiagrams.ParallelDown
import MackeyDiagrams.ParallelDotChain
import MackeyDiagrams.ProjectionDotChain
import MackeyDiagrams.Replacement
import MackeyDiagrams.RightCurlLabels
import MackeyDiagrams.Trivalent

/-! Record the oriented drawing separately from its group labels and evaluation.
A straight mixed vertex and its expanded presentation can have different drawings. -/

namespace MackeyDiagrams

universe u v

inductive VertexKind where
  | upDot | downDot | algebraUpDot | linearDownDot
  | mergeUp | splitUp | mergeDown | splitDown
  | multiplicationCap | traceCap | ordinaryCup | reverseCup
  | mixedMultiplication | mixedProjection | parallelUp | parallelDown
  | expandedMixedProjection (opening : ProjectionOpening) (closing : ProjectionClosing)
  | expandedProjectionChain (dotCount : Nat) (opening : ProjectionOpening) (closing : ProjectionClosing)
  | rightCurlUp
  | parallelUpChain (dotCount : Nat) | parallelDownChain (dotCount : Nat)
  | bentMultiplicationCap | bentOrdinaryCup | bentTraceCap | bentReverseCup | bentTraceCapOnLeft
  | trivalent (kind : TrivalentKind)
  deriving DecidableEq, Repr

inductive DrawingShape where
  | straight (directions : List Bool)
  | vertex (kind : VertexKind)
  | vertical (below above : DrawingShape)
  | horizontal (left right : DrawingShape)
  | zero (bottom top : List Bool)
  | add (left right : DrawingShape)
  | scale (shape : DrawingShape)
  deriving DecidableEq, Repr

namespace DrawingShape

/-- Association and empty factors contribute no visible vertices. -/
def stack : DrawingShape → DrawingShape → DrawingShape
  | .straight _, above => above
  | below, .straight _ => below
  | .vertical first rest, above => .vertical first (stack rest above)
  | below, above => .vertical below above

def juxtapose : DrawingShape → DrawingShape → DrawingShape
  | .straight [], right => right
  | left, .straight [] => left
  | .straight l, .straight r => .straight (l ++ r)
  | .horizontal first rest, right => .horizontal first (juxtapose rest right)
  | left, right => .horizontal left right

end DrawingShape

variable {U : Type u} [Group U] {K H : Subgroup U}



def Word.directions : {K H : Subgroup U} → Word K H → List Bool
  | _, _, .empty _ => []
  | _, _, .up _ => [true]
  | _, _, .down _ => [false]
  | _, _, .tensor p q => p.directions ++ q.directions

def Diagram.drawing {R : Type v} :
    {K H : Subgroup U} → {p q : Word K H} → Diagram R p q → DrawingShape
  | _, _, _, _, .id p => .straight p.directions
  | _, _, _, _, .upDot _ => .vertex .upDot
  | _, _, _, _, .downDot _ => .vertex .downDot
  | _, _, _, _, .mergeUp _ _ => .vertex .mergeUp
  | _, _, _, _, .splitUp _ _ => .vertex .splitUp
  | _, _, _, _, .mergeDown _ _ => .vertex .mergeDown
  | _, _, _, _, .splitDown _ _ => .vertex .splitDown
  | _, _, _, _, .multiplicationCap _ => .vertex .multiplicationCap
  | _, _, _, _, .traceCap _ => .vertex .traceCap
  | _, _, _, _, .ordinaryCup _ => .vertex .ordinaryCup
  | _, _, _, _, .reverseCup _ _ => .vertex .reverseCup
  | _, _, _, _, .mixedMultiplication _ _ _ _ _ => .vertex .mixedMultiplication
  | _, _, _, _, .mixedProjection _ _ _ _ _ _ => .vertex .mixedProjection
  | _, _, _, _, .leftUnit p => .straight p.directions
  | _, _, _, _, .rightUnit p => .straight p.directions
  | _, _, _, _, .insertLeftUnit p => .straight p.directions
  | _, _, _, _, .insertRightUnit p => .straight p.directions
  | _, _, _, _, .associate p q r => .straight (p.directions ++ q.directions ++ r.directions)
  | _, _, _, _, .unassociate p q r => .straight (p.directions ++ q.directions ++ r.directions)
  | _, _, _, _, .vertical d e => d.drawing.stack e.drawing
  | _, _, _, _, .horizontal d e => d.drawing.juxtapose e.drawing
  | _, _, _, _, .zero p q => .zero p.directions q.directions
  | _, _, _, _, .add d e => .add d.drawing e.drawing
  | _, _, _, _, .scale _ d => .scale d.drawing

def BentVertex.kind {p q : Word K H} : BentVertex p q → VertexKind
  | .multiplicationCap _ _ => .bentMultiplicationCap
  | .ordinaryCup _ _ => .bentOrdinaryCup
  | .traceCap _ _ => .bentTraceCap
  | .reverseCup _ _ _ => .bentReverseCup

/-- The exact local index condition belongs to the projection label. -/
structure ProjectionDot (a : ConjEmbedding K H) (b : ConjEmbedding K H)
    {X Y : Type u} (multiplication : Dot a b → X → Y) where
  dot : Dot a b
  finite : ∀ y, Set.Finite {x | multiplication dot x = y}

namespace ProjectionDot

abbrev Mixed {J F : Subgroup U}
    (a : ConjEmbedding K J) (b : ConjEmbedding H J)
    (l : ConjEmbedding F K) (r : ConjEmbedding F H) :=
  ProjectionDot (a.comp l) (b.comp r) (Generator.mixedMultiplicationBasis a b l r)

end ProjectionDot

/-- The dot in a right curl has the same finite, termwise-eligible label as
every other dot. Keep the weighted mark inside the actual cup/cap composite. -/
def ScopedDiagram.linearRightCurlUp {R : Type v} [CommSemiring R]
    {A B C : Subgroup U} (inner : ConjEmbedding A B)
    {a b : ConjEmbedding B C}
    (label : List (R × Dot (a.comp inner) (b.comp inner)))
    (finite : inner.toHom.range.FiniteIndex) : ScopedDiagram R (.up a) (.up b) :=
  .vertical (.bentVertex (.reverseCup a inner finite))
    (.vertical (.horizontal (.weightedUpDot label) (.ordinary (.id (.down inner))))
      (.bentVertex (.multiplicationCap b inner)))

/-- Typed labellings of the basic drawings. A scope with an infinite-index
cup is admitted here only through the prescribed expanded projection. -/
inductive LabelledDrawing (R : Type v) [CommSemiring R] :
    {K H : Subgroup U} → Word K H → Word K H → Type (max u v)
  | ordinary {K H : Subgroup U} {p q : Word K H} (d : Diagram R p q) : LabelledDrawing R p q
  | upDot {A B : Subgroup U} {a b : ConjEmbedding A B}
      (label : List (R × Dot a b)) : LabelledDrawing R (.up a) (.up b)
  | downDot {A B : Subgroup U} {a b : ConjEmbedding A B}
      (label : List (R × Dot a b)) : LabelledDrawing R (.down a) (.down b)
  | trivalent {K H : Subgroup U} {p q : Word K H}
      (vertex : TrivalentVertex p q) : LabelledDrawing R p q
  | parallelUp {K H H' G : Subgroup U}
      (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
      (label : List (R × Dot (b.comp a) (b'.comp a'))) :
      LabelledDrawing R ((Word.up b).tensor (.up a)) ((Word.up b').tensor (.up a'))
  | parallelDown {K H H' G : Subgroup U}
      (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
      (label : List (R × Dot (b.comp a) (b'.comp a'))) :
      LabelledDrawing R ((Word.down a).tensor (.down b)) ((Word.down a').tensor (.down b'))
  | parallelUpChain {K H H' G : Subgroup U}
      (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
      (labels : LinearDotChain R (b.comp a) (b'.comp a')) :
      LabelledDrawing R ((Word.up b).tensor (.up a)) ((Word.up b').tensor (.up a'))
  | parallelDownChain {K H H' G : Subgroup U}
      (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
      (labels : LinearDotChain R (b.comp a) (b'.comp a')) :
      LabelledDrawing R ((Word.down a).tensor (.down b)) ((Word.down a').tensor (.down b'))
  | mixedMultiplication {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
      (r : ConjEmbedding L H) (label : List (R × Dot (a.comp l) (b.comp r))) :
      LabelledDrawing R ((Word.up l).tensor (.down r)) ((Word.down a).tensor (.up b))
  | rightCurlUp {K H G : Subgroup U}
      (inner : ConjEmbedding K H) {a b : ConjEmbedding H G}
      (label : List (R × Dot (a.comp inner) (b.comp inner)))
      (finite : inner.toHom.range.FiniteIndex) :
      LabelledDrawing R (.up a) (.up b)
  | bentVertex {K H : Subgroup U} {p q : Word K H} (b : BentVertex p q) : LabelledDrawing R p q
  | expandedProjection {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
      (r : ConjEmbedding L H) (label : List (R × ProjectionDot.Mixed a b l r))
      (opening : ProjectionOpening) (closing : ProjectionClosing) :
      LabelledDrawing R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | expandedProjectionChain {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
      (r : ConjEmbedding L H) (chain : DotChain (b.comp r) (a.comp l))
      (finite : ∀ x, Set.Finite {w |
        Generator.mixedMultiplicationBasis a b l r chain.product.inverse w = x})
      (opening : ProjectionOpening) (closing : ProjectionClosing) :
      LabelledDrawing R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | expandedLinearDotProjection {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
      (r : ConjEmbedding L H) (chain : LinearDotChain R (b.comp r) (a.comp l))
      (finite : ∀ term ∈ chain.terms, ∀ x, Set.Finite {w |
        Generator.mixedMultiplicationBasis a b l r term.2.product.inverse w = x})
      (opening : ProjectionOpening) (closing : ProjectionClosing) :
      LabelledDrawing R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | compactProjection {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
      (r : ConjEmbedding L H) (label : List (R × ProjectionDot.Mixed a b l r)) :
      LabelledDrawing R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | add {K H : Subgroup U} {p q : Word K H}
      (left right : LabelledDrawing R p q) : LabelledDrawing R p q
  | scale {K H : Subgroup U} {p q : Word K H}
      (coefficient : R) (term : LabelledDrawing R p q) : LabelledDrawing R p q
  | vertical {K H : Subgroup U} {p q t : Word K H}
      (below : LabelledDrawing R p q) (above : LabelledDrawing R q t) : LabelledDrawing R p t
  | horizontal {K H J : Subgroup U} {p p' : Word K H} {q q' : Word H J}
      (left : LabelledDrawing R p p') (right : LabelledDrawing R q q') :
      LabelledDrawing R (p.tensor q) (p'.tensor q')

namespace LabelledDrawing

variable {R : Type v} [CommSemiring R] {p q : Word K H}



noncomputable def interpret :
    {K H : Subgroup U} → {p q : Word K H} → LabelledDrawing R p q → ScopedDiagram R p q
  | _, _, _, _, .ordinary d => .ordinary d
  | _, _, _, _, .upDot label => .weightedUpDot label
  | _, _, _, _, .downDot label => .weightedDownDot label
  | _, _, _, _, .trivalent vertex => .ordinary vertex.expand
  | _, _, _, _, .parallelUp b a b' a' label => .linearCombination <| label.map fun (c, d) =>
    (c, .ordinary (.parallelUp b a b' a' d))
  | _, _, _, _, .parallelDown b a b' a' label => .linearCombination <| label.map fun (c, d) =>
    (c, .ordinary (.parallelDown b a b' a' d))
  | _, _, _, _, .parallelUpChain b a b' a' labels =>
    .vertical (.ordinary (.mergeUp b a)) (.vertical labels.upDrawing (.ordinary (.splitUp b' a')))
  | _, _, _, _, .parallelDownChain b a b' a' labels =>
    .vertical (.ordinary (.mergeDown b a)) (.vertical labels.downDrawing (.ordinary (.splitDown b' a')))
  | _, _, _, _, .mixedMultiplication a b l r label => .linearCombination <| label.map fun (c, d) =>
    (c, .ordinary (.mixedMultiplication a b l r d))
  | _, _, _, _, .rightCurlUp inner label finite => .linearRightCurlUp inner label finite
  | _, _, _, _, .bentVertex d => .bentVertex d
  | _, _, _, _, .expandedProjection a b l r label opening closing =>
    .expandedProjectionFrame a b l r opening closing <| .linearCombination <| label.map fun (c, e) =>
      (c, .expandedMixedProjectionOfFinite a b l r e.dot e.finite)
  | _, _, _, _, .expandedLinearDotProjection a b l r chain finite opening closing =>
    .expandedProjectionFrame a b l r opening closing (.expandedLinearDotProjection a b l r chain finite)
  | _, _, _, _, .expandedProjectionChain a b l r chain finite opening closing =>
    .expandedProjectionFrame a b l r opening closing (.expandedProjectionChain a b l r chain finite)
  | _, _, _, _, .compactProjection a b l r label => .linearCombination <| label.map fun (c, e) =>
    (c, .ordinary (.mixedProjection a b l r e.dot e.finite))
  | _, _, _, _, .add d e => .add d.interpret e.interpret
  | _, _, _, _, .scale c d => .scale c d.interpret
  | _, _, _, _, .vertical d e => .vertical d.interpret e.interpret
  | _, _, _, _, .horizontal d e => .horizontal d.interpret e.interpret

def erase :
    {K H : Subgroup U} → {p q : Word K H} → LabelledDrawing R p q → DrawingShape
  | _, _, _, _, .ordinary d => d.drawing
  | _, _, _, _, .upDot _ => .vertex .upDot
  | _, _, _, _, .downDot _ => .vertex .downDot
  | _, _, _, _, .trivalent vertex => .vertex (.trivalent vertex.kind)
  | _, _, _, _, .parallelUp _ _ _ _ _ => .vertex .parallelUp
  | _, _, _, _, .parallelDown _ _ _ _ _ => .vertex .parallelDown
  | _, _, _, _, .parallelUpChain _ _ _ _ labels => .vertex (.parallelUpChain labels.length)
  | _, _, _, _, .parallelDownChain _ _ _ _ labels => .vertex (.parallelDownChain labels.length)
  | _, _, _, _, .mixedMultiplication _ _ _ _ _ => .vertex .mixedMultiplication
  | _, _, _, _, .rightCurlUp _ _ _ => .vertex .rightCurlUp
  | _, _, _, _, .bentVertex b => .vertex b.kind
  | _, _, _, _, .expandedProjection _ _ _ _ _ opening closing => .vertex (.expandedMixedProjection opening closing)
  | _, _, _, _, .expandedProjectionChain _ _ _ _ chain _ opening closing =>
    .vertex (.expandedProjectionChain chain.length opening closing)
  | _, _, _, _, .expandedLinearDotProjection _ _ _ _ chain _ opening closing =>
    .vertex (.expandedProjectionChain chain.length opening closing)
  | _, _, _, _, .compactProjection _ _ _ _ _ => .vertex .mixedProjection
  | _, _, _, _, .add d e => .add d.erase e.erase
  | _, _, _, _, .scale _ d => .scale d.erase
  | _, _, _, _, .vertical d e => d.erase.stack e.erase
  | _, _, _, _, .horizontal d e => d.erase.juxtapose e.erase

end LabelledDrawing

namespace DrawingShape

def upwardDots : Nat → DrawingShape
  | 0 => .straight [true]
  | n+1 => (DrawingShape.vertex .upDot).stack (upwardDots n)

def downwardDots : Nat → DrawingShape
  | 0 => .straight [false]
  | n+1 => (DrawingShape.vertex .downDot).stack (downwardDots n)

/-- The geometric stages of the expanded Mackey projection. -/
def expandedProjectionGeometry (dotCount : Nat)
    (opening : ProjectionOpening) (closing : ProjectionClosing) : DrawingShape :=
  let start : DrawingShape := match opening with
    | .junction => .horizontal (.straight [false]) (.vertex .bentReverseCup)
    | .cupAndMerge =>
      (DrawingShape.horizontal (.straight [false, true]) (.vertex .reverseCup)).stack
        (.horizontal (.straight [false]) (.horizontal (.vertex .mergeUp) (.straight [false])))
  let close : DrawingShape := match closing with
    | .junction => .horizontal (.vertex .bentTraceCapOnLeft) (.straight [false])
    | .splitAndTrace =>
      (DrawingShape.horizontal (.straight [false])
        (.horizontal (.vertex .splitUp) (.straight [false]))).stack
        (.horizontal (.vertex .traceCap) (.straight [true, false]))
  start.stack
      ((DrawingShape.horizontal (.straight [false]) (.horizontal (upwardDots dotCount) (.straight [false]))).stack
        close)

def rightCurlGeometry : DrawingShape :=
  (DrawingShape.vertex .bentReverseCup).stack
    ((DrawingShape.horizontal (.vertex .upDot) (.straight [false])).stack
      (.vertex .bentMultiplicationCap))

/-- Forget the allowed label sort at a dot while retaining the visible mark. -/
def geometry : DrawingShape → DrawingShape
  | .vertex .algebraUpDot => .vertex .upDot
  | .vertex .linearDownDot => .vertex .downDot
  | .vertex .rightCurlUp => rightCurlGeometry
  | .vertex (.parallelUpChain count) =>
    (DrawingShape.vertex .mergeUp).stack ((upwardDots count).stack (.vertex .splitUp))
  | .vertex (.parallelDownChain count) =>
    (DrawingShape.vertex .mergeDown).stack ((downwardDots count).stack (.vertex .splitDown))
  | .vertex (.expandedMixedProjection opening closing) => expandedProjectionGeometry 1 opening closing
  | .vertex (.expandedProjectionChain count opening closing) => expandedProjectionGeometry count opening closing
  | .vertical below above => below.geometry.stack above.geometry
  | .horizontal left right => left.geometry.juxtapose right.geometry
  | .add left right => .add left.geometry right.geometry
  | .scale d => .scale d.geometry
  | s => s

end DrawingShape

namespace LabelledDrawing

variable {R : Type v} [CommSemiring R]

section
variable {p q : Word K H}

/-- A fixed drawing receives all typed labellings which erase to it at these words. -/
def Labellings (R : Type v) [CommSemiring R] (p q : Word K H) (s : DrawingShape) :=
  {d : LabelledDrawing R p q // d.erase.geometry = s.geometry}

/-- A checked instance of the replacement relation with the entire syntactic fiber. -/
theorem replaces_iff_at_word {s t : DrawingShape} :
    (∀ d : Labellings R p q s, ∃ e : Labellings R p q t,
        d.val.interpret.eval = e.val.interpret.eval) ↔
      Set.range (fun d : Labellings R p q s => d.val.interpret.eval) ⊆
        Set.range (fun e : Labellings R p q t => e.val.interpret.eval) :=
  ScopedDiagram.replaces_iff_attainable_subset
    (fun a (d : Labellings R p q a) => d.val.interpret) s t

end

structure AtBoundary (R : Type v) [CommSemiring R]
    (p q : Boundary K H) (s : DrawingShape) where
  bottom : Word K H
  top : Word K H
  diagram : LabelledDrawing R bottom top
  bottom_eq : bottom.boundary = p
  top_eq : top.boundary = q
  shape_eq : diagram.erase.geometry = s.geometry

noncomputable def AtBoundary.interpret {p q : Boundary K H} {s : DrawingShape}
    (label : AtBoundary R p q s) : ScopedDiagram R p.word q.word := by
  obtain ⟨bottom,top,diagram,hbottom,htop,_⟩ := label
  subst p
  subst q
  exact diagram.interpret.atBoundary

/-- Keeping a linear label on the same crossing preserves evaluation when it is expanded. -/
theorem eval_expandProjection {A B G L : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding B G) (l : ConjEmbedding L A)
    (r : ConjEmbedding L B) (label : List (R × ProjectionDot.Mixed a b l r))
    (opening : ProjectionOpening) (closing : ProjectionClosing) :
    (expandedProjection a b l r label opening closing).interpret.eval =
      (compactProjection a b l r label).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold interpret
  rw [ScopedDiagram.eval_expandedProjectionFrame,
    ScopedDiagram.eval_linearCombination_apply, ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  obtain ⟨coeff, entry⟩ := term
  change coeff • ((ScopedDiagram.expandedMixedProjectionOfFinite a b l r
        entry.dot entry.finite).eval.toLinearMap x) =
    coeff • ((Diagram.mixedProjection a b l r entry.dot entry.finite).eval.toLinearMap x)
  rw [ScopedDiagram.eval_expandedMixedProjection]

theorem eval_expandedProjection_opening {A B G L : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding B G) (l : ConjEmbedding L A)
    (r : ConjEmbedding L B) (label : List (R × ProjectionDot.Mixed a b l r))
    (closing : ProjectionClosing) :
    (expandedProjection a b l r label .junction closing).interpret.eval =
      (expandedProjection a b l r label .cupAndMerge closing).interpret.eval :=
  (eval_expandProjection a b l r label .junction closing).trans
    (eval_expandProjection a b l r label .cupAndMerge closing).symm

theorem eval_expandedProjection_closing {A B G L : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding B G) (l : ConjEmbedding L A)
    (r : ConjEmbedding L B) (label : List (R × ProjectionDot.Mixed a b l r))
    (opening : ProjectionOpening) :
    (expandedProjection a b l r label opening .junction).interpret.eval =
      (expandedProjection a b l r label opening .splitAndTrace).interpret.eval :=
  (eval_expandProjection a b l r label opening .junction).trans
    (eval_expandProjection a b l r label opening .splitAndTrace).symm

/-- All admissible syntactic labellings at each fixed ordered boundary are used. -/
def Replaces (R : Type v) [CommSemiring R] (s t : DrawingShape) : Prop :=
  ∀ (A B : Subgroup U) (p q : Boundary A B),
    ScopedDiagram.Replaces (fun v (label : AtBoundary R p q v) => label.interpret) s t

theorem replaces_iff_attainable_subset (s t : DrawingShape) :
    Replaces (U := U) R s t ↔
    ∀ (A B : Subgroup U) (p q : Boundary A B),
      ScopedDiagram.attainable (fun v (label : AtBoundary R p q v) => label.interpret) s ⊆
      ScopedDiagram.attainable (fun v (label : AtBoundary R p q v) => label.interpret) t := by
  constructor
  · intro h A B p q
    exact (ScopedDiagram.replaces_iff_attainable_subset _ _ _).mp (h A B p q)
  · intro h A B p q
    exact (ScopedDiagram.replaces_iff_attainable_subset _ _ _).mpr (h A B p q)

theorem replaces_refl (s : DrawingShape) : Replaces (U := U) R s s :=
  fun _ _ _ _ => ScopedDiagram.replaces_refl _ _

theorem replaces_trans {s t w : DrawingShape}
    (h : Replaces (U := U) R s t) (k : Replaces (U := U) R t w) :
    Replaces (U := U) R s w :=
  fun A B p q => ScopedDiagram.replaces_trans _ (h A B p q) (k A B p q)

end LabelledDrawing

end MackeyDiagrams

namespace MackeyDiagrams.LabelledDrawing

universe u v

variable {U : Type u} [Group U] {K H H' G : Subgroup U}
variable {R : Type v} [CommSemiring R]

theorem single_parallelUpChain_geometry
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (labels : List (R × Dot (b.comp a) (b'.comp a')))
    (d : Dot (b.comp a) (b'.comp a')) :
    (parallelUpChain b a b' a' (.cons labels (.empty (b'.comp a')))).erase.geometry =
      (ordinary (Diagram.parallelUp (R := R) b a b' a' d)).erase.geometry := rfl

theorem single_parallelDownChain_geometry
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (labels : List (R × Dot (b.comp a) (b'.comp a')))
    (d : Dot (b.comp a) (b'.comp a')) :
    (parallelDownChain b a b' a' (.cons labels (.empty (b'.comp a')))).erase.geometry =
      (ordinary (Diagram.parallelDown (R := R) b a b' a' d)).erase.geometry := rfl

end MackeyDiagrams.LabelledDrawing
