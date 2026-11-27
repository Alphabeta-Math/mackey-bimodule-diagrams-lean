import MackeyDiagrams.DotLabels

/-! Shapes are ordered oriented wiring, not a choice of evaluation or labelling
rules. Flatten a typed drawing to positioned vertices and quotient by exchanges
of disjoint vertices. Tensor parentheses, identity subdivisions and the height
order of independent operations disappear. Dots retain one visible mark for
every finite linear label. Arithmetic boxes retain their actual scope.

Only this geometric quotient defines shape equality. Reidemeister moves,
dot slides and bend identities are statements about evaluated maps, not
additional shape identifications. -/

namespace MackeyDiagrams

namespace VertexKind

def canonical : VertexKind → VertexKind
  | .algebraUpDot => .upDot
  | .linearDownDot => .downDot
  | .mergeUp => .trivalent .mergeUp
  | .splitUp => .trivalent .splitUp
  | .mergeDown => .trivalent .mergeDown
  | .splitDown => .trivalent .splitDown
  | .bentMultiplicationCap => .trivalent .upDownToUp
  | .bentTraceCap => .trivalent .downUpToDown
  | .bentOrdinaryCup => .trivalent .upToDownUp
  | .bentReverseCup => .trivalent .upToUpDown
  | .bentTraceCapOnLeft => .trivalent .downUpToUp
  | k => k

def inputs : VertexKind → List Bool
  | .upDot | .algebraUpDot | .rightCurlUp => [true]
  | .downDot | .linearDownDot => [false]
  | .mergeUp | .parallelUp | .parallelUpChain _ => [true, true]
  | .splitUp => [true]
  | .mergeDown | .parallelDown | .parallelDownChain _ => [false, false]
  | .splitDown => [false]
  | .multiplicationCap | .mixedMultiplication | .bentMultiplicationCap => [true, false]
  | .traceCap | .mixedProjection | .expandedMixedProjection _ _ |
      .expandedProjectionChain _ _ _ | .bentTraceCap | .bentTraceCapOnLeft => [false, true]
  | .ordinaryCup | .reverseCup => []
  | .bentOrdinaryCup | .bentReverseCup => [true]
  | .trivalent k => k.inputs

def outputs : VertexKind → List Bool
  | .upDot | .algebraUpDot | .rightCurlUp | .mergeUp |
      .bentMultiplicationCap | .bentTraceCapOnLeft => [true]
  | .downDot | .linearDownDot | .mergeDown | .bentTraceCap => [false]
  | .splitUp | .parallelUp | .parallelUpChain _ => [true, true]
  | .splitDown | .parallelDown | .parallelDownChain _ => [false, false]
  | .multiplicationCap | .traceCap => []
  | .ordinaryCup | .mixedMultiplication | .bentOrdinaryCup => [false, true]
  | .reverseCup | .mixedProjection | .expandedMixedProjection _ _ |
      .expandedProjectionChain _ _ _ | .bentReverseCup => [true, false]
  | .trivalent k => k.outputs

end VertexKind

def DrawingShape.inputs : DrawingShape → List Bool
  | .straight ds => ds
  | .vertex k => k.inputs
  | .vertical below _ => below.inputs
  | .horizontal left right => left.inputs ++ right.inputs
  | .zero below _ => below
  | .add left _ => left.inputs
  | .scale body => body.inputs

def DrawingShape.outputs : DrawingShape → List Bool
  | .straight ds => ds
  | .vertex k => k.outputs
  | .vertical _ above => above.outputs
  | .horizontal left right => left.outputs ++ right.outputs
  | .zero _ above => above
  | .add left _ => left.outputs
  | .scale body => body.outputs

inductive PlanarEvent where
  | vertex (position : Nat) (kind : VertexKind)
  | zero (position : Nat) (inputs outputs : List Bool)
  | add (position : Nat) (inputs outputs : List Bool) (left right : List PlanarEvent)
  | scale (position : Nat) (inputs outputs : List Bool) (body : List PlanarEvent)
  deriving Repr

namespace PlanarEvent

def position : PlanarEvent → Nat
  | .vertex p _ | .zero p _ _ | .add p _ _ _ _ | .scale p _ _ _ => p

def place (p : Nat) : PlanarEvent → PlanarEvent
  | .vertex _ k => .vertex p k
  | .zero _ b t => .zero p b t
  | .add _ b t left right => .add p b t left right
  | .scale _ b t body => .scale p b t body

def inputs : PlanarEvent → List Bool
  | .vertex _ k => k.inputs
  | .zero _ b _ | .add _ b _ _ _ | .scale _ b _ _ => b

def outputs : PlanarEvent → List Bool
  | .vertex _ k => k.outputs
  | .zero _ _ t | .add _ _ t _ _ | .scale _ _ t _ => t

end PlanarEvent

namespace PlanarCode

abbrev Code := List PlanarEvent

def shift (n : Nat) (code : Code) : Code := code.map fun e => e.place (n + e.position)

def encode : DrawingShape → Code
  | .straight _ => []
  | .vertex k => [.vertex 0 k.canonical]
  | .vertical below above => encode below ++ encode above
  | .horizontal left right => encode left ++ shift left.outputs.length (encode right)
  | .zero below above => [.zero 0 below above]
  | .add left right => [.add 0 left.inputs left.outputs (encode left) (encode right)]
  | .scale body => [.scale 0 body.inputs body.outputs (encode body)]

/-- Exchange precisely two disjoint events. The position of the right event
changes by the left event's change of arity. No crossing or dot-slide rule
appears here. Boxes may be exchanged with independent events as whole boxes. -/
inductive Equivalent : Code → Code → Prop
  | refl (a) : Equivalent a a
  | symm {a b} : Equivalent a b → Equivalent b a
  | trans {a b c} : Equivalent a b → Equivalent b c → Equivalent a c
  | context (before after) {a b} : Equivalent a b →
      Equivalent (before ++ a ++ after) (before ++ b ++ after)
  | exchange (before after : Code) (i gap : Nat) (left right : PlanarEvent) :
      Equivalent
        (before ++ [left.place i, right.place (i + left.outputs.length + gap)] ++ after)
        (before ++ [right.place (i + left.inputs.length + gap), left.place i] ++ after)
  | scale (i : Nat) (below above : List Bool) {a b : Code} : Equivalent a b →
      Equivalent [.scale i below above a] [.scale i below above b]
  | add (i : Nat) (below above : List Bool) {a b c d : Code} :
      Equivalent a b → Equivalent c d →
      Equivalent [.add i below above a c] [.add i below above b d]

def setoid : Setoid Code where
  r := Equivalent
  iseqv := ⟨Equivalent.refl, Equivalent.symm, Equivalent.trans⟩

theorem length_eq {a b : Code} (h : Equivalent a b) : a.length = b.length := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | context before after _ ih => simp only [List.length_append]; rw [ih]
  | exchange => simp only [List.length_append, List.length_cons, List.length_nil]
  | scale => rfl
  | add => rfl

end PlanarCode

structure PlanarShape where
  bottom : List Bool
  top : List Bool
  wiring : Quotient PlanarCode.setoid

universe u v
variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace LabelledDrawing

def planarShape {p q : Word K H} (d : LabelledDrawing R p q) : PlanarShape where
  bottom := p.directions
  top := q.directions
  wiring := Quotient.mk PlanarCode.setoid (PlanarCode.encode d.erase.geometry)

/-- Shapes at one ordered orientation boundary must come from a typed drawing.
This excludes malformed raw stacks and does not use evaluated map equality. -/
def Shapes (R : Type v) [CommSemiring R] (boundary : List Bool × List Bool) :=
  {s : PlanarShape // ∃ (A B : Subgroup U) (p q : Word A B)
    (d : LabelledDrawing R p q),
    (p.directions, q.directions) = boundary ∧ d.planarShape = s}

theorem Shapes.boundary {boundary : List Bool × List Bool}
    (s : Shapes (U := U) R boundary) : (s.val.bottom, s.val.top) = boundary := by
  obtain ⟨A, B, p, q, d, h, hd⟩ := s.property
  rw [← hd]
  exact h

/-- At one fixed boundary this is the entire fiber of the shared syntax's
geometric erasure. There is no freely supplied labelling family or evaluator. -/
structure PlanarAtBoundary (R : Type v) [CommSemiring R]
    (p q : Boundary K H) (s : PlanarShape) where
  bottom : Word K H
  top : Word K H
  diagram : LabelledDrawing R bottom top
  bottom_eq : bottom.boundary = p
  top_eq : top.boundary = q
  shape_eq : diagram.planarShape = s

noncomputable def PlanarAtBoundary.interpret {p q : Boundary K H} {s : PlanarShape}
    (label : PlanarAtBoundary R p q s) : ScopedDiagram R p.word q.word := by
  obtain ⟨bottom, top, diagram, hbottom, htop, _⟩ := label
  subst p
  subst q
  exact diagram.interpret.atBoundary

def PlanarReplaces (R : Type v) [CommSemiring R] (s t : PlanarShape) : Prop :=
  ∀ (A B : Subgroup U) (p q : Boundary A B),
    ScopedDiagram.Replaces (fun v (label : PlanarAtBoundary R p q v) => label.interpret) s t

theorem planarReplaces_iff_attainable_subset (s t : PlanarShape) :
    PlanarReplaces (U := U) R s t ↔
    ∀ (A B : Subgroup U) (p q : Boundary A B),
      ScopedDiagram.attainable (fun v (label : PlanarAtBoundary R p q v) => label.interpret) s ⊆
      ScopedDiagram.attainable (fun v (label : PlanarAtBoundary R p q v) => label.interpret) t := by
  constructor
  · intro h A B p q
    exact (ScopedDiagram.replaces_iff_attainable_subset _ _ _).mp (h A B p q)
  · intro h A B p q
    exact (ScopedDiagram.replaces_iff_attainable_subset _ _ _).mpr (h A B p q)

theorem planarReplaces_refl (s : PlanarShape) : PlanarReplaces (U := U) R s s :=
  fun _ _ _ _ => ScopedDiagram.replaces_refl _ _

theorem planarReplaces_trans {s t z : PlanarShape}
    (h : PlanarReplaces (U := U) R s t) (k : PlanarReplaces (U := U) R t z) :
    PlanarReplaces (U := U) R s z :=
  fun A B p q => ScopedDiagram.replaces_trans _ (h A B p q) (k A B p q)

/-- The article's relation, restricted to genuine shapes with the same
ordered bottom and top orientations. -/
def ShapeReplaces {boundary : List Bool × List Bool}
    (s t : Shapes (U := U) R boundary) : Prop := PlanarReplaces (U := U) R s.val t.val

theorem shapeReplaces_iff_attainable_subset {boundary : List Bool × List Bool}
    (s t : Shapes (U := U) R boundary) :
    ShapeReplaces s t ↔
    ∀ (A B : Subgroup U) (p q : Boundary A B),
      ScopedDiagram.attainable (fun v (label : PlanarAtBoundary R p q v) => label.interpret) s.val ⊆
      ScopedDiagram.attainable (fun v (label : PlanarAtBoundary R p q v) => label.interpret) t.val :=
  planarReplaces_iff_attainable_subset s.val t.val

theorem shapeReplaces_refl {boundary : List Bool × List Bool}
    (s : Shapes (U := U) R boundary) : ShapeReplaces s s := planarReplaces_refl s.val

theorem shapeReplaces_trans {boundary : List Bool × List Bool}
    {s t z : Shapes (U := U) R boundary} (h : ShapeReplaces s t) (k : ShapeReplaces t z) :
    ShapeReplaces s z := planarReplaces_trans h k

end LabelledDrawing
end MackeyDiagrams
