import MackeyDiagrams.AlgebraDot
import MackeyDiagrams.BentVertices

/-!
# A reverse cup evaluated through its tail

A scope records the actual reverse cup on the right of a word and every typed
operation in its tail. It assigns a map to the whole scope when the tail leaves
finitely many nonzero terms on each input basis vector. The index set may be
infinite. Equivariance is a proof obligation on the resulting basis formula.
-/

namespace MackeyDiagrams

universe u v
noncomputable section

variable {U : Type u} [Group U] {A B K : Subgroup U}
variable {R : Type v} [CommSemiring R]

abbrev reverseCupWord (a : ConjEmbedding A B) : Word B B :=
  (Word.up a).tensor (.down a)

abbrev reverseCupUnitFiber (a : ConjEmbedding A B) :=
  {z : (reverseCupWord a).basis.carrier // Generator.multiplicationCapBasis a z = 1}

namespace RightCupTrace

variable {p q : Word K B} {a : ConjEmbedding A B}

/-- One term is paired with the input and passed through the whole typed tail. -/
def term (tail : Diagram R (p.tensor (reverseCupWord a)) q)
    (x : p.basis.carrier) (i : reverseCupUnitFiber a) : q.basis.carrier →₀ R :=
  tail.eval.toLinearMap (Finsupp.single (p.basis.pair (reverseCupWord a).basis x i.val) 1)

def FiniteAfter (tail : Diagram R (p.tensor (reverseCupWord a)) q) : Prop :=
  ∀ x : p.basis.carrier, Set.Finite { i : reverseCupUnitFiber a | term tail x i ≠ 0 }

def basisSum (tail : Diagram R (p.tensor (reverseCupWord a)) q)
    (finiteAfter : FiniteAfter tail) (x : p.basis.carrier) : q.basis.carrier →₀ R :=
  ∑ i ∈ (finiteAfter x).toFinset, term tail x i

end RightCupTrace

structure RightCupTrace (R : Type v) [CommSemiring R] (p q : Word K B)
    (a : ConjEmbedding A B) where
  tail : Diagram R (p.tensor (reverseCupWord a)) q
  finiteAfter : RightCupTrace.FiniteAfter tail
  equivariant : ∀ g x, RightCupTrace.basisSum tail finiteAfter (p.basis.act g x) =
    q.basis.actLinear R g (RightCupTrace.basisSum tail finiteAfter x)

namespace RightCupTrace

variable {p q : Word K B} {a : ConjEmbedding A B}

def eval (scope : RightCupTrace R p q a) : Biset.Hom R p.basis q.basis :=
  Biset.Hom.ofBasis (basisSum scope.tail scope.finiteAfter) scope.equivariant

theorem eval_single (scope : RightCupTrace R p q a) (x : p.basis.carrier) :
    scope.eval.toLinearMap (Finsupp.single x 1) = basisSum scope.tail scope.finiteAfter x := by
  change (Biset.Hom.ofBasis (basisSum scope.tail scope.finiteAfter) scope.equivariant).toLinearMap
    (Finsupp.single x 1) = _
  have h := Biset.Hom.ofBasis_single (basisSum scope.tail scope.finiteAfter)
    scope.equivariant x (1 : R)
  rw [one_smul] at h
  exact h

end RightCupTrace

inductive ProjectionOpening where
  | junction | cupAndMerge
  deriving DecidableEq, Repr

inductive ProjectionClosing where
  | junction | splitAndTrace
  deriving DecidableEq, Repr

/-- Typed syntax containing the ordinary diagram language and scoped cups. -/
inductive ScopedDiagram (R : Type v) [CommSemiring R] :
    {K H : Subgroup U} → Word K H → Word K H → Type (max u v)
  | ordinary {K H : Subgroup U} {p q : Word K H} (d : Diagram R p q) : ScopedDiagram R p q
  | bentVertex {K H : Subgroup U} {p q : Word K H} (vertex : BentVertex p q) :
      ScopedDiagram R p q
  | algebraUpDot {A B : Subgroup U} {a b : ConjEmbedding A B} (d : AlgebraUpDot R a b) :
      ScopedDiagram R (.up a) (.up b)
  | weightedUpDot {A B : Subgroup U} {a b : ConjEmbedding A B}
      (label : List (R × Dot a b)) : ScopedDiagram R (.up a) (.up b)
  | weightedDownDot {A B : Subgroup U} {a b : ConjEmbedding A B}
      (label : List (R × Dot a b)) : ScopedDiagram R (.down a) (.down b)
  | rightCupTrace {A B K : Subgroup U} {p q : Word K B} {a : ConjEmbedding A B}
      (scope : RightCupTrace R p q a) : ScopedDiagram R p q
  | expandedProjectionFrame {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G)
      (l : ConjEmbedding L K) (r : ConjEmbedding L H)
      (opening : ProjectionOpening) (closing : ProjectionClosing)
      (body : ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))) :
      ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | vertical {K H : Subgroup U} {p q t : Word K H}
      (bottom : ScopedDiagram R p q) (top : ScopedDiagram R q t) : ScopedDiagram R p t
  | horizontal {K H J : Subgroup U} {p p' : Word K H} {q q' : Word H J}
      (left : ScopedDiagram R p p') (right : ScopedDiagram R q q') :
      ScopedDiagram R (p.tensor q) (p'.tensor q')
  | zero {K H : Subgroup U} (p q : Word K H) : ScopedDiagram R p q
  | add {K H : Subgroup U} {p q : Word K H}
      (d e : ScopedDiagram R p q) : ScopedDiagram R p q
  | scale {K H : Subgroup U} {p q : Word K H} (r : R)
      (d : ScopedDiagram R p q) : ScopedDiagram R p q

namespace ScopedDiagram

def eval {K H : Subgroup U} {p q : Word K H} (d : ScopedDiagram R p q) :
    Biset.Hom R p.basis q.basis :=
  match d with
  | .ordinary d => d.eval
  | .bentVertex vertex => vertex.expand.eval
  | .algebraUpDot d => d.eval
  | .weightedUpDot label =>
    (Diagram.finiteSum (label.map fun (c,d) => .scale c (.upDot d))).eval
  | .weightedDownDot label =>
    (Diagram.finiteSum (label.map fun (c,d) => .scale c (.downDot d))).eval
  | .rightCupTrace s => s.eval
  | .expandedProjectionFrame _ _ _ _ _ _ body => body.eval
  | .vertical d e => d.eval.vertical e.eval
  | .horizontal d e => d.eval.horizontal e.eval
  | .zero _ _ => Biset.Hom.zero
  | .add d e => d.eval.add e.eval
  | .scale r d => d.eval.scale r

@[simp] theorem eval_expandedProjectionFrame {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (opening : ProjectionOpening) (closing : ProjectionClosing)
    (body : ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))) :
    (expandedProjectionFrame a b l r opening closing body).eval = body.eval := rfl

theorem expandedProjectionFrames_ne_opening {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (closing : ProjectionClosing)
    (body₁ body₂ : ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))) :
    expandedProjectionFrame a b l r .junction closing body₁ ≠
      expandedProjectionFrame a b l r .cupAndMerge closing body₂ := by
  intro he
  cases he

theorem expandedProjectionFrames_ne_closing {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (opening : ProjectionOpening)
    (body₁ body₂ : ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))) :
    expandedProjectionFrame a b l r opening .junction body₁ ≠
      expandedProjectionFrame a b l r opening .splitAndTrace body₂ := by
  intro he
  cases he

/-- Interpret a finite linear label by expanding it into typed terms. -/
def linearCombination {K H : Subgroup U} {p q : Word K H}
    (terms : List (R × ScopedDiagram R p q)) : ScopedDiagram R p q :=
  terms.foldr (fun term total => .add (.scale term.1 term.2) total) (.zero p q)

theorem eval_linearCombination_apply {K H : Subgroup U} {p q : Word K H}
    (terms : List (R × ScopedDiagram R p q)) (x : p.basis.carrier →₀ R) :
    (linearCombination terms).eval.toLinearMap x =
      (terms.map fun term => term.1 • term.2.eval.toLinearMap x).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    change term.1 • term.2.eval.toLinearMap x + (linearCombination terms).eval.toLinearMap x =
      term.1 • term.2.eval.toLinearMap x +
        (terms.map fun term => term.1 • term.2.eval.toLinearMap x).sum
    rw [ih]

@[simp] theorem rightCupTrace_eval_single {p q : Word K B} {a : ConjEmbedding A B}
    (scope : RightCupTrace R p q a) (x : p.basis.carrier) :
    (rightCupTrace scope).eval.toLinearMap (Finsupp.single x 1) =
      RightCupTrace.basisSum scope.tail scope.finiteAfter x :=
  RightCupTrace.eval_single scope x

@[simp] theorem eval_bentVertex {K H : Subgroup U} {p q : Word K H}
    (vertex : BentVertex p q) :
    (bentVertex (R := R) vertex).eval = (vertex.expand (R := R)).eval := rfl

/-- The label is a single vertex, and its coefficient vector acts by right multiplication. -/
@[simp] theorem algebraUpDot_eval_apply {a b : ConjEmbedding A B} (d : AlgebraUpDot R a b)
    (x : B →₀ R) :
    (algebraUpDot d).eval.toLinearMap x = (MonoidAlgebra.ofCoeff x * d.label).coeff := rfl

end ScopedDiagram

end
end MackeyDiagrams
