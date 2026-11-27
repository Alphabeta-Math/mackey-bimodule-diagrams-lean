import MackeyDiagrams.ScopedCupEquivariance

/-! The prescribed tail of the expanded Mackey projection.
At infinite index the cup is evaluated only through this tail. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace Diagram

/-- Bend an upward split through the trace of the larger group. -/
def traceCapOnLeft (a : ConjEmbedding K G) (l : ConjEmbedding L K) :
    Diagram R ((Word.down a).tensor (.up (a.comp l))) (.up l) :=
  .vertical (.horizontal (.id (.down a)) (.splitUp a l))
    (.vertical (.unassociate (.down a) (.up a) (.up l))
      (.vertical (.horizontal (.traceCap a) (.id (.up l))) (.leftUnit (.up l))))

/-- Merge the cup branch, apply the marked middle strand, and trace through the left boundary. -/
def mixedProjectionTailWithMiddle (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (middle : Diagram R (.up (b.comp r)) (.up (a.comp l))) :
    Diagram R (((Word.down a).tensor (.up b)).tensor (reverseCupWord r))
      ((Word.up l).tensor (.down r)) :=
  let kg := Word.down a
  let gh := Word.up b
  let hl := Word.up r
  let lh := Word.down r
  .vertical (.associate kg gh (reverseCupWord r))
    (.vertical (.horizontal (.id kg) (.unassociate gh hl lh))
      (.vertical
        (.horizontal (.id kg)
          (.horizontal (.vertical (.mergeUp b r) middle) (.id lh)))
        (.vertical (.unassociate kg (.up (a.comp l)) lh)
          (.horizontal (traceCapOnLeft a l) (.id lh)))))

def mixedProjectionTail (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (d : Dot (a.comp l) (b.comp r)) :
    Diagram R (((Word.down a).tensor (.up b)).tensor (reverseCupWord r))
      ((Word.up l).tensor (.down r)) :=
  mixedProjectionTailWithMiddle a b l r (.upDot d.inverse)

theorem eval_mixedProjectionTailWithMiddle_congr (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    {d e : Diagram R (.up (b.comp r)) (.up (a.comp l))}
    (h : d.eval = e.eval) :
    (mixedProjectionTailWithMiddle a b l r d).eval =
      (mixedProjectionTailWithMiddle a b l r e).eval := by
  simp only [mixedProjectionTailWithMiddle, Diagram.eval, h]

end Diagram

namespace ScopedDiagram

/-- The expanded Mackey projection, with the cup evaluated through its prescribed trace. -/
def expandedMixedProjection (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (d : Dot (a.comp l) (b.comp r))
    (finiteAfter : RightCupTrace.FiniteAfter (Diagram.mixedProjectionTail (R := R) a b l r d)) :
    ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r)) :=
  .rightCupTrace (RightCupTrace.ofFiniteAfter (.mixedProjectionTail a b l r d) finiteAfter)

end ScopedDiagram

end MackeyDiagrams
