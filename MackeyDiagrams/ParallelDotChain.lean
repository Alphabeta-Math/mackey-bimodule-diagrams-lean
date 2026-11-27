import MackeyDiagrams.ScopedCup
import MackeyDiagrams.DotChain

/-! Keep each linear dot on a parallel crossing as one marked vertex. -/

namespace MackeyDiagrams.LinearDotChain

universe u v

variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

def upDrawing : {a b : ConjEmbedding H K} →
    LinearDotChain R a b → ScopedDiagram R (.up a) (.up b)
  | _, _, .empty a => .ordinary (.id (.up a))
  | _, _, .cons dots rest => .vertical (.weightedUpDot dots) rest.upDrawing

def downDrawing : {a b : ConjEmbedding H K} →
    LinearDotChain R a b → ScopedDiagram R (.down a) (.down b)
  | _, _, .empty a => .ordinary (.id (.down a))
  | _, _, .cons dots rest => .vertical (.weightedDownDot dots) rest.downDrawing

end MackeyDiagrams.LinearDotChain
