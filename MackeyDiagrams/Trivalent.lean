import MackeyDiagrams.BentVertices
import MackeyDiagrams.MixedProjectionExpansion

/-! The twelve oriented trivalent junctions. Their meanings are the actual
cup/cap/merge/split composites, not arbitrary maps of the same boundary type.
The standalone junctions involving a reverse cup carry its finite-index proof.
Scoped infinite-index projection frames are separate syntax. -/

namespace MackeyDiagrams

universe u v

inductive TrivalentKind where
  | mergeUp | splitUp | mergeDown | splitDown
  | upDownToUp | downUpToDown | upToDownUp | upToUpDown
  | downUpToUp | upDownToDown | downToDownUp | downToUpDown
  deriving DecidableEq, Repr

def TrivalentKind.inputs : TrivalentKind → List Bool
  | .mergeUp => [true, true]
  | .splitUp | .upToDownUp | .upToUpDown => [true]
  | .mergeDown => [false, false]
  | .splitDown | .downToDownUp | .downToUpDown => [false]
  | .upDownToUp | .upDownToDown => [true, false]
  | .downUpToDown | .downUpToUp => [false, true]

def TrivalentKind.outputs : TrivalentKind → List Bool
  | .mergeUp | .upDownToUp | .downUpToUp => [true]
  | .splitUp => [true, true]
  | .mergeDown | .downUpToDown | .upDownToDown => [false]
  | .splitDown => [false, false]
  | .upToDownUp | .downToDownUp => [false, true]
  | .upToUpDown | .downToUpDown => [true, false]

variable {U : Type u} [Group U]

inductive TrivalentVertex : {K H : Subgroup U} → Word K H → Word K H → Type u
  | mergeUp {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex ((Word.up b).tensor (.up a)) (.up (b.comp a))
  | splitUp {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex (.up (b.comp a)) ((Word.up b).tensor (.up a))
  | mergeDown {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex ((Word.down a).tensor (.down b)) (.down (b.comp a))
  | splitDown {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex (.down (b.comp a)) ((Word.down a).tensor (.down b))
  | upDownToUp {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex ((Word.up (b.comp a)).tensor (.down a)) (.up b)
  | downUpToDown {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex ((Word.down (b.comp a)).tensor (.up b)) (.down a)
  | upToDownUp {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex (.up a) ((Word.down b).tensor (.up (b.comp a)))
  | upToUpDown {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (finite : a.toHom.range.FiniteIndex) :
      TrivalentVertex (.up b) ((Word.up (b.comp a)).tensor (.down a))
  | downUpToUp {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex ((Word.down b).tensor (.up (b.comp a))) (.up a)
  | upDownToDown {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex ((Word.up a).tensor (.down (b.comp a))) (.down b)
  | downToDownUp {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      TrivalentVertex (.down a) ((Word.down (b.comp a)).tensor (.up b))
  | downToUpDown {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (finite : a.toHom.range.FiniteIndex) :
      TrivalentVertex (.down b) ((Word.up a).tensor (.down (b.comp a)))

def TrivalentVertex.kind {K H : Subgroup U} {p q : Word K H} :
    TrivalentVertex p q → TrivalentKind
  | .mergeUp _ _ => .mergeUp
  | .splitUp _ _ => .splitUp
  | .mergeDown _ _ => .mergeDown
  | .splitDown _ _ => .splitDown
  | .upDownToUp _ _ => .upDownToUp
  | .downUpToDown _ _ => .downUpToDown
  | .upToDownUp _ _ => .upToDownUp
  | .upToUpDown _ _ _ => .upToUpDown
  | .downUpToUp _ _ => .downUpToUp
  | .upDownToDown _ _ => .upDownToDown
  | .downToDownUp _ _ => .downToDownUp
  | .downToUpDown _ _ _ => .downToUpDown

def TrivalentVertex.expand {R : Type v} {K H : Subgroup U} {p q : Word K H} :
    TrivalentVertex p q → Diagram R p q
  | .mergeUp b a => .mergeUp b a
  | .splitUp b a => .splitUp b a
  | .mergeDown b a => .mergeDown b a
  | .splitDown b a => .splitDown b a
  | .upDownToUp b a => (BentVertex.multiplicationCap b a).expand
  | .downUpToDown b a => (BentVertex.traceCap b a).expand
  | .upToDownUp b a => (BentVertex.ordinaryCup b a).expand
  | .upToUpDown b a finite => (BentVertex.reverseCup b a finite).expand
  | .downUpToUp b a => .traceCapOnLeft b a
  | .upDownToDown b a =>
      .vertical (.horizontal (.id (.up a)) (.splitDown b a))
        (.vertical (.unassociate (.up a) (.down a) (.down b))
          (.vertical (.horizontal (.multiplicationCap a) (.id (.down b)))
            (.leftUnit (.down b))))
  | .downToDownUp b a =>
      .vertical (.insertRightUnit (.down a))
        (.vertical (.horizontal (.id (.down a)) (.ordinaryCup b))
          (.vertical (.unassociate (.down a) (.down b) (.up b))
            (.horizontal (.mergeDown b a) (.id (.up b)))))
  | .downToUpDown b a finite =>
      .vertical (.insertLeftUnit (.down b))
        (.vertical (.horizontal (.reverseCup a finite) (.id (.down b)))
          (.vertical (.associate (.up a) (.down a) (.down b))
            (.horizontal (.id (.up a)) (.mergeDown b a))))

end MackeyDiagrams
