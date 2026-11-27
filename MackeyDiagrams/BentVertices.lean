import MackeyDiagrams.Diagram

/-! A straight mixed-orientation trivalent vertex records one junction.
Its interpretation expands that junction using a cup or cap and a merge or split. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U]

inductive BentVertex : {K H : Subgroup U} → Word K H → Word K H → Type u
  | multiplicationCap {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      BentVertex ((Word.up (b.comp a)).tensor (.down a)) (.up b)
  | ordinaryCup {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      BentVertex (.up a) ((Word.down b).tensor (.up (b.comp a)))
  | traceCap {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
      BentVertex ((Word.down (b.comp a)).tensor (.up b)) (.down a)
  | reverseCup {K H G : Subgroup U} (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (finite : a.toHom.range.FiniteIndex) :
      BentVertex (.up b) ((Word.up (b.comp a)).tensor (.down a))

namespace BentVertex

def expand {R : Type v} {K H : Subgroup U} {p q : Word K H} :
    BentVertex p q → Diagram R p q
  | .multiplicationCap b a =>
    let upB := Word.up b
    let upA := Word.up a
    let downA := Word.down a
    .vertical (.horizontal (.splitUp b a) (.id downA))
      (.vertical (.associate upB upA downA)
        (.vertical (.horizontal (.id upB) (.multiplicationCap a)) (.rightUnit upB)))
  | .ordinaryCup b a =>
    let upA := Word.up a
    let upB := Word.up b
    let downB := Word.down b
    .vertical (.insertLeftUnit upA)
      (.vertical (.horizontal (.ordinaryCup b) (.id upA))
        (.vertical (.associate downB upB upA) (.horizontal (.id downB) (.mergeUp b a))))
  | .traceCap b a =>
    let downA := Word.down a
    let downB := Word.down b
    let upB := Word.up b
    .vertical (.horizontal (.splitDown b a) (.id upB))
      (.vertical (.associate downA downB upB)
        (.vertical (.horizontal (.id downA) (.traceCap b)) (.rightUnit downA)))
  | .reverseCup b a finite =>
    let upB := Word.up b
    let upA := Word.up a
    let downA := Word.down a
    .vertical (.insertRightUnit upB)
      (.vertical (.horizontal (.id upB) (.reverseCup a finite))
        (.vertical (.unassociate upB upA downA) (.horizontal (.mergeUp b a) (.id downA))))

end BentVertex
end MackeyDiagrams
