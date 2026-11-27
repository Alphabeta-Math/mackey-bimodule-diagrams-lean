import MackeyDiagrams.Diagram

/-! The ordered boundary data of an oriented drawing. Association and empty
factors in a tensor expression leave its boundary unchanged. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U]

inductive Strand : Subgroup U → Subgroup U → Type u
  | up {K H : Subgroup U} (a : ConjEmbedding H K) : Strand K H
  | down {K H : Subgroup U} (a : ConjEmbedding K H) : Strand K H

def Strand.word {K H : Subgroup U} : Strand K H → Word K H
  | .up a => .up a
  | .down a => .down a

inductive Boundary : Subgroup U → Subgroup U → Type u
  | empty (K : Subgroup U) : Boundary K K
  | cons {K H J : Subgroup U} (strand : Strand K H) (rest : Boundary H J) : Boundary K J

namespace Boundary

def append {K H J : Subgroup U} : Boundary K H → Boundary H J → Boundary K J
  | .empty _, next => next
  | .cons s rest, next => .cons s (append rest next)

def word {K H : Subgroup U} : Boundary K H → Word K H
  | .empty K => .empty K
  | .cons s rest => .tensor s.word rest.word

theorem append_empty {K H : Subgroup U} (a : Boundary K H) :
    a.append (.empty H) = a := by
  induction a with
  | empty => rfl
  | cons s rest ih => exact congrArg (fun rest => Boundary.cons s rest) ih

theorem append_assoc {K H J F : Subgroup U} (a : Boundary K H) (b : Boundary H J)
    (c : Boundary J F) : (a.append b).append c = a.append (b.append c) := by
  induction a with
  | empty => rfl
  | cons s rest ih => exact congrArg (fun rest => Boundary.cons s rest) (ih b)

def appendDiagram {R : Type v} {K H J : Subgroup U} :
    (a : Boundary K H) → (b : Boundary H J) → Diagram R (a.word.tensor b.word) (a.append b).word
  | .empty _, b => .leftUnit b.word
  | .cons s rest, b =>
    .vertical (.associate s.word rest.word b.word)
      (.horizontal (.id s.word) (appendDiagram rest b))

def splitDiagram {R : Type v} {K H J : Subgroup U} :
    (a : Boundary K H) → (b : Boundary H J) → Diagram R (a.append b).word (a.word.tensor b.word)
  | .empty _, b => .insertLeftUnit b.word
  | .cons s rest, b =>
    .vertical (.horizontal (.id s.word) (splitDiagram rest b))
      (.unassociate s.word rest.word b.word)

end Boundary

namespace Word

def boundary {K H : Subgroup U} : Word K H → Boundary K H
  | .empty K => .empty K
  | .up a => .cons (.up a) (.empty _)
  | .down a => .cons (.down a) (.empty _)
  | .tensor p q => p.boundary.append q.boundary

@[simp] theorem boundary_word {K H : Subgroup U} (b : Boundary K H) :
    b.word.boundary = b := by
  induction b with
  | empty => rfl
  | cons s rest ih =>
    cases s <;> change Boundary.cons _ rest.word.boundary = Boundary.cons _ rest <;> rw [ih]

@[simp] theorem boundary_associate {K H J F : Subgroup U}
    (p : Word K H) (q : Word H J) (r : Word J F) :
    ((p.tensor q).tensor r).boundary = (p.tensor (q.tensor r)).boundary :=
  Boundary.append_assoc p.boundary q.boundary r.boundary

@[simp] theorem boundary_leftUnit {K H : Subgroup U} (p : Word K H) :
    ((Word.empty K).tensor p).boundary = p.boundary := rfl

@[simp] theorem boundary_rightUnit {K H : Subgroup U} (p : Word K H) :
    (p.tensor (.empty H)).boundary = p.boundary :=
  Boundary.append_empty p.boundary

def reorderToBoundary {R : Type v} {K H : Subgroup U} (p : Word K H) :
    Diagram R p p.boundary.word :=
  match p with
  | .empty K => .id (.empty K)
  | .up a => .insertRightUnit (.up a)
  | .down a => .insertRightUnit (.down a)
  | .tensor p q =>
    .vertical (.horizontal (p.reorderToBoundary) (q.reorderToBoundary))
      (Boundary.appendDiagram p.boundary q.boundary)

def reorderFromBoundary {R : Type v} {K H : Subgroup U} (p : Word K H) :
    Diagram R p.boundary.word p :=
  match p with
  | .empty K => .id (.empty K)
  | .up a => .rightUnit (.up a)
  | .down a => .rightUnit (.down a)
  | .tensor p q =>
    .vertical (Boundary.splitDiagram p.boundary q.boundary)
      (.horizontal (p.reorderFromBoundary) (q.reorderFromBoundary))

end Word
end MackeyDiagrams
