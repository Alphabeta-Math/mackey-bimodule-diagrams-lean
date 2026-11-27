import MackeyDiagrams.Mixed
import MackeyDiagrams.Unitors

/-!
# Typed diagrams

The indices of a strand word list the exterior groups in left-to-right
order. The indices of a diagram give its actual bottom and top words.
Evaluation keeps both of these boundaries fixed.
-/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U]

inductive Word : Subgroup U → Subgroup U → Type u
  | empty (A : Subgroup U) : Word A A
  | up {A B : Subgroup U} (a : ConjEmbedding A B) : Word B A
  | down {A B : Subgroup U} (a : ConjEmbedding A B) : Word A B
  | tensor {A B C : Subgroup U} (left : Word A B) (right : Word B C) : Word A C

@[reducible] def Word.basis {A B : Subgroup U} (w : Word A B) : Biset A B :=
  match w with
  | .empty A => Biset.regular A
  | .up a => Biset.induction a
  | .down a => Biset.restriction a
  | .tensor p q => p.basis.tensor q.basis

inductive Diagram (R : Type v) : {K H : Subgroup U} → Word K H → Word K H → Type (max u v)
  | id {K H : Subgroup U} (p : Word K H) : Diagram R p p
  | upDot {A B : Subgroup U} {a b : ConjEmbedding A B} (d : Dot a b) :
    Diagram R (.up a) (.up b)
  | downDot {A B : Subgroup U} {a b : ConjEmbedding A B} (d : Dot a b) :
    Diagram R (.down a) (.down b)
  | mergeUp {A B C : Subgroup U} (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Diagram R ((Word.up b).tensor (.up a)) (.up (b.comp a))
  | splitUp {A B C : Subgroup U} (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Diagram R (.up (b.comp a)) ((Word.up b).tensor (.up a))
  | mergeDown {A B C : Subgroup U} (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Diagram R ((Word.down a).tensor (.down b)) (.down (b.comp a))
  | splitDown {A B C : Subgroup U} (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Diagram R (.down (b.comp a)) ((Word.down a).tensor (.down b))
  | multiplicationCap {A B : Subgroup U} (a : ConjEmbedding A B) :
    Diagram R ((Word.up a).tensor (.down a)) (.empty B)
  | traceCap {A B : Subgroup U} (a : ConjEmbedding A B) :
    Diagram R ((Word.down a).tensor (.up a)) (.empty A)
  | reverseCup {A B : Subgroup U} (a : ConjEmbedding A B) (finite : a.toHom.range.FiniteIndex) :
    Diagram R (.empty B) ((Word.up a).tensor (.down a))
  | ordinaryCup {A B : Subgroup U} (a : ConjEmbedding A B) :
    Diagram R (.empty A) ((Word.down a).tensor (.up a))
  | leftUnit {K H : Subgroup U} (p : Word K H) :
    Diagram R ((Word.empty K).tensor p) p
  | rightUnit {K H : Subgroup U} (p : Word K H) :
    Diagram R (p.tensor (.empty H)) p
  | insertLeftUnit {K H : Subgroup U} (p : Word K H) :
    Diagram R p ((Word.empty K).tensor p)
  | insertRightUnit {K H : Subgroup U} (p : Word K H) :
    Diagram R p (p.tensor (.empty H))
  | associate {K H J F : Subgroup U} (p : Word K H) (q : Word H J) (r : Word J F) :
    Diagram R ((p.tensor q).tensor r) (p.tensor (q.tensor r))
  | unassociate {K H J F : Subgroup U} (p : Word K H) (q : Word H J) (r : Word J F) :
    Diagram R (p.tensor (q.tensor r)) ((p.tensor q).tensor r)
  | mixedMultiplication {H K G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G)
      (l : ConjEmbedding L K) (r : ConjEmbedding L H)
      (d : Dot (a.comp l) (b.comp r)) :
      Diagram R ((Word.up l).tensor (.down r)) ((Word.down a).tensor (.up b))
  | mixedProjection {H K G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G)
      (l : ConjEmbedding L K) (r : ConjEmbedding L H)
      (d : Dot (a.comp l) (b.comp r))
      (finite : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
      Diagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | vertical {K H : Subgroup U} {p q r : Word K H} (bottom : Diagram R p q)
      (top : Diagram R q r) : Diagram R p r
  | horizontal {K H J : Subgroup U} {p p' : Word K H} {q q' : Word H J}
      (left : Diagram R p p') (right : Diagram R q q') :
      Diagram R (p.tensor q) (p'.tensor q')
  | zero {K H : Subgroup U} (p q : Word K H) : Diagram R p q
  | add {K H : Subgroup U} {p q : Word K H} (x y : Diagram R p q) : Diagram R p q
  | scale {K H : Subgroup U} {p q : Word K H} (r : R) (x : Diagram R p q) : Diagram R p q

namespace Diagram

variable {R : Type v} [CommSemiring R]

noncomputable def eval {K H : Subgroup U} {p q : Word K H} (d : Diagram R p q) :
    Biset.Hom R p.basis q.basis :=
  match d with
  | .id p => Biset.Hom.id p.basis
  | .upDot d => Generator.upDot R d
  | .downDot d => Generator.downDot R d
  | .mergeUp b a => Generator.mergeUp R b a
  | .splitUp b a => Generator.splitUp R b a
  | .mergeDown b a => Generator.mergeDown R b a
  | .splitDown b a => Generator.splitDown R b a
  | .multiplicationCap a => Generator.multiplicationCap R a
  | .traceCap a => Generator.traceCap R a
  | .reverseCup a finite => Generator.reverseCup R a finite
  | .ordinaryCup a => Generator.ordinaryCup R a
  | .leftUnit p => Biset.leftUnit p.basis R
  | .rightUnit p => Biset.rightUnit p.basis R
  | .insertLeftUnit p => Biset.insertLeftUnit p.basis R
  | .insertRightUnit p => Biset.insertRightUnit p.basis R
  | .associate p q r => Biset.associate p.basis q.basis r.basis R
  | .unassociate p q r => Biset.unassociate p.basis q.basis r.basis R
  | .mixedMultiplication a b l r d => Generator.mixedMultiplication a b l r d R
  | .mixedProjection a b l r d finite => Generator.mixedProjection a b l r d R finite
  | .vertical d e => d.eval.vertical e.eval
  | .horizontal d e => d.eval.horizontal e.eval
  | .zero _ _ => Biset.Hom.zero
  | .add d e => d.eval.add e.eval
  | .scale r d => d.eval.scale r

/-- Equality of diagrams at a fixed boundary is equality of their evaluated maps. -/
def evaluationSetoid {K H : Subgroup U} (p q : Word K H) : Setoid (Diagram R p q) where
  r := fun d e => d.eval = e.eval
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

end Diagram

end MackeyDiagrams

