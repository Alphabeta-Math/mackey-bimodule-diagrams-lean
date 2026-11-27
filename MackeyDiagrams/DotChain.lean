import MackeyDiagrams.Parallel

/-! Retain every group-element dot in a labelled strand, while evaluating their product. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H : Subgroup U}

inductive DotChain : ConjEmbedding H K → ConjEmbedding H K → Type u
  | empty (a : ConjEmbedding H K) : DotChain a a
  | cons {a b c : ConjEmbedding H K} (dot : Dot a b) (rest : DotChain b c) : DotChain a c

namespace DotChain

def length : {a b : ConjEmbedding H K} → DotChain a b → Nat
  | _, _, .empty _ => 0
  | _, _, .cons _ rest => 1 + rest.length

def product : {a b : ConjEmbedding H K} → DotChain a b → Dot a b
  | _, _, .empty a => Dot.id a
  | _, _, .cons dot rest => dot.vertical rest.product

def diagram {R : Type v} : {a b : ConjEmbedding H K} → DotChain a b → Diagram R (.up a) (.up b)
  | _, _, .empty a => .id (.up a)
  | _, _, .cons dot rest => .vertical (.upDot dot) rest.diagram

theorem eval_diagram {R : Type v} [CommSemiring R] {a b : ConjEmbedding H K}
    (chain : DotChain a b) :
    (chain.diagram (R := R)).eval = (Diagram.upDot chain.product).eval := by
  induction chain with
  | empty a => exact (Diagram.eval_upDot_id (R := R) a).symm
  | cons dot rest ih =>
    change (Diagram.upDot (R := R) dot).eval.vertical (rest.diagram (R := R)).eval =
      (Diagram.upDot (dot.vertical rest.product)).eval
    rw [ih]
    exact Diagram.upDot_vertical dot rest.product

end DotChain
end MackeyDiagrams

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H : Subgroup U}

/-- Each successive mark can carry a finite linear label between its own embeddings. -/
inductive LinearDotChain (R : Type v) : ConjEmbedding H K → ConjEmbedding H K → Type (max u v)
  | empty (a : ConjEmbedding H K) : LinearDotChain R a a
  | cons {a b c : ConjEmbedding H K} (label : List (R × Dot a b))
      (rest : LinearDotChain R b c) : LinearDotChain R a c

namespace LinearDotChain

variable {R : Type v}

def length : {a b : ConjEmbedding H K} → LinearDotChain R a b → Nat
  | _, _, .empty _ => 0
  | _, _, .cons _ rest => 1 + rest.length

def terms [Semiring R] : {a b : ConjEmbedding H K} →
    LinearDotChain R a b → List (R × DotChain a b)
  | _, _, .empty a => [(1, .empty a)]
  | _, _, .cons labels rest =>
    labels.flatMap fun (c, d) =>
      rest.terms.map fun (e, chain) => (c * e, .cons d chain)

theorem term_length [Semiring R] {a b : ConjEmbedding H K} (chain : LinearDotChain R a b)
    {term : R × DotChain a b} (h : term ∈ chain.terms) : term.2.length = chain.length := by
  induction chain with
  | empty a =>
    rw [terms, List.mem_singleton] at h
    rw [h]
    rfl
  | cons labels rest ih =>
    rw [terms, List.mem_flatMap] at h
    obtain ⟨⟨scalar,dot⟩,_,hm⟩ := h
    rw [List.mem_map] at hm
    obtain ⟨⟨coeff,tail⟩, ht, hterm⟩ := hm
    rw [← hterm]
    change 1 + tail.length = 1 + rest.length
    rw [ih ht]

end LinearDotChain
end MackeyDiagrams
