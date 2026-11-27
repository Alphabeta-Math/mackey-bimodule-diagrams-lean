import Mathlib.Basic.Complex.Basic
import MackeyDiagrams
import MackeyDiagrams.StructuralBasis

namespace CaseFiveInfiniteAux
open MackeyDiagrams

universe u
variable {V : Type u} [Group V] {A B C D : Subgroup V}

@[reducible] def Raw : {A B : Subgroup V} → Word A B → Type u
  | _, _, .empty _ => PUnit
  | _, _, @Word.up _ _ _ H _ => H
  | _, _, @Word.down _ _ _ H _ => H
  | _, _, .tensor p q => Raw p × Raw q

def rawPoint : {A B : Subgroup V} → (p : Word A B) → Raw p → p.basis.carrier
  | _, _, .empty _, _ => 1
  | _, _, .up _, x => x
  | _, _, .down _, x => x
  | _, _, .tensor p q, x => p.basis.pair q.basis (rawPoint p x.1) (rawPoint q x.2)

abbrev Slot (V : Type u) [Group V] := Subgroup V × Subgroup V × V

def slots : {A B : Subgroup V} → (p : Word A B) → Raw p → List (Slot V)
  | _, _, .empty _, _ => []
  | A, B, .up _, x => [(A, B, x.val)]
  | A, B, .down _, x => [(A, B, x.val)]
  | _, _, .tensor p q, x => slots p x.1 ++ slots q x.2

noncomputable def basisVector (p : Word A B) (x : Raw p) : p.basis.carrier →₀ Complex :=
  Finsupp.single (rawPoint p x) 1

theorem slots_length (p : Word A B) (x : Raw p) :
    (slots p x).length = p.directions.length := by
  induction p with
  | empty | up | down => rfl
  | tensor p q hp hq => simp [slots, Word.directions, hp, hq]

def Selected (xs : List (Slot V)) (n : Nat) (x : V) : Prop :=
  ∃ G G' y z, xs[n]? = some (⊥, G, y) ∧ xs[n+1]? = some (G', ⊥, z) ∧ y*z = x

theorem selected_append_left (l r : List (Slot V)) (n : Nat) (x : V)
    (h : n+1 < l.length) : Selected (l ++ r) n x → Selected l n x := by
  intro ⟨G,G',y,z,hy,hz,hx⟩
  have hn : n < l.length := by omega
  rw [List.getElem?_append_left hn] at hy
  rw [List.getElem?_append_left h] at hz
  exact ⟨G,G',y,z,hy,hz,hx⟩

theorem selected_append_right (l r : List (Slot V)) (n : Nat) (x : V) :
    Selected (l ++ r) (l.length + n) x → Selected r n x := by
  intro ⟨G,G',y,z,hy,hz,hx⟩
  rw [List.getElem?_append_right (by omega), show l.length + n - l.length = n by omega] at hy
  rw [List.getElem?_append_right (by omega), show l.length + n + 1 - l.length = n+1 by omega] at hz
  exact ⟨G,G',y,z,hy,hz,hx⟩

theorem raw_projection_zero (a : ConjEmbedding A C) (b : ConjEmbedding B C)
    (l : ConjEmbedding D A) (r : ConjEmbedding D B) (s : ProjectionDot.Mixed a b l r)
    (xy : Raw ((Word.down a).tensor (.up b))) (z : V)
    (hx : Selected (slots ((Word.down a).tensor (.up b)) xy) 0 z)
    (h : z ≠ s.dot.element.val) :
    (Diagram.mixedProjection (R := Complex) a b l r s.dot s.finite).eval.toLinearMap
      (basisVector ((Word.down a).tensor (.up b)) xy) = 0 := by
  obtain ⟨G,G',y,w,hy,hw,hz⟩ := hx
  change some (A,C,xy.1.val) = some (⊥,G,y) at hy
  change some (C,B,xy.2.val) = some (G',⊥,w) at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hy hw
  have he (t : (Word.basis ((Word.up l).tensor (.down r))).carrier) :
      Generator.mixedProduct a b (Generator.mixedMultiplicationBasis a b l r s.dot t) =
        s.dot.element := by
    refine Quotient.inductionOn t (fun uv => ?_)
    have h₁ : uv.1 = 1 := Subtype.ext (hy.1 ▸ uv.1.property)
    have h₂ : uv.2 = 1 := Subtype.ext (hw.2.1 ▸ uv.2.property)
    change Generator.mixedProduct a b
      (Generator.mixedPair a b (a.toHom uv.1 * s.dot.element * b.toHom uv.2)) = _
    simp [h₁, h₂]
  change (Generator.mixedProjection a b l r s.dot Complex s.finite).toLinearMap
    (Finsupp.single ((Biset.restriction a).pair (Biset.induction b) xy.1 xy.2) 1) = 0
  rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]
  apply Finset.sum_eq_zero
  intro t ht
  exfalso
  rw [Set.Finite.mem_toFinset] at ht
  have hf := ht
  change Generator.mixedMultiplicationBasis a b l r s.dot t =
    (Biset.restriction a).pair (Biset.induction b) xy.1 xy.2 at hf
  have ht' := he t
  rw [hf] at ht'
  let v₁ : C := xy.1
  let v₂ : C := xy.2
  change v₁ * v₂ = _ at ht'
  apply h
  rw [← hz, ← hy.2.2, ← hw.2.2]
  exact congrArg Subtype.val ht'

end CaseFiveInfiniteAux
