import MackeyDiagrams.Embedding

/-!
# Biset bases of strings and horizontal words

The action of (k,h) represents x ↦ k • x • h⁻¹. Composing bases
balances the opposite actions of the common group by a quotient.
-/

namespace MackeyDiagrams

universe u

structure Biset (K H : Type u) [Group K] [Group H] where
  carrier : Type u
  act : K × H → carrier → carrier
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ g h x, act (g * h) x = act g (act h x)

namespace Biset

variable {K H J : Type u} [Group K] [Group H] [Group J]

abbrev regular (H : Type u) [Group H] : Biset H H where
  carrier := H
  act := fun (g, h) x => g * x * h⁻¹
  one_act := by simp
  mul_act := fun (g, h) (g', h') x => by
    change (g * g') * x * (h * h')⁻¹ = g * (g' * x * h'⁻¹) * h⁻¹
    simp [mul_assoc]

variable {U : Type u} [Group U] {A B : Subgroup U}

abbrev induction (a : ConjEmbedding A B) : Biset B A where
  carrier := B
  act := fun (g, h) x => g * x * (a.toHom h)⁻¹
  one_act := by simp
  mul_act := fun (g, h) (g', h') x => by
    change (g * g') * x * (a.toHom (h * h'))⁻¹ = g * (g' * x * (a.toHom h')⁻¹) * (a.toHom h)⁻¹
    simp [mul_assoc]

abbrev restriction (a : ConjEmbedding A B) : Biset A B where
  carrier := B
  act := fun (h, g) x => a.toHom h * x * g⁻¹
  one_act := by simp
  mul_act := fun (h, g) (h', g') x => by
    change a.toHom (h * h') * x * (g * g')⁻¹ = a.toHom h * (a.toHom h' * x * g'⁻¹) * g⁻¹
    simp [mul_assoc]

def balance (X : Biset K H) (Y : Biset H J) : Setoid (X.carrier × Y.carrier) where
  r := fun x y => ∃ h : H, X.act (1, h) x.1 = y.1 ∧ Y.act (h, 1) x.2 = y.2
  iseqv := by
    constructor
    · intro x
      exact ⟨1, X.one_act x.1, Y.one_act x.2⟩
    · rintro x y ⟨h, hx, hy⟩
      refine ⟨h⁻¹, ?_, ?_⟩
      · rw [← hx, ← X.mul_act]
        rw [Prod.mk_mul_mk, one_mul, inv_mul_cancel]
        exact X.one_act x.1
      · rw [← hy, ← Y.mul_act]
        rw [Prod.mk_mul_mk, one_mul, inv_mul_cancel]
        exact Y.one_act x.2
    · rintro x y z ⟨h, hx, hy⟩ ⟨h', hx', hy'⟩
      refine ⟨h' * h, ?_, ?_⟩
      · rw [← hx, ← X.mul_act] at hx'
        simpa using hx'
      · rw [← hy, ← Y.mul_act] at hy'
        simpa using hy'

private def actPair (X : Biset K H) (Y : Biset H J) (g : K × J)
    (x : X.carrier × Y.carrier) : X.carrier × Y.carrier :=
  (X.act (g.1, 1) x.1, Y.act (1, g.2) x.2)

private theorem actPair_balance (X : Biset K H) (Y : Biset H J) (g : K × J)
    {x y : X.carrier × Y.carrier} (hxy : (balance X Y).r x y) :
    (balance X Y).r (actPair X Y g x) (actPair X Y g y) := by
  obtain ⟨h, hx, hy⟩ := hxy
  refine ⟨h, ?_, ?_⟩
  · change X.act (1, h) (X.act (g.1, 1) x.1) = X.act (g.1, 1) y.1
    rw [← hx, ← X.mul_act, ← X.mul_act]
    simp
  · change Y.act (h, 1) (Y.act (1, g.2) x.2) = Y.act (1, g.2) y.2
    rw [← hy, ← Y.mul_act, ← Y.mul_act]
    simp

def tensor (X : Biset K H) (Y : Biset H J) : Biset K J where
  carrier := Quotient (balance X Y)
  act := fun g => Quotient.map' (actPair X Y g) (fun _ _ proof => actPair_balance X Y g proof)
  one_act := by
    intro z
    induction z using Quotient.inductionOn with
    | h x =>
      change Quotient.mk (balance X Y) (actPair X Y 1 x) = Quotient.mk (balance X Y) x
      congr 1
      apply Prod.ext
      · exact X.one_act x.1
      · exact Y.one_act x.2
  mul_act := by
    intro g h z
    induction z using Quotient.inductionOn with
    | h x =>
      change Quotient.mk (balance X Y) (actPair X Y (g * h) x) = Quotient.mk (balance X Y) (actPair X Y g (actPair X Y h x))
      congr 1
      apply Prod.ext
      · change X.act (g.1 * h.1, 1) x.1 = X.act (g.1, 1) (X.act (h.1, 1) x.1)
        rw [← X.mul_act]
        simp
      · change Y.act (1, g.2 * h.2) x.2 = Y.act (1, g.2) (Y.act (1, h.2) x.2)
        rw [← Y.mul_act]
        simp

def pair (X : Biset K H) (Y : Biset H J) (x : X.carrier) (y : Y.carrier) :
    (tensor X Y).carrier :=
  Quotient.mk (balance X Y) (x, y)

theorem pair_balance (X : Biset K H) (Y : Biset H J)
    (h : H) (x : X.carrier) (y : Y.carrier) :
    pair X Y (X.act (1,h⁻¹) x) y = pair X Y x (Y.act (h,1) y) := by
  change Quotient.mk (balance X Y) _ = Quotient.mk (balance X Y) _
  apply Quotient.sound
  refine ⟨h, ?_, rfl⟩
  rw [← X.mul_act]
  rw [Prod.mk_mul_mk, one_mul, mul_inv_cancel]
  exact X.one_act x

end Biset

end MackeyDiagrams

