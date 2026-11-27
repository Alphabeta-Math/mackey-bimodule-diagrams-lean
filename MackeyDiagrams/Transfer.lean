import MackeyDiagrams.Trace
import Mathlib.GroupTheory.Index

/-!
# Finite fibers, projection, and the reverse cup

The transfer sends a basis element to the sum of its preimages. Finiteness
is required for each fiber. This models projection crossings independently
of the existence of a standalone reverse cup.
-/

namespace MackeyDiagrams

universe u v
noncomputable section

namespace Biset

variable {K H : Type u} [Group K] [Group H]

def actEquiv (X : Biset K H) (g : K × H) : X.carrier ≃ X.carrier where
  toFun := X.act g
  invFun := X.act g⁻¹
  left_inv x := by rw [← X.mul_act, inv_mul_cancel, X.one_act]
  right_inv x := by rw [← X.mul_act, mul_inv_cancel, X.one_act]

namespace Hom

variable (R : Type v) [CommSemiring R]
variable {X Y : Biset K H}

def transferBasis (f : X.carrier → Y.carrier)
    (finite : ∀ y, Set.Finite {x | f x = y}) (y : Y.carrier) : X.carrier →₀ R := by
  classical
  exact Finsupp.onFinset (finite y).toFinset (fun x => if f x = y then 1 else 0) (by
    intro x hx
    by_cases h : f x = y
    · exact (finite y).mem_toFinset.mpr h
    · simp [h] at hx)

theorem transferBasis_apply (f : X.carrier → Y.carrier)
    (finite : ∀ y, Set.Finite {x | f x = y}) (y : Y.carrier) (x : X.carrier)
    [Decidable (f x = y)] :
    transferBasis R f finite y x = if f x = y then 1 else 0 := by
  by_cases h : f x = y <;> simp [transferBasis, Finsupp.onFinset_apply, h]

def transfer (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) : Hom R Y X :=
  ofBasis (transferBasis R f finite) (by
    classical
    intro g y
    apply Finsupp.ext
    intro z
    obtain ⟨x, rfl⟩ := (X.actEquiv g).surjective z
    have hi : Function.Injective (X.act g) := (X.actEquiv g).injective
    change transferBasis R f finite (Y.act g y) (X.act g x) =
      Finsupp.mapDomain (X.act g) (transferBasis R f finite y) (X.act g x)
    rw [Finsupp.mapDomain_apply_of_injective hi]
    rw [transferBasis_apply, transferBasis_apply, hf]
    have hj : Function.Injective (Y.act g) := (Y.actEquiv g).injective
    rw [hj.eq_iff])

end Hom
end Biset

namespace Generator

variable {U : Type u} [Group U] {A B : Subgroup U}

private def rightCosetToCapFiber (a : ConjEmbedding A B) (z : B) :
    Quotient (QuotientGroup.rightRel a.toHom.range) →
      {w : ((Biset.induction a).tensor (Biset.restriction a)).carrier //
        multiplicationCapBasis a w = z} :=
  Quotient.lift (fun t : B => ⟨(Biset.induction a).pair (Biset.restriction a) (z * t⁻¹) t,
    by change z * t⁻¹ * t = z; group⟩) (by
    intro t s hts
    have hmem : s * t⁻¹ ∈ a.toHom.range := QuotientGroup.rightRel_apply.mp hts
    obtain ⟨k, hk⟩ := hmem
    apply Subtype.ext
    apply Quotient.sound
    refine ⟨k, ?_, ?_⟩
    · change 1 * (z * t⁻¹) * (a.toHom k)⁻¹ = z * s⁻¹
      rw [hk]
      group
    · change a.toHom k * t * (1 : B)⁻¹ = s
      rw [hk]
      group)

private theorem rightCosetToCapFiber_surjective (a : ConjEmbedding A B) (z : B) :
    Function.Surjective (rightCosetToCapFiber a z) := by
  intro w
  obtain ⟨⟨x,t⟩, h⟩ := Quotient.exists_rep w.val
  have hpair : (Biset.induction a).pair (Biset.restriction a) x t = w.val := h
  have hprod : x * t = z := by
    have hw := w.property
    rw [← hpair] at hw
    exact hw
  refine ⟨Quotient.mk _ t, Subtype.ext ?_⟩
  change (Biset.induction a).pair (Biset.restriction a) (z * t⁻¹) t = w.val
  rw [← hpair, ← hprod, mul_assoc, mul_inv_cancel, mul_one]

private theorem rightCosetToCapFiber_injective (a : ConjEmbedding A B) (z : B) :
    Function.Injective (rightCosetToCapFiber a z) := by
  intro x y
  refine Quotient.inductionOn₂ x y (fun s t h => ?_)
  have heq :
      (Biset.induction a).pair (Biset.restriction a) (z*s⁻¹) s =
        (Biset.induction a).pair (Biset.restriction a) (z*t⁻¹) t :=
    congrArg Subtype.val h
  obtain ⟨k, _, hk⟩ := Quotient.exact heq
  change a.toHom k * s * (1 : B)⁻¹ = t at hk
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  refine ⟨k, ?_⟩
  rw [← hk]
  group

/-- The multiplication cap fibers are parametrized by the right cosets. -/
def rightCosetEquivCapFiber (a : ConjEmbedding A B) (z : B) :
    Quotient (QuotientGroup.rightRel a.toHom.range) ≃
      {w : ((Biset.induction a).tensor (Biset.restriction a)).carrier //
        multiplicationCapBasis a w = z} :=
  Equiv.ofBijective (rightCosetToCapFiber a z)
    ⟨rightCosetToCapFiber_injective a z, rightCosetToCapFiber_surjective a z⟩

theorem capFiber_card (a : ConjEmbedding A B) (z : B) :
    Nat.card {w // multiplicationCapBasis a w = z} = a.toHom.range.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr ((rightCosetEquivCapFiber a z).symm.trans
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel a.toHom.range))


theorem multiplicationCap_finiteFiber (a : ConjEmbedding A B) (finite : a.toHom.range.FiniteIndex)
    (z : B) : Set.Finite {w | multiplicationCapBasis a w = z} := by
  letI := finite
  letI : Finite (Quotient (QuotientGroup.rightRel a.toHom.range)) :=
    Finite.of_injective _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel a.toHom.range).injective
  letI : Finite {w | multiplicationCapBasis a w = z} :=
    Finite.of_surjective _ (rightCosetToCapFiber_surjective a z)
  exact Set.toFinite _

def reverseCup (R : Type v) [CommSemiring R] (a : ConjEmbedding A B)
    (finite : a.toHom.range.FiniteIndex) :
    Biset.Hom R (Biset.regular B) ((Biset.induction a).tensor (Biset.restriction a)) :=
  Biset.Hom.transfer R (multiplicationCapBasis a) (by
    intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    rcases g with ⟨g,h⟩
    change (g * x.1 * (a.toHom 1)⁻¹) * (a.toHom 1 * x.2 * h⁻¹) =
      g * (x.1 * x.2) * h⁻¹
    simp [mul_assoc]) (multiplicationCap_finiteFiber a finite)

end Generator

end
end MackeyDiagrams

