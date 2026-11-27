import MackeyDiagrams.MixedIdentities
import Mathlib.Data.Set.Card

/-! The reverse cup and multiplication cap give the subgroup-index scalar. -/

namespace MackeyDiagrams.Diagram

universe u v
noncomputable section
variable {U : Type u} [Group U] {A B : Subgroup U}
variable {R : Type v} [CommSemiring R]

theorem eval_ext_on_generators {K H : Subgroup U} {p q : Word K H} {x y : Diagram R p q}
    (h : ∀ z : p.basis.carrier,
      x.eval.toLinearMap (Finsupp.single z 1) = y.eval.toLinearMap (Finsupp.single z 1)) :
    x.eval = y.eval := by
  apply eval_ext
  intro z r
  have hr : Finsupp.single z r = r • Finsupp.single z (1 : R) := by
    simp [Finsupp.smul_single, smul_eq_mul]
  rw [hr, map_smul, map_smul, h z]

theorem reverseCup_multiplicationCap (a : ConjEmbedding A B) (finite : a.toHom.range.FiniteIndex) :
    ((reverseCup (R := R) a finite).vertical (multiplicationCap a)).eval =
      (scale (a.toHom.range.index : R) (id (.empty B))).eval := by
  apply eval_ext_on_generators
  intro z
  change B at z
  have hc := Biset.Hom.transfer_then_push_single
    (X := (Biset.induction a).tensor (Biset.restriction a)) (Y := Biset.regular B)
    R (Generator.multiplicationCapBasis a)
    (by
      intro g w
      refine Quotient.inductionOn w (fun x => ?_)
      rcases g with ⟨g,h⟩
      change (g * x.1 * (a.toHom 1)⁻¹) * (a.toHom 1 * x.2 * h⁻¹) =
        g * (x.1 * x.2) * h⁻¹
      simp [mul_assoc]) (Generator.multiplicationCap_finiteFiber a finite) z
  have hi : (Generator.multiplicationCap_finiteFiber a finite z).toFinset.card =
      a.toHom.range.index := by
    calc
      _ = ({w | Generator.multiplicationCapBasis a w = z} : Set _).ncard :=
        (Set.ncard_eq_toFinset_card _ (Generator.multiplicationCap_finiteFiber a finite z)).symm
      _ = Nat.card {w // Generator.multiplicationCapBasis a w = z} := rfl
      _ = a.toHom.range.index := Generator.capFiber_card a z
  rw [hi] at hc
  change _ = (a.toHom.range.index : R) • Finsupp.single z (1 : R)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  exact hc

end
end MackeyDiagrams.Diagram

