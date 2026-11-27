import MackeyDiagrams.Replacement
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.GroupAction.Basic

/-! Evaluate the right-input and trunk dots at the tensor of the two units. -/

namespace MackeyDiagrams.Diagram

universe u v

noncomputable section

variable {U : Type u} [Group U] {K H G : Subgroup U}

/-- Fixing a left leg and the merged embedding fixes the internal right embedding. -/
theorem mergeUp_rightEmbedding_eq (b : ConjEmbedding H G) {a a' : ConjEmbedding K H}
    (h : b.comp a' = b.comp a) : a' = a := by
  apply ConjEmbedding.ext
  apply MonoidHom.ext
  intro k
  apply b.injective
  exact congrArg (fun c : ConjEmbedding K G => c.toHom k) h

theorem mergeUp_rightInput_ne_trunk {R : Type v} [CommSemiring R] [Nontrivial R]
    (b : ConjEmbedding H G) (a : ConjEmbedding K H) (d : Dot a a)
    (e : Dot (b.comp a) (b.comp a)) (outside : e.element ∉ b.toHom.range) :
    (((id (R := R) (.up b)).horizontal (.upDot d)).vertical (.mergeUp b a)).eval ≠
      ((mergeUp b a).vertical (.upDot e)).eval := by
  rw [mergeUp_slide_right]
  intro h
  let z := (Biset.induction b).pair (Biset.induction a) 1 1
  have he := congrArg (fun f => f.toLinearMap (Finsupp.single z (1 : R))) h
  change
    (upDot (R := R) (d.whisker b)).eval.toLinearMap
      ((mergeUp b a).eval.toLinearMap (Finsupp.single z 1)) =
    (upDot (R := R) e).eval.toLinearMap
      ((mergeUp b a).eval.toLinearMap (Finsupp.single z 1)) at he
  dsimp only [z] at he
  rw [eval_mergeUp_single, map_one, one_mul, eval_upDot_single, eval_upDot_single,
    one_mul, one_mul] at he
  have hne : (d.whisker b).element ≠ e.element := fun h => outside ⟨d.element, h⟩
  have hv := DFunLike.congr_fun he e.element
  rw [Finsupp.single_eq_of_ne hne.symm, Finsupp.single_eq_same] at hv
  exact zero_ne_one hv

end

namespace DotSlideExample

open Equiv Equiv.Perm

private abbrev U := Equiv.Perm (Fin 4)

private def H : Subgroup U := MulAction.stabilizer U (3 : Fin 4)
private def K : Subgroup U := MulAction.stabilizer U (2 : Fin 4) ⊓ H
private def G : Subgroup U := ⊤

private def a : ConjEmbedding K H where
  toHom := Subgroup.inclusion inf_le_right
  hasRepresentative := ⟨1, by intro k; change (k : U) = _; simp⟩

private def b : ConjEmbedding H G where
  toHom := Subgroup.inclusion le_top
  hasRepresentative := ⟨1, by intro h; change (h : U) = _; simp⟩

private def g : G := ⟨Equiv.swap (2 : Fin 4) 3, by trivial⟩

private def e : Dot (b.comp a) (b.comp a) where
  element := g
  intertwines := by
    intro k
    have hk : (k : U) (2 : Fin 4) = 2 :=
      MulAction.mem_stabilizer_iff.mp k.property.1
    have hk' : (k : U) (3 : Fin 4) = 3 :=
      MulAction.mem_stabilizer_iff.mp k.property.2
    apply Subtype.ext
    change (k : U) * Equiv.swap 2 3 = Equiv.swap 2 3 * (k : U)
    rw [mul_swap_eq_swap_mul, hk, hk']

private theorem outside : e.element ∉ b.toHom.range := by
  rintro ⟨h, he⟩
  have hh : (h : U) (3 : Fin 4) = 3 := MulAction.mem_stabilizer_iff.mp h.property
  have hg : (h : U) = Equiv.swap 2 3 := congrArg Subtype.val he
  rw [hg, Equiv.swap_apply_right] at hh
  exact (by decide : (2 : Fin 4) ≠ 3) hh

/-- The merged-strand dot (3 4) cannot be placed on the right input of the fixed merge. -/
theorem no_rightInput_replacement {R : Type v} [CommSemiring R] [Nontrivial R]
    (d : Dot a a) :
    (((id (R := R) (.up b)).horizontal (.upDot d)).vertical (.mergeUp b a)).eval ≠
      ((mergeUp b a).vertical (.upDot e)).eval :=
  mergeUp_rightInput_ne_trunk b a d e outside

end DotSlideExample
end MackeyDiagrams.Diagram
