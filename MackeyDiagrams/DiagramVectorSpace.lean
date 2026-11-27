import MackeyDiagrams.DrawingShape
import Mathlib.LinearAlgebra.Isomorphisms

/-! A fixed pair of fully labelled boundary words determines a vector space
of finite formal linear combinations of diagram expressions. Quotient by the
kernel of evaluation, so equality in the quotient is exactly equality of the
resulting bimodule maps. This does not identify geometric shapes. -/

namespace MackeyDiagrams.DiagramVectorSpace
set_option maxHeartbeats 2000000
universe u v
variable {U : Type u} [Group U] {K H : Subgroup U}
variable (R : Type v) [CommRing R] (p q : Word K H)

abbrev Expressions := LabelledDrawing R p q →₀ R

noncomputable def evaluate : Expressions R p q →ₗ[R]
    ((p.basis.carrier →₀ R) →ₗ[R] (q.basis.carrier →₀ R)) :=
  freeLift R fun d => d.interpret.eval.toLinearMap

abbrev MapClasses := Expressions R p q ⧸ (evaluate R p q).ker

theorem quotient_eq_iff (x y : Expressions R p q) :
    (Submodule.Quotient.mk x : MapClasses R p q) = Submodule.Quotient.mk y ↔
      evaluate R p q x = evaluate R p q y := by
  rw [Submodule.Quotient.eq]
  simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]

theorem singleton_eval (d : LabelledDrawing R p q) :
    evaluate R p q (Finsupp.single d 1) = d.interpret.eval.toLinearMap := by
  rw [evaluate, freeLift_single, one_smul]

theorem singleton_classes_eq_iff (d e : LabelledDrawing R p q) :
    (Submodule.Quotient.mk (Finsupp.single d 1) : MapClasses R p q) =
      Submodule.Quotient.mk (Finsupp.single e 1) ↔ d.interpret.eval = e.interpret.eval := by
  rw [quotient_eq_iff, singleton_eval, singleton_eval]
  constructor
  · exact Biset.Hom.ext
  · intro h; exact congrArg Biset.Hom.toLinearMap h

/-- Older `Diagram.eval` statements embed in the eligible labelled syntax:
    passing to classes neither adds nor loses equality of evaluated maps. -/
theorem ordinary_classes_eq_iff (d e : Diagram R p q) :
    (Submodule.Quotient.mk (Finsupp.single (.ordinary d) 1) : MapClasses R p q) =
      Submodule.Quotient.mk (Finsupp.single (.ordinary e) 1) ↔ d.eval = e.eval := by
  exact singleton_classes_eq_iff R p q (.ordinary d) (.ordinary e)

theorem singleton_add (d e : LabelledDrawing R p q) :
    (Submodule.Quotient.mk (Finsupp.single (.add d e) 1) : MapClasses R p q) =
      Submodule.Quotient.mk (Finsupp.single d 1 + Finsupp.single e 1) := by
  apply (quotient_eq_iff R p q _ _).2
  rw [map_add, singleton_eval, singleton_eval, singleton_eval]
  rfl

theorem singleton_scale (c : R) (d : LabelledDrawing R p q) :
    (Submodule.Quotient.mk (Finsupp.single (.scale c d) 1) : MapClasses R p q) =
      Submodule.Quotient.mk (c • Finsupp.single d 1) := by
  apply (quotient_eq_iff R p q _ _).2
  rw [map_smul, singleton_eval, singleton_eval]
  rfl

end MackeyDiagrams.DiagramVectorSpace
