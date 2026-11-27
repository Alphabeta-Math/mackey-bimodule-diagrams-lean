import MackeyDiagrams.DiagramVectorSpace
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.TransferInstance

/-! The endomorphism maps presented by diagrams form a unital algebra.
Multiplication uses ordinary function composition: the right factor is
stacked below the left factor. -/
namespace MackeyDiagrams.DiagramAlgebra
universe u v
variable {U : Type u} [Group U] {K H : Subgroup U}
variable (R : Type v) [CommRing R] (p : Word K H)

abbrev Carrier := p.basis.carrier →₀ R

noncomputable def presented : Subalgebra R (Module.End R (Carrier R p)) where
  carrier := Set.range fun d : LabelledDrawing R p p => d.interpret.eval.toLinearMap
  zero_mem' := ⟨.ordinary (.zero p p), rfl⟩
  add_mem' := by
    rintro _ _ ⟨d, rfl⟩ ⟨e, rfl⟩
    exact ⟨.add d e, rfl⟩
  one_mem' := ⟨.ordinary (.id p), rfl⟩
  mul_mem' := by
    rintro _ _ ⟨d, rfl⟩ ⟨e, rfl⟩
    exact ⟨.vertical e d, rfl⟩
  algebraMap_mem' := by
    intro c
    refine ⟨.scale c (.ordinary (.id p)), ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    rfl

theorem evaluated_mem (x : DiagramVectorSpace.Expressions R p p) :
    DiagramVectorSpace.evaluate R p p x ∈ presented R p := by
  change DiagramVectorSpace.evaluate R p p x ∈ (presented R p).toSubmodule
  rw [DiagramVectorSpace.evaluate, freeLift, Finsupp.lsum_apply]
  change (∑ d ∈ x.support, x d • d.interpret.eval.toLinearMap) ∈ (presented R p).toSubmodule
  apply Submodule.sum_mem
  intro d hd
  exact (presented R p).smul_mem ⟨d, rfl⟩ (x d)

theorem evaluation_range_eq :
    (DiagramVectorSpace.evaluate R p p).range = (presented R p).toSubmodule := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact evaluated_mem R p x
  · rintro ⟨d, rfl⟩
    exact ⟨Finsupp.single d 1, DiagramVectorSpace.singleton_eval R p p d⟩

section Generic
variable {S A B : Type*} [CommRing S] [AddCommGroup A] [Module S A]
  [AddCommGroup B] [Module S B]

noncomputable def quotientImage (f : A →ₗ[S] B) (T : Submodule S B)
    (h : f.range = T) : (A ⧸ f.ker) ≃ₗ[S] T :=
  f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ h)
end Generic

/-! Transport the algebra structure from a subalgebra that is exactly the
    range of a linear evaluation map. These are explicit structures, not
    global instances, to avoid changing the existing quotient module instance. -/
section AlgebraTransport
variable {S A B : Type*} [CommRing S] [AddCommGroup A] [Module S A]
  [Ring B] [Algebra S B]
variable (f : A →ₗ[S] B) (T : Subalgebra S B) (h : f.range = T.toSubmodule)

noncomputable def quotientEquiv : (A ⧸ f.ker) ≃ T :=
  (quotientImage f T.toSubmodule h).toEquiv

theorem quotientEquiv_mk (x : A) :
    ((quotientEquiv f T h (Submodule.Quotient.mk x) : T) : B) = f x := by
  simp [quotientEquiv, quotientImage, LinearMap.quotKerEquivRange_apply_mk]
theorem quotientEquiv_add (x y : A ⧸ f.ker) :
    quotientEquiv f T h (x + y) = quotientEquiv f T h x + quotientEquiv f T h y := by
  exact (quotientImage f T.toSubmodule h).map_add x y

theorem quotientEquiv_smul (c : S) (x : A ⧸ f.ker) :
    quotientEquiv f T h (c • x) = c • quotientEquiv f T h x := by
  exact (quotientImage f T.toSubmodule h).map_smul c x

@[instance_reducible] noncomputable def quotientRing : Ring (A ⧸ f.ker) :=
  Equiv.ring (quotientEquiv f T h)

@[instance_reducible] noncomputable def quotientAlgebra :
    letI := quotientRing f T h
    Algebra S (A ⧸ f.ker) :=
  Equiv.algebra S (quotientEquiv f T h)

noncomputable def quotientAlgEquiv :
    letI := quotientRing f T h
    letI := quotientAlgebra f T h
    (A ⧸ f.ker) ≃ₐ[S] T :=
  Equiv.algEquiv S (quotientEquiv f T h)
end AlgebraTransport

end MackeyDiagrams.DiagramAlgebra
