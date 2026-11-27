import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Basic.Complex.Basic
import Proofs.ConjugationEmbeddingCentralizerCoset
import Proofs.Bimodule
import Proofs.ModuleTensorUniversalProperty
import MackeyDiagrams

section
open MackeyDiagrams
universe u w

-- Alphabeta Math, Steps 3.1, 4.1 and 5.1. For two linearized bisets the
-- additive relations already hold by bilinearity. The orbit quotient enforces
-- diagonal group balance. Extend this to the middle group algebra by linearity.
private theorem strandBalancedProduct {K H J : Type u} [Group K] [Group H] [Group J]
    (X : Biset K H) (Y : Biset H J) :
    let right := fun (r : MonoidAlgebra Complex H) (x : X.carrier →₀ Complex) =>
      freeLift Complex (fun h : H => X.actLinear Complex (1, h⁻¹) x) r.coeff
    let left := fun (r : MonoidAlgebra Complex H) (y : Y.carrier →₀ Complex) =>
      freeLift Complex (fun h : H => Y.actLinear Complex (h, 1) y) r.coeff
    let pair := Biset.pairLinear Complex X Y
    (∀ r x y, pair (right r x) y = pair x (left r y)) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module Complex M]
        (f : (X.carrier →₀ Complex) →ₗ[Complex] (Y.carrier →₀ Complex) →ₗ[Complex] M),
      (∀ r x y, f (right r x) y = f x (left r y)) →
      ∃! lift : ((X.tensor Y).carrier →₀ Complex) →ₗ[Complex] M,
        ∀ x y, lift (pair x y) = f x y) := by
  intro right left pair
  have undo (h : H) (x : X.carrier →₀ Complex) :
      X.actLinear Complex (1, h⁻¹) (X.actLinear Complex (1, h) x) = x := by
    have comp_eq :
        (X.actLinear Complex (1, h⁻¹)).comp (X.actLinear Complex (1, h)) =
          LinearMap.id := by
      apply Finsupp.lhom_ext
      intro a c
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Biset.actLinear_single, ← X.mul_act,
        Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, X.one_act]
    exact LinearMap.congr_fun comp_eq x
  have right_single (h : H) (x : X.carrier →₀ Complex) :
      right (MonoidAlgebra.single h 1) x = X.actLinear Complex (1, h⁻¹) x := by
    simp [right]
  have left_single (h : H) (y : Y.carrier →₀ Complex) :
      left (MonoidAlgebra.single h 1) y = Y.actLinear Complex (h, 1) y := by
    simp [left]
  constructor
  · intro r x y
    let l := (pair.flip y).comp
      (freeLift Complex (fun h : H => X.actLinear Complex (1, h⁻¹) x))
    let m := (pair x).comp
      (freeLift Complex (fun h : H => Y.actLinear Complex (h, 1) y))
    have hlm : l = m := by
      apply Finsupp.lhom_ext
      intro h c
      change pair (freeLift Complex _ (Finsupp.single h c)) y =
        pair x (freeLift Complex _ (Finsupp.single h c))
      simp only [freeLift_single, map_smul, LinearMap.smul_apply]
      -- Reindex the inverse in the first slot of diagonal balance.
      have heq := Biset.pairLinear_balance Complex X Y h
        (X.actLinear Complex (1, h⁻¹) x) y
      have hinv := undo h⁻¹ x
      simp only [inv_inv] at hinv
      rw [hinv] at heq
      exact congrArg (fun z => c • z) heq.symm
    exact LinearMap.congr_fun hlm r.coeff
  · intro M _ _ f hf
    have diagonal : Biset.IsBalanced f := by
      intro h x y
      have heq := hf (MonoidAlgebra.single h 1) (X.actLinear Complex (1, h) x) y
      rw [right_single, left_single, undo] at heq
      exact heq.symm
    exact ⟨Biset.liftBalanced f diagonal, Biset.liftBalanced_pairLinear f diagonal,
      fun g hg => Biset.liftBalanced_unique f diagonal g hg⟩

-- A pair of group elements acts by left and right multiplication on basis
-- vectors. Both expressions extend to the whole group algebra by linearity.
private theorem strandBasisMultiplication {G : Type u} [Group G] (a b : G)
    (x : MonoidAlgebra Complex G) :
    MonoidAlgebra.ofCoeff
      (Finsupp.lmapDomain Complex Complex (fun z : G => a * z * b) x.coeff) =
      MonoidAlgebra.single a 1 * (x * MonoidAlgebra.single b 1) := by
  induction x using MonoidAlgebra.induction_on with
  | of z =>
    simp [MonoidAlgebra.of_apply, Finsupp.lmapDomain_apply, MonoidAlgebra.single_mul_single,
      mul_assoc]
  | add x y hx hy =>
    simpa only [MonoidAlgebra.coeff_add, map_add, MonoidAlgebra.ofCoeff_add, add_mul,
      mul_add, hx, hy]
  | smul r x hx =>
    simpa only [MonoidAlgebra.coeff_smul, map_smul, MonoidAlgebra.ofCoeff_smul,
      smul_mul_assoc, mul_smul_comm, hx]

end
