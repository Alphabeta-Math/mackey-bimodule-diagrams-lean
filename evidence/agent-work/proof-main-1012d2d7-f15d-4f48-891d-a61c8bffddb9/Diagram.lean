import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Iso
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
namespace InductionRestrictionAdjunctionSupport

open MackeyDiagrams
universe u

section
variable {U : Type u} [Group U] {H G : Subgroup U} (a : ConjEmbedding H G)

local notation "B" => MonoidAlgebra Complex G
local notation "φ" => MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
local notation "D" => Biset.restriction a
local notation "I" => Biset.induction a

-- The middle actions on D and I are regular. In their balanced quotient
-- [x,y] = [x*y,1]. This is the group-basis form of Alphabeta Math's tensor
-- universal property, Steps 3.1, 4.1 and 5.1. The diagonal action encodes
-- the balance relation, and linearization extends the map to group algebras.
private def downUpProduct : (Biset.tensor D I).carrier ≃ G where
  toFun := Quotient.lift (fun p : G × G => p.1 * p.2) (by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨g, hx, hy⟩
    change (a.toHom 1 * x * g⁻¹ = x') at hx
    change (g * y * (a.toHom 1)⁻¹ = y') at hy
    change x * y = x' * y'
    rw [← hx, ← hy]
    simp [mul_assoc])
  invFun x := Biset.pair D I x 1
  left_inv z := by
    refine Quotient.inductionOn z ?_
    rintro ⟨x, y⟩
    apply Quotient.sound (s := Biset.balance D I)
    refine ⟨y, ?_, ?_⟩
    · change a.toHom 1 * (x * y) * y⁻¹ = x
      simp [mul_assoc]
    · change y * 1 * (a.toHom 1)⁻¹ = y
      simp
  right_inv x := mul_one x

private noncomputable def downUpLinear : ((Biset.tensor D I).carrier →₀ Complex) ≃ₗ[Complex] B :=
  (Finsupp.domLCongr (downUpProduct a)).trans (MonoidAlgebra.coeffLinearEquiv Complex).symm

private theorem downUpLinear_single (x y : G) (c : Complex) :
    downUpLinear a (Finsupp.single (Biset.pair D I x y) c) = MonoidAlgebra.single (x * y) c := by
  simp only [downUpLinear, LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  rfl

-- Compare both bilinear maps on group elements with arbitrary coefficients.
private theorem bilinear_eq_of_single {G₁ G₂ : Type u} {V : Type u}
    [AddCommMonoid V] [Module Complex V]
    {p q : (G₁ →₀ Complex) →ₗ[Complex] (G₂ →₀ Complex) →ₗ[Complex] V}
    (hs : ∀ (g : G₁) (h : G₂) (r s : Complex),
      p (Finsupp.single g r) (Finsupp.single h s) =
        q (Finsupp.single g r) (Finsupp.single h s)) : p = q := by
  apply Finsupp.lhom_ext
  intro g r
  apply Finsupp.lhom_ext
  intro h s
  exact hs g h r s

private noncomputable def coeffProduct {G : Type u} [Group G] :
    (G →₀ Complex) →ₗ[Complex] (G →₀ Complex) →ₗ[Complex] MonoidAlgebra Complex G :=
  ((LinearMap.mul Complex (MonoidAlgebra Complex G)).compl₂
    (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap

private theorem downUpLinear_pair (x y : B) :
    downUpLinear a (Biset.pairLinear Complex D I x.coeff y.coeff) = x * y := by
  have he : (Biset.pairLinear Complex D I).compr₂ (downUpLinear a).toLinearMap =
      coeffProduct := by
    apply bilinear_eq_of_single
    intro g h r s
    change downUpLinear a (Biset.pairLinear Complex D I (Finsupp.single g r)
      (Finsupp.single h s)) = MonoidAlgebra.single g r * MonoidAlgebra.single h s
    rw [Biset.pairLinear_single, downUpLinear_single, MonoidAlgebra.single_mul_single]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x.coeff) y.coeff

private theorem downUpLinear_action (k l : H) (z : (Biset.tensor D I).carrier →₀ Complex) :
    downUpLinear a (Biset.actLinear Complex (Biset.tensor D I) (k, l⁻¹) z) =
      φ (MonoidAlgebra.single k 1) * downUpLinear a z * φ (MonoidAlgebra.single l 1) := by
  let left : B →ₗ[Complex] B :=
    LinearMap.mul Complex B (φ (MonoidAlgebra.single k 1))
  let right : B →ₗ[Complex] B :=
    (LinearMap.mul Complex B).flip (φ (MonoidAlgebra.single l 1))
  have he :
      (downUpLinear a).toLinearMap.comp (Biset.actLinear Complex (Biset.tensor D I) (k, l⁻¹)) =
        right.comp (left.comp (downUpLinear a).toLinearMap) := by
    apply Finsupp.lhom_ext
    intro q c
    refine Quotient.inductionOn q ?_
    rintro ⟨x, y⟩
    change downUpLinear a (Biset.actLinear Complex (Biset.tensor D I) (k, l⁻¹)
        (Finsupp.single (Biset.pair D I x y) c)) =
      φ (MonoidAlgebra.single k 1) * downUpLinear a (Finsupp.single (Biset.pair D I x y) c) *
        φ (MonoidAlgebra.single l 1)
    rw [Biset.actLinear_single]
    change downUpLinear a (Finsupp.single (Biset.pair D I (a.toHom k * x * (1 : G)⁻¹)
        ((1 : G) * y * (a.toHom l⁻¹)⁻¹)) c) = _
    simp only [downUpLinear_single, inv_one, mul_one, one_mul, map_inv, inv_inv]
    change _ = MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single k 1) * _ *
      MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single l 1)
    simp [MonoidAlgebra.mapDomain_single, MonoidAlgebra.single_mul_single, mul_assoc]
  exact LinearMap.congr_fun he z

private theorem ordinaryCup_pair
    (hφ : ∀ (h : H) (c : Complex), φ (MonoidAlgebra.single h c) = MonoidAlgebra.single (a.toHom h) c)
    (h : MonoidAlgebra Complex H) :
    (Diagram.ordinaryCup (R := Complex) a).eval.toLinearMap h.coeff =
      Biset.pairLinear Complex D I (φ h).coeff (MonoidAlgebra.coeff (1 : B)) := by
  let coeff := MonoidAlgebra.coeffLinearEquiv (M := G) (S := Complex) Complex
  let q := (Biset.pairLinear Complex D I).flip (MonoidAlgebra.coeff (1 : B))
  have he :
      (Diagram.ordinaryCup (R := Complex) a).eval.toLinearMap =
        q.comp (coeff.toLinearMap.comp ((φ).toLinearMap.comp
          (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap)) := by
    apply Finsupp.lhom_ext
    intro k c
    change (Diagram.ordinaryCup (R := Complex) a).eval.toLinearMap (Finsupp.single k c) =
      Biset.pairLinear Complex D I (φ (MonoidAlgebra.single k c)).coeff (Finsupp.single 1 1)
    rw [hφ, MonoidAlgebra.coeff_single, Biset.pairLinear_single, mul_one,
      Diagram.eval_ordinaryCup_single]
  exact LinearMap.congr_fun he h.coeff

private theorem multiplicationCap_pair (x y : B) :
    (Diagram.multiplicationCap (R := Complex) a).eval.toLinearMap
      (Biset.pairLinear Complex I D x.coeff y.coeff) = (x * y).coeff := by
  let coeff := MonoidAlgebra.coeffLinearEquiv (M := G) (S := Complex) Complex
  let cap := (Diagram.multiplicationCap (R := Complex) a).eval.toLinearMap
  apply coeff.symm.injective
  have he : (Biset.pairLinear Complex I D).compr₂ (coeff.symm.toLinearMap.comp cap) =
      coeffProduct := by
    apply bilinear_eq_of_single
    intro g h r s
    change MonoidAlgebra.ofCoeff (cap (Biset.pairLinear Complex I D
      (Finsupp.single g r) (Finsupp.single h s))) =
      MonoidAlgebra.single g r * MonoidAlgebra.single h s
    rw [Biset.pairLinear_single, Diagram.eval_multiplicationCap_single,
      MonoidAlgebra.single_mul_single]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun he x.coeff) y.coeff

end
end InductionRestrictionAdjunctionSupport
