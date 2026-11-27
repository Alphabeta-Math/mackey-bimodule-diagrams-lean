import Mathlib.Data.Finsupp.ToDFinsupp
import MackeyDiagrams
import Proofs.ComplexEilenbergWatts
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionAdjunction
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.ModuleTensorUniversalProperty
import Proofs.BalancedTensorAssociativity
set_option maxHeartbeats 2000000

open MackeyDiagrams
open scoped ModuleCat.Algebra

namespace DiagramFunctorProof

universe u v
open MonoidAlgebra

private abbrev Alg (H : Type u) [Monoid H] := MonoidAlgebra Complex H

-- Xiao § 1.3. The left cosets index a basis for the right action.
-- No finiteness of the left-coset space is needed.
private theorem freeRight {H G : Type u} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) :
    letI : Module (Alg H)ᵐᵒᵖ (Alg G) :=
      Module.compHom (Alg G) (RingHom.op (mapDomainAlgHom Complex Complex f).toRingHom)
    Module.Free (Alg H)ᵐᵒᵖ (Alg G) := by
  classical
  let A := Alg H
  let B := Alg G
  let I := G ⧸ f.range
  let φ : A →ₐ[Complex] B := mapDomainAlgHom Complex Complex f
  letI : Module Aᵐᵒᵖ B := Module.compHom B (RingHom.op φ.toRingHom)
  let rep (i : I) : G := Quotient.out i
  let keys : (Sigma fun _ : I => H) ≃ G :=
    Equiv.ofBijective (fun ih => rep ih.1 * f ih.2) (by
      have quotient_eq (i : I) (h : H) : ((rep i * f h : G) : I) = i := by
        refine (QuotientGroup.eq.mpr ?_).trans (Quotient.out_eq' i)
        exact ⟨h⁻¹, by simp [rep, mul_inv_rev, mul_assoc]⟩
      constructor
      · rintro ⟨i, h⟩ ⟨j, k⟩ (e : rep i * f h = rep j * f k)
        have eqij : i = j := (quotient_eq i h).symm.trans
          ((congrArg (fun x : G => (x : I)) e).trans (quotient_eq j k))
        subst j
        congr 1
        exact hf (mul_left_cancel e)
      · intro g
        let i : I := (g : I)
        have eqi : ((rep i : G) : I) = (g : I) := Quotient.out_eq' i
        obtain ⟨h, hh⟩ := QuotientGroup.eq.mp eqi
        exact ⟨⟨i, h⟩, by change rep i * f h = g; rw [hh, mul_inv_cancel_left]⟩)
  let summands : (I →₀ A) ≃ₗ[Complex] B :=
    ((finsuppLequivDFinsupp Complex).trans
      ((DFinsupp.mapRange.linearEquiv (fun _ => coeffLinearEquiv Complex)).trans
        (sigmaFinsuppLequivDFinsupp Complex).symm)).trans
      ((Finsupp.domLCongr (R := Complex) keys).trans (coeffLinearEquiv Complex).symm)
  have onSingle (i : I) (h : H) (z : Complex) :
      summands (Finsupp.single i (MonoidAlgebra.single h z)) =
        MonoidAlgebra.single (rep i * f h) z := by
    apply (coeffLinearEquiv Complex).injective
    change (Finsupp.domLCongr (R := Complex) keys)
      ((sigmaFinsuppLequivDFinsupp Complex).symm
        ((DFinsupp.mapRange.linearEquiv (fun _ => coeffLinearEquiv Complex))
          (finsuppLequivDFinsupp Complex (Finsupp.single i (MonoidAlgebra.single h z))))) =
      Finsupp.single (keys ⟨i, h⟩) z
    simp only [finsuppLequivDFinsupp_apply_apply, Finsupp.toDFinsupp_single,
      DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single,
      coeffLinearEquiv_apply]
    have hs : sigmaFinsuppEquivDFinsupp.symm
        (DFinsupp.single i (Finsupp.single h z) : Π₀ _ : I, H →₀ Complex) =
          Finsupp.single (⟨i, h⟩ : Sigma fun _ : I => H) z :=
      sigmaFinsuppEquivDFinsupp.symm_apply_eq.mpr
        (sigmaFinsuppEquivDFinsupp_single (⟨i, h⟩ : Sigma fun _ : I => H) z).symm
    change Finsupp.equivMapDomain keys
      (sigmaFinsuppEquivDFinsupp.symm (DFinsupp.single i (Finsupp.single h z))) = _
    rw [hs, Finsupp.equivMapDomain_single]
  have onSummand (i : I) (a : A) :
      summands (Finsupp.single i a) = MonoidAlgebra.single (rep i) 1 * φ a := by
    induction a using MonoidAlgebra.induction_on with
    | of h =>
        change summands (Finsupp.single i (MonoidAlgebra.single h 1)) = _
        rw [onSingle]
        change _ = MonoidAlgebra.single (rep i) 1 * MonoidAlgebra.mapDomain f
          (MonoidAlgebra.single h 1)
        rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.single_mul_single, one_mul]
    | add a b ha hb => rw [Finsupp.single_add, map_add, ha, hb, map_add, mul_add]
    | smul z a ha =>
        rw [← Finsupp.smul_single, map_smul, ha, map_smul, mul_smul_comm]
  let e : (I →₀ A) ≃ₗ[Aᵐᵒᵖ] B :=
    { toEquiv := summands.toEquiv
      map_add' := summands.map_add
      map_smul' := fun r x => by
        change summands (r • x) = summands x * φ r.unop
        induction x using Finsupp.induction_linear with
        | zero => simp
        | add x y hx hy => simp only [smul_add, map_add, hx, hy, add_mul]
        | single i a =>
            rw [Finsupp.smul_single, onSummand, onSummand]
            change MonoidAlgebra.single (rep i) 1 * φ (a * r.unop) = _
            rw [map_mul, mul_assoc] }
  exact Module.Free.of_equiv ((Finsupp.mapRange.linearEquiv
    (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm).trans e)

end DiagramFunctorProof
