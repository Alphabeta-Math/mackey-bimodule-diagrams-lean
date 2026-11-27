import MackeyDiagrams.Identities

/-! Fiber formulas for the two mixed crossing orders. -/

namespace MackeyDiagrams

universe u v
noncomputable section

namespace Biset.Hom

variable {K H : Type u} [Group K] [Group H] {X Y : Biset K H}
variable (R : Type v) [CommSemiring R]

theorem transferBasis_sum (f : X.carrier → Y.carrier)
    (finite : ∀ y, Set.Finite {x | f x = y}) (y : Y.carrier) :
    transferBasis R f finite y = ∑ x ∈ (finite y).toFinset, Finsupp.single x (1 : R) := by
  classical
  apply Finsupp.ext
  intro x
  rw [transferBasis_apply]
  change (if f x = y then 1 else 0) =
    (Finsupp.lapply x : (X.carrier →₀ R) →ₗ[R] R)
      (∑ t ∈ (finite y).toFinset, Finsupp.single t 1)
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  simp [(finite y).mem_toFinset]

@[simp] theorem transfer_single (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) (y : Y.carrier) (r : R) :
    (transfer R f hf finite).toLinearMap (Finsupp.single y r) =
      r • transferBasis R f finite y :=
  ofBasis_single _ _ _ _

theorem transfer_then_push_single (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) (y : Y.carrier) :
    ((transfer R f hf finite).vertical (ofFunction f hf)).toLinearMap (Finsupp.single y 1) =
      Finsupp.single y ((finite y).toFinset.card : R) := by
  classical
  change (ofFunction f hf : Hom R X Y).toLinearMap
      ((transfer R f hf finite).toLinearMap (Finsupp.single y 1)) = _
  rw [transfer_single, one_smul, transferBasis_sum, map_sum]
  have hs :
      ∑ x ∈ (finite y).toFinset, (ofFunction f hf : Hom R X Y).toLinearMap (Finsupp.single x 1) =
      ∑ _x ∈ (finite y).toFinset, Finsupp.single y (1 : R) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [ofFunction_single]
    have heq : f x = y := (finite y).mem_toFinset.mp hx
    rw [heq]
  rw [hs]
  rw [Finset.sum_const]
  change (finite y).toFinset.card • (Finsupp.lsingle y : R →ₗ[R] Y.carrier →₀ R) 1 = _
  rw [← map_nsmul]
  simp

theorem push_then_transfer_single (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) (x : X.carrier) :
    ((ofFunction f hf : Hom R X Y).vertical (transfer R f hf finite)).toLinearMap
        (Finsupp.single x 1) =
      ∑ z ∈ (finite (f x)).toFinset, Finsupp.single z (1 : R) := by
  change (transfer R f hf finite).toLinearMap
      ((ofFunction f hf : Hom R X Y).toLinearMap (Finsupp.single x 1)) = _
  rw [ofFunction_single, transfer_single, one_smul, transferBasis_sum]

end Biset.Hom

namespace Diagram

variable {U : Type u} [Group U] {H K G L : Subgroup U}
variable (R : Type v) [CommSemiring R]
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))
variable (finite : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z})

theorem projection_then_inclusion_single
    (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    ((mixedProjection (R := R) a b l r d finite).vertical
      (mixedMultiplication a b l r d)).eval.toLinearMap (Finsupp.single z 1) =
      Finsupp.single z ((finite z).toFinset.card : R) :=
  Biset.Hom.transfer_then_push_single R (Generator.mixedMultiplicationBasis a b l r d)
    (Generator.mixedMultiplication_equivariant a b l r d) finite z

theorem inclusion_then_projection_single
    (z : ((Biset.induction l).tensor (Biset.restriction r)).carrier) :
    ((mixedMultiplication (R := R) a b l r d).vertical
      (mixedProjection a b l r d finite)).eval.toLinearMap (Finsupp.single z 1) =
      ∑ w ∈ (finite (Generator.mixedMultiplicationBasis a b l r d z)).toFinset,
        Finsupp.single w (1 : R) :=
  Biset.Hom.push_then_transfer_single R (Generator.mixedMultiplicationBasis a b l r d)
    (Generator.mixedMultiplication_equivariant a b l r d) finite z

end Diagram

end
end MackeyDiagrams

