import MackeyDiagrams.ScopedCupEquivariance
import MackeyDiagrams.MixedIdentities

/-! At finite index a scoped reverse cup evaluates as the ordinary cup followed by its tail. -/

namespace MackeyDiagrams

universe u v
noncomputable section

variable {U : Type u} [Group U] {A B K : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace RightCupTrace

variable {p q : Word K B} {a : ConjEmbedding A B}

theorem eval_eq_reverseCup (scope : RightCupTrace R p q a)
    (finite : a.toHom.range.FiniteIndex) :
    scope.eval =
      (Diagram.vertical (Diagram.insertRightUnit p)
        (Diagram.vertical (Diagram.horizontal (Diagram.id p) (Diagram.reverseCup a finite))
          scope.tail)).eval := by
  classical
  let fiber := Generator.multiplicationCap_finiteFiber a finite (1 : B)
  letI : Fintype (reverseCupUnitFiber a) := fiber.fintype
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  suffices h : scope.eval.toLinearMap (Finsupp.single x 1) =
      (Diagram.vertical (Diagram.insertRightUnit p)
        (Diagram.vertical (Diagram.horizontal (Diagram.id p) (Diagram.reverseCup a finite))
          scope.tail)).eval.toLinearMap (Finsupp.single x 1) by
    have hr : Finsupp.single x r = r • Finsupp.single x (1 : R) := by
      simp [Finsupp.smul_single, smul_eq_mul]
    rw [hr, map_smul, map_smul, h]
  rw [eval_single]
  change basisSum scope.tail scope.finiteAfter x =
    scope.tail.eval.toLinearMap
      (((Biset.Hom.id p.basis : Biset.Hom R p.basis p.basis).horizontal
          (Generator.reverseCup R a finite)).toLinearMap
        ((Biset.insertRightUnit p.basis R).toLinearMap (Finsupp.single x 1)))
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single, Biset.Hom.horizontal_single, one_smul]
  change basisSum scope.tail scope.finiteAfter x =
    scope.tail.eval.toLinearMap
      (Biset.pairLinear R p.basis (reverseCupWord a).basis (Finsupp.single x 1)
        ((Generator.reverseCup R a finite).toLinearMap (Finsupp.single (1 : B) 1)))
  unfold Generator.reverseCup
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum, map_sum, map_sum]
  simp only [Biset.pairLinear_single, one_mul]
  calc
    basisSum scope.tail scope.finiteAfter x =
        ∑ i : reverseCupUnitFiber a, term scope.tail x i := by
      unfold basisSum
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_contra hterm
      exact hi (((scope.finiteAfter x).mem_toFinset).mpr hterm)
    _ = _ := by
      refine Finset.sum_bij (fun (i : reverseCupUnitFiber a) _ => i.val) ?_ ?_ ?_ ?_
      · intro i _
        exact fiber.mem_toFinset.mpr i.property
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro z hz
        exact ⟨⟨z, fiber.mem_toFinset.mp hz⟩, Finset.mem_univ _, rfl⟩
      · intro i _
        rfl

end RightCupTrace

end
end MackeyDiagrams
