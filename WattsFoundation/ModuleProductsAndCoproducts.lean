import Mathlib.Algebra.Category.ModuleCat.Products
import MackeyDiagrams
import WattsFoundation.ConcreteTensorBimoduleMap
import WattsFoundation.WattsMathlibReverse
import WattsFoundation.General.OriginalBimoduleAdapter
import WattsFoundation.ClassicalReconstruction

set_option maxHeartbeats 2000000

theorem ModuleProductsAndCoproducts : (
∀ {R : Type u} [Ring R] {I : Type v} (M : I → ModuleCat.{max v w} R),
  letI : DecidableEq I := Classical.decEq I
  let inclusion := DirectSum.coeFnLinearMap R (ι := I) (M := fun i => ↥(M i))
  Nonempty (CategoryTheory.Limits.IsLimit
    (CategoryTheory.Limits.Fan.mk (ModuleCat.of R (∀ i : I, ↥(M i)))
      (fun i => ModuleCat.ofHom (LinearMap.proj i)))) ∧
  Nonempty (CategoryTheory.Limits.IsColimit
    (CategoryTheory.Limits.Cofan.mk (ModuleCat.of R (DirectSum I (fun i => ↥(M i))))
      (fun i => ModuleCat.ofHom (DirectSum.lof R I (fun j => ↥(M j)) i)))) ∧
  Function.Injective inclusion ∧
  (∀ x : ∀ i : I, ↥(M i), x ∈ Set.range inclusion ↔ Set.Finite {i : I | x i ≠ 0})
) :=
(by
  intro R _ I M
  dsimp only
  let _ : DecidableEq I := Classical.decEq I
  -- Proposition 5.7's product uses coordinatewise linear maps. The checked
  -- product cone has the stated projections and lifts by assembling the coordinates.
  refine ⟨⟨ModuleCat.productConeIsLimit M⟩, ?_, ?_, ?_⟩
  · -- Alphabeta Math steps 1.1 and 2.1 construct the finite sum as a linear map.
    -- The checked cocone uses DirectSum.toModule for this map. Its factorization
    -- through each coordinate inclusion and uniqueness by linear map extensionality
    -- give steps 2.2 and 2.3. The index type is arbitrary, so step 3.1 is included.
    -- The reviewed Classical.decEq supplies the equality test for the inclusions.
    exact ⟨ModuleCat.coproductCoconeIsColimit M⟩
  · -- A dependent finitely supported function is determined by its coordinates.
    exact DFunLike.coe_injective
  · -- The article also identifies the image inside the product. Alphabeta Math
    -- assumes finite support in F1. Here we prove both directions of the image criterion.
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      exact DFinsupp.finite_support m
    · intro h
      let s := h.toFinset
      refine ⟨DFinsupp.mk s (fun i => x i), ?_⟩
      funext i
      change DFinsupp.mk (β := fun j => ↥(M j)) s (fun j => x j) i = x i
      by_cases hi : i ∈ s
      · exact DFinsupp.mk_of_mem hi
      · have hz : x i = 0 := by
          by_contra hn
          exact hi (h.mem_toFinset.mpr hn)
        exact (DFinsupp.mk_of_notMem hi).trans hz.symm)
