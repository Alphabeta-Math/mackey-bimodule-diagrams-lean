import Mathlib.Algebra.Category.ModuleCat.Products

universe u v w

private theorem finiteSupportIffInRange {R : Type u} [Ring R] {I : Type v}
    {M : I → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (x : ∀ i, M i) :
    x ∈ Set.range (DirectSum.coeFnLinearMap R (ι := I) (M := M)) ↔
      Set.Finite {i : I | x i ≠ 0} := by
  classical
  constructor
  · rintro ⟨m, rfl⟩
    exact DFinsupp.finite_support m
  · intro h
    let s := h.toFinset
    refine ⟨DFinsupp.mk s (fun i => x i), ?_⟩
    funext i
    change DFinsupp.mk s (fun j => x j) i = x i
    by_cases hi : i ∈ s
    · exact DFinsupp.mk_of_mem (β := M) (x := fun j => x j) hi
    · have hz : x i = 0 := by
        by_contra hn
        exact hi (h.mem_toFinset.mpr hn)
      exact (DFinsupp.mk_of_notMem (β := M) (x := fun j => x j) hi).trans hz.symm

theorem ModuleProductsAndCoproducts :
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
      (∀ x : ∀ i : I, ↥(M i), x ∈ Set.range inclusion ↔ Set.Finite {i : I | x i ≠ 0}) := by
  intro R _ I M
  dsimp only
  refine ⟨⟨ModuleCat.productConeIsLimit M⟩,
    ⟨@ModuleCat.coproductCoconeIsColimit R _ I M (Classical.decEq I)⟩, ?_, ?_⟩
  · exact DFunLike.coe_injective
  · exact finiteSupportIffInRange (R := R)

#print axioms ModuleProductsAndCoproducts
