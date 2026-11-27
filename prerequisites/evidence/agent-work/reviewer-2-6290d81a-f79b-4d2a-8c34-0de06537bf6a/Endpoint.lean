import Mathlib.Algebra.Category.ModuleCat.Products

universe u v w

noncomputable def Endpoint : Prop :=
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
