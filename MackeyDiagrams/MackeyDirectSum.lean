import MackeyDiagrams.MackeyOrthogonality
import Mathlib.LinearAlgebra.DFinsupp

/-! Orthogonal inclusions and projections with a pointwise finite identity
sum give the dependent direct sum of the summands. -/

namespace MackeyDiagrams

universe u v w

variable {R : Type v} [CommSemiring R] {J : Type w}
variable {V : Type u} [AddCommMonoid V] [Module R V]
variable {W : J → Type u} [∀ j, AddCommMonoid (W j)] [∀ j, Module R (W j)]

section
variable (inc : ∀ j, W j →ₗ[R] V) (proj : ∀ j, V →ₗ[R] W j)
variable (finite : ∀ x, Set.Finite (Function.support (fun j => inc j (proj j x))))
variable (sum : ∀ x, x = ∑ j ∈ (finite x).toFinset, inc j (proj j x))
variable (diagonal : ∀ j y, proj j (inc j y) = y)
variable (offDiagonal : ∀ i j, i ≠ j → ∀ y, proj j (inc i y) = 0)

include diagonal in
private theorem supported_projection (x : V) (j : J) :
    proj j x ≠ 0 ↔ inc j (proj j x) ≠ 0 := by
  constructor
  · intro h he
    apply h
    have hh := congrArg (proj j) he
    rw [diagonal, map_zero] at hh
    exact hh
  · intro h he
    exact h (by rw [he, map_zero])

private noncomputable def projectIntoSumValue (x : V) : Π₀ j, W j := by
  classical
  exact DFinsupp.mk (finite x).toFinset (fun j => proj j x)

include diagonal in
private theorem projectIntoSumValue_apply (x : V) (j : J) :
    projectIntoSumValue inc proj finite x j = proj j x := by
  classical
  unfold projectIntoSumValue
  rw [DFinsupp.mk_apply]
  split
  · rfl
  · rename_i outside
    symm
    by_contra he
    exact outside ((finite x).mem_toFinset.mpr ((supported_projection inc proj diagonal x j).mp he))

private noncomputable def projectIntoSum (diagonal : ∀ j y, proj j (inc j y) = y) :
    V →ₗ[R] (Π₀ j, W j) where
  toFun := projectIntoSumValue inc proj finite
  map_add' x y := by
    apply DFinsupp.ext
    intro j
    change projectIntoSumValue inc proj finite (x+y) j =
      projectIntoSumValue inc proj finite x j + projectIntoSumValue inc proj finite y j
    repeat rw [projectIntoSumValue_apply inc proj finite diagonal]
    rw [map_add]
  map_smul' c x := by
    apply DFinsupp.ext
    intro j
    change projectIntoSumValue inc proj finite (c • x) j =
      c • projectIntoSumValue inc proj finite x j
    repeat rw [projectIntoSumValue_apply inc proj finite diagonal]
    rw [map_smul]

private theorem projectIntoSum_apply (x : V) (j : J) :
    (projectIntoSum inc proj finite diagonal x) j = proj j x :=
  projectIntoSumValue_apply inc proj finite diagonal x j

include sum diagonal offDiagonal in
/-- The coordinates of the direct sum equivalence are the given projections. -/
noncomputable def orthogonalDirectSum : V ≃ₗ[R] (Π₀ j, W j) := by
  classical
  let f := projectIntoSum inc proj finite diagonal
  let g := DFinsupp.lsum R inc
  have right : f.comp g = LinearMap.id := by
    apply DFinsupp.lhom_ext
    intro i y
    change f (g (DFinsupp.single i y)) = DFinsupp.single i y
    rw [show g (DFinsupp.single i y) = inc i y from DFinsupp.lsum_single R inc i y]
    ext j
    change (f (inc i y)) j = (DFinsupp.single i y) j
    rw [projectIntoSum_apply]
    by_cases h : j = i
    · subst j
      rw [DFinsupp.single_eq_same, diagonal]
    · rw [DFinsupp.single_eq_of_ne h, offDiagonal i j (fun e => h e.symm)]
  have left (x : V) : g (f x) = x := by
    dsimp only [g]
    rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
    have hs : (f x).support = (finite x).toFinset := by
      ext j
      rw [DFinsupp.mem_support_iff, Set.Finite.mem_toFinset, projectIntoSum_apply]
      exact supported_projection inc proj diagonal x j
    change (∑ j ∈ (f x).support, inc j ((f x) j)) = x
    rw [hs]
    calc
      _ = ∑ j ∈ (finite x).toFinset, inc j (proj j x) :=
        Finset.sum_congr rfl (fun j _ => congrArg (inc j) (projectIntoSum_apply inc proj finite diagonal x j))
      _ = x := (sum x).symm
  exact LinearEquiv.ofLinearMap f g right (LinearMap.ext left)

theorem orthogonalDirectSum_apply (x : V) (j : J) :
    (orthogonalDirectSum inc proj finite sum diagonal offDiagonal x) j = proj j x :=
  projectIntoSum_apply inc proj finite diagonal x j

end
end MackeyDiagrams
