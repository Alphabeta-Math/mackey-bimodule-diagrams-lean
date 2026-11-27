import MackeyDiagrams.Embedding
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Group-element dots

A dot is a particular intertwining group element. Upward and downward dots
evaluate to right multiplication by that element and left multiplication by
its inverse, respectively.
-/

namespace MackeyDiagrams

variable {U : Type*} [Group U] {H G : Subgroup U}

structure Dot (a b : ConjEmbedding H G) where
  element : G
  intertwines : ∀ h : H, a.toHom h * element = element * b.toHom h

namespace Dot

variable {a b c : ConjEmbedding H G}

@[ext] theorem ext {d e : Dot a b} (h : d.element = e.element) : d = e := by
  cases d
  cases e
  cases h
  rfl

def id (a : ConjEmbedding H G) : Dot a a where
  element := 1
  intertwines := by simp

def ofRepresentatives (x y : U)
    (hx : ∀ h : H, (a.toHom h : U) = x * (h : U) * x⁻¹)
    (hy : ∀ h : H, (b.toHom h : U) = y * (h : U) * y⁻¹)
    (hG : x * y⁻¹ ∈ G) : Dot a b where
  element := ⟨x * y⁻¹, hG⟩
  intertwines := fun h => by
    apply Subtype.ext
    change (a.toHom h : U) * (x * y⁻¹) = (x * y⁻¹) * (b.toHom h : U)
    rw [hx, hy]
    group

/-- Stack the dot from a to b below the dot from b to c. -/
def vertical (d : Dot a b) (e : Dot b c) : Dot a c where
  element := d.element * e.element
  intertwines := fun h => by
    rw [← mul_assoc, d.intertwines, mul_assoc, e.intertwines, ← mul_assoc]

def inverse (d : Dot a b) : Dot b a where
  element := d.element⁻¹
  intertwines := fun h => by
    calc
      b.toHom h * d.element⁻¹ =
          d.element⁻¹ * (d.element * b.toHom h) * d.element⁻¹ := by group
      _ = d.element⁻¹ * (a.toHom h * d.element) * d.element⁻¹ := by rw [d.intertwines]
      _ = d.element⁻¹ * a.toHom h := by group

@[simp] theorem then_inverse (d : Dot a b) : d.vertical d.inverse = id a := by
  apply Dot.ext
  exact mul_inv_cancel d.element

@[simp] theorem inverse_then (d : Dot a b) : d.inverse.vertical d = id b := by
  apply Dot.ext
  exact inv_mul_cancel d.element

variable (R : Type*) [CommSemiring R]

noncomputable def evalUp (d : Dot a b) :
    MonoidAlgebra R G →ₗ[R] MonoidAlgebra R G where
  toFun := fun x => x * MonoidAlgebra.single d.element 1
  map_add' := fun x y => add_mul x y _
  map_smul' := fun r x => smul_mul_assoc r x _

noncomputable def evalDown (d : Dot a b) :
    MonoidAlgebra R G →ₗ[R] MonoidAlgebra R G where
  toFun := fun x => MonoidAlgebra.single d.element⁻¹ 1 * x
  map_add' := fun x y => mul_add _ x y
  map_smul' := fun r x => mul_smul_comm r _ x

@[simp] theorem evalUp_apply (d : Dot a b) (x : MonoidAlgebra R G) :
    d.evalUp R x = x * MonoidAlgebra.single d.element 1 := rfl

@[simp] theorem evalDown_apply (d : Dot a b) (x : MonoidAlgebra R G) :
    d.evalDown R x = MonoidAlgebra.single d.element⁻¹ 1 * x := rfl

theorem evalUp_intertwines_right (d : Dot a b) (h : H) (x : MonoidAlgebra R G) :
    d.evalUp R (x * MonoidAlgebra.single (a.toHom h) 1) =
      d.evalUp R x * MonoidAlgebra.single (b.toHom h) 1 := by
  simp [mul_assoc, d.intertwines]

theorem evalDown_intertwines_left (d : Dot a b) (h : H) (x : MonoidAlgebra R G) :
    d.evalDown R (MonoidAlgebra.single (a.toHom h) 1 * x) =
      MonoidAlgebra.single (b.toHom h) 1 * d.evalDown R x := by
  simp only [evalDown_apply, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one]
  have heq : b.toHom h * d.element⁻¹ = d.element⁻¹ * a.toHom h := d.inverse.intertwines h
  rw [heq]

@[simp] theorem evalUp_then (d : Dot a b) (e : Dot b c) :
    (d.vertical e).evalUp R = (e.evalUp R).comp (d.evalUp R) := by
  apply LinearMap.ext
  intro x
  simp [vertical, mul_assoc]

@[simp] theorem evalDown_then (d : Dot a b) (e : Dot b c) :
    (d.vertical e).evalDown R = (e.evalDown R).comp (d.evalDown R) := by
  apply LinearMap.ext
  intro x
  simp [vertical, ← mul_assoc]

end Dot

end MackeyDiagrams

