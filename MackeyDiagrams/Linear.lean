import MackeyDiagrams.Biset
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Linearization

A morphism is an equivariant linear map on the free modules of the two bases.
Equivariance uses the combined left action and inverse right action.
-/

namespace MackeyDiagrams

universe u v

noncomputable section

variable (R : Type v) [CommSemiring R]

noncomputable def freeLift {X : Type u} {M : Type*} [AddCommMonoid M] [Module R M]
    (f : X → M) : (X →₀ R) →ₗ[R] M :=
  Finsupp.lsum R (fun x => LinearMap.toSpanSingleton R M (f x))

@[simp] theorem freeLift_single {X : Type u} {M : Type*} [AddCommMonoid M] [Module R M]
    (f : X → M) (x : X) (r : R) :
    freeLift R f (Finsupp.single x r) = r • f x := by
  simp [freeLift, LinearMap.toSpanSingleton_apply]

namespace Biset

variable {K H J : Type u} [Group K] [Group H] [Group J]

noncomputable def actLinear (X : Biset K H) (g : K × H) :
    (X.carrier →₀ R) →ₗ[R] X.carrier →₀ R :=
  Finsupp.lmapDomain R R (X.act g)

@[simp] theorem actLinear_single (X : Biset K H) (g : K × H) (x : X.carrier) (r : R) :
    X.actLinear R g (Finsupp.single x r) = Finsupp.single (X.act g x) r := by
  simp [actLinear]

@[simp] theorem actLinear_one (X : Biset K H) :
    X.actLinear R 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x r
  simp [X.one_act]

structure Hom (X Y : Biset K H) where
  toLinearMap : (X.carrier →₀ R) →ₗ[R] Y.carrier →₀ R
  commutes : ∀ g x, toLinearMap (X.actLinear R g x) = Y.actLinear R g (toLinearMap x)

namespace Hom

variable {R} {W X Y Z : Biset K H}

@[ext] theorem ext {f g : Hom R X Y} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

noncomputable def ofBasis (f : X.carrier → Y.carrier →₀ R)
    (hf : ∀ g x, f (X.act g x) = Y.actLinear R g (f x)) : Hom R X Y where
  toLinearMap := freeLift R f
  commutes := by
    intro g
    have h :
        (freeLift R f).comp (X.actLinear R g) =
          (Y.actLinear R g).comp (freeLift R f) := by
      apply Finsupp.lhom_ext
      intro x r
      simp [hf]
    exact LinearMap.congr_fun h

@[simp] theorem ofBasis_single (f : X.carrier → Y.carrier →₀ R)
    (hf : ∀ g x, f (X.act g x) = Y.actLinear R g (f x)) (x : X.carrier) (r : R) :
    (ofBasis f hf).toLinearMap (Finsupp.single x r) = r • f x :=
  freeLift_single R f x r

noncomputable def ofFunction (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x)) : Hom R X Y :=
  ofBasis (fun x => Finsupp.single (f x) 1) (by intro g x; simp [hf])

@[simp] theorem ofFunction_single (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x)) (x : X.carrier) (r : R) :
    (ofFunction f hf : Hom R X Y).toLinearMap (Finsupp.single x r) = Finsupp.single (f x) r := by
  simp [ofFunction, Finsupp.smul_single]

def id (X : Biset K H) : Hom R X X where
  toLinearMap := LinearMap.id
  commutes := by simp

def vertical (f : Hom R X Y) (g : Hom R Y Z) : Hom R X Z where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  commutes := by intro k x; simp only [LinearMap.comp_apply, f.commutes, g.commutes]

def zero : Hom R X Y where
  toLinearMap := 0
  commutes := by simp

def add (f g : Hom R X Y) : Hom R X Y where
  toLinearMap := f.toLinearMap + g.toLinearMap
  commutes := by intro k x; simp only [LinearMap.add_apply, f.commutes, g.commutes, map_add]

def scale (r : R) (f : Hom R X Y) : Hom R X Y where
  toLinearMap := r • f.toLinearMap
  commutes := by intro k x; simp only [LinearMap.smul_apply, f.commutes, map_smul]

@[simp] theorem vertical_id (f : Hom R X Y) : f.vertical (id Y) = f := rfl

@[simp] theorem id_vertical (f : Hom R X Y) : (id X).vertical f = f := rfl

theorem vertical_assoc (f : Hom R W X) (g : Hom R X Y) (h : Hom R Y Z) :
    (f.vertical g).vertical h = f.vertical (g.vertical h) := rfl

end Hom

noncomputable def pairLinear (X : Biset K H) (Y : Biset H J) :
    (X.carrier →₀ R) →ₗ[R] (Y.carrier →₀ R) →ₗ[R] (X.tensor Y).carrier →₀ R :=
  freeLift R (fun x => Finsupp.lmapDomain R R (X.pair Y x))

@[simp] theorem pairLinear_single (X : Biset K H) (Y : Biset H J)
    (x : X.carrier) (y : Y.carrier) (a b : R) :
    pairLinear R X Y (Finsupp.single x a) (Finsupp.single y b) =
      Finsupp.single (X.pair Y x y) (a * b) := by
  simp [pairLinear, Finsupp.smul_single, smul_eq_mul]

theorem pairLinear_action (X : Biset K H) (Y : Biset H J)
    (gx : K × H) (gy : H × J) (gz : K × J)
    (h : ∀ x y, X.pair Y (X.act gx x) (Y.act gy y) = (X.tensor Y).act gz (X.pair Y x y))
    (x : X.carrier →₀ R) (y : Y.carrier →₀ R) :
    pairLinear R X Y (X.actLinear R gx x) (Y.actLinear R gy y) =
      (X.tensor Y).actLinear R gz (pairLinear R X Y x y) := by
  have outer :
      ((pairLinear R X Y).flip (Y.actLinear R gy y)).comp (X.actLinear R gx) =
      ((X.tensor Y).actLinear R gz).comp ((pairLinear R X Y).flip y) := by
    apply Finsupp.lhom_ext
    intro x a
    have inner :
        (pairLinear R X Y (Finsupp.single (X.act gx x) a)).comp (Y.actLinear R gy) =
        ((X.tensor Y).actLinear R gz).comp (pairLinear R X Y (Finsupp.single x a)) := by
      apply Finsupp.lhom_ext
      intro y b
      simp [h]
    simpa using LinearMap.congr_fun inner y
  exact LinearMap.congr_fun outer x

theorem pairLinear_balance (X : Biset K H) (Y : Biset H J) (h : H)
    (x : X.carrier →₀ R) (y : Y.carrier →₀ R) :
    pairLinear R X Y (X.actLinear R (1, h) x) (Y.actLinear R (h, 1) y) =
      pairLinear R X Y x y := by
  have heq (s : X.carrier) (t : Y.carrier) :
      X.pair Y (X.act (1, h) s) (Y.act (h, 1) t) = (X.tensor Y).act 1 (X.pair Y s t) := by
    rw [Biset.one_act]
    exact (Quotient.sound (s := X.balance Y) (a := (s,t))
      (b := (X.act (1, h) s, Y.act (h, 1) t)) ⟨h, rfl, rfl⟩).symm
  simpa using pairLinear_action R X Y (1,h) (h,1) 1 heq x y

namespace Hom

variable {R} {X X' : Biset K H} {Y Y' : Biset H J}

private noncomputable def horizontalBasis (f : Hom R X X') (g : Hom R Y Y') :
    (X.tensor Y).carrier → (X'.tensor Y').carrier →₀ R :=
  Quotient.lift (fun z : X.carrier × Y.carrier =>
    pairLinear R X' Y' (f.toLinearMap (Finsupp.single z.1 1))
      (g.toLinearMap (Finsupp.single z.2 1))) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    rw [← hx, ← hy, ← X.actLinear_single R (1,h), ← Y.actLinear_single R (h,1)]
    rw [f.commutes, g.commutes, pairLinear_balance])

/-- Tensor two equivariant linear maps over the middle group, on balanced bases. -/
noncomputable def horizontal (f : Hom R X X') (g : Hom R Y Y') :
    Hom R (X.tensor Y) (X'.tensor Y') :=
  ofBasis (horizontalBasis f g) (by
    intro h z
    refine Quotient.inductionOn z (fun x => ?_)
    change pairLinear R X' Y'
      (f.toLinearMap (Finsupp.single (X.act (h.1,1) x.1) 1))
      (g.toLinearMap (Finsupp.single (Y.act (1,h.2) x.2) 1)) = _
    rw [← X.actLinear_single R (h.1,1), ← Y.actLinear_single R (1,h.2)]
    rw [f.commutes, g.commutes]
    exact pairLinear_action R X' Y' (h.1,1) (1,h.2) h (fun _ _ => rfl) _ _)

@[simp] theorem horizontal_single (f : Hom R X X') (g : Hom R Y Y')
    (x : X.carrier) (y : Y.carrier) (r : R) :
    (f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r) =
      r • pairLinear R X' Y' (f.toLinearMap (Finsupp.single x 1))
        (g.toLinearMap (Finsupp.single y 1)) := by
  exact ofBasis_single _ _ _ _

end Hom


end Biset

end

end MackeyDiagrams

