import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BimoduleTensorFunctoriality

set_option maxHeartbeats 2000000

namespace NotesBalancedAssoc

open CategoryTheory

noncomputable section

-- Ian X, Theorem 6.5, p. 19, and Alphabeta Math's numbered proof:
-- https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19
-- https://alphabetamath.cc/item/thm-associativity-of-balanced-tensor-products
-- Proofs.BalancedTensorAssociativity was checked with the permitted axioms
-- (source SHA-256 2069082f489690ee0a881df7f2f5ebad33d114cdd97398518f7d740ef23f279e).
-- Its theorem and this endpoint share the global name BalancedTensorAssociativity.
-- Importing the supplier produces Lean's "has already been declared" diagnostic.
-- BimoduleTensorFunctoriality uses a FreeAddGroup quotient and ULift.
-- Local descent and generator extensionality work on the specified Finsupp
-- quotient and its exact generators.

private abbrev gen {X Y : Type*} (x : X) (y : Y) : (X × Y) →₀ ℤ :=
  Finsupp.single (x, y) 1

section Tensor

variable (R : Type*) [Ring R]
variable (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
variable [Module (MulOpposite R) X] [Module R Y]

private abbrev rel : AddSubgroup ((X × Y) →₀ ℤ) :=
  AddSubgroup.closure
    { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
          (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
          (∃ (a : R) (x : X) (y : Y),
            z = gen (MulOpposite.op a • x) y - gen x (a • y)) }

abbrev Tensor := HasQuotient.Quotient ((X × Y) →₀ ℤ) (rel R X Y)

variable {X Y}

abbrev pure (x : X) (y : Y) : Tensor R X Y :=
  QuotientAddGroup.mk' (rel R X Y) (gen x y)

private theorem add_left (x x' : X) (y : Y) :
    pure R (x + x') y = pure R x y + pure R x' y := by
  have h : gen (x + x') y - gen x y - gen x' y ∈ rel R X Y :=
    AddSubgroup.subset_closure (Or.inl ⟨x, x', y, rfl⟩)
  have hz := (QuotientAddGroup.eq_zero_iff _).2 h
  change QuotientAddGroup.mk' (rel R X Y) _ = 0 at hz
  rwa [map_sub, map_sub, sub_sub, sub_eq_zero] at hz

private theorem add_right (x : X) (y y' : Y) :
    pure R x (y + y') = pure R x y + pure R x y' := by
  have h : gen x (y + y') - gen x y - gen x y' ∈ rel R X Y :=
    AddSubgroup.subset_closure (Or.inr (Or.inl ⟨x, y, y', rfl⟩))
  have hz := (QuotientAddGroup.eq_zero_iff _).2 h
  change QuotientAddGroup.mk' (rel R X Y) _ = 0 at hz
  rwa [map_sub, map_sub, sub_sub, sub_eq_zero] at hz

private theorem balance (a : R) (x : X) (y : Y) :
    pure R (MulOpposite.op a • x) y = pure R x (a • y) := by
  have h : gen (MulOpposite.op a • x) y - gen x (a • y) ∈ rel R X Y :=
    AddSubgroup.subset_closure (Or.inr (Or.inr ⟨a, x, y, rfl⟩))
  have hz := (QuotientAddGroup.eq_zero_iff _).2 h
  change QuotientAddGroup.mk' (rel R X Y) _ = 0 at hz
  rwa [map_sub, sub_eq_zero] at hz

variable {A : Type*} [AddCommGroup A]

private def mkAdd {D : Type*} [AddZeroClass D] (f : D → A)
    (ha : ∀ x y, f (x + y) = f x + f y) : D →+ A where
  toFun := f
  map_add' := ha
  map_zero' := by
    have h := ha 0 0
    rw [zero_add] at h
    exact (add_left_cancel (show f 0 + 0 = f 0 + f 0 by simpa only [add_zero] using h)).symm

private def pureLeft (y : Y) : X →+ Tensor R X Y := mkAdd (fun x => pure R x y)
  (fun x x' => add_left R x x' y)

private def pureRight (x : X) : Y →+ Tensor R X Y := mkAdd (pure R x) (add_right R x)

variable (f : X →+ Y →+ A)

private def extend : ((X × Y) →₀ ℤ) →+ A :=
  Finsupp.liftAddHom (fun p => zmultiplesHom A (f p.1 p.2))

private theorem extend_gen (x : X) (y : Y) : extend f (gen x y) = f x y := by
  change Finsupp.liftAddHom _ (Finsupp.single (x, y) (1 : ℤ)) = _
  rw [Finsupp.liftAddHom_apply_single]
  exact one_zsmul _

private theorem rel_le_ker
    (hb : ∀ (a : R) x y, f (MulOpposite.op a • x) y = f x (a • y)) : rel R X Y ≤ (extend f).ker := by
  apply (AddSubgroup.closure_le _).2
  intro z hz
  apply AddMonoidHom.mem_ker.mpr
  rcases hz with ⟨x, x', y, rfl⟩ | ⟨x, y, y', rfl⟩ | ⟨a, x, y, rfl⟩
  · rw [map_sub, map_sub, sub_sub, extend_gen, extend_gen, extend_gen, map_add,
      AddMonoidHom.add_apply, sub_self]
  · rw [map_sub, map_sub, sub_sub, extend_gen, extend_gen, extend_gen, map_add, sub_self]
  · rw [map_sub, extend_gen, extend_gen, hb, sub_self]

private def lift (hb : ∀ (a : R) x y, f (MulOpposite.op a • x) y = f x (a • y)) :
    Tensor R X Y →+ A :=
  QuotientAddGroup.lift (rel R X Y) (extend f) (rel_le_ker R f hb)

@[simp] private theorem lift_pure
    (hb : ∀ (a : R) x y, f (MulOpposite.op a • x) y = f x (a • y)) (x : X) (y : Y) : lift R f hb (pure R x y) = f x y :=
  (QuotientAddGroup.lift_mk _ _ _).trans (extend_gen f x y)

private theorem hom_ext (f g : Tensor R X Y →+ A)
    (h : ∀ x y, f (pure R x y) = g (pure R x y)) : f = g := by
  let q := QuotientAddGroup.mk' (rel R X Y)
  have hq : f.comp q = g.comp q := by
    apply Finsupp.addHom_ext'
    intro p
    apply (zmultiplesHom A).symm.injective
    exact h p.1 p.2
  apply AddMonoidHom.ext
  intro z
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective (rel R X Y) z
  exact DFunLike.congr_fun hq u

end Tensor

section Maps

variable {R : Type*} [Ring R]
variable {X X' Y Y' : Type*} [AddCommGroup X] [AddCommGroup X']
variable [AddCommGroup Y] [AddCommGroup Y']
variable [Module (MulOpposite R) X] [Module (MulOpposite R) X'] [Module R Y] [Module R Y']

private def tensorMap (f : X →ₗ[MulOpposite R] X') (g : Y →ₗ[R] Y') :
    Tensor R X Y →+ Tensor R X' Y' :=
  lift R
    (mkAdd (fun x => (pureRight R (f x)).comp g.toAddMonoidHom) (fun x x' => by
      apply AddMonoidHom.ext
      intro y
      change pure R (f (x + x')) (g y) = pure R (f x) (g y) + pure R (f x') (g y)
      rw [map_add, add_left]))
    (fun a x y => by
      change pure R (f (MulOpposite.op a • x)) (g y) = pure R (f x) (g (a • y))
      rw [map_smul, map_smul, balance])

@[simp] private theorem tensorMap_pure (f : X →ₗ[MulOpposite R] X') (g : Y →ₗ[R] Y')
    (x : X) (y : Y) : tensorMap f g (pure R x y) = pure R (f x) (g y) :=
  lift_pure R _ _ x y

end Maps

section Actions

variable {R K : Type*} [Ring R] [Ring K]
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable [Module (MulOpposite R) X] [Module R Y]

private def scalarLinear {D E : Type*} [Ring D] [AddCommGroup E] [Module D E] [Module K E]
    [SMulCommClass K D E] (k : K) : E →ₗ[D] E where
  toFun := (k • ·)
  map_add' := smul_add k
  map_smul' d x := smul_comm k d x

@[simp] private theorem scalarLinear_apply {D E : Type*} [Ring D] [AddCommGroup E]
    [Module D E] [Module K E] [SMulCommClass K D E] (k : K) (x : E) :
    (scalarLinear (D := D) k) x = k • x := rfl

@[instance_reducible] private def moduleOfMaps {E : Type*} [AddCommGroup E] (a : K → E →+ E)
    (h1 : a 1 = AddMonoidHom.id E) (hm : ∀ k l, a (k * l) = (a k).comp (a l))
    (ha : ∀ k l, a (k + l) = a k + a l) (h0 : a 0 = 0) : Module K E where
  smul k x := a k x
  one_smul x := DFunLike.congr_fun h1 x
  mul_smul k l x := DFunLike.congr_fun (hm k l) x
  smul_zero k := map_zero (a k)
  smul_add k := map_add (a k)
  add_smul k l x := DFunLike.congr_fun (ha k l) x
  zero_smul x := DFunLike.congr_fun h0 x

-- The portal assumes the intermediate actions in L1. Here the commuting
-- actions allow descent of the scalar maps and prove the module laws.
@[instance_reducible] def leftModule [Module K X] [SMulCommClass K (MulOpposite R) X] :
    Module K (Tensor R X Y) :=
  moduleOfMaps (fun k => tensorMap (scalarLinear (D := MulOpposite R) k) LinearMap.id)
    (hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, scalarLinear_apply, LinearMap.id_apply, one_smul,
        AddMonoidHom.id_apply])
    (fun k l => hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, AddMonoidHom.comp_apply, scalarLinear_apply, LinearMap.id_apply,
        mul_smul])
    (fun k l => hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, AddMonoidHom.add_apply, scalarLinear_apply, LinearMap.id_apply,
        add_smul, add_left])
    (hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, scalarLinear_apply, LinearMap.id_apply, zero_smul,
        AddMonoidHom.zero_apply]
      exact map_zero (pureLeft R y))

@[simp] theorem left_pure [Module K X] [SMulCommClass K (MulOpposite R) X]
    (k : K) (x : X) (y : Y) :
    (leftModule (K := K) (R := R) (X := X) (Y := Y)).smul k (pure R x y) =
      pure R (k • x) y :=
  tensorMap_pure _ _ x y

@[instance_reducible] def rightModule [Module K Y] [SMulCommClass K R Y] :
    Module K (Tensor R X Y) :=
  moduleOfMaps (fun k => tensorMap LinearMap.id (scalarLinear (D := R) k))
    (hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, scalarLinear_apply, LinearMap.id_apply, one_smul,
        AddMonoidHom.id_apply])
    (fun k l => hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, AddMonoidHom.comp_apply, scalarLinear_apply, LinearMap.id_apply,
        mul_smul])
    (fun k l => hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, AddMonoidHom.add_apply, scalarLinear_apply, LinearMap.id_apply,
        add_smul, add_right])
    (hom_ext R _ _ fun x y => by
      simp only [tensorMap_pure, scalarLinear_apply, LinearMap.id_apply, zero_smul,
        AddMonoidHom.zero_apply]
      exact map_zero (pureRight R x))

@[simp] theorem right_pure [Module K Y] [SMulCommClass K R Y]
    (k : K) (x : X) (y : Y) :
    (rightModule (K := K) (R := R) (X := X) (Y := Y)).smul k (pure R x y) =
      pure R x (k • y) :=
  tensorMap_pure _ _ x y

private def smulAdd {D E : Type*} [Ring D] [AddCommGroup E] [Module D E] (d : D) :
    E →+ E where
  toFun := (d • ·)
  map_zero' := smul_zero d
  map_add' := smul_add d

theorem commute {J : Type*} [Ring J] [Module K X] [Module J Y]
    [SMulCommClass K (MulOpposite R) X] [SMulCommClass J R Y] :
    letI := leftModule (K := K) (R := R) (X := X) (Y := Y)
    letI := rightModule (K := J) (R := R) (X := X) (Y := Y)
    SMulCommClass J K (Tensor R X Y) := by
  let l := leftModule (K := K) (R := R) (X := X) (Y := Y)
  let r := rightModule (K := J) (R := R) (X := X) (Y := Y)
  let _ := l
  let _ := r
  refine ⟨fun j k z => ?_⟩
  let f := (smulAdd j : Tensor R X Y →+ Tensor R X Y).comp (smulAdd k)
  let g := (smulAdd k : Tensor R X Y →+ Tensor R X Y).comp (smulAdd j)
  have h : f = g := hom_ext R _ _ fun x y => by
    change r.smul j (l.smul k (pure R x y)) = l.smul k (r.smul j (pure R x y))
    simp only [l, r, left_pure, right_pure]
  exact DFunLike.congr_fun h z

end Actions

section LinearMaps

variable {R K : Type*} [Ring R] [Ring K]
variable {X X' Y Y' : Type*} [AddCommGroup X] [AddCommGroup X']
variable [AddCommGroup Y] [AddCommGroup Y']
variable [Module (MulOpposite R) X] [Module (MulOpposite R) X'] [Module R Y] [Module R Y']

private def leftMap [Module K X] [Module K X']
    [SMulCommClass K (MulOpposite R) X] [SMulCommClass K (MulOpposite R) X']
    (f : X →ₗ[MulOpposite R] X') (g : Y →ₗ[R] Y')
    (hf : ∀ k : K, ∀ x, f (k • x) = k • f x) :
    letI := leftModule (K := K) (R := R) (X := X) (Y := Y)
    letI := leftModule (K := K) (R := R) (X := X') (Y := Y')
    Tensor R X Y →ₗ[K] Tensor R X' Y' := by
  letI := leftModule (K := K) (R := R) (X := X) (Y := Y)
  letI := leftModule (K := K) (R := R) (X := X') (Y := Y')
  let map := tensorMap f g
  refine { map with map_smul' := fun k z => ?_ }
  have h : map.comp (smulAdd k) = (smulAdd k).comp map :=
    hom_ext R _ _ fun x y => by
      change map ((leftModule (K := K)).smul k (pure R x y)) =
        (leftModule (K := K)).smul k (map (pure R x y))
      simp only [map, left_pure, tensorMap_pure, hf]
  exact DFunLike.congr_fun h z

private theorem leftMap_pure [Module K X] [Module K X']
    [SMulCommClass K (MulOpposite R) X] [SMulCommClass K (MulOpposite R) X']
    (f : X →ₗ[MulOpposite R] X') (g : Y →ₗ[R] Y')
    (hf : ∀ k : K, ∀ x, f (k • x) = k • f x) (x : X) (y : Y) :
    leftMap f g hf (pure R x y) = pure R (f x) (g y) :=
  tensorMap_pure f g x y

private def rightMap [Module K Y] [Module K Y'] [SMulCommClass K R Y] [SMulCommClass K R Y']
    (f : X →ₗ[MulOpposite R] X') (g : Y →ₗ[R] Y')
    (hg : ∀ k : K, ∀ y, g (k • y) = k • g y) :
    letI := rightModule (K := K) (R := R) (X := X) (Y := Y)
    letI := rightModule (K := K) (R := R) (X := X') (Y := Y')
    Tensor R X Y →ₗ[K] Tensor R X' Y' := by
  letI := rightModule (K := K) (R := R) (X := X) (Y := Y)
  letI := rightModule (K := K) (R := R) (X := X') (Y := Y')
  let map := tensorMap f g
  refine { map with map_smul' := fun k z => ?_ }
  have h : map.comp (smulAdd k) = (smulAdd k).comp map :=
    hom_ext R _ _ fun x y => by
      change map ((rightModule (K := K)).smul k (pure R x y)) =
        (rightModule (K := K)).smul k (map (pure R x y))
      simp only [map, right_pure, tensorMap_pure, hg]
  exact DFunLike.congr_fun h z

private theorem rightMap_pure [Module K Y] [Module K Y'] [SMulCommClass K R Y] [SMulCommClass K R Y']
    (f : X →ₗ[MulOpposite R] X') (g : Y →ₗ[R] Y')
    (hg : ∀ k : K, ∀ y, g (k • y) = k • g y) (x : X) (y : Y) :
    rightMap f g hg (pure R x y) = pure R (f x) (g y) :=
  tensorMap_pure f g x y

end LinearMaps

section Assoc

variable {T S R : Type*} [Ring T] [Ring S] [Ring R]
variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module (MulOpposite S) X] [Module S Y] [Module (MulOpposite R) Y] [Module R Z]
variable [SMulCommClass (MulOpposite R) S Y] [SMulCommClass S (MulOpposite R) Y]
variable [Module T X] [SMulCommClass T (MulOpposite S) X]

@[reducible] local instance cbRight : Module (MulOpposite R) (Tensor S X Y) := rightModule
@[reducible] local instance bmLeft : Module S (Tensor R Y Z) := leftModule
@[reducible] local instance cbLeft : Module T (Tensor S X Y) := leftModule
local instance cbComm : SMulCommClass (MulOpposite R) T (Tensor S X Y) := commute
local instance cbComm' : SMulCommClass T (MulOpposite R) (Tensor S X Y) :=
  SMulCommClass.symm _ _ _

variable (S R X Y Z) in
abbrev L := Tensor R (Tensor S X Y) Z
variable (S R X Y Z) in
abbrev U := Tensor S X (Tensor R Y Z)

variable (S R) in
abbrev lp (x : X) (y : Y) (z : Z) : L S R X Y Z := pure R (pure S x y) z
variable (S R) in
abbrev up (x : X) (y : Y) (z : Z) : U S R X Y Z := pure S x (pure R y z)

@[reducible] local instance actL : Module T (L S R X Y Z) := leftModule
@[reducible] local instance actU : Module T (U S R X Y Z) := leftModule

-- Steps 1.1 and 1.2 verify both balancing relations. The forward map
-- descends in C,B with values in additive maps out of M, so additivity in M
-- is built into the first lift. The second balancing relation is checked by
-- hom_ext in the descended variable (steps 2.1 and 2.2).
private def forwardInner : Tensor S X Y →+ Z →+ U S R X Y Z :=
  lift S
    (mkAdd (fun x => mkAdd (fun y => (pureRight S x).comp (pureRight R y)) (fun y y' => by
      apply AddMonoidHom.ext
      intro z
      change up S R x (y + y') z = up S R x y z + up S R x y' z
      simp only [up, add_left, add_right])) (fun x x' => by
      apply AddMonoidHom.ext
      intro y
      apply AddMonoidHom.ext
      intro z
      change up S R (x + x') y z = up S R x y z + up S R x' y z
      exact add_left S x x' _))
    (fun s x y => by
      apply AddMonoidHom.ext
      intro z
      change up S R (MulOpposite.op s • x) y z = up S R x (s • y) z
      rw [up, up, balance, show s • pure R y z = pure R (s • y) z from left_pure s y z])

omit [SMulCommClass (MulOpposite R) S Y] in
private theorem forwardInner_pure (x : X) (y : Y) (z : Z) :
    (forwardInner (S := S) (R := R) (X := X) (Y := Y) (Z := Z) (pure S x y)) z = up S R x y z := by
  rw [forwardInner, lift_pure]
  rfl

private def forward : L S R X Y Z →+ U S R X Y Z :=
  lift R forwardInner (fun r q z => by
    let f := (AddMonoidHom.eval z).comp
      ((forwardInner (S := S) (R := R) (X := X) (Y := Y) (Z := Z)).comp (smulAdd (MulOpposite.op r)))
    let g := (AddMonoidHom.eval (r • z)).comp
      (forwardInner (S := S) (R := R) (X := X) (Y := Y) (Z := Z))
    have h : f = g := hom_ext S _ _ fun x y => by
      change (forwardInner ((rightModule (K := MulOpposite R)).smul
        (MulOpposite.op r) (pure S x y))) z = (forwardInner (pure S x y)) (r • z)
      simp only [right_pure, forwardInner_pure, up, balance]
    exact DFunLike.congr_fun h q)

private theorem forward_pure (x : X) (y : Y) (z : Z) :
    forward (lp S R x y z) = up S R x y z := by
  exact (lift_pure R _ _ (pure S x y) z).trans (forwardInner_pure x y z)

private def backwardInner (x : X) : Tensor R Y Z →+ L S R X Y Z :=
  lift R
    (mkAdd (fun y => pureRight R (pure S x y)) (fun y y' => by
      apply AddMonoidHom.ext
      intro z
      change lp S R x (y + y') z = lp S R x y z + lp S R x y' z
      simp only [lp, add_right, add_left]))
    (fun r y z => by
      change lp S R x (MulOpposite.op r • y) z = lp S R x y (r • z)
      exact (congrArg (fun q : Tensor S X Y => pure R q z) (right_pure (MulOpposite.op r) x y)).symm.trans
        (balance R r (pure S x y) z))

omit [SMulCommClass S (MulOpposite R) Y] in
private theorem backwardInner_pure (x : X) (y : Y) (z : Z) :
    backwardInner x (pure R y z) = lp S R x y z := by
  rw [backwardInner, lift_pure]
  rfl

private def backward : U S R X Y Z →+ L S R X Y Z :=
  lift S (mkAdd (backwardInner (S := S) (R := R) (X := X) (Y := Y) (Z := Z))
    (fun x x' => hom_ext R _ _ fun y z => by
      simp only [AddMonoidHom.add_apply, backwardInner_pure, lp, add_left]))
    (fun s x q => by
      let f := backwardInner (S := S) (R := R) (Y := Y) (Z := Z) (MulOpposite.op s • x)
      let g := (backwardInner (S := S) (R := R) (Y := Y) (Z := Z) x).comp (smulAdd s)
      have eq : f = g := hom_ext R _ _ fun y z => by
        change backwardInner (S := S) (MulOpposite.op s • x) (pure R y z) =
          backwardInner (S := S) x ((leftModule (K := S)).smul s (pure R y z))
        simp only [left_pure, backwardInner_pure, lp, balance]
      exact DFunLike.congr_fun eq q)

private theorem backward_pure (x : X) (y : Y) (z : Z) :
    backward (up S R x y z) = lp S R x y z := by
  exact (lift_pure S _ _ x (pure R y z)).trans (backwardInner_pure x y z)

-- Homomorphisms out of either nesting are determined by their pure triples.
-- This proves the two composite identities in step 3.1.
omit [SMulCommClass S (MulOpposite R) Y] in
private theorem left_ext {A : Type*} [AddCommGroup A] (f g : L S R X Y Z →+ A)
    (h : ∀ x y z, f (lp S R x y z) = g (lp S R x y z)) : f = g :=
  hom_ext R _ _ fun q z =>
    DFunLike.congr_fun (hom_ext S (f.comp (pureLeft R z)) (g.comp (pureLeft R z))
      fun x y => h x y z) q

omit [SMulCommClass (MulOpposite R) S Y] in
private theorem right_ext {A : Type*} [AddCommGroup A] (f g : U S R X Y Z →+ A)
    (h : ∀ x y z, f (up S R x y z) = g (up S R x y z)) : f = g :=
  hom_ext S _ _ fun x q =>
    DFunLike.congr_fun (hom_ext R (f.comp (pureRight S x)) (g.comp (pureRight S x))
      fun y z => h x y z) q

omit [SMulCommClass S (MulOpposite R) Y] in
@[simp] theorem actL_pure (t : T) (x : X) (y : Y) (z : Z) :
    (actL (T := T)).smul t (lp S R x y z) = lp S R (t • x) y z := by
  change (leftModule (K := T)).smul t (pure R (pure S x y) z) = _
  rw [left_pure]
  change pure R ((leftModule (K := T)).smul t (pure S x y)) z = _
  rw [left_pure]

omit [SMulCommClass (MulOpposite R) S Y] in
@[simp] theorem actU_pure (t : T) (x : X) (y : Y) (z : Z) :
    (actU (T := T)).smul t (up S R x y z) = up S R (t • x) y z :=
  left_pure t x _

-- Step 3.2 proves equivariance on pure triples and extends it by left_ext.
-- Step 4.1 packages the isomorphism with the specified module structures.
def assoc : L S R X Y Z ≃ₗ[T] U S R X Y Z where
  toAddEquiv :=
    { forward with
      invFun := backward
      left_inv := fun q => DFunLike.congr_fun
        (left_ext (backward.comp forward) (AddMonoidHom.id _)
          fun x y z => by simp only [AddMonoidHom.comp_apply, forward_pure, backward_pure,
            AddMonoidHom.id_apply]) q
      right_inv := fun q => DFunLike.congr_fun
        (right_ext (forward.comp backward) (AddMonoidHom.id _)
          fun x y z => by simp only [AddMonoidHom.comp_apply, backward_pure, forward_pure,
            AddMonoidHom.id_apply]) q }
  map_smul' t q := by
    let F : L S R X Y Z →+ U S R X Y Z := forward
    have h : F.comp (smulAdd t) = (smulAdd t).comp F :=
      left_ext _ _ fun x y z => by
        change forward ((actL (T := T)).smul t (lp S R x y z)) =
          (actU (T := T)).smul t (forward (lp S R x y z))
        simp only [actL_pure, actU_pure, forward_pure]
    exact DFunLike.congr_fun h q

@[simp] theorem assoc_pure (x : X) (y : Y) (z : Z) :
    assoc (T := T) (lp S R x y z) = up S R x y z :=
  forward_pure x y z

variable {X' Y' Z' : Type*} [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
variable [Module (MulOpposite S) X'] [Module S Y'] [Module (MulOpposite R) Y'] [Module R Z']
variable [SMulCommClass (MulOpposite R) S Y'] [SMulCommClass S (MulOpposite R) Y']
variable [Module T X'] [SMulCommClass T (MulOpposite S) X']

variable (f : X →ₗ[MulOpposite S] X') (g : Y →ₗ[S] Y') (h : Z →ₗ[R] Z')
variable (hf : ∀ t : T, ∀ x, f (t • x) = t • f x)
variable (hg : ∀ a : MulOpposite R, ∀ y, g (a • y) = a • g y)

private def gRight : Y →ₗ[MulOpposite R] Y' :=
  { g.toAddMonoidHom with map_smul' := hg }

private def mapL : L S R X Y Z →ₗ[T] L S R X' Y' Z' :=
  leftMap (rightMap f g hg) h (fun t q => map_smul (leftMap f g hf) t q)

private def mapU : U S R X Y Z →ₗ[T] U S R X' Y' Z' :=
  leftMap f (leftMap (gRight g hg) h (fun s y => map_smul g s y)) hf

omit [SMulCommClass S (MulOpposite R) Y] [SMulCommClass S (MulOpposite R) Y'] in
private theorem mapL_pure (x : X) (y : Y) (z : Z) :
    mapL f g h hf hg (lp S R x y z) = lp S R (f x) (g y) (h z) := by
  exact (leftMap_pure (rightMap f g hg) h _ (pure S x y) z).trans
    (congrArg (fun q : Tensor S X' Y' => pure R q (h z)) (rightMap_pure f g hg x y))

omit [SMulCommClass (MulOpposite R) S Y] [SMulCommClass (MulOpposite R) S Y'] in
private theorem mapU_pure (x : X) (y : Y) (z : Z) :
    mapU f g h hf hg (up S R x y z) = up S R (f x) (g y) (h z) := by
  let g' := gRight g hg
  let hg' (s : S) (y : Y) : g' (s • y) = s • g' y := map_smul g s y
  exact (leftMap_pure f (leftMap g' h hg') hf x (pure R y z)).trans
    (congrArg (pure S (f x)) (leftMap_pure g' h hg' y z))

-- The last part of step 3.2 checks the naturality square on the three
-- generators. left_ext upgrades the equality to the whole source.
include hf hg in
theorem natural :
    ∃ (l : L S R X Y Z →ₗ[T] L S R X' Y' Z') (u : U S R X Y Z →ₗ[T] U S R X' Y' Z'),
      (∀ x y z, l (lp S R x y z) = lp S R (f x) (g y) (h z) ∧
        u (up S R x y z) = up S R (f x) (g y) (h z)) ∧
      ∀ q : L S R X Y Z, assoc (T := T) (l q) = u (assoc (T := T) q) := by
  refine ⟨mapL f g h hf hg, mapU f g h hf hg, fun x y z => ⟨mapL_pure f g h hf hg x y z,
    mapU_pure f g h hf hg x y z⟩, fun q => ?_⟩
  let l := (mapL f g h hf hg).toAddMonoidHom
  let u := (mapU f g h hf hg).toAddMonoidHom
  let e : L S R X Y Z ≃ₗ[T] U S R X Y Z := assoc
  let e' : L S R X' Y' Z' ≃ₗ[T] U S R X' Y' Z' := assoc
  have he : e'.toLinearMap.toAddMonoidHom.comp l = u.comp e.toLinearMap.toAddMonoidHom :=
    left_ext _ _ fun x y z => by
      change e' (mapL f g h hf hg (lp S R x y z)) =
        mapU f g h hf hg (e (lp S R x y z))
      simp only [e, e', mapL_pure, mapU_pure, assoc_pure]
  exact DFunLike.congr_fun he q

end Assoc

section Functors

universe r s v
variable {R : Type r} [Ring R] {S : Type s} [Ring S]

abbrev Bimod (R : Type r) [Ring R] (S : Type s) [Ring S] :=
  AdditiveFunctor (SingleObj (MulOpposite R)) (ModuleCat.{v} S)

local notation "★" => SingleObj.star (MulOpposite R)

abbrev carrier (B : Bimod.{r,s,v} R S) := B.obj.obj ★

private def actionHom (B : Bimod.{r,s,v} R S) : MulOpposite R →+* Module.End S (carrier B) where
  toFun a := (B.obj.map (show ★ ⟶ ★ from a)).hom
  map_one' := congrArg ModuleCat.Hom.hom (B.obj.map_id ★)
  map_mul' a b := congrArg ModuleCat.Hom.hom
    (B.obj.map_comp (show ★ ⟶ ★ from b) (show ★ ⟶ ★ from a))
  map_zero' := congrArg ModuleCat.Hom.hom (B.obj.map_zero ★ ★)
  map_add' a b := congrArg ModuleCat.Hom.hom
    (B.obj.map_add (f := (show ★ ⟶ ★ from a)) (g := (show ★ ⟶ ★ from b)))

@[reducible] def rightAction (B : Bimod.{r,s,v} R S) : Module (MulOpposite R) (carrier B) :=
  Module.compHom (carrier B) (actionHom B)

theorem rightAction_comm (B : Bimod.{r,s,v} R S) :
    letI := rightAction B
    SMulCommClass (MulOpposite R) S (carrier B) := by
  let _ := rightAction B
  exact ⟨fun a s x => map_smul (actionHom B a) s x⟩

@[reducible] local instance (B : Bimod.{r,s,v} R S) : Module (MulOpposite R) (carrier B) :=
  rightAction B

def evalRight {B B' : Bimod.{r,s,v} R S} (f : B ⟶ B') :
    carrier B →ₗ[MulOpposite R] carrier B' :=
  { (f.hom.app ★).hom.toAddMonoidHom with
    map_smul' a x := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (f.hom.naturality (show ★ ⟶ ★ from a))) x }

end Functors

end
end NotesBalancedAssoc

theorem BalancedTensorAssociativity : (
∀ (T : Type t) (S : Type s) (R : Type r) [Ring T] [Ring S] [Ring R],
  let TS := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite S)) (ModuleCat.{c} T)
  let SR := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{b} S)
  let starS := CategoryTheory.SingleObj.star (MulOpposite S)
  let starR := CategoryTheory.SingleObj.star (MulOpposite R)
  let carrierC := fun (C : TS) => C.obj.obj starS
  let carrierB := fun (B : SR) => B.obj.obj starR
  let rightC := fun (C : TS) (s : S) (c : carrierC C) =>
    (C.obj.map (show Quiver.Hom starS starS from MulOpposite.op s)) c
  let rightB := fun (B : SR) (r : R) (b : carrierB B) =>
    (B.obj.map (show Quiver.Hom starR starR from MulOpposite.op r)) b
  let CB := fun (C : TS) (B : SR) =>
    let X := carrierC C
    let Y := carrierB B
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : S) (x : X) (y : Y), z = gen (rightC C a x) y - gen x (a • y)) }
    (⟨K, fun x y => QuotientAddGroup.mk' K (gen x y)⟩ :
      Sigma (fun K : AddSubgroup F => X → Y → HasQuotient.Quotient F K))
  let BM := fun (B : SR) (M : ModuleCat.{m} R) =>
    let X := carrierB B
    let Y := M
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : R) (x : X) (y : Y), z = gen (rightB B a x) y - gen x (a • y)) }
    (⟨K, fun x y => QuotientAddGroup.mk' K (gen x y)⟩ :
      Sigma (fun K : AddSubgroup F => X → Y → HasQuotient.Quotient F K))
  let CBType := fun (C : TS) (B : SR) =>
    HasQuotient.Quotient (Finsupp (Prod (carrierC C) (carrierB B)) Int) (CB C B).1
  let BMType := fun (B : SR) (M : ModuleCat.{m} R) =>
    HasQuotient.Quotient (Finsupp (Prod (carrierB B) M) Int) (BM B M).1
  let Left := fun (C : TS) (B : SR) (M : ModuleCat.{m} R)
      (rightCB : Module (MulOpposite R) (CBType C B)) =>
    let X := CBType C B
    let Y := M
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : R) (x : X) (y : Y), z = gen (rightCB.smul (MulOpposite.op a) x) y - gen x (a • y)) }
    (⟨K, fun c b m => QuotientAddGroup.mk' K (gen ((CB C B).2 c b) m)⟩ :
      Sigma (fun K : AddSubgroup F => carrierC C → carrierB B → M → HasQuotient.Quotient F K))
  let Right := fun (C : TS) (B : SR) (M : ModuleCat.{m} R)
      (leftBM : Module S (BMType B M)) =>
    letI := leftBM
    let X := carrierC C
    let Y := BMType B M
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : S) (x : X) (y : Y), z = gen (rightC C a x) y - gen x (a • y)) }
    (⟨K, fun c b m => QuotientAddGroup.mk' K (gen c ((BM B M).2 b m))⟩ :
      Sigma (fun K : AddSubgroup F => carrierC C → carrierB B → M → HasQuotient.Quotient F K))
  ∃ (leftCB : ∀ C B, Module T (CBType C B))
    (rightCB : ∀ C B, Module (MulOpposite R) (CBType C B))
    (leftBM : ∀ B (M : ModuleCat.{m} R), Module S (BMType B M)),
    (∀ (C : TS) (B : SR),
      (letI := leftCB C B
       letI := rightCB C B
       SMulCommClass (MulOpposite R) T (CBType C B)) ∧
      (∀ (t : T) (c : carrierC C) (b : carrierB B),
        (leftCB C B).smul t ((CB C B).2 c b) = (CB C B).2 (t • c) b) ∧
      (∀ (r : R) (c : carrierC C) (b : carrierB B),
        (rightCB C B).smul (MulOpposite.op r) ((CB C B).2 c b) = (CB C B).2 c (rightB B r b))) ∧
    (∀ (B : SR) (M : ModuleCat.{m} R) (s : S) (b : carrierB B) (m : M),
      (leftBM B M).smul s ((BM B M).2 b m) = (BM B M).2 (s • b) m) ∧
    (let L := fun (C : TS) (B : SR) (M : ModuleCat.{m} R) =>
       HasQuotient.Quotient (Finsupp (Prod (CBType C B) M) Int) (Left C B M (rightCB C B)).1
     let U := fun (C : TS) (B : SR) (M : ModuleCat.{m} R) =>
       HasQuotient.Quotient (Finsupp (Prod (carrierC C) (BMType B M)) Int) (Right C B M (leftBM B M)).1
     let pureL := fun C B M => (Left C B M (rightCB C B)).2
     let pureU := fun C B M => (Right C B M (leftBM B M)).2
     ∃ (actL : ∀ C B M, Module T (L C B M))
       (actU : ∀ C B M, Module T (U C B M))
       (α : ∀ C B M,
         letI := actL C B M
         letI := actU C B M
         LinearEquiv (RingHom.id T) (L C B M) (U C B M)),
       (∀ (C : TS) (B : SR) (M : ModuleCat.{m} R)
           (c : carrierC C) (b : carrierB B) (m : M),
         α C B M (pureL C B M c b m) = pureU C B M c b m ∧
         ∀ t : T,
           (actL C B M).smul t (pureL C B M c b m) = pureL C B M (t • c) b m ∧
           (actU C B M).smul t (pureU C B M c b m) = pureU C B M (t • c) b m) ∧
       (∀ {C C' : TS} {B B' : SR} {M M' : ModuleCat.{m} R}
           (f : Quiver.Hom C C') (g : Quiver.Hom B B') (h : Quiver.Hom M M'),
         letI := actL C B M
         letI := actL C' B' M'
         letI := actU C B M
         letI := actU C' B' M'
         ∃ (l : LinearMap (RingHom.id T) (L C B M) (L C' B' M'))
           (u : LinearMap (RingHom.id T) (U C B M) (U C' B' M')),
           (∀ (c : carrierC C) (b : carrierB B) (m : M),
             l (pureL C B M c b m) =
               pureL C' B' M' ((f.hom.app starS) c) ((g.hom.app starR) b) (h m) ∧
             u (pureU C B M c b m) =
               pureU C' B' M' ((f.hom.app starS) c) ((g.hom.app starR) b) (h m)) ∧
           (∀ q : L C B M, α C' B' M' (l q) = u (α C B M q))))
) :=
(by
  intro T S R _ _ _ TS SR starS starR carrierC carrierB rightC rightB
    CB BM CBType BMType Left Right
  -- Evaluate both additive functors at their unique object. Their functor
  -- and additivity laws supply the right-module laws, and their maps are
  -- linear for the original left actions. The quotient identifications
  -- below are definitional, including the classes of the generators.
  let leftCB (C : TS) (B : SR) : Module T (CBType C B) := by
    let _ := NotesBalancedAssoc.rightAction C
    let _ := NotesBalancedAssoc.rightAction_comm C
    let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
    exact NotesBalancedAssoc.leftModule (K := T) (R := S)
      (X := carrierC C) (Y := carrierB B)
  let rightCB (C : TS) (B : SR) : Module (MulOpposite R) (CBType C B) := by
    let _ := NotesBalancedAssoc.rightAction C
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm B
    exact NotesBalancedAssoc.rightModule (K := MulOpposite R) (R := S)
      (X := carrierC C) (Y := carrierB B)
  let leftBM (B : SR) (M : ModuleCat R) : Module S (BMType B M) := by
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm B
    let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
    exact NotesBalancedAssoc.leftModule (K := S) (R := R) (X := carrierB B) (Y := M)
  refine ⟨leftCB, rightCB, leftBM, ?_, ?_, ?_⟩
  · intro C B
    let _ := NotesBalancedAssoc.rightAction C
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm C
    let _ := NotesBalancedAssoc.rightAction_comm B
    let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
    exact ⟨NotesBalancedAssoc.commute (R := S) (K := T) (J := MulOpposite R)
        (X := carrierC C) (Y := carrierB B),
      fun t c b => NotesBalancedAssoc.left_pure (R := S) t c b,
      fun r c b => NotesBalancedAssoc.right_pure (R := S) (MulOpposite.op r) c b⟩
  · intro B M s b m
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm B
    let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
    exact NotesBalancedAssoc.left_pure (R := R) s b m
  · intro L U pureL pureU
    let actL (C : TS) (B : SR) (M : ModuleCat R) : Module T (L C B M) := by
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      exact NotesBalancedAssoc.actL (T := T) (S := S) (R := R)
        (X := carrierC C) (Y := carrierB B) (Z := M)
    let actU (C : TS) (B : SR) (M : ModuleCat R) : Module T (U C B M) := by
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      exact NotesBalancedAssoc.actU (T := T) (S := S) (R := R)
        (X := carrierC C) (Y := carrierB B) (Z := M)
    let α (C : TS) (B : SR) (M : ModuleCat R) :
        letI := actL C B M
        letI := actU C B M
        LinearEquiv (RingHom.id T) (L C B M) (U C B M) := by
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      exact NotesBalancedAssoc.assoc (T := T) (S := S) (R := R)
        (X := carrierC C) (Y := carrierB B) (Z := M)
    refine ⟨actL, actU, α, ?_, ?_⟩
    · intro C B M c b m
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      exact ⟨NotesBalancedAssoc.assoc_pure (T := T) (S := S) (R := R) c b m,
        fun t => ⟨NotesBalancedAssoc.actL_pure (S := S) (R := R) t c b m,
          NotesBalancedAssoc.actU_pure (S := S) (R := R) t c b m⟩⟩
    · intro C C' B B' M M' f g h
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction C'
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction B'
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm C'
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := NotesBalancedAssoc.rightAction_comm B'
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C')
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B')
      exact NotesBalancedAssoc.natural (NotesBalancedAssoc.evalRight f)
        (g.hom.app starR).hom h.hom (fun t c => map_smul (f.hom.app starS).hom t c)
        (fun r b => map_smul (NotesBalancedAssoc.evalRight g) r b))

#print axioms BalancedTensorAssociativity
