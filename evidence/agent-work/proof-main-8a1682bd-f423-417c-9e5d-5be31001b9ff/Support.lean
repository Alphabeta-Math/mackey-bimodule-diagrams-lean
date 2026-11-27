open CategoryTheory

namespace CanonicalWattsComparisonSupport

universe u v w z y

noncomputable section Tensor

variable {A : Type u} {M : Type w} {X : Type z} [Ring A] [AddCommGroup M]
  [AddCommGroup X] [Module A X]

private abbrev gen (m : M) (x : X) : (M × X) →₀ ℤ :=
  Finsupp.single (m, x) 1

private abbrev relations (right : A → M → M) (X : Type z)
    [AddCommGroup X] [Module A X] : AddSubgroup ((M × X) →₀ ℤ) :=
  AddSubgroup.closure
    {p | (∃ (m m' : M) (x : X), p = gen (m + m') x - gen m x - gen m' x) ∨
      (∃ (m : M) (x x' : X), p = gen m (x + x') - gen m x - gen m x') ∨
      (∃ (a : A) (m : M) (x : X), p = gen (right a m) x - gen m (a • x))}

private abbrev Tensor (right : A → M → M) (X : Type z) [AddCommGroup X] [Module A X] :=
  ((M × X) →₀ ℤ) ⧸ relations right X

private abbrev pure (right : A → M → M) (m : M) (x : X) : Tensor right X :=
  QuotientAddGroup.mk' (relations right X) (gen m x)

private def Balanced {Y : Type y} [AddCommGroup Y] (right : A → M → M)
    (f : M → X → Y) : Prop :=
  (∀ m m' x, f (m + m') x = f m x + f m' x) ∧
  (∀ m x x', f m (x + x') = f m x + f m x') ∧
  (∀ a m x, f (right a m) x = f m (a • x))

variable {right : A → M → M}

private theorem pure_balanced [Module (MulOpposite A) M]
    (hright : ∀ a m, MulOpposite.op a • m = right a m) :
    Balanced right (pure (X := X) right) := by
  have h : right = fun a m => MulOpposite.op a • m :=
    funext fun a => funext fun m => (hright a m).symm
  subst right
  exact (ModuleTensorUniversalProperty.{u,w,z,0} A M X).1

private theorem tensor_ext [Module (MulOpposite A) M]
    (hright : ∀ a m, MulOpposite.op a • m = right a m) {Y : Type y} [AddCommGroup Y]
    (f g : Tensor right X →+ Y) (heq : ∀ m x, f (pure right m x) = g (pure right m x)) :
    f = g := by
  have h : right = fun a m => MulOpposite.op a • m :=
    funext fun a => funext fun m => (hright a m).symm
  subst right
  have ⟨⟨addLeft, addRight, balance⟩, univ⟩ := ModuleTensorUniversalProperty A M X
  obtain ⟨k, _, unique⟩ := (univ Y).1
    ⟨fun p => f (pure _ p.1 p.2),
      fun m m' x => (congrArg f (addLeft m m' x)).trans (map_add f _ _),
      fun m x x' => (congrArg f (addRight m x x')).trans (map_add f _ _),
      fun a m x => congrArg f (balance a m x)⟩
  exact (unique f (fun _ _ => rfl)).trans (unique g (fun m x => (heq m x).symm)).symm

-- Step 3.1 uses the universal property. Use the supplier for uniqueness
-- and implement its extension formula directly, so the map is defined by
-- the specified generators and relations. Mathlib's TensorProduct.liftAddHom
-- requires a commutative base semiring, while A is an arbitrary ring here.
private noncomputable def extend {Y : Type y} [AddCommGroup Y] (f : M → X → Y) :
    ((M × X) →₀ ℤ) →+ Y :=
  Finsupp.liftAddHom (fun p => zmultiplesHom Y (f p.1 p.2))

omit [AddCommGroup M] [AddCommGroup X] in
private theorem extend_gen {Y : Type y} [AddCommGroup Y] (f : M → X → Y) (m : M) (x : X) :
    extend f (gen m x) = f m x := by
  unfold extend
  rw [Finsupp.liftAddHom_apply_single]
  exact one_zsmul _

private noncomputable def lift {Y : Type y} [AddCommGroup Y] (f : M → X → Y)
    (hf : Balanced right f) : Tensor right X →+ Y :=
  QuotientAddGroup.lift (relations right X) (extend f) (by
    apply (AddSubgroup.closure_le _).2
    intro p hp
    apply AddMonoidHom.mem_ker.mpr
    rcases hp with ⟨m, m', x, rfl⟩ | ⟨m, x, x', rfl⟩ | ⟨a, m, x, rfl⟩
    · rw [map_sub, map_sub, sub_sub, extend_gen, extend_gen, extend_gen, hf.1, sub_self]
    · rw [map_sub, map_sub, sub_sub, extend_gen, extend_gen, extend_gen, hf.2.1, sub_self]
    · rw [map_sub, extend_gen, extend_gen, hf.2.2, sub_self])

private theorem lift_pure {Y : Type y} [AddCommGroup Y] (f : M → X → Y)
    (hf : Balanced right f) (m : M) (x : X) :
    lift f hf (pure right m x) = f m x :=
  extend_gen f m x

variable {B : Type v} [Ring B] [Module B M] [Module (MulOpposite A) M]
variable (hright : ∀ a m, MulOpposite.op a • m = right a m)
variable [SMulCommClass (MulOpposite A) B M]

-- Step 3.1 invokes the induced outer action. Build that action for this
-- quotient by descending m ↦ b • m for fixed b, using the commuting actions.
include hright in
private theorem scaleBalanced (b : B) :
    Balanced right (fun m (x : X) => pure right (b • m) x) := by
  have hp := pure_balanced (X := X) hright
  refine ⟨fun m m' x => ?_, fun m x x' => hp.2.1 _ x x', fun a m x => ?_⟩
  · change pure right (b • (m + m')) x = pure right (b • m) x + pure right (b • m') x
    rw [smul_add, hp.1]
  · change pure right (b • right a m) x = pure right (b • m) (a • x)
    rw [← hright, ← smul_comm (MulOpposite.op a) b m, hright, hp.2.2]

private def scale (b : B) : Tensor right X →+ Tensor right X :=
  lift _ (scaleBalanced hright b)

private theorem scale_pure (b : B) (m : M) (x : X) :
    scale hright b (pure right m x) = pure right (b • m) x :=
  lift_pure _ _ _ _

@[instance_reducible] private def outerModule : Module B (Tensor right X) where
  smul b t := scale hright b t
  one_smul t := by
    have h : scale hright (1 : B) = AddMonoidHom.id (Tensor right X) :=
      tensor_ext hright _ _ (fun m x => by simp only [scale_pure, one_smul, AddMonoidHom.id_apply])
    exact DFunLike.congr_fun h t
  mul_smul b c t := by
    have h : scale (X := X) hright (b * c) = (scale hright b).comp (scale hright c) :=
      tensor_ext hright _ _ (fun m x => by
        simp only [scale_pure, AddMonoidHom.comp_apply, mul_smul])
    exact DFunLike.congr_fun h t
  smul_zero b := map_zero (scale hright b)
  smul_add b t t' := map_add (scale hright b) t t'
  add_smul b c t := by
    have h : scale (X := X) hright (b + c) = scale hright b + scale hright c :=
      tensor_ext hright _ _ (fun m x => by
        simp only [scale_pure, AddMonoidHom.add_apply, add_smul, (pure_balanced (X := X) hright).1])
    exact DFunLike.congr_fun h t
  zero_smul t := by
    have h : scale hright (0 : B) = (0 : Tensor right X →+ Tensor right X) :=
      tensor_ext hright _ _ (fun _ x => by
        simp only [scale_pure, zero_smul, AddMonoidHom.zero_apply]
        have hzero := (pure_balanced hright).1 (0 : M) 0 x
        rw [zero_add] at hzero
        apply add_left_cancel (a := pure right (0 : M) x)
        rw [add_zero, ← hzero])
    exact DFunLike.congr_fun h t

private theorem outer_smul_pure (b : B) (m : M) (x : X) :
    letI : Module B (Tensor right X) := outerModule hright
    b • pure right m x = pure right (b • m) x :=
  scale_pure hright b m x

private def linearLift {Y : Type y} [AddCommGroup Y] [Module B Y]
    (f : M → X → Y) (hf : Balanced right f)
    (hB : ∀ (b : B) m x, f (b • m) x = b • f m x) :
    @LinearMap B B _ _ (RingHom.id B) (Tensor right X) Y _ _
      (outerModule hright) _ :=
  letI : Module B (Tensor right X) := outerModule hright
  { lift f hf with
    map_smul' := by
      intro b t
      let bY := DistribSMul.toAddMonoidHom Y b
      have h : (lift f hf).comp (scale hright b) = bY.comp (lift f hf) :=
        tensor_ext hright _ _ (fun m x => by
          simp only [AddMonoidHom.comp_apply, scale_pure, lift_pure]
          exact hB b m x)
      exact DFunLike.congr_fun h t }

private theorem linearLift_pure {Y : Type y} [AddCommGroup Y] [Module B Y]
    (f : M → X → Y) (hf : Balanced right f)
    (hB : ∀ (b : B) m x, f (b • m) x = b • f m x) (m : M) (x : X) :
    linearLift hright f hf hB (pure right m x) = f m x :=
  lift_pure f hf m x

end Tensor
end CanonicalWattsComparisonSupport
