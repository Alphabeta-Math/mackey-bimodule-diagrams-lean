import WattsFoundation.WattsActions

/-! The free-module step of Eilenberg–Watts, using the checked coproduct
property of the noncommutative tensor construction. -/

set_option backward.isDefEq.respectTransparency false

namespace WattsFoundation

universe u
open CategoryTheory

variable {A B : Type u} [Ring A] [Ring B]
variable (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive]

local instance WattsFreeComparison_local1 : Module (MulOpposite A) (ChoiceFreeWatts.M F) := wattsRightModule F
local instance WattsFreeComparison_local2 : SMulCommClass (MulOpposite A) B (ChoiceFreeWatts.M F) := wattsRight_commutes F
local instance WattsFreeComparison_local3 {X : Type u} [AddCommGroup X] [Module A X] :
    AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := A) (M := ChoiceFreeWatts.M F)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup _
local instance WattsFreeComparison_local4 {X : Type u} [AddCommGroup X] [Module A X] :
    Module B (ChoiceFreeWatts.Tensor (rightAction (R := A) (M := ChoiceFreeWatts.M F)) X) :=
  ChoiceFreeWatts.outerModule _ right_commute

/-- The two concrete presentations induce the same map on each tensor. -/
theorem watts_concrete_map {X Y : ModuleCat.{u} A} (f : X ⟶ Y) :
    concreteTensorMap (M := ChoiceFreeWatts.M F) (S := B) f.hom =
      (ChoiceFreeWatts.tensorMap F f).hom := by
  apply LinearMap.toAddMonoidHom_injective
  apply ChoiceFreeWatts.tensorExt (rightAction (R := A) (M := ChoiceFreeWatts.M F))
  intro m x
  change concreteTensorMap (M := ChoiceFreeWatts.M F) (S := B) f.hom
      (concretePure (R := A) (M := ChoiceFreeWatts.M F) m x) = _
  rw [concreteTensorMap_pure]
  change ChoiceFreeWatts.pure (fun a m => ChoiceFreeWatts.right F a m) m (f.hom x) =
    (ChoiceFreeWatts.tensorMap F f).hom
      (ChoiceFreeWatts.pure (fun a m => ChoiceFreeWatts.right F a m) m x)
  exact (ChoiceFreeWatts.tensorMap_pure F f m x).symm

/-- The canonical inclusion of a copy of `F(A)` into the tensor of a free module. -/
def wattsFreeLeg (I : Type u) (i : I) : ChoiceFreeWatts.M F →ₗ[B]
    ChoiceFreeWatts.tensorObj F (ChoiceFreeWatts.freeObj (A := A) I) :=
  (ChoiceFreeWatts.tensorMap F (ChoiceFreeWatts.freeIncl I i)).hom.comp
    (ChoiceFreeWatts.regularInverse F)

/-- These maps form a coproduct of copies of the regular-module value. -/
theorem wattsFreeLeg_coproduct (I : Type u) :
    ∀ (Q : Type u) [AddCommGroup Q] [Module B Q]
      (legs : ∀ i : I, ChoiceFreeWatts.M F →ₗ[B] Q),
      ∃! d : ChoiceFreeWatts.tensorObj F (ChoiceFreeWatts.freeObj (A := A) I) →ₗ[B] Q,
        ∀ i m, d (wattsFreeLeg F I i m) = legs i m := by
  intro Q _ _ legs
  have hmap (i : I) :
      concreteTensorMap (M := ChoiceFreeWatts.M F) (S := B)
          (ChoiceFreeWatts.sumIncl (fun _ : I => ChoiceFreeWatts.regular A) i) =
        (ChoiceFreeWatts.tensorMap F (ChoiceFreeWatts.freeIncl I i)).hom := by
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := A) (M := ChoiceFreeWatts.M F))
    intro m x
    change concreteTensorMap (M := ChoiceFreeWatts.M F) (S := B) _
        (concretePure (R := A) (M := ChoiceFreeWatts.M F) m x) = _
    rw [concreteTensorMap_pure]
    change ChoiceFreeWatts.pure (fun a m => ChoiceFreeWatts.right F a m) m
        ((ChoiceFreeWatts.freeIncl I i).hom x) =
      (ChoiceFreeWatts.tensorMap F (ChoiceFreeWatts.freeIncl I i)).hom
        (ChoiceFreeWatts.pure (fun a m => ChoiceFreeWatts.right F a m) m x)
    exact (ChoiceFreeWatts.tensorMap_pure F (ChoiceFreeWatts.freeIncl I i) m x).symm
  obtain ⟨d, hd, unique⟩ := concrete_tensor_preserves_coproduct
    (M := ChoiceFreeWatts.M F) (S := B) (fun _ : I => ChoiceFreeWatts.regular A)
    Q (fun i => (legs i).comp (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.regular A)))
  refine ⟨d, ?_, ?_⟩
  · intro i m
    change d ((ChoiceFreeWatts.tensorMap F (ChoiceFreeWatts.freeIncl I i)).hom
      (ChoiceFreeWatts.regularInverse F m)) = legs i m
    have h := hd i (ChoiceFreeWatts.regularInverse F m)
    rw [hmap i] at h
    have inv : ChoiceFreeWatts.comparison F (ChoiceFreeWatts.regular A)
        (ChoiceFreeWatts.regularInverse F m) = m :=
      DFunLike.congr_fun (ChoiceFreeWatts.comparison_regular_right F) m
    change d ((ChoiceFreeWatts.tensorMap F (ChoiceFreeWatts.freeIncl I i)).hom
      (ChoiceFreeWatts.regularInverse F m)) =
        legs i (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.regular A)
          (ChoiceFreeWatts.regularInverse F m)) at h
    rw [inv] at h
    exact h
  · intro e he
    apply unique
    intro i t
    have inv : ChoiceFreeWatts.regularInverse F
        (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.regular A) t) = t :=
      DFunLike.congr_fun (ChoiceFreeWatts.comparison_regular_left F) t
    rw [hmap i]
    have hp := he i (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.regular A) t)
    change e ((ChoiceFreeWatts.tensorMap F (ChoiceFreeWatts.freeIncl I i)).hom
      (ChoiceFreeWatts.regularInverse F (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.regular A) t))) = _ at hp
    rw [inv] at hp
    exact hp

/-- The canonical comparison is bijective on each free module whenever the
additive functor carries that free coproduct to a coproduct. -/
theorem watts_comparison_free_bijective (I : Type u)
    (hcoprod : ∀ (Q : ModuleCat.{u} B) (legs : ∀ _ : I, ChoiceFreeWatts.M F ⟶ Q),
      ∃! d : F.obj (ChoiceFreeWatts.freeObj (A := A) I) ⟶ Q,
        ∀ i, F.map (ChoiceFreeWatts.freeIncl I i) ≫ d = legs i) :
    Function.Bijective (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.freeObj (A := A) I)) := by
  have fc (Q : Type u) [AddCommGroup Q] [Module B Q]
      (legs : ∀ _ : I, ChoiceFreeWatts.M F →ₗ[B] Q) :
      ∃! d : F.obj (ChoiceFreeWatts.freeObj (A := A) I) →ₗ[B] Q,
        ∀ i m, d ((F.map (ChoiceFreeWatts.freeIncl I i)).hom m) = legs i m := by
    obtain ⟨d, hd, unique⟩ := hcoprod (ModuleCat.of B Q) (fun i => ModuleCat.ofHom (legs i))
    refine ⟨d.hom, ?_, ?_⟩
    · intro i m
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (hd i)) m
    · intro e he
      have hm : ModuleCat.ofHom e = d := by
        apply unique
        intro i
        apply ModuleCat.hom_ext
        ext m
        exact he i m
      exact congrArg ModuleCat.Hom.hom hm
  let c := ChoiceFreeWatts.comparison F (ChoiceFreeWatts.freeObj (A := A) I)
  let fincl (i : I) := (F.map (ChoiceFreeWatts.freeIncl I i)).hom
  have comparison_leg (i : I) : c.comp (wattsFreeLeg F I i) = fincl i := by
    change (ChoiceFreeWatts.comparison F _).comp
        ((ChoiceFreeWatts.tensorMap F (ChoiceFreeWatts.freeIncl I i)).hom.comp
          (ChoiceFreeWatts.regularInverse F)) = _
    rw [← LinearMap.comp_assoc, ChoiceFreeWatts.comparison_naturality,
      LinearMap.comp_assoc, ChoiceFreeWatts.comparison_regular_right, LinearMap.comp_id]
  obtain ⟨d, hd, _⟩ := fc (ChoiceFreeWatts.tensorObj F (ChoiceFreeWatts.freeObj (A := A) I))
    (wattsFreeLeg F I)
  have cd : c.comp d = LinearMap.id := by
    obtain ⟨a, ha, unique⟩ := fc (F.obj (ChoiceFreeWatts.freeObj (A := A) I)) fincl
    have hcd : ∀ i m, (c.comp d) (fincl i m) = fincl i m := by
      intro i m
      change c (d (fincl i m)) = _
      rw [hd]
      exact DFunLike.congr_fun (comparison_leg i) m
    have hid : ∀ i m, (LinearMap.id : F.obj (ChoiceFreeWatts.freeObj (A := A) I) →ₗ[B] _) (fincl i m) = fincl i m := by intros; rfl
    exact (unique _ hcd).trans (unique _ hid).symm
  have dc : d.comp c = LinearMap.id := by
    obtain ⟨a, ha, unique⟩ := wattsFreeLeg_coproduct F I
      (ChoiceFreeWatts.tensorObj F (ChoiceFreeWatts.freeObj (A := A) I)) (wattsFreeLeg F I)
    have hdc : ∀ i m, (d.comp c) (wattsFreeLeg F I i m) = wattsFreeLeg F I i m := by
      intro i m
      change d (c (wattsFreeLeg F I i m)) = _
      have hm := DFunLike.congr_fun (comparison_leg i) m
      change c (wattsFreeLeg F I i m) = fincl i m at hm
      rw [hm]
      exact hd i m
    have hid : ∀ i m, (LinearMap.id : ChoiceFreeWatts.tensorObj F (ChoiceFreeWatts.freeObj (A := A) I) →ₗ[B] _) (wattsFreeLeg F I i m) = wattsFreeLeg F I i m := by intros; rfl
    exact (unique _ hdc).trans (unique _ hid).symm
  constructor
  · intro x y h
    have hx := DFunLike.congr_fun dc x
    have hy := DFunLike.congr_fun dc y
    change d (c x) = x at hx
    change d (c y) = y at hy
    change c x = c y at h
    exact hx.symm.trans ((congrArg d h).trans hy)
  · intro y
    exact ⟨d y, DFunLike.congr_fun cd y⟩

#print axioms wattsFreeLeg_coproduct
#print axioms watts_comparison_free_bijective

end WattsFoundation
