import NotesProofs.General.OriginalTensorComposite

/-! Construction of the tensor-composition associator for the paper-style
bimodule encoding. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs.General

universe u v
open CategoryTheory

variable (R S T : Type u) [Ring R] [Ring S] [Ring T]
variable (C : OriginalBimodule.{u,v} S T) (B : OriginalBimodule.{u,v} R S)
variable (X : ModuleCat.{max u v} R)

/-- The nested elementary tensor is balanced in the first two variables. -/
theorem originalAssocPartial_balanced (x : X) :
    originalBalanced S T C B.1 ((originalTensor S T C).obj ((originalTensor R S B).obj X))
      (fun c b => originalTensorPure S T C ((originalTensor R S B).obj X) c
        (originalTensorPure R S B X b x)) := by
  have hc := (originalTensorPure_universal S T C ((originalTensor R S B).obj X)).1
  have hb := (originalTensorPure_universal R S B X).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c c' b
    exact hc.1 c c' _
  · intro c b b'
    dsimp only
    rw [hb.1, hc.2.1]
  · intro t c b
    exact hc.2.2.1 t c _
  · intro s c b
    dsimp only
    rw [hc.2.2.2, ← hb.2.2.1]

/-- For a fixed rightmost tensor factor, descend the nested tensor map
through the first balanced product. -/
noncomputable def originalAssocPartial (x : X) :
    ((originalTensor S T C).obj B.1) →ₗ[T]
      ((originalTensor S T C).obj ((originalTensor R S B).obj X)) :=
  Classical.choose ((originalTensorPure_universal S T C B.1).2
    ((originalTensor S T C).obj ((originalTensor R S B).obj X))
    (fun c b => originalTensorPure S T C ((originalTensor R S B).obj X) c
      (originalTensorPure R S B X b x)) (originalAssocPartial_balanced R S T C B X x))

@[simp] theorem originalAssocPartial_pure (x : X) (c : C.1) (b : B.1) :
    originalAssocPartial R S T C B X x (originalTensorPure S T C B.1 c b) =
      originalTensorPure S T C ((originalTensor R S B).obj X) c (originalTensorPure R S B X b x) :=
  (Classical.choose_spec ((originalTensorPure_universal S T C B.1).2
    ((originalTensor S T C).obj ((originalTensor R S B).obj X))
    (fun c b => originalTensorPure S T C ((originalTensor R S B).obj X) c
      (originalTensorPure R S B X b x)) (originalAssocPartial_balanced R S T C B X x))).1 c b

/-- The descended map is additive in the remaining tensor variable. -/
theorem originalAssocPartial_add (x y : X)
    (z : (originalTensor S T C).obj B.1) :
    originalAssocPartial R S T C B X (x + y) z =
      originalAssocPartial R S T C B X x z + originalAssocPartial R S T C B X y z := by
  let P := fun c b => originalTensorPure S T C ((originalTensor R S B).obj X) c
    (originalTensorPure R S B X b (x + y))
  obtain ⟨g, hg, unique⟩ := (originalTensorPure_universal S T C B.1).2
    ((originalTensor S T C).obj ((originalTensor R S B).obj X)) P
    (originalAssocPartial_balanced R S T C B X (x + y))
  have h1 : ∀ c b, originalAssocPartial R S T C B X (x + y) (originalTensorPure S T C B.1 c b) = P c b := by
    intro c b; exact originalAssocPartial_pure R S T C B X (x + y) c b
  have h2 : ∀ c b, (originalAssocPartial R S T C B X x + originalAssocPartial R S T C B X y)
      (originalTensorPure S T C B.1 c b) = P c b := by
    intro c b
    change originalAssocPartial R S T C B X x (originalTensorPure S T C B.1 c b) +
      originalAssocPartial R S T C B X y (originalTensorPure S T C B.1 c b) = _
    rw [originalAssocPartial_pure, originalAssocPartial_pure]
    change _ = originalTensorPure S T C ((originalTensor R S B).obj X) c (originalTensorPure R S B X b (x + y))
    rw [(originalTensorPure_universal R S B X).1.2.1, (originalTensorPure_universal S T C _).1.2.1]
  have eq := (unique _ h1).trans (unique _ h2).symm
  exact DFunLike.congr_fun eq z

/-- The descended map is balanced for the induced right R-action. -/
theorem originalAssocPartial_balance (r : R) (x : X)
    (z : (originalTensor S T C).obj B.1) :
    originalAssocPartial R S T C B X x (originalRight R T (originalCompositeBimodule R S T C B) z r) =
      originalAssocPartial R S T C B X (r • x) z := by
  letI : Module (MulOpposite R) ((originalTensor S T C).obj B.1) := originalCompositeRightModule R S T C B
  letI : SMulCommClass (MulOpposite R) T ((originalTensor S T C).obj B.1) := originalCompositeRightCommutes R S T C B
  let act := DistribSMul.toLinearMap T ((originalTensor S T C).obj B.1) (MulOpposite.op r)
  let P := fun c b => originalTensorPure S T C ((originalTensor R S B).obj X) c
    (originalTensorPure R S B X b (r • x))
  obtain ⟨g, hg, unique⟩ := (originalTensorPure_universal S T C B.1).2
    ((originalTensor S T C).obj ((originalTensor R S B).obj X)) P
    (originalAssocPartial_balanced R S T C B X (r • x))
  have h1 : ∀ c b, ((originalAssocPartial R S T C B X x).comp act)
      (originalTensorPure S T C B.1 c b) = P c b := by
    intro c b
    change originalAssocPartial R S T C B X x
      (originalRight R T (originalCompositeBimodule R S T C B) (originalTensorPure S T C B.1 c b) r) = _
    rw [originalCompositeBimodule_right, originalAssocPartial_pure]
    change _ = originalTensorPure S T C ((originalTensor R S B).obj X) c (originalTensorPure R S B X b (r • x))
    rw [(originalTensorPure_universal R S B X).1.2.2.2]
  have h2 : ∀ c b, originalAssocPartial R S T C B X (r • x)
      (originalTensorPure S T C B.1 c b) = P c b := by
    intro c b; exact originalAssocPartial_pure R S T C B X (r • x) c b
  have eq := (unique _ h1).trans (unique _ h2).symm
  exact DFunLike.congr_fun eq z

/-- The associator's forward generator map is balanced in the outer tensor. -/
theorem originalAssocForward_balanced :
    originalBalanced R T (originalCompositeBimodule R S T C B) X
      ((originalTensor S T C).obj ((originalTensor R S B).obj X))
      (fun z x => originalAssocPartial R S T C B X x z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z z' x; exact map_add (originalAssocPartial R S T C B X x) z z'
  · intro z x y; exact originalAssocPartial_add R S T C B X x y z
  · intro t z x; exact (originalAssocPartial R S T C B X x).map_smul t z
  · intro r z x; exact originalAssocPartial_balance R S T C B X r x z

/-- The forward comparison for composition of tensor functors. -/
noncomputable def originalAssocForward :
    (originalTensor R T (originalCompositeBimodule R S T C B)).obj X →ₗ[T]
      (originalTensor S T C).obj ((originalTensor R S B).obj X) :=
  Classical.choose ((originalTensorPure_universal R T (originalCompositeBimodule R S T C B) X).2
    ((originalTensor S T C).obj ((originalTensor R S B).obj X))
    (fun z x => originalAssocPartial R S T C B X x z) (originalAssocForward_balanced R S T C B X))

/-- The forward comparison has the expected formula on nested generators. -/
theorem originalAssocForward_pure (c : C.1) (b : B.1) (x : X) :
    originalAssocForward R S T C B X
      (originalTensorPure R T (originalCompositeBimodule R S T C B) X
        (originalTensorPure S T C B.1 c b) x) =
      originalTensorPure S T C ((originalTensor R S B).obj X) c (originalTensorPure R S B X b x) := by
  have h := (Classical.choose_spec ((originalTensorPure_universal R T (originalCompositeBimodule R S T C B) X).2
    ((originalTensor S T C).obj ((originalTensor R S B).obj X))
    (fun z x => originalAssocPartial R S T C B X x z) (originalAssocForward_balanced R S T C B X))).1
      (originalTensorPure S T C B.1 c b) x
  exact h.trans (originalAssocPartial_pure R S T C B X x c b)

/-- For fixed c, the reverse generator map is balanced over R. -/
theorem originalAssocReversePartial_balanced (c : C.1) :
    ChoiceFreeWatts.Balanced (fun r b => originalRight R S B b r)
      (fun b x => originalTensorPure R T (originalCompositeBimodule R S T C B) X
        (originalTensorPure S T C B.1 c b) x) := by
  have hc := (originalTensorPure_universal S T C B.1).1
  have hp := (originalTensorPure_universal R T (originalCompositeBimodule R S T C B) X).1
  refine ⟨?_, ?_, ?_⟩
  · intro b b' x
    dsimp only
    rw [hc.2.1, hp.1]
  · intro b x y
    exact hp.2.1 _ x y
  · intro r b x
    dsimp only
    rw [← originalCompositeBimodule_right, hp.2.2.2]

/-- Descend the reverse map in its inner tensor variable. -/
noncomputable def originalAssocReversePartial (c : C.1) :
    ((originalTensor R S B).obj X) →+ ((originalTensor R T (originalCompositeBimodule R S T C B)).obj X) := by
  letI : AddCommGroup (ChoiceFreeWatts.Tensor (fun r b => originalRight R S B b r) X) :=
    ChoiceFreeWatts.tensorAddCommGroup _
  exact ChoiceFreeWatts.tensorLift (fun r b => originalRight R S B b r)
    (fun b x => originalTensorPure R T (originalCompositeBimodule R S T C B) X
      (originalTensorPure S T C B.1 c b) x)
    (originalAssocReversePartial_balanced R S T C B X c)

@[simp] theorem originalAssocReversePartial_pure (c : C.1) (b : B.1) (x : X) :
    originalAssocReversePartial R S T C B X c (originalTensorPure R S B X b x) =
      originalTensorPure R T (originalCompositeBimodule R S T C B) X
        (originalTensorPure S T C B.1 c b) x := by
  exact ChoiceFreeWatts.tensorLift_pure (fun r b => originalRight R S B b r)
    (fun b x => originalTensorPure R T (originalCompositeBimodule R S T C B) X
      (originalTensorPure S T C B.1 c b) x)
    (originalAssocReversePartial_balanced R S T C B X c) b x

/-- Additive maps out of the concrete tensor are determined by elementary tensors. -/
theorem originalTensor_addExt {Y : Type (max u v)} [AddCommGroup Y]
    (f g : ((originalTensor R S B).obj X) →+ Y)
    (h : ∀ b x, f (originalTensorPure R S B X b x) = g (originalTensorPure R S B X b x)) : f = g := by
  apply ChoiceFreeWatts.tensorExt (fun r b => originalRight R S B b r)
  exact h

/-- The reverse partial map is additive in the first tensor variable. -/
theorem originalAssocReversePartial_add (c c' : C.1)
    (z : (originalTensor R S B).obj X) :
    originalAssocReversePartial R S T C B X (c + c') z =
      originalAssocReversePartial R S T C B X c z + originalAssocReversePartial R S T C B X c' z := by
  have eq : originalAssocReversePartial R S T C B X (c + c') =
      originalAssocReversePartial R S T C B X c + originalAssocReversePartial R S T C B X c' := by
    apply originalTensor_addExt R S B X
    intro b x
    change originalAssocReversePartial R S T C B X (c + c') (originalTensorPure R S B X b x) =
      originalAssocReversePartial R S T C B X c (originalTensorPure R S B X b x) +
        originalAssocReversePartial R S T C B X c' (originalTensorPure R S B X b x)
    rw [originalAssocReversePartial_pure, originalAssocReversePartial_pure, originalAssocReversePartial_pure,
      (originalTensorPure_universal S T C B.1).1.1,
      (originalTensorPure_universal R T (originalCompositeBimodule R S T C B) X).1.1]
  exact DFunLike.congr_fun eq z

/-- The reverse partial map respects the middle balancing action. -/
theorem originalAssocReversePartial_balance (s : S) (c : C.1)
    (z : (originalTensor R S B).obj X) :
    originalAssocReversePartial R S T C B X (originalRight S T C c s) z =
      originalAssocReversePartial R S T C B X c (s • z) := by
  let act := DistribSMul.toAddMonoidHom ((originalTensor R S B).obj X) s
  have eq : originalAssocReversePartial R S T C B X (originalRight S T C c s) =
      (originalAssocReversePartial R S T C B X c).comp act := by
    apply originalTensor_addExt R S B X
    intro b x
    change originalAssocReversePartial R S T C B X (originalRight S T C c s)
        (originalTensorPure R S B X b x) =
      originalAssocReversePartial R S T C B X c (s • originalTensorPure R S B X b x)
    rw [← (originalTensorPure_universal R S B X).1.2.2.1,
      originalAssocReversePartial_pure, originalAssocReversePartial_pure,
      (originalTensorPure_universal S T C B.1).1.2.2.2]
  exact DFunLike.congr_fun eq z

/-- The reverse partial map respects the outer left T-action. -/
theorem originalAssocReversePartial_outer (t : T) (c : C.1)
    (z : (originalTensor R S B).obj X) :
    originalAssocReversePartial R S T C B X (t • c) z =
      t • originalAssocReversePartial R S T C B X c z := by
  let act := DistribSMul.toAddMonoidHom ((originalTensor R T (originalCompositeBimodule R S T C B)).obj X) t
  have eq : originalAssocReversePartial R S T C B X (t • c) =
      act.comp (originalAssocReversePartial R S T C B X c) := by
    apply originalTensor_addExt R S B X
    intro b x
    change originalAssocReversePartial R S T C B X (t • c) (originalTensorPure R S B X b x) =
      t • originalAssocReversePartial R S T C B X c (originalTensorPure R S B X b x)
    rw [originalAssocReversePartial_pure, originalAssocReversePartial_pure,
      (originalTensorPure_universal S T C B.1).1.2.2.1,
      (originalTensorPure_universal R T (originalCompositeBimodule R S T C B) X).1.2.2.1]
  exact DFunLike.congr_fun eq z

/-- The reverse generator map is balanced for the outer tensor. -/
theorem originalAssocReverse_balanced :
    originalBalanced S T C ((originalTensor R S B).obj X)
      ((originalTensor R T (originalCompositeBimodule R S T C B)).obj X)
      (fun c z => originalAssocReversePartial R S T C B X c z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c c' z; exact originalAssocReversePartial_add R S T C B X c c' z
  · intro c z z'; exact map_add (originalAssocReversePartial R S T C B X c) z z'
  · intro t c z; exact originalAssocReversePartial_outer R S T C B X t c z
  · intro s c z; exact originalAssocReversePartial_balance R S T C B X s c z

/-- The reverse comparison for composition of tensor functors. -/
noncomputable def originalAssocReverse :
    (originalTensor S T C).obj ((originalTensor R S B).obj X) →ₗ[T]
      (originalTensor R T (originalCompositeBimodule R S T C B)).obj X :=
  Classical.choose ((originalTensorPure_universal S T C ((originalTensor R S B).obj X)).2
    ((originalTensor R T (originalCompositeBimodule R S T C B)).obj X)
    (fun c z => originalAssocReversePartial R S T C B X c z) (originalAssocReverse_balanced R S T C B X))

/-- The reverse comparison has the expected formula on nested generators. -/
theorem originalAssocReverse_pure (c : C.1) (b : B.1) (x : X) :
    originalAssocReverse R S T C B X
      (originalTensorPure S T C ((originalTensor R S B).obj X) c (originalTensorPure R S B X b x)) =
      originalTensorPure R T (originalCompositeBimodule R S T C B) X
        (originalTensorPure S T C B.1 c b) x := by
  have h := (Classical.choose_spec ((originalTensorPure_universal S T C ((originalTensor R S B).obj X)).2
    ((originalTensor R T (originalCompositeBimodule R S T C B)).obj X)
    (fun c z => originalAssocReversePartial R S T C B X c z) (originalAssocReverse_balanced R S T C B X))).1
      c (originalTensorPure R S B X b x)
  exact h.trans (originalAssocReversePartial_pure R S T C B X c b x)

/-- Fixing the second variable gives a left-linear map on a tensor. -/
noncomputable def originalPureLeftLinear (A B : Type u) [Ring A] [Ring B]
    (M : OriginalBimodule.{u,v} A B) (Y : ModuleCat.{max u v} A) (y : Y) :
    M.1 →ₗ[B] (originalTensor A B M).obj Y where
  toFun m := originalTensorPure A B M Y m y
  map_add' m n := (originalTensorPure_universal A B M Y).1.1 m n y
  map_smul' b m := (originalTensorPure_universal A B M Y).1.2.2.1 b m y

/-- Fixing the first variable gives an additive map on a tensor. -/
noncomputable def originalPureRightAdd (A B : Type u) [Ring A] [Ring B]
    (M : OriginalBimodule.{u,v} A B) (Y : ModuleCat.{max u v} A) (m : M.1) :
    Y →+ (originalTensor A B M).obj Y :=
  AddMonoidHom.mk' (fun y => originalTensorPure A B M Y m y)
    (fun y y' => (originalTensorPure_universal A B M Y).1.2.1 m y y')

/-- The two associator maps are inverse on the left-associated tensor. -/
theorem originalAssocReverse_forward :
    (originalAssocReverse R S T C B X).comp (originalAssocForward R S T C B X) = LinearMap.id := by
  apply LinearMap.toAddMonoidHom_injective
  apply ChoiceFreeWatts.tensorExt (fun r z => originalRight R T (originalCompositeBimodule R S T C B) z r)
  intro z x
  let p := originalPureLeftLinear R T (originalCompositeBimodule R S T C B) X x
  have eq : (originalAssocReverse R S T C B X).comp ((originalAssocForward R S T C B X).comp p) = p := by
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (fun s c => originalRight S T C c s)
    intro c b
    change originalAssocReverse R S T C B X (originalAssocForward R S T C B X
      (originalTensorPure R T (originalCompositeBimodule R S T C B) X
        (originalTensorPure S T C B.1 c b) x)) = _
    rw [originalAssocForward_pure, originalAssocReverse_pure]
    rfl
  exact DFunLike.congr_fun eq z

/-- The two associator maps are inverse on the right-associated tensor. -/
theorem originalAssocForward_reverse :
    (originalAssocForward R S T C B X).comp (originalAssocReverse R S T C B X) = LinearMap.id := by
  apply LinearMap.toAddMonoidHom_injective
  apply ChoiceFreeWatts.tensorExt (fun s c => originalRight S T C c s)
  intro c z
  let p := originalPureRightAdd S T C ((originalTensor R S B).obj X) c
  have eq : ((originalAssocForward R S T C B X).comp (originalAssocReverse R S T C B X)).toAddMonoidHom.comp p = p := by
    apply originalTensor_addExt R S B X
    intro b x
    change originalAssocForward R S T C B X (originalAssocReverse R S T C B X
      (originalTensorPure S T C ((originalTensor R S B).obj X) c (originalTensorPure R S B X b x))) = _
    rw [originalAssocReverse_pure, originalAssocForward_pure]
    rfl
  exact DFunLike.congr_fun eq z

/-- The tensor-composition associator at a module. -/
noncomputable def originalAssocIso :
    (originalTensor R T (originalCompositeBimodule R S T C B)).obj X ≃ₗ[T]
      (originalTensor S T C).obj ((originalTensor R S B).obj X) :=
  LinearEquiv.ofLinearMap (originalAssocForward R S T C B X) (originalAssocReverse R S T C B X)
    (originalAssocForward_reverse R S T C B X) (originalAssocReverse_forward R S T C B X)

/-- The associator is natural in the rightmost module. -/
noncomputable def originalAssocNatIso :
    originalTensor R T (originalCompositeBimodule R S T C B) ≅
      originalTensor R S B ⋙ originalTensor S T C := by
  refine NatIso.ofComponents (fun X => (originalAssocIso R S T C B X).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply ChoiceFreeWatts.tensorExt (fun r z => originalRight R T (originalCompositeBimodule R S T C B) z r)
  intro z x
  let p := originalPureLeftLinear R T (originalCompositeBimodule R S T C B) X x
  have eq : (originalAssocForward R S T C B Y).comp
        (((originalTensor R T (originalCompositeBimodule R S T C B)).map f).hom.comp p) =
      (((originalTensor S T C).map ((originalTensor R S B).map f)).hom).comp
        ((originalAssocForward R S T C B X).comp p) := by
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (fun s c => originalRight S T C c s)
    intro c b
    change originalAssocForward R S T C B Y
        (((originalTensor R T (originalCompositeBimodule R S T C B)).map f).hom
          (originalTensorPure R T (originalCompositeBimodule R S T C B) X (originalTensorPure S T C B.1 c b) x)) =
      ((originalTensor S T C).map ((originalTensor R S B).map f)).hom
        (originalAssocForward R S T C B X
          (originalTensorPure R T (originalCompositeBimodule R S T C B) X (originalTensorPure S T C B.1 c b) x))
    rw [originalTensorPure_map, originalAssocForward_pure, originalAssocForward_pure,
      originalTensorPure_map, originalTensorPure_map]
  exact DFunLike.congr_fun eq z

/-- The natural associator has the paper's formula on nested tensors. -/
theorem originalAssocNatIso_pure (c : C.1) (b : B.1) (x : X) :
    ((originalAssocNatIso R S T C B).hom.app X).hom
      (originalTensorPure R T (originalCompositeBimodule R S T C B) X
        (originalTensorPure S T C B.1 c b) x) =
      originalTensorPure S T C ((originalTensor R S B).obj X) c (originalTensorPure R S B X b x) :=
  originalAssocForward_pure R S T C B X c b x

#print axioms originalAssocNatIso
#print axioms originalAssocNatIso_pure
#print axioms originalAssocIso
#print axioms originalAssocReverse_forward
#print axioms originalAssocForward_reverse
#print axioms originalAssocReverse_pure
#print axioms originalAssocReversePartial_pure
#print axioms originalAssocForward_pure
#print axioms originalAssocPartial_pure

end NotesProofs.General
