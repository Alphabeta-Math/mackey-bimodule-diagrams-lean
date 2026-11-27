import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Coinvariants
import MackeyDiagrams.Balanced

namespace ParabolicTensorSupport

open CategoryTheory Representation Representation.Coinvariants
open scoped TensorProduct

universe u
noncomputable section

variable {K H J F : Type} [Group K] [Group H] [Group J] [Group F]

private abbrev leftAct (X : Rep.{u} Complex (K × H))
    (a : MonoidAlgebra Complex K) (x : X.V) :=
  Finsupp.sum a.coeff (fun k c => c • X.ρ (k, 1) x)

private abbrev rightAct (X : Rep.{u} Complex (K × H))
    (a : MonoidAlgebra Complex H) (x : X.V) :=
  Finsupp.sum a.coeff (fun h c => c • X.ρ (1, h⁻¹) x)

private abbrev GroupBalanced (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {W : Type*} [AddCommGroup W] [Module Complex W] (b : X.V →ₗ[Complex] Y.V →ₗ[Complex] W) :=
  ∀ h : H, ∀ x y, b (X.ρ (1, h) x) (Y.ρ (h, 1) y) = b x y

private abbrev AlgebraBalanced (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {W : Type*} [AddCommGroup W] [Module Complex W] (b : X.V →ₗ[Complex] Y.V →ₗ[Complex] W) :=
  ∀ a x y, b (rightAct X a x) y = b x (leftAct Y a y)

private theorem prodRep_mul_apply {G : Type} [Group G] (X : Rep.{u} Complex G)
    (g h : G) (x : X.V) : X.ρ (g * h) x = X.ρ g (X.ρ h x) := by
  rw [map_mul]
  rfl

private theorem prodOne {G L : Type} [Group G] [Group L]
    (X : Rep.{u} Complex (G × L)) (x : X.V) : X.ρ (1, 1) x = x := by
  change X.ρ 1 x = x
  rw [map_one]
  rfl

private theorem groupSingle (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {W : Type*} [AddCommGroup W] [Module Complex W] {b : X.V →ₗ[Complex] Y.V →ₗ[Complex] W}
    (hb : GroupBalanced X Y b) (h : H) (x : X.V) (y : Y.V) :
    b (X.ρ (1, h⁻¹) x) y = b x (Y.ρ (h, 1) y) := by
  have he := hb h (X.ρ (1, h⁻¹) x) y
  rwa [← prodRep_mul_apply, Prod.mk_mul_mk, mul_one, mul_inv_cancel, prodOne, eq_comm] at he

private theorem algebraBalanced_iff (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {W : Type*} [AddCommGroup W] [Module Complex W] (b : X.V →ₗ[Complex] Y.V →ₗ[Complex] W) :
    AlgebraBalanced X Y b ↔ GroupBalanced X Y b := by
  constructor
  · intro h t x y
    have hh := h (MonoidAlgebra.of Complex H t) (X.ρ (1, t) x) y
    change b (Finsupp.sum (Finsupp.single t (1 : Complex))
      (fun h c => c • X.ρ (1, h⁻¹) (X.ρ (1, t) x))) y =
      b (X.ρ (1, t) x) (Finsupp.sum (Finsupp.single t (1 : Complex)) (fun h c => c • Y.ρ (h, 1) y)) at hh
    simpa [Finsupp.sum_single_index, ← prodRep_mul_apply, prodOne, eq_comm] using hh
  · intro h a x y
    change b.flip y (∑ t ∈ a.coeff.support, a.coeff t • X.ρ (1, t⁻¹) x) =
      b x (∑ t ∈ a.coeff.support, a.coeff t • Y.ρ (t, 1) y)
    simp only [map_sum, map_smul, LinearMap.flip_apply, groupSingle X Y h]

private abbrev middle (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J)) :
    Representation Complex H (X.V ⊗[Complex] Y.V) :=
  Representation.tprod (X.ρ.comp (MonoidHom.inr K H)) (Y.ρ.comp (MonoidHom.inl H J))

private abbrev Carrier (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J)) :=
  (middle X Y).Coinvariants

private abbrev pure (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J)) :
    X.V →ₗ[Complex] Y.V →ₗ[Complex] Carrier X Y :=
  (TensorProduct.mk Complex X.V Y.V).compr₂ (Coinvariants.mk (middle X Y))

private theorem mid_pure (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    (h : H) (x : X.V) (y : Y.V) :
    middle X Y h (x ⊗ₜ[Complex] y) = X.ρ (1, h) x ⊗ₜ[Complex] Y.ρ (h, 1) y :=
  TensorProduct.map_tmul _ _ _ _

private theorem pure_balanced (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J)) :
    GroupBalanced X Y (pure X Y) := by
  intro h x y
  change Coinvariants.mk _ (X.ρ (1, h) x ⊗ₜ[Complex] Y.ρ (h, 1) y) =
    Coinvariants.mk _ (x ⊗ₜ[Complex] y)
  rw [← mid_pure, Coinvariants.mk_self_apply]

private theorem pure_ext (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {W : Type*} [AddCommGroup W] [Module Complex W] {f g : Carrier X Y →ₗ[Complex] W}
    (h : ∀ x y, f (pure X Y x y) = g (pure X Y x y)) : f = g := by
  apply Coinvariants.hom_ext
  apply TensorProduct.ext
  ext x y
  exact h x y

-- Alphabeta Math's tensor universal property, steps 1.2, 4.1 and 5.1:
-- descend the balanced map and prove uniqueness on pure tensors. Commuting
-- complex scalars allow Mathlib's tensor of vector spaces followed by
-- coinvariants. ModuleTensorUniversalProperty gives additive lifts out of
-- its integer free-group quotient. This representation needs complex-linear
-- lifts out of the displayed coinvariant quotient. Here the group equation
-- is equivalent to balance over the entire complex group algebra, and
-- Coinvariants.lift and Coinvariants.hom_ext supply the two lift laws.
private def lift (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {W : Type*} [AddCommGroup W] [Module Complex W]
    (b : X.V →ₗ[Complex] Y.V →ₗ[Complex] W) (hb : GroupBalanced X Y b) :
    Carrier X Y →ₗ[Complex] W :=
  Coinvariants.lift (middle X Y) (TensorProduct.lift b) (by
    intro h
    apply TensorProduct.ext
    ext x y
    change TensorProduct.lift b (middle X Y h (x ⊗ₜ[Complex] y)) =
      TensorProduct.lift b (x ⊗ₜ[Complex] y)
    rw [mid_pure, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
    exact hb h x y)

@[simp] private theorem lift_pure (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {W : Type*} [AddCommGroup W] [Module Complex W]
    (b : X.V →ₗ[Complex] Y.V →ₗ[Complex] W) (hb : GroupBalanced X Y b) (x : X.V) (y : Y.V) :
    lift X Y b hb (pure X Y x y) = b x y := by
  exact TensorProduct.lift.tmul x y

private theorem right_left_comm (X : Rep.{u} Complex (K × H))
    (k : K) (h : H) (x : X.V) :
    X.ρ (1, h) (X.ρ (k, 1) x) = X.ρ (k, 1) (X.ρ (1, h) x) := by
  simp only [← prodRep_mul_apply, Prod.mk_mul_mk, mul_one, one_mul]

private def exterior (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    (g : K × J) : Carrier X Y →ₗ[Complex] Carrier X Y :=
  lift X Y (((pure X Y).comp (X.ρ (g.1, 1))).compl₂ (Y.ρ (1, g.2))) (by
    intro h x y
    change pure X Y (X.ρ (g.1, 1) (X.ρ (1, h) x)) (Y.ρ (1, g.2) (Y.ρ (h, 1) y)) = _
    rw [← right_left_comm X, right_left_comm Y]
    exact pure_balanced X Y h _ _)

@[simp] private theorem exterior_pure (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    (g : K × J) (x : X.V) (y : Y.V) :
    exterior X Y g (pure X Y x y) = pure X Y (X.ρ (g.1, 1) x) (Y.ρ (1, g.2) y) :=
  lift_pure _ _ _ _ _ _

private def tensor (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J)) :
    Rep.{u} Complex (K × J) :=
  Rep.of (X := Carrier X Y)
    { toFun := exterior X Y
      map_one' := by
        apply pure_ext X Y
        intro x y
        change exterior X Y (1, 1) (pure X Y x y) = pure X Y x y
        simp only [exterior_pure, prodOne]
      map_mul' := by
        intro g h
        apply pure_ext X Y
        intro x y
        change exterior X Y (g * h) (pure X Y x y) =
          exterior X Y g (exterior X Y h (pure X Y x y))
        simp only [exterior_pure, ← prodRep_mul_apply, Prod.mk_mul_mk, Prod.fst_mul, Prod.snd_mul,
          mul_one] }

@[simp] private theorem tensor_act_pure (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    (g : K × J) (x : X.V) (y : Y.V) :
    (tensor X Y).ρ g (pure X Y x y) = pure X Y (X.ρ (g.1, 1) x) (Y.ρ (1, g.2) y) :=
  exterior_pure X Y g x y

private theorem exteriorAlgebra (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    (a : MonoidAlgebra Complex K) (b : MonoidAlgebra Complex J) (x : X.V) (y : Y.V) :
    pure X Y (leftAct X a x) (rightAct Y b y) =
      leftAct (tensor X Y) a (rightAct (tensor X Y) b (pure X Y x y)) := by
  have right : pure X Y x (rightAct Y b y) = rightAct (tensor X Y) b (pure X Y x y) := by
    change pure X Y x (∑ j ∈ b.coeff.support, b.coeff j • Y.ρ (1, j⁻¹) y) =
      ∑ j ∈ b.coeff.support, b.coeff j • (tensor X Y).ρ (1, j⁻¹) (pure X Y x y)
    simp only [map_sum, map_smul, tensor_act_pure, prodOne] <;> rfl
  rw [← right]
  change (pure X Y).flip (rightAct Y b y) (∑ k ∈ a.coeff.support, a.coeff k • X.ρ (k, 1) x) =
    ∑ k ∈ a.coeff.support, a.coeff k • (tensor X Y).ρ (k, 1) (pure X Y x (rightAct Y b y))
  simp only [map_sum, map_smul, LinearMap.flip_apply, tensor_act_pure, prodOne] <;> rfl



open MackeyDiagrams

private abbrev linearize (X : Biset K H) : Rep.{u} Complex (K × H) :=
  letI : MulAction (K × H) (ULift.{u} X.carrier) :=
    { smul := fun g x => ⟨X.act g x.down⟩
      one_smul := fun x => congrArg ULift.up (X.one_act x.down)
      mul_smul := fun g h x => congrArg ULift.up (X.mul_act g h x.down) }
  Rep.ofMulAction Complex (K × H) (ULift.{u} X.carrier)


private theorem linearize_single (X : Biset K H) (g : K × H) (x : X.carrier) (c : Complex) :
    (linearize.{u} X).ρ g (MonoidAlgebra.single (ULift.up x) c) =
      MonoidAlgebra.single (ULift.up (X.act g x)) c := by
  letI : MulAction (K × H) (ULift.{u} X.carrier) :=
    { smul := fun g x => ⟨X.act g x.down⟩
      one_smul := fun x => congrArg ULift.up (X.one_act x.down)
      mul_smul := fun g h x => congrArg ULift.up (X.mul_act g h x.down) }
  exact Representation.ofMulAction_single (k := Complex) g (ULift.up x) c

private def basisCoords (X : Biset K H) : (X.carrier →₀ Complex) ≃ₗ[Complex] (linearize.{u} X).V :=
  (Finsupp.domLCongr Equiv.ulift.symm).trans (MonoidAlgebra.coeffLinearEquiv Complex).symm

private theorem basisCoords_single (X : Biset K H) (x : X.carrier) (c : Complex) :
    basisCoords.{u} X (Finsupp.single x c) = MonoidAlgebra.single (ULift.up x) c := by
  simp only [basisCoords, LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  rfl

private theorem basisCoords_action (X : Biset K H) (g : K × H) (x : X.carrier →₀ Complex) :
    basisCoords.{u} X (X.actLinear Complex g x) = (linearize X).ρ g (basisCoords.{u} X x) := by
  apply LinearMap.congr_fun
    (f := (basisCoords.{u} X).toLinearMap.comp (X.actLinear Complex g))
    (g := ((linearize.{u} X).ρ g).comp (basisCoords.{u} X).toLinearMap)
  apply Finsupp.lhom_ext
  intro a c
  change basisCoords.{u} X (X.actLinear Complex g (Finsupp.single a c)) =
    (linearize X).ρ g (basisCoords.{u} X (Finsupp.single a c))
  rw [Biset.actLinear_single, basisCoords_single, basisCoords_single, linearize_single]

private def equivariantIso {G : Type} [Group G] {M N : Rep.{u} Complex G}
    (e : M.V ≃ₗ[Complex] N.V) (h : ∀ g x, e (M.ρ g x) = N.ρ g (e x)) : M ≅ N :=
  Rep.mkIso (Representation.Equiv.mk e (fun g => LinearMap.ext (h g)))

private def bisetPair (X : Biset K H) (Y : Biset H J) :
    (linearize.{u} X).V →ₗ[Complex] (linearize.{u} Y).V →ₗ[Complex] (linearize.{u} (X.tensor Y)).V :=
  ((((Biset.pairLinear Complex X Y).comp (basisCoords X).symm.toLinearMap).compl₂
    (basisCoords Y).symm.toLinearMap).compr₂ (basisCoords (X.tensor Y)).toLinearMap)

private theorem bisetPair_coords (X : Biset K H) (Y : Biset H J)
    (x : X.carrier →₀ Complex) (y : Y.carrier →₀ Complex) :
    bisetPair X Y (basisCoords.{u} X x) (basisCoords.{u} Y y) =
      basisCoords.{u} (X.tensor Y) (Biset.pairLinear Complex X Y x y) := by
  change basisCoords.{u} (X.tensor Y) (Biset.pairLinear Complex X Y
    ((basisCoords.{u} X).symm (basisCoords.{u} X x)) ((basisCoords.{u} Y).symm (basisCoords.{u} Y y))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

private theorem bisetPair_action (X : Biset K H) (Y : Biset H J) (g : K × J)
    (x : (linearize.{u} X).V) (y : (linearize.{u} Y).V) :
    bisetPair X Y ((linearize X).ρ (g.1, 1) x) ((linearize Y).ρ (1, g.2) y) =
      (linearize (X.tensor Y)).ρ g (bisetPair X Y x y) := by
  obtain ⟨v, rfl⟩ := (basisCoords X).surjective x
  obtain ⟨w, rfl⟩ := (basisCoords Y).surjective y
  rw [← basisCoords_action X _ v, ← basisCoords_action Y _ w, bisetPair_coords,
    bisetPair_coords, ← basisCoords_action]
  exact congrArg (basisCoords.{u} (X.tensor Y))
    (Biset.pairLinear_action Complex X Y (g.1, 1) (1, g.2) g (fun _ _ => rfl) v w)

private theorem bisetPair_balanced (X : Biset K H) (Y : Biset H J) :
    GroupBalanced (linearize.{u} X) (linearize.{u} Y) (bisetPair X Y) := by
  intro h x y
  obtain ⟨v, rfl⟩ := (basisCoords X).surjective x
  obtain ⟨w, rfl⟩ := (basisCoords Y).surjective y
  rw [← basisCoords_action X _ v, ← basisCoords_action Y _ w, bisetPair_coords,
    bisetPair_coords, Biset.pairLinear_balance]

private def compareForward (X : Biset K H) (Y : Biset H J) :
    Carrier (linearize.{u} X) (linearize.{u} Y) →ₗ[Complex] (linearize.{u} (X.tensor Y)).V :=
  lift _ _ (bisetPair X Y) (bisetPair_balanced X Y)

private theorem compareForward_pure (X : Biset K H) (Y : Biset H J)
    (x : (linearize.{u} X).V) (y : (linearize.{u} Y).V) :
    compareForward X Y (pure (linearize X) (linearize Y) x y) = bisetPair X Y x y :=
  lift_pure _ _ _ _ _ _

-- The route's balanced-biset lift applies after transporting along the
-- basis coordinates. Its hypothesis is the diagonal group balance proved
-- for the same pure pairs. The uniqueness lemma checks the inverse.
private def compareBackward (X : Biset K H) (Y : Biset H J) :
    (linearize.{u} (X.tensor Y)).V →ₗ[Complex] Carrier (linearize.{u} X) (linearize.{u} Y) :=
  let b := (((pure (linearize.{u} X) (linearize.{u} Y)).comp
    (basisCoords X).toLinearMap).compl₂ (basisCoords Y).toLinearMap)
  let hb : Biset.IsBalanced b := by
    intro h x y
    change pure (linearize X) (linearize Y) (basisCoords X (X.actLinear Complex (1, h) x))
      (basisCoords Y (Y.actLinear Complex (h, 1) y)) = _
    rw [basisCoords_action, basisCoords_action]
    exact pure_balanced (linearize X) (linearize Y) h _ _
  (Biset.liftBalanced b hb).comp (basisCoords (X.tensor Y)).symm.toLinearMap

private theorem compareBackward_pair (X : Biset K H) (Y : Biset H J)
    (x : (linearize.{u} X).V) (y : (linearize.{u} Y).V) :
    compareBackward X Y (bisetPair X Y x y) = pure (linearize X) (linearize Y) x y := by
  obtain ⟨v, rfl⟩ := (basisCoords X).surjective x
  obtain ⟨w, rfl⟩ := (basisCoords Y).surjective y
  rw [bisetPair_coords]
  unfold compareBackward
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  erw [Biset.liftBalanced_pairLinear]
  rfl

private theorem bisetPair_ext (X : Biset K H) (Y : Biset H J)
    {W : Type*} [AddCommGroup W] [Module Complex W]
    (f g : (linearize.{u} (X.tensor Y)).V →ₗ[Complex] W)
    (h : ∀ x y, f (bisetPair X Y x y) = g (bisetPair X Y x y)) : f = g := by
  let b := ((bisetPair X Y).compr₂ f).comp (basisCoords.{u} X).toLinearMap |>.compl₂
    (basisCoords.{u} Y).toLinearMap
  have hb : Biset.IsBalanced b := by
    intro h x y
    change f (bisetPair X Y (basisCoords X (X.actLinear Complex (1, h) x))
      (basisCoords Y (Y.actLinear Complex (h, 1) y))) = _
    rw [basisCoords_action, basisCoords_action, bisetPair_balanced]
    rfl
  have hf (q : (linearize.{u} (X.tensor Y)).V →ₗ[Complex] W)
      (hq : ∀ x y, q (bisetPair X Y x y) = f (bisetPair X Y x y)) :
      q.comp (basisCoords (X.tensor Y)).toLinearMap = Biset.liftBalanced b hb := by
    apply Biset.liftBalanced_unique b hb
    intro x y
    change q (basisCoords (X.tensor Y) (Biset.pairLinear Complex X Y x y)) =
      f (bisetPair X Y (basisCoords X x) (basisCoords Y y))
    rw [← bisetPair_coords, hq]
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (basisCoords (X.tensor Y)).surjective z
  exact LinearMap.congr_fun ((hf f (fun _ _ => rfl)).trans (hf g (fun x y => (h x y).symm)).symm) z

private def compareTensor (X : Biset K H) (Y : Biset H J) :
    tensor (linearize.{u} X) (linearize.{u} Y) ≅ linearize.{u} (X.tensor Y) := by
  let forward := compareForward.{u} X Y
  let backward := compareBackward.{u} X Y
  have left : backward.comp forward = LinearMap.id := by
    apply pure_ext (linearize X) (linearize Y)
    intro x y
    change compareBackward X Y (compareForward X Y (pure (linearize X) (linearize Y) x y)) = _
    rw [compareForward_pure, compareBackward_pair]
    rfl
  have right : forward.comp backward = LinearMap.id := by
    apply bisetPair_ext X Y
    intro x y
    change compareForward X Y (compareBackward X Y (bisetPair X Y x y)) = _
    rw [compareBackward_pair, compareForward_pure]
    rfl
  apply equivariantIso (LinearEquiv.ofLinearMap forward backward right left)
  intro g
  apply LinearMap.congr_fun
    (f := forward.comp ((tensor (linearize X) (linearize Y)).ρ g))
    (g := ((linearize (X.tensor Y)).ρ g).comp forward)
  apply pure_ext (linearize X) (linearize Y)
  intro x y
  change compareForward X Y ((tensor (linearize X) (linearize Y)).ρ g (pure (linearize X) (linearize Y) x y)) =
    (linearize (X.tensor Y)).ρ g (compareForward X Y (pure (linearize X) (linearize Y) x y))
  rw [tensor_act_pure, compareForward_pure, compareForward_pure, bisetPair_action]

private theorem tensorSpec {K H J : Type} [Group K] [Group H] [Group J] (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J)) :
    AlgebraBalanced X Y (pure X Y) ∧
    (∀ a b x y, pure X Y (leftAct X a x) (rightAct Y b y) =
      leftAct (tensor X Y) a (rightAct (tensor X Y) b (pure X Y x y))) ∧
    ∀ (V : Type u) [AddCommGroup V] [Module Complex V]
      (b : X.V →ₗ[Complex] Y.V →ₗ[Complex] V),
      AlgebraBalanced X Y b → ∃! f : (tensor X Y).V →ₗ[Complex] V,
        ∀ x y, f (pure X Y x y) = b x y := by
  refine ⟨(algebraBalanced_iff X Y _).mpr (pure_balanced X Y), exteriorAlgebra X Y, ?_⟩
  intro V _ _ b hb
  let h := (algebraBalanced_iff X Y b).mp hb
  exact ⟨lift X Y b h, lift_pure X Y b h,
    fun _ hf => pure_ext X Y (fun x y => (hf x y).trans (lift_pure X Y b h x y).symm)⟩

private theorem compareTensor_hom_pure (X : Biset K H) (Y : Biset H J)
    (x : (linearize.{u} X).V) (y : (linearize.{u} Y).V) :
    (compareTensor X Y).hom.hom (pure (linearize X) (linearize Y) x y) =
      bisetPair X Y x y :=
  compareForward_pure X Y x y

private theorem compareTensor_inv_pair (X : Biset K H) (Y : Biset H J)
    (x : (linearize.{u} X).V) (y : (linearize.{u} Y).V) :
    (compareTensor X Y).inv.hom (bisetPair X Y x y) =
      pure (linearize X) (linearize Y) x y :=
  compareBackward_pair X Y x y

private theorem hom_leftAct {X Y : Rep.{u} Complex (K × H)} (f : X ⟶ Y)
    (a : MonoidAlgebra Complex K) (x : X.V) :
    f.hom (leftAct X a x) = leftAct Y a (f.hom x) := by
  change f.hom (∑ k ∈ a.coeff.support, a.coeff k • X.ρ (k, 1) x) =
    ∑ k ∈ a.coeff.support, a.coeff k • Y.ρ (k, 1) (f.hom x)
  simp only [map_sum, map_smul, Rep.hom_comm_apply]

private theorem hom_rightAct {X Y : Rep.{u} Complex (K × H)} (f : X ⟶ Y)
    (a : MonoidAlgebra Complex H) (x : X.V) :
    f.hom (rightAct X a x) = rightAct Y a (f.hom x) := by
  change f.hom (∑ h ∈ a.coeff.support, a.coeff h • X.ρ (1, h⁻¹) x) =
    ∑ h ∈ a.coeff.support, a.coeff h • Y.ρ (1, h⁻¹) (f.hom x)
  simp only [map_sum, map_smul, Rep.hom_comm_apply]

#print axioms tensorSpec
#print axioms compareTensor
#print axioms compareTensor_hom_pure
#print axioms compareTensor_inv_pair
#print axioms hom_leftAct
#print axioms hom_rightAct

end
end ParabolicTensorSupport
