import Mathlib.RepresentationTheory.Coinvariants
import MackeyDiagrams
import Proofs.ModuleTensorUniversalProperty
import Proofs.MackeyDecompositionWithParabolicRepresentatives

set_option maxHeartbeats 2000000

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
-- coinvariants. The registered integer free-group quotient has an additive
-- universal property in a different presentation. The group equation below
-- is equivalent to balance over the entire complex group algebra.
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


private def equivariantHom {G : Type} [Group G] {X Y : Rep.{u} Complex G}
    (f : X.V →ₗ[Complex] Y.V) (hf : ∀ g x, f (X.ρ g x) = Y.ρ g (f x)) : X ⟶ Y :=
  Rep.ofHom ⟨f, fun g => LinearMap.ext (hf g)⟩

private theorem repHom_ext {G : Type} [Group G] {X Y : Rep.{u} Complex G}
    {f g : X ⟶ Y} (h : ∀ x, f.hom x = g.hom x) : f = g := by
  apply Rep.hom_ext
  ext x
  exact h x

private theorem pure_hom_ext (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
    {T : Rep.{u} Complex (K × J)} {f g : tensor X Y ⟶ T}
    (h : ∀ x y, f.hom (pure X Y x y) = g.hom (pure X Y x y)) : f = g := by
  apply repHom_ext
  exact LinearMap.congr_fun (pure_ext X Y h)

private def tensorMapLinear {X X' : Rep.{u} Complex (K × H)} {Y Y' : Rep.{u} Complex (H × J)}
    (f : X ⟶ X') (g : Y ⟶ Y') : Carrier X Y →ₗ[Complex] Carrier X' Y' :=
  lift X Y (((pure X' Y').comp f.hom.toLinearMap).compl₂ g.hom.toLinearMap) (by
    intro h x y
    change pure X' Y' (f.hom (X.ρ (1, h) x)) (g.hom (Y.ρ (h, 1) y)) = _
    rw [Rep.hom_comm_apply, Rep.hom_comm_apply]
    exact pure_balanced X' Y' h _ _)

@[simp] private theorem tensorMapLinear_pure {X X' : Rep.{u} Complex (K × H)}
    {Y Y' : Rep.{u} Complex (H × J)} (f : X ⟶ X') (g : Y ⟶ Y') (x : X.V) (y : Y.V) :
    tensorMapLinear f g (pure X Y x y) = pure X' Y' (f.hom x) (g.hom y) :=
  lift_pure _ _ _ _ _ _

private def tensorMap {X X' : Rep.{u} Complex (K × H)} {Y Y' : Rep.{u} Complex (H × J)}
    (f : X ⟶ X') (g : Y ⟶ Y') : tensor X Y ⟶ tensor X' Y' :=
  equivariantHom (tensorMapLinear f g) (by
    intro h
    apply LinearMap.congr_fun
      (f := (tensorMapLinear f g).comp ((tensor X Y).ρ h))
      (g := ((tensor X' Y').ρ h).comp (tensorMapLinear f g))
    apply pure_ext X Y
    intro x y
    change tensorMapLinear f g ((tensor X Y).ρ h (pure X Y x y)) =
      (tensor X' Y').ρ h (tensorMapLinear f g (pure X Y x y))
    rw [tensor_act_pure, tensorMapLinear_pure, tensorMapLinear_pure, tensor_act_pure,
      Rep.hom_comm_apply, Rep.hom_comm_apply])

@[simp] private theorem tensorMap_pure {X X' : Rep.{u} Complex (K × H)}
    {Y Y' : Rep.{u} Complex (H × J)} (f : X ⟶ X') (g : Y ⟶ Y') (x : X.V) (y : Y.V) :
    (tensorMap f g).hom (pure X Y x y) = pure X' Y' (f.hom x) (g.hom y) :=
  tensorMapLinear_pure f g x y

private def tensorIso {X X' : Rep.{u} Complex (K × H)} {Y Y' : Rep.{u} Complex (H × J)}
    (f : X ≅ X') (g : Y ≅ Y') : tensor X Y ≅ tensor X' Y' where
  hom := tensorMap f.hom g.hom
  inv := tensorMap f.inv g.inv
  hom_inv_id := by
    apply pure_hom_ext X Y
    intro x y
    change (tensorMap f.inv g.inv).hom ((tensorMap f.hom g.hom).hom (pure X Y x y)) = pure X Y x y
    rw [tensorMap_pure, tensorMap_pure, Rep.inv_hom_apply, Rep.inv_hom_apply]
  inv_hom_id := by
    apply pure_hom_ext X' Y'
    intro x y
    change (tensorMap f.hom g.hom).hom ((tensorMap f.inv g.inv).hom (pure X' Y' x y)) = pure X' Y' x y
    rw [tensorMap_pure, tensorMap_pure, Rep.hom_inv_apply, Rep.hom_inv_apply]

variable {V₁ V₂ V₃ V₄ V₅ : Type u}
variable [AddCommGroup V₁] [Module Complex V₁] [AddCommGroup V₂] [Module Complex V₂]
variable [AddCommGroup V₃] [Module Complex V₃] [AddCommGroup V₄] [Module Complex V₄]
variable [AddCommGroup V₅] [Module Complex V₅]

private def nestedBilinear (outer : V₁ →ₗ[Complex] V₄ →ₗ[Complex] V₅)
    (inner : V₂ →ₗ[Complex] V₃ →ₗ[Complex] V₄) :
    V₁ →ₗ[Complex] V₂ →ₗ[Complex] V₃ →ₗ[Complex] V₅ where
  toFun x := inner.compr₂ (outer x)
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

variable (X : Rep.{u} Complex (K × H)) (Y : Rep.{u} Complex (H × J))
variable (Z : Rep.{u} Complex (J × F))

-- Alphabeta Math bicategory coherence, step 1.1. Descend the two
-- trilinear maps, verifying balance in both middle groups. The action
-- convention on the right factor uses the inverse when moving a group
-- element across the tensor and the diagonal action for coinvariants.
private def assocForwardInner :
    Carrier X Y →ₗ[Complex] Z.V →ₗ[Complex] Carrier X (tensor Y Z) :=
  lift X Y (nestedBilinear (pure X (tensor Y Z)) (pure Y Z)) (by
    intro h x y
    ext z
    change pure X (tensor Y Z) (X.ρ (1, h) x) (pure Y Z (Y.ρ (h, 1) y) z) = _
    rw [← show (tensor Y Z).ρ (h, 1) (pure Y Z y z) = pure Y Z (Y.ρ (h, 1) y) z from by
      simp only [tensor_act_pure, prodOne] <;> rfl]
    exact pure_balanced X (tensor Y Z) h x _)

@[simp] private theorem assocForwardInner_pure (x : X.V) (y : Y.V) (z : Z.V) :
    assocForwardInner X Y Z (pure X Y x y) z = pure X (tensor Y Z) x (pure Y Z y z) := by
  unfold assocForwardInner
  rw [lift_pure]
  rfl

private def assocForward : Carrier (tensor X Y) Z →ₗ[Complex] Carrier X (tensor Y Z) :=
  lift (tensor X Y) Z (assocForwardInner X Y Z) (by
    intro h p z
    apply LinearMap.congr_fun
      (f := ((assocForwardInner X Y Z).flip (Z.ρ (h, 1) z)).comp ((tensor X Y).ρ (1, h)))
      (g := (assocForwardInner X Y Z).flip z)
    apply pure_ext X Y
    intro x y
    change assocForwardInner X Y Z ((tensor X Y).ρ (1, h) (pure X Y x y)) (Z.ρ (h, 1) z) =
      assocForwardInner X Y Z (pure X Y x y) z
    simp only [tensor_act_pure, prodOne, assocForwardInner_pure,
      pure_balanced Y Z h y z] <;> rfl)

@[simp] private theorem assocForward_pure (x : X.V) (y : Y.V) (z : Z.V) :
    assocForward X Y Z (pure (tensor X Y) Z (pure X Y x y) z) =
      pure X (tensor Y Z) x (pure Y Z y z) := by
  unfold assocForward
  erw [lift_pure]

private def assocBackwardInner :
    Carrier Y Z →ₗ[Complex] X.V →ₗ[Complex] Carrier (tensor X Y) Z :=
  lift Y Z ((LinearMap.lflip (R₀ := Complex)).toLinearMap.comp
    (nestedBilinear (pure (tensor X Y) Z).flip (pure X Y))).flip (by
    intro h y z
    ext x
    change pure (tensor X Y) Z (pure X Y x (Y.ρ (1, h) y)) (Z.ρ (h, 1) z) = _
    rw [← show (tensor X Y).ρ (1, h) (pure X Y x y) = pure X Y x (Y.ρ (1, h) y) from by
      simp only [tensor_act_pure, prodOne] <;> rfl]
    exact pure_balanced (tensor X Y) Z h _ z)

@[simp] private theorem assocBackwardInner_pure (x : X.V) (y : Y.V) (z : Z.V) :
    assocBackwardInner X Y Z (pure Y Z y z) x = pure (tensor X Y) Z (pure X Y x y) z := by
  unfold assocBackwardInner
  rw [lift_pure]
  rfl

private def assocBackward : Carrier X (tensor Y Z) →ₗ[Complex] Carrier (tensor X Y) Z :=
  lift X (tensor Y Z) (assocBackwardInner X Y Z).flip (by
    intro h x p
    apply LinearMap.congr_fun
      (f := ((assocBackwardInner X Y Z).flip (X.ρ (1, h) x)).comp ((tensor Y Z).ρ (h, 1)))
      (g := (assocBackwardInner X Y Z).flip x)
    apply pure_ext Y Z
    intro y z
    change assocBackwardInner X Y Z ((tensor Y Z).ρ (h, 1) (pure Y Z y z)) (X.ρ (1, h) x) =
      assocBackwardInner X Y Z (pure Y Z y z) x
    simp only [tensor_act_pure, prodOne, assocBackwardInner_pure,
      pure_balanced X Y h x y] <;> rfl)

@[simp] private theorem assocBackward_pure (x : X.V) (y : Y.V) (z : Z.V) :
    assocBackward X Y Z (pure X (tensor Y Z) x (pure Y Z y z)) =
      pure (tensor X Y) Z (pure X Y x y) z := by
  unfold assocBackward
  erw [lift_pure]


private theorem leftTriple_ext {W : Type*} [AddCommGroup W] [Module Complex W]
    {f g : Carrier (tensor X Y) Z →ₗ[Complex] W}
    (h : ∀ x y z, f (pure (tensor X Y) Z (pure X Y x y) z) =
      g (pure (tensor X Y) Z (pure X Y x y) z)) : f = g := by
  apply pure_ext (tensor X Y) Z
  intro p z
  exact LinearMap.congr_fun (pure_ext X Y (f := f.comp ((pure (tensor X Y) Z).flip z))
    (g := g.comp ((pure (tensor X Y) Z).flip z)) fun x y => h x y z) p

private theorem rightTriple_ext {W : Type*} [AddCommGroup W] [Module Complex W]
    {f g : Carrier X (tensor Y Z) →ₗ[Complex] W}
    (h : ∀ x y z, f (pure X (tensor Y Z) x (pure Y Z y z)) =
      g (pure X (tensor Y Z) x (pure Y Z y z))) : f = g := by
  apply pure_ext X (tensor Y Z)
  intro x p
  exact LinearMap.congr_fun (pure_ext Y Z (f := f.comp (pure X (tensor Y Z) x))
    (g := g.comp (pure X (tensor Y Z) x)) fun y z => h x y z) p

private def associator : tensor (tensor X Y) Z ≅ tensor X (tensor Y Z) where
  hom := equivariantHom (assocForward X Y Z) (by
    intro g
    apply LinearMap.congr_fun
      (f := (assocForward X Y Z).comp ((tensor (tensor X Y) Z).ρ g))
      (g := ((tensor X (tensor Y Z)).ρ g).comp (assocForward X Y Z))
    apply leftTriple_ext X Y Z
    intro x y z
    change assocForward X Y Z ((tensor (tensor X Y) Z).ρ g (pure (tensor X Y) Z (pure X Y x y) z)) =
      (tensor X (tensor Y Z)).ρ g (assocForward X Y Z (pure (tensor X Y) Z (pure X Y x y) z))
    simp only [tensor_act_pure, prodOne, assocForward_pure] <;> rfl)
  inv := equivariantHom (assocBackward X Y Z) (by
    intro g
    apply LinearMap.congr_fun
      (f := (assocBackward X Y Z).comp ((tensor X (tensor Y Z)).ρ g))
      (g := ((tensor (tensor X Y) Z).ρ g).comp (assocBackward X Y Z))
    apply rightTriple_ext X Y Z
    intro x y z
    change assocBackward X Y Z ((tensor X (tensor Y Z)).ρ g (pure X (tensor Y Z) x (pure Y Z y z))) =
      (tensor (tensor X Y) Z).ρ g (assocBackward X Y Z (pure X (tensor Y Z) x (pure Y Z y z)))
    simp only [tensor_act_pure, prodOne, assocBackward_pure] <;> rfl)
  hom_inv_id := by
    apply repHom_ext
    apply LinearMap.congr_fun
      (f := (assocBackward X Y Z).comp (assocForward X Y Z)) (g := LinearMap.id)
    apply leftTriple_ext X Y Z
    intro x y z
    change assocBackward X Y Z (assocForward X Y Z (pure (tensor X Y) Z (pure X Y x y) z)) = _
    rw [assocForward_pure, assocBackward_pure]
    rfl
  inv_hom_id := by
    apply repHom_ext
    apply LinearMap.congr_fun
      (f := (assocForward X Y Z).comp (assocBackward X Y Z)) (g := LinearMap.id)
    apply rightTriple_ext X Y Z
    intro x y z
    change assocForward X Y Z (assocBackward X Y Z (pure X (tensor Y Z) x (pure Y Z y z))) = _
    rw [assocBackward_pure, assocForward_pure]
    rfl

private theorem associator_pure (x : X.V) (y : Y.V) (z : Z.V) :
    (associator X Y Z).hom.hom (pure (tensor X Y) Z (pure X Y x y) z) =
      pure X (tensor Y Z) x (pure Y Z y z) :=
  assocForward_pure X Y Z x y z


open MackeyDiagrams

private abbrev linearize (X : Biset K H) : Rep.{u} Complex (K × H) :=
  letI : MulAction (K × H) (ULift.{u} X.carrier) :=
    { smul := fun g x => ⟨X.act g x.down⟩
      one_smul := fun x => congrArg ULift.up (X.one_act x.down)
      mul_smul := fun g h x => congrArg ULift.up (X.mul_act g h x.down) }
  Rep.ofMulAction Complex (K × H) (ULift.{u} X.carrier)

private abbrev sumBasis {ι : Type} (X : ι → Biset K H) : Biset K H where
  carrier := Sigma (fun i => (X i).carrier)
  act g x := ⟨x.1, (X x.1).act g x.2⟩
  one_act x := Sigma.ext rfl (heq_of_eq ((X x.1).one_act x.2))
  mul_act g h x := Sigma.ext rfl (heq_of_eq ((X x.1).mul_act g h x.2))

private abbrev sumTensorBasis {ι κ : Type} (X : ι → Biset K H) (Y : κ → Biset H J) :=
  sumBasis (fun ij : ι × κ => (X ij.1).tensor (Y ij.2))

private def distributeBasis {ι κ : Type} (X : ι → Biset K H) (Y : κ → Biset H J) :
    ((sumBasis X).tensor (sumBasis Y)).carrier ≃ (sumTensorBasis X Y).carrier where
  toFun := Quotient.lift
    (fun z => ⟨(z.1.1, z.2.1), (X z.1.1).pair (Y z.2.1) z.1.2 z.2.2⟩)
    (by
      rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩ ⟨⟨i', x'⟩, ⟨j', y'⟩⟩ ⟨h, hx, hy⟩
      change (⟨i, (X i).act (1, h) x⟩ : Sigma fun i => (X i).carrier) = ⟨i', x'⟩ at hx
      change (⟨j, (Y j).act (h, 1) y⟩ : Sigma fun j => (Y j).carrier) = ⟨j', y'⟩ at hy
      cases hx
      cases hy
      change (⟨(i, j), (X i).pair (Y j) x y⟩ : (sumTensorBasis X Y).carrier) =
        ⟨(i, j), (X i).pair (Y j) ((X i).act (1, h) x) ((Y j).act (h, 1) y)⟩
      exact congrArg (Sigma.mk (i, j)) (Quotient.sound ⟨h, rfl, rfl⟩))
  invFun := fun ⟨(i, j), z⟩ =>
    Quotient.lift (fun p => (sumBasis X).pair (sumBasis Y) ⟨i, p.1⟩ ⟨j, p.2⟩)
      (by
        rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨h, hx, hy⟩
        exact Quotient.sound ⟨h, by exact congrArg (Sigma.mk i) hx,
          by exact congrArg (Sigma.mk j) hy⟩) z
  left_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨i, j⟩, z⟩
    refine Quotient.inductionOn z ?_
    rintro ⟨x, y⟩
    rfl

private theorem distributeBasis_action {ι κ : Type} (X : ι → Biset K H) (Y : κ → Biset H J)
    (g : K × J) (z : ((sumBasis X).tensor (sumBasis Y)).carrier) :
    distributeBasis X Y (((sumBasis X).tensor (sumBasis Y)).act g z) =
      (sumTensorBasis X Y).act g (distributeBasis X Y z) := by
  refine Quotient.inductionOn z ?_
  rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩
  rfl

private theorem distribute {ι κ : Type} (X : ι → Biset K H) (Y : κ → Biset H J) :
    let source := Biset.tensor (sumBasis X) (sumBasis Y)
    let target := sumTensorBasis X Y
    ∃ e : (source.carrier →₀ Complex) ≃ₗ[Complex] (target.carrier →₀ Complex),
      (∀ g x, e (source.actLinear Complex g x) = target.actLinear Complex g (e x)) ∧
      ∀ (i : ι) (j : κ) (x : (X i).carrier) (y : (Y j).carrier),
        e (Biset.pairLinear Complex (sumBasis X) (sumBasis Y)
          (Finsupp.single ⟨i, x⟩ 1) (Finsupp.single ⟨j, y⟩ 1)) =
          Finsupp.single ⟨(i, j), (X i).pair (Y j) x y⟩ 1 := by
  intro source target
  let e := Finsupp.domLCongr (R := Complex) (M := Complex) (distributeBasis X Y)
  refine ⟨e, ?_, ?_⟩
  · intro g
    apply LinearMap.congr_fun
      (f := e.toLinearMap.comp (source.actLinear Complex g))
      (g := (target.actLinear Complex g).comp e.toLinearMap)
    apply Finsupp.lhom_ext
    intro x c
    change e (source.actLinear Complex g (Finsupp.single x c)) =
      target.actLinear Complex g (e (Finsupp.single x c))
    dsimp only [source, target, e]
    rw [Biset.actLinear_single, Finsupp.domLCongr_single, Finsupp.domLCongr_single,
      Biset.actLinear_single, distributeBasis_action]
  · intro i j x y
    change e (Biset.pairLinear Complex (sumBasis X) (sumBasis Y)
      (Finsupp.single ⟨i, x⟩ 1) (Finsupp.single ⟨j, y⟩ 1)) = _
    rw [Biset.pairLinear_single, one_mul]
    dsimp only [e]
    rw [Finsupp.domLCongr_single]
    rfl

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

private def liftBisetEquiv {X Y : Biset K H}
    (e : (X.carrier →₀ Complex) ≃ₗ[Complex] (Y.carrier →₀ Complex))
    (he : ∀ g x, e (X.actLinear Complex g x) = Y.actLinear Complex g (e x)) :
    linearize.{u} X ≅ linearize.{u} Y :=
  equivariantIso ((basisCoords X).symm.trans (e.trans (basisCoords Y))) (by
    intro g x
    obtain ⟨v, rfl⟩ := (basisCoords X).surjective x
    change basisCoords Y (e ((basisCoords X).symm ((linearize X).ρ g (basisCoords X v)))) =
      (linearize Y).ρ g (basisCoords Y (e ((basisCoords X).symm (basisCoords X v))))
    rw [← basisCoords_action X g v, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      he, basisCoords_action])

private def liftBasisEquiv {X Y : Biset K H} (e : X.carrier ≃ Y.carrier)
    (h : ∀ g x, e (X.act g x) = Y.act g (e x)) : linearize.{u} X ≅ linearize.{u} Y :=
  liftBisetEquiv (Finsupp.domLCongr e) (by
    intro g
    apply LinearMap.congr_fun
      (f := (Finsupp.domLCongr (R := Complex) (M := Complex) e).toLinearMap.comp (X.actLinear Complex g))
      (g := (Y.actLinear Complex g).comp (Finsupp.domLCongr e).toLinearMap)
    apply Finsupp.lhom_ext
    intro x c
    change Finsupp.domLCongr (R := Complex) (M := Complex) e (X.actLinear Complex g (Finsupp.single x c)) =
      Y.actLinear Complex g (Finsupp.domLCongr e (Finsupp.single x c))
    simp only [Biset.actLinear_single, Finsupp.domLCongr_single, h])


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

private abbrev Reg (H : Type) [Group H] := linearize.{u} (Biset.regular H)

private theorem monoExt {G : Type*} {W : Type*} [AddCommGroup W] [Module Complex W]
    {l m : MonoidAlgebra Complex G →ₗ[Complex] W}
    (h : ∀ g c, l (MonoidAlgebra.single g c) = m (MonoidAlgebra.single g c)) : l = m := by
  apply LinearMap.ext
  intro a
  have he : l.comp (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap =
      m.comp (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    exact h
  exact LinearMap.congr_fun he a.coeff

private def leftUnitorPair (X : Rep.{u} Complex (K × H)) :
    (Reg.{u} K).V →ₗ[Complex] X.V →ₗ[Complex] X.V :=
  (freeLift Complex (fun a : ULift.{u} K => X.ρ (a.down, 1))).comp
    (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap

private def rightUnitorPair (X : Rep.{u} Complex (K × H)) :
    X.V →ₗ[Complex] (Reg.{u} H).V →ₗ[Complex] X.V :=
  ((freeLift Complex (fun a : ULift.{u} H => X.ρ (1, a.down⁻¹))).comp
    (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap).flip

private theorem leftUnitorPair_single (X : Rep.{u} Complex (K × H)) (k : K) (c : Complex) (x : X.V) :
    leftUnitorPair X (MonoidAlgebra.single (ULift.up k) c) x = c • X.ρ (k, 1) x := by
  change freeLift Complex (fun a : ULift.{u} K => X.ρ (a.down, 1)) (Finsupp.single (ULift.up k) c) x = _
  rw [freeLift_single]
  rfl

private theorem rightUnitorPair_single (X : Rep.{u} Complex (K × H)) (h : H) (c : Complex) (x : X.V) :
    rightUnitorPair X x (MonoidAlgebra.single (ULift.up h) c) = c • X.ρ (1, h⁻¹) x := by
  change freeLift Complex (fun a : ULift.{u} H => X.ρ (1, a.down⁻¹)) (Finsupp.single (ULift.up h) c) x = _
  rw [freeLift_single]
  rfl

private theorem leftUnitorPair_balanced (X : Rep.{u} Complex (K × H)) :
    GroupBalanced (Reg.{u} K) X (leftUnitorPair X) := by
  intro k a x
  apply LinearMap.congr_fun
    (f := ((leftUnitorPair X).flip (X.ρ (k, 1) x)).comp ((Reg.{u} K).ρ (1, k)))
    (g := (leftUnitorPair X).flip x)
  apply monoExt
  rintro ⟨g⟩ c
  change leftUnitorPair X ((Reg.{u} K).ρ (1, k) (MonoidAlgebra.single (ULift.up g) c))
    (X.ρ (k, 1) x) = leftUnitorPair X (MonoidAlgebra.single (ULift.up g) c) x
  have he := linearize_single.{u} (Biset.regular K) (1, k) g c
  change (Reg.{u} K).ρ (1, k) (MonoidAlgebra.single (ULift.up g) c) =
    MonoidAlgebra.single (ULift.up (1 * g * k⁻¹)) c at he
  rw [he, leftUnitorPair_single, leftUnitorPair_single, ← prodRep_mul_apply]
  simp

private theorem rightUnitorPair_balanced (X : Rep.{u} Complex (K × H)) :
    GroupBalanced X (Reg.{u} H) (rightUnitorPair X) := by
  intro h x a
  apply LinearMap.congr_fun
    (f := (rightUnitorPair X (X.ρ (1, h) x)).comp ((Reg.{u} H).ρ (h, 1)))
    (g := rightUnitorPair X x)
  apply monoExt
  rintro ⟨g⟩ c
  change rightUnitorPair X (X.ρ (1, h) x)
    ((Reg.{u} H).ρ (h, 1) (MonoidAlgebra.single (ULift.up g) c)) =
      rightUnitorPair X x (MonoidAlgebra.single (ULift.up g) c)
  have he := linearize_single.{u} (Biset.regular H) (h, 1) g c
  change (Reg.{u} H).ρ (h, 1) (MonoidAlgebra.single (ULift.up g) c) =
    MonoidAlgebra.single (ULift.up (h * g * 1⁻¹)) c at he
  rw [he, rightUnitorPair_single, rightUnitorPair_single, ← prodRep_mul_apply]
  simp [mul_assoc]

private abbrev lunitLinear (X : Rep.{u} Complex (K × H)) :=
  lift (Reg.{u} K) X (leftUnitorPair X) (leftUnitorPair_balanced X)

private abbrev runitLinear (X : Rep.{u} Complex (K × H)) :=
  lift X (Reg.{u} H) (rightUnitorPair X) (rightUnitorPair_balanced X)

private abbrev idBasis (G : Type) [One G] : MonoidAlgebra Complex (ULift.{u} G) :=
  MonoidAlgebra.single (ULift.up 1) 1

private def lunitInsert (X : Rep.{u} Complex (K × H)) : X.V →ₗ[Complex] Carrier (Reg.{u} K) X :=
  pure (Reg.{u} K) X (idBasis K)

private def runitInsert (X : Rep.{u} Complex (K × H)) : X.V →ₗ[Complex] Carrier X (Reg.{u} H) :=
  (pure X (Reg.{u} H)).flip (idBasis H)

-- Alphabeta Math bicategory coherence, step 1.2. The regular bimodule
-- unitors are the extended actions. The inverse inserts the identity
-- basis vector. The two inverse laws use balance on the pure tensors.
private def lunitEquiv (X : Rep.{u} Complex (K × H)) : Carrier (Reg.{u} K) X ≃ₗ[Complex] X.V := by
  have h₁ : (lunitLinear X).comp (lunitInsert X) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change lunitLinear X (pure (Reg.{u} K) X (idBasis K) x) = x
    rw [lift_pure, leftUnitorPair_single, one_smul, prodOne]
  have h₂ : (lunitInsert X).comp (lunitLinear X) = LinearMap.id := by
    apply pure_ext (Reg.{u} K) X
    intro a x
    apply LinearMap.congr_fun
      (f := (lunitInsert X).comp ((leftUnitorPair X).flip x))
      (g := (pure (Reg.{u} K) X).flip x)
    · apply monoExt
      rintro ⟨k⟩ c
      change lunitInsert X (leftUnitorPair X (MonoidAlgebra.single (ULift.up k) c) x) =
        pure (Reg.{u} K) X (MonoidAlgebra.single (ULift.up k) c) x
      rw [leftUnitorPair_single, map_smul]
      change c • pure (Reg.{u} K) X (idBasis K) (X.ρ (k, 1) x) = _
      rw [← groupSingle _ _ (pure_balanced (Reg.{u} K) X) k]
      have he := linearize_single.{u} (Biset.regular K) (1, k⁻¹) (1 : K) 1
      change (Reg.{u} K).ρ (1, k⁻¹) (idBasis K) = MonoidAlgebra.single (ULift.up (1 * 1 * (k⁻¹)⁻¹)) 1 at he
      rw [he]
      simp only [one_mul, inv_inv]
      change c • (pure (Reg.{u} K) X).flip x (MonoidAlgebra.single (ULift.up k) 1) = _
      rw [← map_smul]
      have hc : c • MonoidAlgebra.single (ULift.up k) 1 = MonoidAlgebra.single (ULift.up k) c := by simp
      rw [hc]
      rfl
  exact LinearEquiv.ofLinearMap (lunitLinear X) (lunitInsert X) h₁ h₂

private def runitEquiv (X : Rep.{u} Complex (K × H)) : Carrier X (Reg.{u} H) ≃ₗ[Complex] X.V := by
  have h₁ : (runitLinear X).comp (runitInsert X) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change runitLinear X (pure X (Reg.{u} H) x (idBasis H)) = x
    rw [lift_pure, rightUnitorPair_single, one_smul, inv_one, prodOne]
  have h₂ : (runitInsert X).comp (runitLinear X) = LinearMap.id := by
    apply pure_ext X (Reg.{u} H)
    intro x a
    apply LinearMap.congr_fun
      (f := (runitInsert X).comp (rightUnitorPair X x))
      (g := pure X (Reg.{u} H) x)
    · apply monoExt
      rintro ⟨h⟩ c
      change runitInsert X (rightUnitorPair X x (MonoidAlgebra.single (ULift.up h) c)) =
        pure X (Reg.{u} H) x (MonoidAlgebra.single (ULift.up h) c)
      rw [rightUnitorPair_single, map_smul]
      change c • pure X (Reg.{u} H) (X.ρ (1, h⁻¹) x) (idBasis H) = _
      rw [groupSingle _ _ (pure_balanced X (Reg.{u} H)) h]
      have he := linearize_single.{u} (Biset.regular H) (h, 1) (1 : H) 1
      change (Reg.{u} H).ρ (h, 1) (idBasis H) = MonoidAlgebra.single (ULift.up (h * 1 * 1⁻¹)) 1 at he
      rw [he]
      simp only [inv_one, mul_one]
      rw [← map_smul]
      congr 1
      change c • MonoidAlgebra.single (ULift.up h) 1 = MonoidAlgebra.single (ULift.up h) c
      simp
  exact LinearEquiv.ofLinearMap (runitLinear X) (runitInsert X) h₁ h₂

private theorem lunitEquiv_pure (X : Rep.{u} Complex (K × H)) (a : (Reg.{u} K).V) (x : X.V) :
    lunitEquiv X (pure (Reg.{u} K) X a x) = leftUnitorPair X a x :=
  lift_pure (Reg K) X (leftUnitorPair X) (leftUnitorPair_balanced X) a x

private theorem runitEquiv_pure (X : Rep.{u} Complex (K × H)) (a : (Reg.{u} H).V) (x : X.V) :
    runitEquiv X (pure X (Reg.{u} H) x a) = rightUnitorPair X x a :=
  lift_pure X (Reg H) (rightUnitorPair X) (rightUnitorPair_balanced X) x a

private def lunit (X : Rep.{u} Complex (K × H)) : tensor (Reg.{u} K) X ≅ X :=
  equivariantIso (lunitEquiv X) (by
    intro g
    apply LinearMap.congr_fun
      (f := (lunitEquiv X).toLinearMap.comp ((tensor (Reg.{u} K) X).ρ g))
      (g := (X.ρ g).comp (lunitEquiv X).toLinearMap)
    apply pure_ext (Reg.{u} K) X
    intro a x
    change lunitEquiv X ((tensor (Reg.{u} K) X).ρ g (pure (Reg.{u} K) X a x)) =
      X.ρ g (lunitEquiv X (pure (Reg.{u} K) X a x))
    rw [tensor_act_pure, lunitEquiv_pure, lunitEquiv_pure]
    apply LinearMap.congr_fun
      (f := ((leftUnitorPair X).flip (X.ρ (1, g.2) x)).comp ((Reg.{u} K).ρ (g.1, 1)))
      (g := (X.ρ g).comp ((leftUnitorPair X).flip x))
    apply monoExt
    rintro ⟨k⟩ c
    change leftUnitorPair X ((Reg.{u} K).ρ (g.1, 1) (MonoidAlgebra.single (ULift.up k) c))
      (X.ρ (1, g.2) x) = X.ρ g (leftUnitorPair X (MonoidAlgebra.single (ULift.up k) c) x)
    have he := linearize_single.{u} (Biset.regular K) (g.1, 1) k c
    change (Reg.{u} K).ρ (g.1, 1) (MonoidAlgebra.single (ULift.up k) c) =
      MonoidAlgebra.single (ULift.up (g.1 * k * 1⁻¹)) c at he
    rw [he, leftUnitorPair_single, leftUnitorPair_single, map_smul, ← prodRep_mul_apply,
      ← prodRep_mul_apply]
    rcases g with ⟨g, h⟩
    simp)

private def runit (X : Rep.{u} Complex (K × H)) : tensor X (Reg.{u} H) ≅ X :=
  equivariantIso (runitEquiv X) (by
    intro g
    apply LinearMap.congr_fun
      (f := (runitEquiv X).toLinearMap.comp ((tensor X (Reg.{u} H)).ρ g))
      (g := (X.ρ g).comp (runitEquiv X).toLinearMap)
    apply pure_ext X (Reg.{u} H)
    intro x a
    change runitEquiv X ((tensor X (Reg.{u} H)).ρ g (pure X (Reg.{u} H) x a)) =
      X.ρ g (runitEquiv X (pure X (Reg.{u} H) x a))
    rw [tensor_act_pure, runitEquiv_pure, runitEquiv_pure]
    apply LinearMap.congr_fun
      (f := (rightUnitorPair X (X.ρ (g.1, 1) x)).comp ((Reg.{u} H).ρ (1, g.2)))
      (g := (X.ρ g).comp (rightUnitorPair X x))
    apply monoExt
    rintro ⟨h⟩ c
    change rightUnitorPair X (X.ρ (g.1, 1) x)
      ((Reg.{u} H).ρ (1, g.2) (MonoidAlgebra.single (ULift.up h) c)) =
        X.ρ g (rightUnitorPair X x (MonoidAlgebra.single (ULift.up h) c))
    have he := linearize_single.{u} (Biset.regular H) (1, g.2) h c
    change (Reg.{u} H).ρ (1, g.2) (MonoidAlgebra.single (ULift.up h) c) =
      MonoidAlgebra.single (ULift.up (1 * h * g.2⁻¹)) c at he
    rw [he, rightUnitorPair_single, rightUnitorPair_single, map_smul, ← prodRep_mul_apply,
      ← prodRep_mul_apply]
    rcases g with ⟨g, h'⟩
    simp)

private theorem lunit_pure (X : Rep.{u} Complex (K × H)) (a : (Reg.{u} K).V) (x : X.V) :
    (lunit X).hom.hom (pure (Reg.{u} K) X a x) = leftUnitorPair X a x :=
  lunitEquiv_pure X a x

private theorem runit_pure (X : Rep.{u} Complex (K × H)) (a : (Reg.{u} H).V) (x : X.V) :
    (runit X).hom.hom (pure X (Reg.{u} H) x a) = rightUnitorPair X x a :=
  runitEquiv_pure X a x

private theorem regCoords_mapDomain {G : Type} [Group G] (a : MonoidAlgebra Complex G) :
    MonoidAlgebra.mapDomain ULift.up a = basisCoords.{u} (Biset.regular G) a.coeff := by
  apply MonoidAlgebra.coeff_injective
  simp only [basisCoords, LinearEquiv.trans_apply, MonoidAlgebra.coeff_mapDomain,
    MonoidAlgebra.coeffLinearEquiv_symm_apply, Finsupp.domLCongr_apply]
  ext z
  exact Finsupp.mapDomain_equiv_apply (f := Equiv.ulift.symm) a.coeff z

private theorem leftUnitorPair_algebra (X : Rep.{u} Complex (K × H)) (a : MonoidAlgebra Complex K) (x : X.V) :
    leftUnitorPair X (MonoidAlgebra.mapDomain ULift.up a) x = leftAct X a x := by
  rw [regCoords_mapDomain]
  change (leftUnitorPair X).flip x (basisCoords (Biset.regular K) a.coeff) =
    ∑ k ∈ a.coeff.support, a.coeff k • X.ρ (k, 1) x
  conv_lhs => rw [← Finsupp.sum_single a.coeff]
  simp only [Finsupp.sum, map_sum, LinearMap.flip_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [basisCoords_single, leftUnitorPair_single]

private theorem rightUnitorPair_algebra (X : Rep.{u} Complex (K × H)) (a : MonoidAlgebra Complex H) (x : X.V) :
    rightUnitorPair X x (MonoidAlgebra.mapDomain ULift.up a) = rightAct X a x := by
  rw [regCoords_mapDomain]
  change rightUnitorPair X x (basisCoords (Biset.regular H) a.coeff) =
    ∑ h ∈ a.coeff.support, a.coeff h • X.ρ (1, h⁻¹) x
  conv_lhs => rw [← Finsupp.sum_single a.coeff]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [basisCoords_single, rightUnitorPair_single]
end
end ParabolicTensorSupport
