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

end
end ParabolicTensorSupport
