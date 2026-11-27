import Mathlib.Algebra.Category.ModuleCat.Ulift
import MackeyDiagrams
import Proofs.Bimodule

set_option maxHeartbeats 2000000
namespace NaturalTransformationsOfTensorFunctorsProof

universe u v w x
variable {A : Type u} {B : Type v} [Ring A] [Ring B]

private abbrev Bimod (A : Type u) (B : Type v) [Ring A] [Ring B] :=
  Sigma (fun M : ModuleCat.{w} B =>
    { D : Bimodule.1 B A M // D.1 = (inferInstance : Module B M) })

private abbrev AMod (A : Type u) [Ring A] := ModuleCat.{max u x} A
private abbrev BMod (A : Type u) (B : Type v) [Ring B] := ModuleCat.{max u w x} B

private abbrev regular (A : Type u) [Ring A] : AMod.{u,x} A :=
  ModuleCat.of A (ULift.{x} A)

private def right (M : Bimod.{u,v,w} A B) (m : M.1) (a : A) : M.1 :=
  letI : Module (MulOpposite A) M.1 := M.2.1.2.1
  MulOpposite.op a • m

private def Balanced (M : Bimod.{u,v,w} A B) (X : AMod.{u,x} A)
    (Y : BMod.{u,v,w,x} A B) (p : ↥M.1 → X → Y) : Prop :=
  (∀ m n : ↥M.1, ∀ a : X, p (m + n) a = p m a + p n a) ∧
  (∀ m : ↥M.1, ∀ a b : X, p m (a + b) = p m a + p m b) ∧
  (∀ b : B, ∀ m : ↥M.1, ∀ a : X, p (b • m) a = b • p m a) ∧
  (∀ a : A, ∀ m : ↥M.1, ∀ y : X, p (right M m a) y = p m (a • y))

private abbrev TensorFunctor (M : Bimod.{u,v,w} A B) :=
  { D : Sigma (fun F : CategoryTheory.Functor (AMod.{u,x} A) (BMod.{u,v,w,x} A B) =>
      ∀ X : AMod.{u,x} A, ↥M.1 → X → F.obj X) //
    (∀ X : AMod.{u,x} A, Balanced M X (D.1.obj X) (D.2 X)) ∧
    (∀ (X : AMod.{u,x} A) (Y : BMod.{u,v,w,x} A B) (p : ↥M.1 → X → Y),
      Balanced M X Y p →
      ∃! k : (D.1.obj X) →ₗ[B] Y,
        ∀ (m : ↥M.1) (y : X), k (D.2 X m y) = p m y) ∧
    (∀ (X Y : AMod.{u,x} A) (h : ModuleCat.Hom X Y) (m : ↥M.1) (y : X),
      (ModuleCat.Hom.hom (D.1.map h)) (D.2 X m y) = D.2 Y m ((ModuleCat.Hom.hom h) y)) }

variable {M N P : Bimod.{u,v,w} A B}
variable {T : TensorFunctor.{u,v,w,x} M} {S : TensorFunctor.{u,v,w,x} N}
variable {U : TensorFunctor.{u,v,w,x} P}

private abbrev NatCode (M N : Bimod.{u,v,w} A B) :=
  {f : M.1 →ₗ[B] N.1 // ∀ (m : ↥M.1) (a : A), f (right M m a) = right N (f m) a}

private abbrev Component (T : TensorFunctor.{u,v,w,x} M)
    (S : TensorFunctor.{u,v,w,x} N) (X : AMod.{u,x} A) :=
  T.1.1.obj X →ₗ[B] S.1.1.obj X

private abbrev NatGraph (T : TensorFunctor.{u,v,w,x} M) (S : TensorFunctor.{u,v,w,x} N) :=
  { G : ∀ X : AMod.{u,x} A, Component T S X → Prop //
    (∀ X : AMod.{u,x} A, ∃! k : Component T S X, G X k) ∧
    (∀ (X Y : AMod.{u,x} A) (h : ModuleCat.Hom X Y)
        (k : Component T S X) (l : Component T S Y),
      G X k → G Y l →
      (ModuleCat.Hom.hom (S.1.1.map h)).comp k =
        l.comp (ModuleCat.Hom.hom (T.1.1.map h))) }

private abbrev Unitor (T : TensorFunctor.{u,v,w,x} M) :=
  T.1.1.obj (regular.{u,x} A) ≃ₗ[B] M.1

private def IsUnitor (rho : Unitor T) : Prop :=
  (∀ (m : ↥M.1) (a : A), rho (T.1.2 (regular A) m (ULift.up a)) = right M m a) ∧
  (∀ m : ↥M.1, rho.symm m = T.1.2 (regular A) m (ULift.up (1 : A)))

private def eval (rho : Unitor T) (sigma : Unitor S) (k : Component T S (regular A)) :
    M.1 →ₗ[B] N.1 :=
  sigma.toLinearMap.comp (k.comp rho.symm.toLinearMap)

private def Pure (f : NatCode M N) (X : AMod.{u,x} A) (k : Component T S X) : Prop :=
  ∀ (m : ↥M.1) (y : X), k (T.1.2 X m y) = S.1.2 X (f.1 m) y

private def Represents (rho : Unitor T) (sigma : Unitor S) (eta : NatGraph T S)
    (f : NatCode M N) : Prop :=
  (∀ k : Component T S (regular A), eta.1 (regular A) k →
    f.1 = eval rho sigma k ∧
    ∀ m : ↥M.1, f.1 m = sigma (k (T.1.2 (regular A) m (ULift.up (1 : A))))) ∧
  (∀ (X : AMod.{u,x} A) (k : Component T S X), eta.1 X k → Pure f X k)

private def InverseAssignments (rho : Unitor T) (sigma : Unitor S) : Prop :=
  (∀ eta : NatGraph T S, ∃! f : NatCode M N, Represents rho sigma eta f) ∧
  (∀ f : NatCode M N, ∃! eta : NatGraph T S, Represents rho sigma eta f)

private def Addition (rho : Unitor T) (sigma : Unitor S) : Prop :=
  ∀ eta theta : NatGraph T S,
    ∃ sum : NatGraph T S,
      (∀ (X : AMod.{u,x} A) (k l : Component T S X),
        eta.1 X k → theta.1 X l → sum.1 X (k + l)) ∧
      (∀ (k l : Component T S (regular A)),
        eta.1 (regular A) k → theta.1 (regular A) l →
        eval rho sigma (k + l) = eval rho sigma k + eval rho sigma l)

private def Identity (rho : Unitor T) : Prop :=
  ∃ identity : NatGraph T T,
    (∀ X : AMod.{u,x} A, identity.1 X LinearMap.id) ∧
    eval rho rho LinearMap.id = LinearMap.id

private def Composition (rho : Unitor T) (sigma : Unitor S) (tau : Unitor U) : Prop :=
  ∀ (eta : NatGraph T S) (theta : NatGraph S U),
    ∃ composite : NatGraph T U,
      (∀ (X : AMod.{u,x} A) (k : Component T S X) (l : Component S U X),
        eta.1 X k → theta.1 X l → composite.1 X (l.comp k)) ∧
      (∀ (k : Component T S (regular A)) (l : Component S U (regular A)),
        eta.1 (regular A) k → theta.1 (regular A) l →
        eval rho tau (l.comp k) = (eval sigma tau l).comp (eval rho sigma k))

private theorem right_add (M : Bimod.{u,v,w} A B) (m n : M.1) (a : A) :
    right M (m + n) a = right M m a + right M n a := by
  letI : Module (MulOpposite A) M.1 := M.2.1.2.1
  exact smul_add (MulOpposite.op a) m n

private theorem right_add_scalar (M : Bimod.{u,v,w} A B) (m : M.1) (a b : A) :
    right M m (a + b) = right M m a + right M m b := by
  letI : Module (MulOpposite A) M.1 := M.2.1.2.1
  exact add_smul (MulOpposite.op a) (MulOpposite.op b) m

private theorem right_one (M : Bimod.{u,v,w} A B) (m : M.1) :
    right M m 1 = m := by
  letI : Module (MulOpposite A) M.1 := M.2.1.2.1
  exact one_smul (MulOpposite A) m

private theorem right_mul (M : Bimod.{u,v,w} A B) (m : M.1) (a b : A) :
    right M (right M m a) b = right M m (a * b) := by
  letI : Module (MulOpposite A) M.1 := M.2.1.2.1
  exact (mul_smul (MulOpposite.op b) (MulOpposite.op a) m).symm

private theorem right_smul (M : Bimod.{u,v,w} A B) (b : B) (m : M.1) (a : A) :
    right M (b • m) a = b • right M m a := by
  rcases M with ⟨L, ⟨⟨left, ⟨rightAction, comm⟩⟩, h⟩⟩
  change left = ModuleCat.isModule L at h
  subst left
  exact comm.smul_comm (MulOpposite.op a) b m

private theorem tensor_ext (T : TensorFunctor.{u,v,w,x} M) (X : AMod.{u,x} A)
    (Y : BMod.{u,v,w,x} A B) (f g : T.1.1.obj X →ₗ[B] Y)
    (h : ∀ (m : ↥M.1) (y : X), f (T.1.2 X m y) = g (T.1.2 X m y)) :
    f = g := by
  let p : ↥M.1 → X → Y := fun m y => g (T.1.2 X m y)
  have ht := T.2.1 X
  have hp : Balanced M X Y p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro m n y
      change g (T.1.2 X (m + n) y) = g (T.1.2 X m y) + g (T.1.2 X n y)
      rw [ht.1, map_add]
    · intro m y z
      change g (T.1.2 X m (y + z)) = g (T.1.2 X m y) + g (T.1.2 X m z)
      rw [ht.2.1, map_add]
    · intro b m y
      change g (T.1.2 X (b • m) y) = b • g (T.1.2 X m y)
      rw [ht.2.2.1, map_smul]
    · intro a m y
      change g (T.1.2 X (right M m a) y) = g (T.1.2 X m (a • y))
      rw [ht.2.2.2]
  obtain ⟨q, _, hq⟩ := T.2.2.1 X Y p hp
  exact (hq f h).trans (hq g (fun _ _ => rfl)).symm

private abbrev liftedCarrier (M : Bimod.{u,v,w} A B) : BMod.{u,v,w,x} A B :=
  ModuleCat.of B (ULift.{max u x} ↥M.1)

private theorem regular_balance (M : Bimod.{u,v,w} A B) :
    Balanced M (regular.{u,x} A) (liftedCarrier.{u,v,w,x} M)
      (fun m r => ULift.up (right M m r.down)) := by
  exact ⟨fun m n r => congrArg ULift.up (right_add M m n r.down),
    fun m r s => congrArg ULift.up (right_add_scalar M m r.down s.down),
    fun b m r => congrArg ULift.up (right_smul M b m r.down),
    fun a m r => congrArg ULift.up (right_mul M m a r.down)⟩

private theorem pure_right_regular (T : TensorFunctor.{u,v,w,x} M)
    (m : M.1) (a : A) :
    T.1.2 (regular A) (right M m a) (ULift.up (1 : A)) =
      T.1.2 (regular A) m (ULift.up a) := by
  rw [(T.2.1 (regular A)).2.2.2]
  exact congrArg (T.1.2 (regular A) m) (congrArg ULift.up (mul_one a))

/-
Alphabeta Math Step 1.1 uses [F1]. The two B-linear unit maps here come from
the pointwise universal property and the explicit map m ↦ m ⊗ 1.
The lift allows the target to have the universe required by that property.
The inverse identity on the tensor module follows by uniqueness on pure tensors.
-/
private theorem exists_unitor (T : TensorFunctor.{u,v,w,x} M) :
    ∃ rho : Unitor T, IsUnitor rho := by
  let X : AMod.{u,x} A := regular A
  let Y : BMod.{u,v,w,x} A B := liftedCarrier M
  let p : ↥M.1 → X → Y := fun m r => ULift.up (right M m r.down)
  obtain ⟨d, hd, _⟩ := T.2.2.1 X Y p (regular_balance M)
  let down : Y →ₗ[B] M.1 :=
    (ULift.moduleEquiv : ULift.{max u x} ↥M.1 ≃ₗ[B] M.1).toLinearMap
  let f : T.1.1.obj X →ₗ[B] M.1 := down.comp d
  let g : M.1 →ₗ[B] T.1.1.obj X :=
    { toFun := fun m => T.1.2 X m (ULift.up (1 : A))
      map_add' := fun m n => (T.2.1 X).1 m n _
      map_smul' := fun b m => (T.2.1 X).2.2.1 b m _ }
  have hf (m : M.1) (a : A) : f (T.1.2 X m (ULift.up a)) = right M m a := by
    exact congrArg down (hd m (ULift.up a))
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro m
    exact (hf m 1).trans (right_one M m)
  have hgf : g.comp f = LinearMap.id := by
    apply tensor_ext T X (T.1.1.obj X)
    intro m r
    change g (f (T.1.2 X m (ULift.up r.down))) = T.1.2 X m r
    rw [hf]
    exact pure_right_regular T m r.down
  let rho : Unitor T := LinearEquiv.ofLinearMap f g hfg hgf
  exact ⟨rho, hf, fun _ => rfl⟩

private theorem eval_on_one (rho : Unitor T) (sigma : Unitor S)
    (hrho : IsUnitor rho) (k : Component T S (regular A)) (m : M.1) :
    eval rho sigma k m = sigma (k (T.1.2 (regular A) m (ULift.up (1 : A)))) := by
  change sigma (k (rho.symm m)) = _
  rw [hrho.2 m]

private abbrev fromRegular (X : AMod.{u,x} A) (y : X) : ModuleCat.Hom (regular A) X :=
  ⟨(ULift.moduleEquiv : ULift.{x} A ≃ₗ[A] A).toLinearMap.smulRight y⟩

private theorem fromRegular_one (X : AMod.{u,x} A) (y : X) :
    (fromRegular X y).hom (ULift.up (1 : A)) = y :=
  one_smul A y

private theorem out_of_regular (rho : Unitor T) (hrho : IsUnitor rho)
    (X : AMod.{u,x} A) (y : X) (z : T.1.1.obj (regular A)) :
    (T.1.1.map (fromRegular X y)).hom z = T.1.2 X (rho z) y := by
  conv_lhs => rw [← rho.symm_apply_apply z, hrho.2]
  rw [T.2.2.2, fromRegular_one]

private theorem natural_at (eta : NatGraph T S) {X Y : AMod.{u,x} A}
    (h : ModuleCat.Hom X Y) {k : Component T S X} {l : Component T S Y}
    (hk : eta.1 X k) (hl : eta.1 Y l) (z : T.1.1.obj X) :
    (S.1.1.map h).hom (k z) = l ((T.1.1.map h).hom z) :=
  DFunLike.congr_fun (eta.2.2 X Y h k l hk hl) z

/-
Alphabeta Math Step 1.1 uses naturality at right multiplication by a.
On the lifted regular module this is fromRegular with y = up a, since
r • a = r * a there. The unitor computation supplies the required right-linearity.
-/
private theorem eval_right (rho : Unitor T) (sigma : Unitor S)
    (hrho : IsUnitor rho) (hsigma : IsUnitor sigma) (eta : NatGraph T S)
    (k : Component T S (regular A)) (hk : eta.1 (regular A) k)
    (m : M.1) (a : A) :
    eval rho sigma k (right M m a) = right N (eval rho sigma k m) a := by
  rw [eval_on_one rho sigma hrho, eval_on_one rho sigma hrho]
  let z : T.1.1.obj (regular A) := T.1.2 (regular A) m (ULift.up (1 : A))
  rw [pure_right_regular T]
  have hn := natural_at eta (fromRegular (regular A) (ULift.up a)) hk hk z
  rw [out_of_regular sigma hsigma, out_of_regular rho hrho, hrho.1, right_one] at hn
  rw [← hn, hsigma.1]

-- Alphabeta Math Step 2.1 applies naturality at r ↦ r • y to m ⊗ 1.
private theorem graph_member_pure (rho : Unitor T) (sigma : Unitor S)
    (hrho : IsUnitor rho) (hsigma : IsUnitor sigma) (eta : NatGraph T S)
    (k : Component T S (regular A)) (hk : eta.1 (regular A) k)
    (f : NatCode M N) (hf : f.1 = eval rho sigma k)
    (X : AMod.{u,x} A) (l : Component T S X) (hl : eta.1 X l) :
    Pure f X l := by
  intro m y
  have hn := natural_at eta (fromRegular X y) hk hl (T.1.2 (regular A) m (ULift.up (1 : A)))
  rw [out_of_regular sigma hsigma, out_of_regular rho hrho, hrho.1, right_one] at hn
  rw [hf, eval_on_one rho sigma hrho]
  exact hn.symm

private theorem pure_exists (f : NatCode M N) (X : AMod.{u,x} A) :
    ∃! k : Component T S X, Pure f X k := by
  let p : ↥M.1 → X → S.1.1.obj X := fun m y => S.1.2 X (f.1 m) y
  have hs := S.2.1 X
  have hp : Balanced M X (S.1.1.obj X) p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro m n y
      change S.1.2 X (f.1 (m + n)) y = _
      rw [map_add]
      exact hs.1 (f.1 m) (f.1 n) y
    · intro m y z
      exact hs.2.1 (f.1 m) y z
    · intro b m y
      change S.1.2 X (f.1 (b • m)) y = _
      rw [map_smul]
      exact hs.2.2.1 b (f.1 m) y
    · intro a m y
      change S.1.2 X (f.1 (right M m a)) y = _
      rw [f.2]
      exact hs.2.2.2 a (f.1 m) y
  exact T.2.2.1 X (S.1.1.obj X) p hp

/-
Alphabeta Math Step 1.2 uses the induced tensor maps of [F5].
Here each component is specified by its pure-tensor equation. The given
universal property supplies pointwise witnesses and proves naturality on
pure tensors. The graph avoids selecting a dependent family of witnesses.
-/
private def pureGraph (f : NatCode M N) : NatGraph T S := by
  refine ⟨Pure f, pure_exists f, ?_⟩
  intro X Y h k l hk hl
  apply tensor_ext T X (S.1.1.obj Y)
  intro m y
  change (S.1.1.map h).hom (k (T.1.2 X m y)) =
    l ((T.1.1.map h).hom (T.1.2 X m y))
  rw [hk m y, T.2.2.2, S.2.2.2, hl m (h.hom y)]

private theorem pureGraph_represents (rho : Unitor T) (sigma : Unitor S)
    (hrho : IsUnitor rho) (hsigma : IsUnitor sigma) (f : NatCode M N) :
    Represents rho sigma (pureGraph f) f := by
  refine ⟨?_, fun _ _ h => h⟩
  intro k hk
  have hp : Pure f (regular A) k := hk
  have h (m : M.1) :
      f.1 m = sigma (k (T.1.2 (regular A) m (ULift.up (1 : A)))) := by
    rw [hp m, hsigma.1, right_one]
  exact ⟨LinearMap.ext (fun m => (h m).trans (eval_on_one rho sigma hrho k m).symm), h⟩

-- Alphabeta Math Step 3.1 uses component uniqueness and graph extensionality.
private theorem inverse_assignments (rho : Unitor T) (sigma : Unitor S)
    (hrho : IsUnitor rho) (hsigma : IsUnitor sigma) :
    InverseAssignments rho sigma := by
  constructor
  · intro eta
    obtain ⟨k, hk, uniq⟩ := eta.2.1 (regular A)
    let f : NatCode M N := ⟨eval rho sigma k, eval_right rho sigma hrho hsigma eta k hk⟩
    refine ⟨f, ⟨?_, graph_member_pure rho sigma hrho hsigma eta k hk f rfl⟩, ?_⟩
    · intro l hl
      rw [uniq l hl]
      exact ⟨rfl, eval_on_one rho sigma hrho k⟩
    · intro g hg
      exact Subtype.ext ((hg.1 k hk).1)
  · intro f
    refine ⟨pureGraph f, pureGraph_represents rho sigma hrho hsigma f, ?_⟩
    intro eta heta
    apply Subtype.ext
    funext X k
    apply propext
    refine ⟨heta.2 X k, ?_⟩
    intro hk
    obtain ⟨l, hl, _⟩ := eta.2.1 X
    obtain ⟨q, _, hq⟩ := pure_exists (T := T) (S := S) f X
    have hkl := (hq k hk).trans (hq l (heta.2 X l hl)).symm
    exact hkl ▸ hl

/-
Alphabeta Math Step 4.1 takes operations componentwise. The graphs for
addition and composition use existential witnesses at the single object in
question. Their uniqueness and naturality use the original graphs at those
objects. Evaluation is conjugation by the unitors.
-/
private theorem add_graphs (rho : Unitor T) (sigma : Unitor S) :
    Addition rho sigma := by
  intro eta theta
  let G (X : AMod.{u,x} A) (s : Component T S X) : Prop :=
    ∃ k l : Component T S X, eta.1 X k ∧ theta.1 X l ∧ s = k + l
  have unique (X : AMod.{u,x} A) : ∃! s, G X s := by
    obtain ⟨k, hk, uk⟩ := eta.2.1 X
    obtain ⟨l, hl, ul⟩ := theta.2.1 X
    refine ⟨k + l, ⟨k, l, hk, hl, rfl⟩, ?_⟩
    rintro s ⟨k', l', hk', hl', rfl⟩
    rw [uk k' hk', ul l' hl']
  let sum : NatGraph T S := ⟨G, unique, by
    rintro X Y h _ _ ⟨k, l, hk, hl, rfl⟩ ⟨k', l', hk', hl', rfl⟩
    apply LinearMap.ext
    intro z
    change (S.1.1.map h).hom (k z + l z) =
      k' ((T.1.1.map h).hom z) + l' ((T.1.1.map h).hom z)
    rw [map_add, natural_at eta h hk hk' z, natural_at theta h hl hl' z]⟩
  refine ⟨sum, fun _ k l hk hl => ⟨k, l, hk, hl, rfl⟩, ?_⟩
  intro k l _ _
  apply LinearMap.ext
  intro m
  change sigma (k (rho.symm m) + l (rho.symm m)) =
    sigma (k (rho.symm m)) + sigma (l (rho.symm m))
  exact map_add sigma _ _

private theorem identity_graph (rho : Unitor T) : Identity rho := by
  let identity : NatGraph T T :=
    ⟨fun _ k => k = LinearMap.id, fun _ => ⟨LinearMap.id, rfl, fun _ h => h⟩,
      by
        rintro X Y h _ _ rfl rfl
        apply LinearMap.ext
        intro z
        rfl⟩
  refine ⟨identity, fun _ => rfl, ?_⟩
  apply LinearMap.ext
  intro m
  exact rho.apply_symm_apply m

private theorem compose_graphs (rho : Unitor T) (sigma : Unitor S) (tau : Unitor U) :
    Composition rho sigma tau := by
  intro eta theta
  let G (X : AMod.{u,x} A) (s : Component T U X) : Prop :=
    ∃ (k : Component T S X) (l : Component S U X), eta.1 X k ∧ theta.1 X l ∧ s = l.comp k
  have unique (X : AMod.{u,x} A) : ∃! s, G X s := by
    obtain ⟨k, hk, uk⟩ := eta.2.1 X
    obtain ⟨l, hl, ul⟩ := theta.2.1 X
    refine ⟨l.comp k, ⟨k, l, hk, hl, rfl⟩, ?_⟩
    rintro s ⟨k', l', hk', hl', rfl⟩
    rw [uk k' hk', ul l' hl']
  let composite : NatGraph T U := ⟨G, unique, by
    rintro X Y h _ _ ⟨k, l, hk, hl, rfl⟩ ⟨k', l', hk', hl', rfl⟩
    apply LinearMap.ext
    intro z
    change (U.1.1.map h).hom (l (k z)) = l' (k' ((T.1.1.map h).hom z))
    rw [natural_at theta h hl hl', natural_at eta h hk hk']⟩
  refine ⟨composite, fun _ k l hk hl => ⟨k, l, hk, hl, rfl⟩, ?_⟩
  intro k l _ _
  apply LinearMap.ext
  intro m
  change tau (l (k (rho.symm m))) = tau (l (sigma.symm (sigma (k (rho.symm m)))))
  rw [sigma.symm_apply_apply]

private theorem assemble (M N P : Bimod.{u,v,w} A B)
    (T : TensorFunctor.{u,v,w,x} M) (S : TensorFunctor.{u,v,w,x} N)
    (U : TensorFunctor.{u,v,w,x} P) :
    ∃ (rho : Unitor T) (sigma : Unitor S) (tau : Unitor U),
      IsUnitor rho ∧ IsUnitor sigma ∧ IsUnitor tau ∧
      InverseAssignments rho sigma ∧ InverseAssignments sigma tau ∧ InverseAssignments rho tau ∧
      Addition rho sigma ∧ Identity rho ∧ Composition rho sigma tau := by
  obtain ⟨rho, hrho⟩ := exists_unitor T
  obtain ⟨sigma, hsigma⟩ := exists_unitor S
  obtain ⟨tau, htau⟩ := exists_unitor U
  exact ⟨rho, sigma, tau, hrho, hsigma, htau,
    inverse_assignments rho sigma hrho hsigma, inverse_assignments sigma tau hsigma htau,
    inverse_assignments rho tau hrho htau, add_graphs rho sigma, identity_graph rho,
    compose_graphs rho sigma tau⟩

end NaturalTransformationsOfTensorFunctorsProof
