import Mathlib.Algebra.Category.ModuleCat.Ulift
import MackeyDiagrams
import Proofs.GeneralizedMackeyDecomposition

set_option maxHeartbeats 2000000

namespace OrdinaryMackeySupport

open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra
universe u v
noncomputable section

-- The coproduct legs and their generator formula are available in the
-- implementation of the registered GeneralizedMackeyDecomposition supplier.
-- Its checked source has SHA-256
-- 044084754209ae3de60b4056dbe9a817bdf369063bb483e8ffaa6e945a2557b2.
local macro "mackey_impl%" id:ident : term => do
  let n := (Lean.Name.num `_private.Proofs.GeneralizedMackeyDecomposition 0) ++
    `GeneralizedMackeySupport ++ id.getId
  return Lean.mkIdent n

variable {A B : Type u} [Group A] [Group B]

abbrev Mod (A : Type u) [Group A] := ModuleCat.{max u v} (MonoidAlgebra Complex A)
private abbrev ofMod (A : Type u) [Group A] : Mod.{u,v} A ⥤ Rep.{max u v} Complex A :=
  Rep.ofModuleMonoidAlgebra
private abbrev toMod (A : Type u) [Group A] : Rep.{max u v} Complex A ⥤ Mod.{u,v} A :=
  Rep.toModuleMonoidAlgebra
abbrev indMod (f : A →* B) : Mod.{u,v} A ⥤ Mod.{u,v} B :=
  (ofMod A ⋙ Rep.indFunctor Complex f) ⋙ toMod B
abbrev resMod (f : A →* B) : Mod.{u,v} B ⥤ Mod.{u,v} A :=
  ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex f).toRingHom

abbrev pure (f : A →* B) (X : Rep.{max u v} Complex A) (g : B) :=
  IndV.mk f X.ρ g⁻¹

abbrev tmul (f : A →* B) (M : Mod.{u,v} A) (b : B) (m : M) :
    (indMod f).obj M :=
  let X := (ofMod A).obj M
  (ind f X.ρ).asModuleEquiv.symm
    (pure f X b ((RestrictScalars.addEquiv Complex (MonoidAlgebra Complex A) M).symm m))

private theorem algebra_of (f : A →* B) (a : A) :
    MonoidAlgebra.mapDomainAlgHom Complex Complex f (MonoidAlgebra.of Complex A a) =
      MonoidAlgebra.of Complex B (f a) := by
  simp [MonoidAlgebra.of_apply]

private theorem ofMod_act (M : Mod.{u,v} A) (a : A) (x : (ofMod A).obj M) :
    ((ofMod A).obj M).ρ a x = (show M from MonoidAlgebra.of Complex A a • (show M from x)) := by
  change ofModule M a x = _
  rw [ofModule, MonoidAlgebra.lift_symm_apply]
  rfl

private def resRepApp (f : A →* B) (M : Mod.{u,v} B) :
    Rep.res f ((ofMod B).obj M) ≅ (ofMod A).obj ((resMod f).obj M) := by
  refine Rep.mkIso (ρ := (Rep.res f ((ofMod B).obj M)).ρ)
    (σ := ((ofMod A).obj ((resMod f).obj M)).ρ) (.mk ?_ ?_)
  · refine
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := ?_ }
    intro z x
    change (algebraMap Complex (MonoidAlgebra Complex B) z) • (show M from x) =
      (MonoidAlgebra.mapDomainAlgHom Complex Complex f
        (algebraMap Complex (MonoidAlgebra Complex A) z)) • (show M from x)
    rw [AlgHom.commutes]
  · intro a
    ext x
    change ((ofMod B).obj M).ρ (f a) x =
      ((ofMod A).obj ((resMod f).obj M)).ρ a x
    have hL := ofMod_act M (f a) x
    have hR := ofMod_act ((resMod f).obj M) a x
    change _ = MonoidAlgebra.mapDomainAlgHom Complex Complex f
      (MonoidAlgebra.of Complex A a) • (show M from x) at hR
    exact hL.trans ((congrArg (fun y : MonoidAlgebra Complex B => y • (show M from x))
      (algebra_of f a).symm).trans hR.symm)

private def resRep (f : A →* B) :
    (ofMod.{u,v} B ⋙ Rep.resFunctor f) ≅ (resMod.{u,v} f ⋙ ofMod.{u,v} A) :=
  NatIso.ofComponents (resRepApp f) (by
    intro X Y g
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    exact LinearMap.ext (fun x => rfl))

private theorem resAct (f : A →* B) (X : Rep.{max u v} Complex B)
    (r : MonoidAlgebra Complex A) :
    (Rep.res f X).ρ.asAlgebraHom r =
      X.ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom Complex Complex f r) := by
  let h := MonoidAlgebra.lift Complex (Module.End Complex X) A
  have he : (Rep.res f X).ρ.asAlgebraHom =
      X.ρ.asAlgebraHom.comp (MonoidAlgebra.mapDomainAlgHom Complex Complex f) := by
    apply h.symm.injective
    apply MonoidHom.ext
    intro a
    simp only [h, MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply,
      ← MonoidAlgebra.of_apply, algebra_of, asAlgebraHom_of]
    rfl
  exact DFunLike.congr_fun he r

private def resModApp (f : A →* B) (X : Rep.{max u v} Complex B) :
    (toMod A).obj (Rep.res f X) ≅ (resMod f).obj ((toMod B).obj X) := by
  let Y := (toMod A).obj (Rep.res f X)
  let Z := (resMod f).obj ((toMod B).obj X)
  refine LinearEquiv.toModuleIso (show Y ≃ₗ[MonoidAlgebra Complex A] Z from ?_)
  refine
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro r x
  change (Rep.res f X).ρ.asAlgebraHom r x =
    X.ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom Complex Complex f r) x
  rw [resAct]

private def resToMod (f : A →* B) :
    (Rep.resFunctor f ⋙ toMod.{u,v} A) ≅ (toMod.{u,v} B ⋙ resMod.{u,v} f) :=
  NatIso.ofComponents (resModApp f) (by
    intro X Y g
    ext x
    rfl)

section Coproduct
variable {K H G : Type u} [Group K] [Group H] [Group G]
variable {J : Type u} {L : J → Type u} [∀ j, Group (L j)]
variable (a : K →* G) (b : H →* G) (l : ∀ j, L j →* K) (r : ∀ j, L j →* H)
variable (s : J → G) (balance : ∀ j t, a (l j t) * s j = s j * b (r j t))

-- The coset partition and stabilizer identification are the hypotheses of
-- the balanced-pair construction in the proof of Theorem 2.2.
-- Use repCofanIsColimit for the coproduct and inclusionAt_pure for its legs.
-- The scalar-restriction comparisons above act by identity on the carriers,
-- so the generator formula survives transport from Rep to ModuleCat.
theorem coproduct
    (bijective : Function.Bijective ((mackey_impl% toGroup) a b l r s balance)) :
    ∃ e : (indMod.{u,v} b ⋙ resMod.{u,v} a) ≅
        sigmaObj (fun j => resMod.{u,v} (r j) ⋙ indMod.{u,v} (l j)),
      ∀ (j : J) (M : Mod.{u,v} H) (k : K) (x : M),
        e.inv.app M ((Sigma.ι (fun j => resMod (r j) ⋙ indMod (l j)) j).app M
          (tmul (l j) ((resMod (r j)).obj M) k x)) =
        tmul b M (a k * s j) x := by
  let P := (Functor.whiskeringLeft _ _ (Rep.{max u v} Complex K)).obj (ofMod.{u,v} H)
  let Q := (Functor.whiskeringRight (Mod.{u,v} H) _ _).obj (toMod.{u,v} K)
  let c := (mackey_impl% repCofan) a b l r s balance
  have hc : IsColimit c := (mackey_impl% repCofanIsColimit) a b l r s balance bijective
  let D := (P ⋙ Q).mapCocone c
  have hD : IsColimit D := isColimitOfPreserves (P ⋙ Q) hc
  let T := fun j => resMod.{u,v} (r j) ⋙ indMod.{u,v} (l j)
  let F : Mod.{u,v} H ⥤ Mod.{u,v} K := indMod b ⋙ resMod a
  let main : D.pt ≅ F :=
    Functor.isoWhiskerLeft (ofMod H ⋙ Rep.indFunctor Complex b) (resToMod a)
  let summand : Discrete.functor (fun j => Rep.resFunctor (r j) ⋙ Rep.indFunctor Complex (l j)) ⋙
      (P ⋙ Q) ≅ Discrete.functor T :=
    Discrete.natIso fun j =>
      Functor.isoWhiskerRight (resRep (r j.as)) (Rep.indFunctor Complex (l j.as) ⋙ toMod K)
  let e₀ := hD.coconePointUniqueUpToIso (colimit.isColimit _)
  let e₁ := HasColimit.isoOfNatIso summand
  let e : F ≅ sigmaObj T := main.symm ≪≫ e₀ ≪≫ e₁
  have legs (j : J) :
      Sigma.ι T j ≫ e.inv = (summand.inv.app ⟨j⟩ ≫ D.ι.app ⟨j⟩) ≫ main.hom := by
    change colimit.ι (Discrete.functor T) ⟨j⟩ ≫ (e₁.inv ≫ e₀.inv ≫ main.hom) = _
    rw [← Category.assoc, HasColimit.ι_isoOfNatIso_inv, Category.assoc,
      ← Category.assoc (colimit.ι _ _) e₀.inv,
      colimit.comp_coconePointUniqueUpToIso_inv hD, Category.assoc]
  refine ⟨e, ?_⟩
  intro j M k x
  have h := congrArg (fun f : T j ⟶ F =>
    f.app M (tmul (l j) ((resMod (r j)).obj M) k x)) (legs j)
  exact h.trans ((mackey_impl% inclusionAt_pure) a b l r s balance j ((ofMod H).obj M) k x)

end Coproduct

section Regular

abbrev regular (A : Type u) [Group A] : Mod.{u,v} A :=
  ModuleCat.of (MonoidAlgebra Complex A) (ULift.{v} (MonoidAlgebra Complex A))

abbrev rightMul (x : MonoidAlgebra Complex A) : regular.{u,v} A ⟶ regular.{u,v} A :=
  (ModuleCat.uliftFunctor.{v,u} (MonoidAlgebra Complex A)).map
    (ModuleCat.ofHom (LinearMap.mulRight (MonoidAlgebra Complex A) x))

private abbrev regRep (A : Type u) [Group A] := (ofMod A).obj (regular.{u,v} A)

private def regDown : regRep.{u,v} A ≃ₗ[Complex] MonoidAlgebra Complex A :=
  { toFun := ULift.down
    invFun := ULift.up
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun z x => Algebra.smul_def z x.down |>.symm }

private def regBasis (A : Type u) [Group A] : Module.Basis A Complex (regRep.{u,v} A) :=
  (MonoidAlgebra.basis A Complex).map regDown.symm

private theorem regBasis_apply (a : A) :
    regBasis.{u,v} A a = ULift.up (MonoidAlgebra.of Complex A a) := rfl

private theorem reg_act (a : A) (x : regRep.{u,v} A) :
    (regRep.{u,v} A).ρ a x = ULift.up (MonoidAlgebra.of Complex A a * x.down) :=
  ofMod_act (regular A) a x

private abbrev alg (b : A →* B) := MonoidAlgebra.mapDomainAlgHom Complex Complex b

private def regProduct (b : A →* B) (g : B) :
    regRep.{u,v} A →ₗ[Complex] regRep.{u,v} B :=
  regDown.symm.toLinearMap ∘ₗ
    LinearMap.mulLeft Complex (MonoidAlgebra.of Complex B g) ∘ₗ
      (alg b).toLinearMap ∘ₗ regDown.toLinearMap

private theorem regProduct_apply (b : A →* B) (g : B) (x : regRep.{u,v} A) :
    regProduct b g x = ULift.up (MonoidAlgebra.of Complex B g * alg b x.down) := rfl

private theorem regProduct_balance (b : A →* B) (g : B) (h : A) (x : regRep.{u,v} A) :
    regProduct b (g * b h) x = regProduct b g ((regRep A).ρ h x) := by
  rw [regProduct_apply, regProduct_apply]
  erw [reg_act]
  change ULift.up (MonoidAlgebra.of Complex B (g * b h) * alg b x.down) =
    ULift.up (MonoidAlgebra.of Complex B g * alg b (MonoidAlgebra.of Complex A h * x.down))
  simp only [map_mul, alg, algebra_of, mul_assoc]

private def regForward (b : A →* B) :
    IndV b (regRep.{u,v} A).ρ →ₗ[Complex] regRep.{u,v} B :=
  (mackey_impl% liftPure) b (regRep A) (regProduct b) (regProduct_balance b)

private theorem regForward_pure (b : A →* B) (g : B) (x : regRep.{u,v} A) :
    regForward b (pure b (regRep A) g x) =
      ULift.up (MonoidAlgebra.of Complex B g * alg b x.down) :=
  (mackey_impl% liftPure_apply) b (regRep A) (regProduct b) (regProduct_balance b) g x

private def regBackward (b : A →* B) :
    regRep.{u,v} B →ₗ[Complex] IndV b (regRep.{u,v} A).ρ :=
  (regBasis B).constr Complex
    (fun g => pure b (regRep A) g (ULift.up (1 : MonoidAlgebra Complex A)))

private theorem regBackward_basis (b : A →* B) (g : B) :
    regBackward b (regBasis.{u,v} B g) =
      pure b (regRep A) g (ULift.up (1 : MonoidAlgebra Complex A)) := by
  exact Module.Basis.constr_basis _ _ _ _

private def regIso (b : A →* B) : Rep.ind b (regRep.{u,v} A) ≅ regRep.{u,v} B := by
  refine Rep.mkIso (ρ := (Rep.ind b (regRep A)).ρ) (σ := (regRep B).ρ)
    (.mk { regForward b with invFun := regBackward b, left_inv := ?_, right_inv := ?_ } ?_)
  · have h : regBackward b ∘ₗ regForward b = LinearMap.id := by
      apply (mackey_impl% pure_ext) b (regRep A)
      intro g
      have hx : (regBackward b ∘ₗ regForward b) ∘ₗ pure b (regRep A) g =
          pure b (regRep A) g := by
        apply (regBasis A).ext
        intro h
        change regBackward b (regForward b (pure b (regRep A) g (regBasis A h))) = _
        rw [regForward_pure, regBasis_apply]
        change regBackward b (ULift.up (MonoidAlgebra.of Complex B g *
          alg b (MonoidAlgebra.of Complex A h))) = _
        rw [alg, algebra_of, ← map_mul, ← regBasis_apply, regBackward_basis]
        erw [(mackey_impl% pure_balance), reg_act]
        change pure b (regRep A) g (ULift.up (MonoidAlgebra.of Complex A h * 1)) =
          pure b (regRep A) g (ULift.up (MonoidAlgebra.of Complex A h))
        rw [mul_one]
      exact DFunLike.congr_fun hx
    exact fun x => DFunLike.congr_fun h x
  · have h : regForward b ∘ₗ regBackward b = LinearMap.id := by
      apply (regBasis B).ext
      intro g
      change regForward b (regBackward b (regBasis B g)) = regBasis B g
      rw [regBackward_basis]
      erw [regForward_pure, regBasis_apply]
      change ULift.up (MonoidAlgebra.of Complex B g * alg b 1) = _
      rw [map_one, mul_one]
    exact fun x => DFunLike.congr_fun h x
  · intro t
    apply (mackey_impl% pure_ext) b (regRep A)
    intro g x
    change regForward b (ind b (regRep A).ρ t (pure b (regRep A) g x)) =
      (regRep B).ρ t (regForward b (pure b (regRep A) g x))
    rw [(mackey_impl% pure_act), regForward_pure]
    rw [reg_act]
    erw [regForward_pure]
    change ULift.up (MonoidAlgebra.of Complex B (t * g) * alg b x.down) =
      ULift.up (MonoidAlgebra.of Complex B t * (MonoidAlgebra.of Complex B g * alg b x.down))
    rw [map_mul, mul_assoc]

variable {K : Type u} [Group K]

def regularComparison (a : K →* B) (b : A →* B) :
    (indMod.{u,v} b ⋙ resMod.{u,v} a).obj (regular A) ≅ (resMod a).obj (regular B) :=
  (resMod a).mapIso ((toMod B).mapIso (regIso b) ≪≫ Rep.counitIso (regular B))

theorem regularComparison_apply_pure (a : K →* B) (b : A →* B) (g : B) (x : regular.{u,v} A) :
    (regularComparison a b).hom (tmul b (regular A) g x) =
      ULift.up (MonoidAlgebra.of Complex B g * alg b x.down) :=
  regForward_pure b g x

theorem regularComparison_right (a : K →* B) (b : A →* B)
    (y : MonoidAlgebra Complex A) (x : (indMod.{u,v} b ⋙ resMod.{u,v} a).obj (regular A)) :
    (regularComparison a b).hom (((indMod b ⋙ resMod a).map (rightMul y)) x) =
      ULift.up (((regularComparison a b).hom x).down * alg b y) := by
  let f := (ofMod A).map (rightMul.{u,v} y)
  have h : regForward b ∘ₗ (Rep.indMap b f).hom.toLinearMap =
      (regDown.symm.toLinearMap ∘ₗ LinearMap.mulRight Complex (alg b y) ∘ₗ
        regDown.toLinearMap) ∘ₗ regForward b := by
    apply (mackey_impl% pure_ext) b (regRep A)
    intro g z
    change regForward b ((Rep.indMap b f).hom (pure b (regRep A) g z)) =
      ULift.up ((regForward b (pure b (regRep A) g z)).down * alg b y)
    rw [(mackey_impl% pure_map), regForward_pure, regForward_pure]
    change ULift.up (MonoidAlgebra.of Complex B g * alg b (z.down * y)) =
      ULift.up ((MonoidAlgebra.of Complex B g * alg b z.down) * alg b y)
    rw [map_mul, mul_assoc]
  exact DFunLike.congr_fun h x

end Regular

section Subgroups

variable {G : Type u} [Group G] (K H : Subgroup G)
variable {L : DoubleCoset.Quotient (K : Set G) (H : Set G) → Type u} [∀ j, Group (L j)]
variable (l : ∀ j, L j →* K) (r : ∀ j, L j →* H)
variable (s : DoubleCoset.Quotient (K : Set G) (H : Set G) → G)
variable (balance : ∀ j t, (l j t : G) * s j = s j * (r j t : G))

-- The ordinary multiplication map lands directly in G. In this inclusion
-- case the intersection witness identifies equal products as balanced pairs.
theorem ordinaryBijective (reps : ∀ j, DoubleCoset.mk K H (s j) = j)
    (intersection : ∀ j (k : K) (h : H), (k : G) = s j * (h : G) * (s j)⁻¹ →
      ∃ t, l j t = k) :
    Function.Bijective ((mackey_impl% toGroup) K.subtype H.subtype l r s balance) := by
  let f := (mackey_impl% toGroup) K.subtype H.subtype l r s balance
  have index_mul (j) (k : K) (h : H) :
      DoubleCoset.mk K H ((k : G) * s j * (h : G)) = j := by
    have hcoset : DoubleCoset.mk K H (s j) = DoubleCoset.mk K H ((k : G) * s j * (h : G)) :=
      DoubleCoset.eq.mpr ⟨(k : G), k.property, (h : G), h.property, rfl⟩
    exact hcoset.symm.trans (reps j)
  have index (j) (q : Quotient ((mackey_impl% summandBasis) l r j)) :
      DoubleCoset.mk K H (f ⟨j, q⟩) = j :=
    Quotient.inductionOn q fun p => index_mul j p.1 p.2
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hij : i = j := (index i x).symm.trans ((congrArg (DoubleCoset.mk K H) he).trans (index j y))
    subst j
    apply congrArg (Sigma.mk i)
    revert he
    refine Quotient.inductionOn₂ x y (fun p q he => ?_)
    change (p.1 : G) * s i * (p.2 : G) = (q.1 : G) * s i * (q.2 : G) at he
    have hs : (↑(q.1⁻¹ * p.1) : G) = s i * (↑(q.2 * p.2⁻¹) : G) * (s i)⁻¹ := by
      change (q.1 : G)⁻¹ * (p.1 : G) = s i * ((q.2 : G) * (p.2 : G)⁻¹) * (s i)⁻¹
      have hh := congrArg (fun z : G => (q.1 : G)⁻¹ * z * (p.2 : G)⁻¹ * (s i)⁻¹) he
      convert hh using 1 <;> group
    obtain ⟨t, ht⟩ := intersection i (q.1⁻¹ * p.1) (q.2 * p.2⁻¹) hs
    have hr : r i t = q.2 * p.2⁻¹ := by
      have h := balance i t
      rw [ht, hs, inv_mul_cancel_right] at h
      exact Subtype.ext (mul_left_cancel h.symm)
    apply Quotient.sound
    change ∃ t : L i, p.1 * (l i t)⁻¹ = q.1 ∧ r i t * p.2 = q.2
    exact ⟨t, by rw [ht]; group, by rw [hr]; group⟩
  · intro g
    let j := DoubleCoset.mk K H g
    obtain ⟨k, hk, h, hh, he⟩ := DoubleCoset.eq.mp (reps j)
    exact ⟨⟨j, Quotient.mk _ (⟨k, hk⟩, ⟨h, hh⟩)⟩, he.symm⟩

end Subgroups

end
end OrdinaryMackeySupport

theorem OrdinaryMackeyDecomposition : (∀ {G : Type u} [Group G] (K H : Subgroup G),
  let I := DoubleCoset.Quotient (K : Set G) (H : Set G)
  ∀ (σ : I → G) (_ : ∀ i : I, DoubleCoset.mk K H (σ i) = i),
    let L := fun i : I => K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (σ i))) H
    let incLK := fun i : I =>
      Subgroup.inclusion (show L i ≤ K from inf_le_left)
    let μ := fun i : I =>
      MonoidHom.codRestrict
        (MonoidHom.comp (MulEquiv.toMonoidHom (MulAut.conj (σ i)⁻¹)) (Subgroup.subtype (L i)))
        H (by
          intro ℓ
          obtain ⟨h, hh, he⟩ := ℓ.property.2
          change σ i * h * (σ i)⁻¹ = (ℓ : G) at he
          change h ∈ H at hh
          change (σ i)⁻¹ * (ℓ : G) * ((σ i)⁻¹)⁻¹ ∈ H
          rw [← he]
          convert hh using 1
          group)
    let Mod := fun A : Type u => fun [Group A] => ModuleCat.{max u v} (MonoidAlgebra Complex A)
    let Res := fun {A B : Type u} [Group A] [Group B] (f : A →* B) =>
      (ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex f).toRingHom :
        CategoryTheory.Functor (Mod B) (Mod A))
    let Ind := fun {A B : Type u} [Group A] [Group B] (f : A →* B) =>
      (CategoryTheory.Functor.comp
        (CategoryTheory.Functor.comp
          (Rep.ofModuleMonoidAlgebra (k := Complex) (G := A))
          (Rep.indFunctor Complex f))
        (Rep.toModuleMonoidAlgebra (k := Complex) (G := B)) :
          CategoryTheory.Functor (Mod A) (Mod B))
    let F := CategoryTheory.Functor.comp (Ind (Subgroup.subtype H)) (Res (Subgroup.subtype K))
    let S := fun i : I => CategoryTheory.Functor.comp (Res (μ i)) (Ind (incLK i))
    let regular := fun (A : Type u) [Group A] =>
      ModuleCat.of (MonoidAlgebra Complex A) (ULift.{v} (MonoidAlgebra Complex A))
    let regularH := regular H
    let regularG := regular G
    let rightMulH := fun a : MonoidAlgebra Complex H =>
      (ModuleCat.uliftFunctor.{v, u} (MonoidAlgebra Complex H)).map
        (ModuleCat.ofHom (LinearMap.mulRight (MonoidAlgebra Complex H) a))
    let tmul := fun {A B : Type u} [Group A] [Group B] (f : A →* B)
        (M : Mod A) (b : B) (m : ↥M) =>
      let N := (Rep.ofModuleMonoidAlgebra (k := Complex) (G := A)).obj M
      let x : ↥N := (RestrictScalars.addEquiv Complex (MonoidAlgebra Complex A) (↥M)).symm m
      let y : ↥(Rep.ind f N) := (Representation.IndV.mk f N.ρ b⁻¹) x
      (show ↥((Ind f).obj M) from
        (Representation.asModuleEquiv (Rep.ind f N).ρ).symm y)
    let targetBasis : G → ↥(F.obj regularH) := fun g =>
      tmul (Subgroup.subtype H) regularH g (ULift.up (1 : MonoidAlgebra Complex H))
    let summandTmul : ∀ i : I, K → H → ↥((S i).obj regularH) := fun i k h =>
      tmul (incLK i) ((Res (μ i)).obj regularH) k (ULift.up (MonoidAlgebra.of Complex H h))
    ∃ (e : CategoryTheory.Iso F (CategoryTheory.Limits.sigmaObj S))
      (c : CategoryTheory.Iso (F.obj regularH) ((Res (Subgroup.subtype K)).obj regularG)),
      (∀ g : G, c.hom (targetBasis g) = ULift.up (MonoidAlgebra.of Complex G g)) ∧
      (∀ (a : MonoidAlgebra Complex H) (x : ↥(F.obj regularH)),
        c.hom ((F.map (rightMulH a)) x) =
          ULift.up (ULift.down (c.hom x) *
            MonoidAlgebra.mapDomainAlgHom Complex Complex (Subgroup.subtype H) a)) ∧
      (∀ (i : I) (k : K) (h : H),
        c.hom (e.inv.app regularH
          ((CategoryTheory.Limits.Sigma.ι S i).app regularH (summandTmul i k h))) =
            ULift.up (MonoidAlgebra.of Complex G ((k : G) * σ i * (h : G))))) :=
(by
  classical
  intro G inst K H I σ reps L incLK μ Mod Res Ind F S regular regularH regularG
    rightMulH tmul targetBasis summandTmul
  -- Xiao, Theorem 2.1, p. 5 of the archived original and p. 7 of the
  -- published 28 November revision.
  -- Specialize the checked coproduct construction of Theorem 2.2 to the
  -- two inclusions. Equations (2.1) and (2.2) give the coset partition and
  -- its stabilizers, which identify the balanced pairs used for (2.3).
  have balance (i : I) (t : L i) :
      (incLK i t : G) * σ i = σ i * (μ i t : G) := by
    change (t : G) * σ i = σ i * ((σ i)⁻¹ * (t : G) * ((σ i)⁻¹)⁻¹)
    group
  have intersection (i : I) (k : K) (h : H)
      (he : (k : G) = σ i * (h : G) * (σ i)⁻¹) : ∃ t : L i, incLK i t = k := by
    exact ⟨⟨k, k.property, ⟨h, h.property, he.symm⟩⟩, rfl⟩
  have bijective := OrdinaryMackeySupport.ordinaryBijective K H incLK μ σ balance reps intersection
  obtain ⟨e, he⟩ := OrdinaryMackeySupport.coproduct.{u,v} K.subtype H.subtype incLK μ σ
    balance bijective
  -- Mathlib induction indexes the first tensor factor by its inverse.
  -- For the regular module the checked comparison evaluates g ⊗ x as
  -- g times the image of x, and intertwines right multiplication.
  let c := OrdinaryMackeySupport.regularComparison.{u,v} K.subtype H.subtype
  refine ⟨e, c, ?_, OrdinaryMackeySupport.regularComparison_right K.subtype H.subtype, ?_⟩
  · intro g
    change c.hom (OrdinaryMackeySupport.tmul H.subtype regularH g (ULift.up 1)) = _
    rw [OrdinaryMackeySupport.regularComparison_apply_pure]
    change ULift.up (MonoidAlgebra.of Complex G g *
      MonoidAlgebra.mapDomainAlgHom Complex Complex H.subtype 1) = _
    rw [map_one, mul_one]
  · intro i k h
    change c.hom (e.inv.app regularH
      ((CategoryTheory.Limits.Sigma.ι S i).app regularH
        (OrdinaryMackeySupport.tmul (incLK i) ((Res (μ i)).obj regularH) k
          (ULift.up (MonoidAlgebra.of Complex H h))))) = _
    rw [he i regularH k, OrdinaryMackeySupport.regularComparison_apply_pure]
    change ULift.up (MonoidAlgebra.of Complex G ((k : G) * σ i) *
      MonoidAlgebra.mapDomainAlgHom Complex Complex H.subtype (MonoidAlgebra.of Complex H h)) = _
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single])
