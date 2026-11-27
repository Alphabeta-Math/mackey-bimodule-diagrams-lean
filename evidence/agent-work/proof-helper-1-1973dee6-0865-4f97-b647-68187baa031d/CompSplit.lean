import CompShared

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

open MackeyDiagrams CategoryTheory WattsFoundation.General
open scoped ModuleCat.Algebra

namespace DiagramFunctorProof
universe u v
variable {U : Type u} [Group U]


section WordComposition
variable {K L H : Subgroup U} (p : Word K L) (q : Word L H)

private noncomputable def wordPair :
    wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex] wordBimod.{u,v} (p.tensor q) :=
  ((LinearMap.llcomp Complex _ _ _) (lower (p.tensor q)).symm.toLinearMap).comp
    (((Biset.pairLinear Complex p.basis q.basis).compl₂ (lower q).toLinearMap).comp
      (lower p).toLinearMap)

private theorem wordPair_apply (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q b c = (lower (p.tensor q)).symm
      (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c)) := rfl

private theorem wordPair_left (a : MonoidAlgebra Complex K)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q (leftHom (wordBimod p) a b) c =
      leftHom (wordBimod (p.tensor q)) a (wordPair p q b c) := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
    rw [left_of (wordBimod.{u,v} p) k b, left_of (wordBimod.{u,v} (p.tensor q)) k]
    apply (lower (p.tensor q)).injective
    change Biset.pairLinear Complex p.basis q.basis
        (p.basis.actLinear Complex (k, 1) (lower p b)) (lower q c) =
      (p.basis.tensor q.basis).actLinear Complex (k, 1)
        (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c))
    simpa only [← Prod.one_eq_mk, Biset.actLinear_one, LinearMap.id_apply] using
      Biset.pairLinear_action Complex p.basis q.basis (k, 1) (1, 1) (k, 1)
        (fun s t => by
          change p.basis.pair q.basis _ _ = p.basis.pair q.basis _ _
          rw [show q.basis.act (1, 1) t = t from q.basis.one_act t])
        (lower p b) (lower q c)
  | add a d ha hd => simp only [map_add, LinearMap.add_apply, ha, hd]
  | smul z a ha => simp only [map_smul, LinearMap.smul_apply, ha]

private theorem wordPair_right (a : MonoidAlgebra Complex H)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q b (rightHom (wordBimod q) (MulOpposite.op a) c) =
      rightHom (wordBimod (p.tensor q)) (MulOpposite.op a) (wordPair p q b c) := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
    rw [right_of (wordBimod.{u,v} q) h c, right_of (wordBimod.{u,v} (p.tensor q)) h]
    apply (lower (p.tensor q)).injective
    change Biset.pairLinear Complex p.basis q.basis
        (lower p b) (q.basis.actLinear Complex (1, h⁻¹) (lower q c)) =
      (p.basis.tensor q.basis).actLinear Complex (1, h⁻¹)
        (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c))
    simpa only [← Prod.one_eq_mk, Biset.actLinear_one, LinearMap.id_apply] using
      Biset.pairLinear_action Complex p.basis q.basis (1, 1) (1, h⁻¹) (1, h⁻¹)
        (fun s t => by
          change p.basis.pair q.basis _ _ = p.basis.pair q.basis _ _
          rw [show p.basis.act (1, 1) s = s from p.basis.one_act s])
        (lower p b) (lower q c)
  | add a d ha hd => simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, ha, hd]
  | smul z a ha => simp only [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, ha]

private theorem wordPairUP {M : Type (max u v)} [AddCommGroup M] [Module Complex M]
    (f : wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex] M)
    (hf : ∀ (a : MonoidAlgebra Complex L) b c,
      f (rightHom (wordBimod p) (MulOpposite.op a) b) c =
      f b (leftHom (wordBimod q) a c)) :
    ∃! g : wordBimod.{u,v} (p.tensor q) →ₗ[Complex] M, ∀ b c, g (wordPair p q b c) = f b c := by
  let f' := (f.compl₂ (lower q).symm.toLinearMap).comp (lower p).symm.toLinearMap
  -- The biset relation acts diagonally. The right algebra action uses the inverse.
  have hf' : Biset.IsBalanced f' := by
    intro l b c
    have e := hf (MonoidAlgebra.of Complex L l)
      ((lower p).symm (p.basis.actLinear Complex (1,l) b)) ((lower q).symm c)
    rw [right_of, left_of] at e
    have undo : (p.basis.actLinear Complex (1,l⁻¹)).comp (p.basis.actLinear Complex (1,l)) =
        LinearMap.id := by
      apply Finsupp.lhom_ext
      intro s r
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Biset.actLinear_single,
        ← Biset.mul_act, Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, Biset.one_act]
    have e' : p.basis.actLinear Complex (1,l⁻¹) (p.basis.actLinear Complex (1,l) b) = b :=
      LinearMap.congr_fun undo b
    change f ((lower p).symm (p.basis.actLinear Complex (1,l⁻¹)
          (p.basis.actLinear Complex (1,l) b))) ((lower q).symm c) =
      f ((lower p).symm (p.basis.actLinear Complex (1,l) b))
        ((lower q).symm (q.basis.actLinear Complex (l,1) c)) at e
    rw [e'] at e
    exact e.symm
  let g := Biset.liftBalanced f' hf'
  have hg := Biset.liftBalanced_pairLinear f' hf'
  refine ⟨g.comp (lower (p.tensor q)).toLinearMap, ?_, ?_⟩
  · intro b c
    change g (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c)) = f b c
    simpa only [f', LinearMap.comp_apply, LinearMap.compl₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using hg (lower p b) (lower q c)
  · intro k hk
    have e : k.comp (lower (p.tensor q)).symm.toLinearMap = g := by
      apply Biset.liftBalanced_unique f' hf'
      intro b c
      change k ((lower (p.tensor q)).symm (Biset.pairLinear Complex p.basis q.basis b c)) =
        f ((lower p).symm b) ((lower q).symm c)
      let x : wordBimod.{u,v} p := (lower p).symm b
      let y : wordBimod.{u,v} q := (lower q).symm c
      have he := hk x y
      rw [wordPair_apply p q x y] at he
      simpa only [x, y, LinearEquiv.apply_symm_apply] using he
    apply LinearMap.ext
    intro y
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      LinearMap.congr_fun e (lower (p.tensor q) y)

end WordComposition

section TensorPureGeneration
variable {K H : Type u} [Group K] [Group H]
variable (B : BM.{u,v} K H) (X : Mod.{u,v} H)

private theorem pure_linear_ext {M : Type (max u v)} [AddCommGroup M] [Module Complex M]
    {f g : V ((tensor B).obj X) →ₗ[Complex] M}
    (eq : ∀ b x, f (pure B X b x) = g (pure B X b x)) : f = g := by
  let Y := (tensor B).obj X
  let S : Set Y := Set.range fun bx : B × X => rawPure B X bx.1 bx.2
  -- The additive subgroup generated by pure tensors is stable under the left algebra.
  -- Its quotient map vanishes on pure tensors, so the Watts uniqueness law makes it zero.
  let A : AddSubgroup Y := AddSubgroup.closure S
  have stable (a : MonoidAlgebra Complex K) :
      A ≤ A.comap (smulAddHom (MonoidAlgebra Complex K) Y a) := by
    apply (AddSubgroup.closure_le _).2
    rintro _ ⟨⟨b,x⟩, rfl⟩
    change a • rawPure B X b x ∈ A
    have e : rawPure B X (leftHom B a b) x = a • rawPure B X b x :=
      (rawUniversal B X).1.2.2.1 a b x
    rw [← e]
    exact AddSubgroup.subset_closure ⟨(leftHom B a b, x), rfl⟩
  let A' : Submodule (MonoidAlgebra Complex K) Y :=
    { A with smul_mem' := fun a _ h => stable a h }
  have hp (b : B) (x : X) : rawPure B X b x ∈ A' :=
    AddSubgroup.subset_closure ⟨(b, x), rfl⟩
  have hz : ModuleCat.ofHom A'.mkQ = (0 : Y ⟶ ModuleCat.of (GC K) (Y ⧸ A')) := by
    apply hom_ext_pure B X
    intro b x
    exact (Submodule.Quotient.mk_eq_zero A').2 (hp b x)
  let E : AddSubgroup Y :=
    { carrier := { y | f (show V Y from y) = g (show V Y from y) }
      zero_mem' := by
        change f (0 : V Y) = g (0 : V Y)
        rw [map_zero, map_zero]
      add_mem' := fun {a b} ha hb => by
        change f (a + b) = g (a + b)
        rw [map_add, map_add, show f a = g a from ha, show f b = g b from hb]
      neg_mem' := fun {a} ha => by
        change f (-a) = g (-a)
        rw [map_neg, map_neg, show f a = g a from ha] }
  have hAE : A ≤ E := (AddSubgroup.closure_le E).2 (by
    rintro _ ⟨⟨b,x⟩, rfl⟩
    exact eq b x)
  apply LinearMap.ext
  intro y
  have hzero : A'.mkQ y = 0 := congrArg (fun h => ModuleCat.Hom.hom h y) hz
  exact hAE ((Submodule.Quotient.mk_eq_zero A').1 hzero)

end TensorPureGeneration

section WordComposition
variable {K L H : Subgroup U} (p : Word K L) (q : Word L H)

private theorem wordPair_middle (a : MonoidAlgebra Complex L)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    wordPair p q (rightHom (wordBimod p) (MulOpposite.op a) b) c =
      wordPair p q b (leftHom (wordBimod q) a c) := by
  induction a using MonoidAlgebra.induction_on with
  | of l =>
    rw [left_of (wordBimod.{u,v} q) l c, right_of (wordBimod.{u,v} p) l b]
    rw [wordPair_apply p q ((wordBimod.{u,v} p).ρ (1,l⁻¹) b) c,
      wordPair_apply p q b ((wordBimod.{u,v} q).ρ (l,1) c)]
    apply congrArg (lower (p.tensor q)).symm
    change Biset.pairLinear Complex p.basis q.basis
        (p.basis.actLinear Complex (1, l⁻¹) (lower p b)) (lower q c) =
      Biset.pairLinear Complex p.basis q.basis (lower p b)
        (q.basis.actLinear Complex (l, 1) (lower q c))
    have E := Biset.pairLinear_balance Complex p.basis q.basis l
      (p.basis.actLinear Complex (1, l⁻¹) (lower p b)) (lower q c)
    have inv : p.basis.actLinear Complex (1,l)
        (p.basis.actLinear Complex (1,l⁻¹) (lower p b)) = lower p b := by
      have e : (p.basis.actLinear Complex (1,l)).comp (p.basis.actLinear Complex (1,l⁻¹)) =
          LinearMap.id := by
        apply Finsupp.lhom_ext
        intro s r
        simp only [LinearMap.comp_apply, LinearMap.id_apply, Biset.actLinear_single,
          ← Biset.mul_act, Prod.mk_mul_mk, one_mul, mul_inv_cancel, ← Prod.one_eq_mk, Biset.one_act]
      exact LinearMap.congr_fun e _
    rw [inv] at E
    exact E.symm
  | add a d ha hd => simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, ha, hd]
  | smul z a ha => simp only [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, ha]

private theorem wordPair_ext {M : Type (max u v)} [AddCommGroup M] [Module Complex M]
    {f g : wordBimod.{u,v} (p.tensor q) →ₗ[Complex] M}
    (h : ∀ b c, f (wordPair p q b c) = g (wordPair p q b c)) : f = g := by
  let t := ((LinearMap.llcomp Complex _ _ _) f).comp (wordPair p q)
  have ht (a : MonoidAlgebra Complex L) (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
      t (rightHom (wordBimod p) (MulOpposite.op a) b) c =
        t b (leftHom (wordBimod q) a c) := by
    change f (wordPair p q (rightHom (wordBimod p) (MulOpposite.op a) b) c) =
      f (wordPair p q b (leftHom (wordBimod q) a c))
    rw [wordPair_middle p q]
  obtain ⟨_, _, uniq⟩ := wordPairUP p q t ht
  exact (uniq f (fun _ _ => rfl)).trans (uniq g (fun b c => (h b c).symm)).symm

private noncomputable def forwardTriple (X : Mod.{u,v} H) :
    wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex]
      V X →ₗ[Complex] V ((T q ⋙ T p).obj X) :=
  { toFun := fun b => ((LinearMap.llcomp Complex _ _ _)
        (pure (wordBimod p) ((T q).obj X) b)).comp (pure (wordBimod q) X)
    map_add' := fun b d => by
      apply LinearMap.ext
      intro c
      apply LinearMap.ext
      intro x
      simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.llcomp_apply]
    map_smul' := fun z b => by
      apply LinearMap.ext
      intro c
      apply LinearMap.ext
      intro x
      simp only [RingHom.id_apply, map_smul, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.llcomp_apply] }

private theorem forwardTriple_balanced (X : Mod.{u,v} H) (a : MonoidAlgebra Complex L)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    forwardTriple p q X (rightHom (wordBimod p) (MulOpposite.op a) b) c =
      forwardTriple p q X b (leftHom (wordBimod q) a c) := by
  apply LinearMap.ext
  intro x
  change pure (wordBimod p) ((T q).obj X) (rightHom (wordBimod p) (MulOpposite.op a) b)
      (pure (wordBimod q) X c x) =
    pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X (leftHom (wordBimod q) a c) x)
  rw [(universal (wordBimod p) ((T q).obj X)).1.2 a b,
    (universal (wordBimod q) X).1.1 a c]

private noncomputable def forwardPairing (X : Mod.{u,v} H) :
    wordBimod.{u,v} (p.tensor q) →ₗ[Complex] V X →ₗ[Complex] V ((T q ⋙ T p).obj X) :=
  Classical.choose ((wordPairUP p q (forwardTriple p q X) (forwardTriple_balanced p q X)).exists)

private theorem forwardPairing_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    forwardPairing p q X (wordPair p q b c) x =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x) := by
  exact LinearMap.congr_fun
    (Classical.choose_spec ((wordPairUP p q (forwardTriple p q X)
      (forwardTriple_balanced p q X)).exists) b c) x

private theorem forwardPairing_balanced (X : Mod.{u,v} H) :
    Balanced (wordBimod (p.tensor q)) X ((T q ⋙ T p).obj X) (forwardPairing p q X) := by
  constructor
  · intro a d x
    let Y := (T q ⋙ T p).obj X
    let act : V Y →ₗ[Complex] V Y := RestrictScalars.lsmul Complex (MonoidAlgebra Complex K) Y a
    have e : ((forwardPairing p q X).flip x).comp (leftHom (wordBimod (p.tensor q)) a) =
        act.comp ((forwardPairing p q X).flip x) := by
      apply wordPair_ext p q
      intro b c
      change forwardPairing p q X (leftHom (wordBimod (p.tensor q)) a (wordPair p q b c)) x =
        a • (show Y from forwardPairing p q X (wordPair p q b c) x)
      rw [← wordPair_left p q, forwardPairing_pure, forwardPairing_pure]
      exact (universal (wordBimod p) ((T q).obj X)).1.1 a b _
    exact LinearMap.congr_fun e d
  · intro a d x
    have e : ((forwardPairing p q X).flip x).comp
        (rightHom (wordBimod (p.tensor q)) (MulOpposite.op a)) =
        (forwardPairing p q X).flip (a • (show X from x)) := by
      apply wordPair_ext p q
      intro b c
      change forwardPairing p q X (rightHom (wordBimod (p.tensor q)) (MulOpposite.op a)
        (wordPair p q b c)) x = forwardPairing p q X (wordPair p q b c) (a • (show X from x))
      rw [← wordPair_right p q, forwardPairing_pure, forwardPairing_pure,
        (universal (wordBimod q) X).1.2 a c x]
    exact LinearMap.congr_fun e d

private noncomputable def compHom (X : Mod.{u,v} H) :
    (T (p.tensor q)).obj X ⟶ (T q ⋙ T p).obj X :=
  Classical.choose (((universal (wordBimod (p.tensor q)) X).2 _
    (forwardPairing p q X) (forwardPairing_balanced p q X)).exists)

private theorem compHom_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    VMap (compHom p q X) (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x) =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x) :=
  (Classical.choose_spec (((universal (wordBimod (p.tensor q)) X).2 _
    (forwardPairing p q X) (forwardPairing_balanced p q X)).exists) (wordPair p q b c) x).trans
      (forwardPairing_pure p q X b c x)

-- Right multiplication on the source gives a left action on the space of linear maps.
private noncomputable def homAction (Y : Mod.{u,v} K) :
    MonoidAlgebra Complex L →+* Module.End Complex (wordBimod.{u,v} p →ₗ[Complex] V Y) where
  toFun a := LinearMap.lcomp Complex (V Y) (rightHom (wordBimod p) (MulOpposite.op a))
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_zero, map_zero, LinearMap.zero_apply]
  map_one' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_one, map_one, one_apply_eq_self]
  map_add' a d := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_add, map_add, LinearMap.add_apply]
  map_mul' a d := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    simp only [LinearMap.lcomp_apply, MulOpposite.op_mul, map_mul, mul_apply_eq_comp]

private noncomputable def homMod (Y : Mod.{u,v} K) : Mod.{u,v} L := by
  letI : Module (MonoidAlgebra Complex L) (wordBimod.{u,v} p →ₗ[Complex] V Y) :=
    Module.compHom _ (homAction p Y)
  exact ModuleCat.of (GC L) (wordBimod.{u,v} p →ₗ[Complex] V Y)

private theorem homMod_smul (Y : Mod.{u,v} K) (a : MonoidAlgebra Complex L)
    (f : homMod p Y) (b : wordBimod.{u,v} p) :
    (show wordBimod.{u,v} p →ₗ[Complex] V Y from a • f) b =
      (show wordBimod.{u,v} p →ₗ[Complex] V Y from f)
        (rightHom (wordBimod p) (MulOpposite.op a) b) := rfl

private noncomputable def inverseTriple (X : Mod.{u,v} H) :
    wordBimod.{u,v} p →ₗ[Complex] wordBimod.{u,v} q →ₗ[Complex]
      V X →ₗ[Complex] V ((T (p.tensor q)).obj X) :=
  ((LinearMap.llcomp Complex _ _ _) (pure (wordBimod (p.tensor q)) X)).comp (wordPair p q)

private noncomputable def inverseCurry (X : Mod.{u,v} H) (c : wordBimod.{u,v} q) (x : X) :
    homMod p ((T (p.tensor q)).obj X) :=
  ((inverseTriple p q X).flip c).flip x

private theorem inverseCurry_apply (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from inverseCurry p q X c x) b =
      pure (wordBimod (p.tensor q)) X (wordPair p q b c) x := rfl

private theorem inverseInner_exists (X : Mod.{u,v} H) :
    ∃ g : (T q).obj X →ₗ[MonoidAlgebra Complex L] homMod p ((T (p.tensor q)).obj X),
      ∀ c x, g (rawPure (wordBimod q) X c x) = inverseCurry p q X c x := by
  apply ((rawUniversal (wordBimod q) X).2 _ (inverseCurry p q X) ?_).exists
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c d x
    change ((inverseTriple p q X).flip (c + d)).flip x =
      ((inverseTriple p q X).flip c).flip x + ((inverseTriple p q X).flip d).flip x
    apply LinearMap.ext
    intro b
    simp only [LinearMap.flip_apply, map_add, LinearMap.add_apply]
  · intro c x y
    change ((inverseTriple p q X).flip c).flip (x + y) =
      ((inverseTriple p q X).flip c).flip x + ((inverseTriple p q X).flip c).flip y
    apply LinearMap.ext
    intro b
    simp only [LinearMap.flip_apply, map_add, LinearMap.add_apply]
  · intro a c x
    change inverseCurry p q X (leftHom (wordBimod q) a c) x = a • inverseCurry p q X c x
    apply LinearMap.ext
    intro b
    rw [homMod_smul, inverseCurry_apply, inverseCurry_apply, wordPair_middle p q]
  · intro a c x
    change inverseCurry p q X (rightHom (wordBimod q) (MulOpposite.op a) c) x =
      inverseCurry p q X c (a • x)
    apply LinearMap.ext
    intro b
    rw [inverseCurry_apply, inverseCurry_apply, wordPair_right p q,
      (universal (wordBimod (p.tensor q)) X).1.2]

private noncomputable def inverseInner (X : Mod.{u,v} H) :
    V ((T q).obj X) →ₗ[Complex] wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) where
  toFun y :=
    let g := Classical.choose (inverseInner_exists p q X)
    g (show (T q).obj X from y)
  map_add' y z := by
    let g := Classical.choose (inverseInner_exists p q X)
    exact g.map_add (show (T q).obj X from y) (show (T q).obj X from z)
  map_smul' z y := by
    let g := Classical.choose (inverseInner_exists p q X)
    have e := g.map_smul (algebraMap Complex (GC L) z) (show (T q).obj X from y)
    apply LinearMap.ext
    intro b
    change (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from
        g ((algebraMap Complex (GC L) z) • (show (T q).obj X from y))) b =
      z • (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from g y) b
    rw [e, homMod_smul, rightHom_scalar, map_smul]

private theorem inverseInner_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    inverseInner p q X (pure (wordBimod q) X c x) b =
      pure (wordBimod (p.tensor q)) X (wordPair p q b c) x := by
  exact (congrArg (fun f : homMod p ((T (p.tensor q)).obj X) =>
    (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from f) b)
    (Classical.choose_spec (inverseInner_exists p q X) c x)).trans (inverseCurry_apply p q X b c x)

private theorem inverseInner_balanced (X : Mod.{u,v} H) :
    Balanced (wordBimod p) ((T q).obj X) ((T (p.tensor q)).obj X) (inverseInner p q X).flip := by
  constructor
  · intro a b y
    let Y := (T (p.tensor q)).obj X
    let act : V Y →ₗ[Complex] V Y := RestrictScalars.lsmul Complex (MonoidAlgebra Complex K) Y a
    have e : (inverseInner p q X).flip (leftHom (wordBimod p) a b) =
        act.comp ((inverseInner p q X).flip b) := by
      apply pure_linear_ext (wordBimod q) X
      intro c x
      change inverseInner p q X (pure (wordBimod q) X c x) (leftHom (wordBimod p) a b) =
        a • (show Y from inverseInner p q X (pure (wordBimod q) X c x) b)
      rw [inverseInner_pure, inverseInner_pure, wordPair_left p q,
        (universal (wordBimod (p.tensor q)) X).1.1]
    exact LinearMap.congr_fun e y
  · intro a b y
    let g := Classical.choose (inverseInner_exists p q X)
    have e := g.map_smul a (show (T q).obj X from y)
    exact (congrArg (fun f : homMod p ((T (p.tensor q)).obj X) =>
      (show wordBimod.{u,v} p →ₗ[Complex] V ((T (p.tensor q)).obj X) from f) b) e).symm

private noncomputable def compInv (X : Mod.{u,v} H) :
    (T q ⋙ T p).obj X ⟶ (T (p.tensor q)).obj X :=
  Classical.choose (((universal (wordBimod p) ((T q).obj X)).2 _
    (inverseInner p q X).flip (inverseInner_balanced p q X)).exists)

private theorem compInv_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    VMap (compInv p q X) (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x)) =
      pure (wordBimod (p.tensor q)) X (wordPair p q b c) x :=
  (Classical.choose_spec (((universal (wordBimod p) ((T q).obj X)).2 _
    (inverseInner p q X).flip (inverseInner_balanced p q X)).exists) b
      (pure (wordBimod q) X c x)).trans (inverseInner_pure p q X b c x)

private theorem word_tensor_hom_ext (X : Mod.{u,v} H) {Y : Mod.{u,v} K}
    {f g : (T (p.tensor q)).obj X ⟶ Y}
    (eq : ∀ b c x,
      VMap f (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x) =
      VMap g (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x)) : f = g := by
  apply hom_ext_pure (wordBimod (p.tensor q)) X
  intro d x
  have e : (VMap f).comp ((pure (wordBimod (p.tensor q)) X).flip x) =
      (VMap g).comp ((pure (wordBimod (p.tensor q)) X).flip x) := by
    apply wordPair_ext p q
    intro b c
    exact eq b c x
  exact LinearMap.congr_fun e d

private theorem nested_tensor_hom_ext (X : Mod.{u,v} H) {Y : Mod.{u,v} K}
    {f g : (T q ⋙ T p).obj X ⟶ Y}
    (eq : ∀ b c x,
      VMap f (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x)) =
      VMap g (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x))) : f = g := by
  apply hom_ext_pure (wordBimod p) ((T q).obj X)
  intro b y
  have e : (VMap f).comp (pure (wordBimod p) ((T q).obj X) b) =
      (VMap g).comp (pure (wordBimod p) ((T q).obj X) b) := by
    apply pure_linear_ext (wordBimod q) X
    intro c x
    exact eq b c x
  exact LinearMap.congr_fun e y

private noncomputable def compApp (X : Mod.{u,v} H) :
    (T (p.tensor q)).obj X ≅ (T q ⋙ T p).obj X where
  hom := compHom p q X
  inv := compInv p q X
  hom_inv_id := by
    apply word_tensor_hom_ext p q X
    intro b c x
    change VMap (compInv p q X)
      (VMap (compHom p q X) (pure (wordBimod (p.tensor q)) X (wordPair p q b c) x)) = _
    rw [compHom_pure, compInv_pure] <;> rfl
  inv_hom_id := by
    apply nested_tensor_hom_ext p q X
    intro b c x
    change VMap (compHom p q X)
      (VMap (compInv p q X) (pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x))) = _
    rw [compInv_pure, compHom_pure] <;> rfl

private noncomputable def compIso :
    T (p.tensor q) ≅ T q ⋙ T p :=
  NatIso.ofComponents (compApp p q) (by
    intro X Y f
    apply word_tensor_hom_ext p q X
    intro b c x
    let P := wordBimod.{u,v} p
    let Q := wordBimod.{u,v} q
    let R := wordBimod.{u,v} (p.tensor q)
    change VMap (compHom p q Y)
        (((tensor R).map f).hom (rawPure R X (wordPair p q b c) x)) =
      ((tensor P).map ((tensor Q).map f)).hom
        (VMap (compHom p q X) (pure R X (wordPair p q b c) x))
    have eR := rawMapInput R f (wordPair p q b c) x
    have eQ := rawMapInput Q f c x
    have eP := rawMapInput P ((tensor Q).map f) b (rawPure Q X c x)
    calc
      _ = VMap (compHom p q Y) (pure R Y (wordPair p q b c) (f.hom x)) :=
        congrArg (VMap (compHom p q Y)) eR
      _ = rawPure P ((tensor Q).obj Y) b (rawPure Q Y c (f.hom x)) :=
        compHom_pure p q Y b c (f.hom x)
      _ = rawPure P ((tensor Q).obj Y) b (((tensor Q).map f).hom (rawPure Q X c x)) :=
        congrArg (rawPure P ((tensor Q).obj Y) b) eQ.symm
      _ = ((tensor P).map ((tensor Q).map f)).hom (rawPure P ((tensor Q).obj X) b (rawPure Q X c x)) :=
        eP.symm
      _ = _ := congrArg (((tensor P).map ((tensor Q).map f)).hom) (compHom_pure p q X b c x).symm)

private theorem compIso_pure (X : Mod.{u,v} H) (b : wordBimod.{u,v} p)
    (c : wordBimod.{u,v} q) (x : V X) :
    VMap ((compIso p q).hom.app X)
      (pure (wordBimod (p.tensor q)) X
        ((lower (p.tensor q)).symm (Biset.pairLinear Complex p.basis q.basis (lower p b) (lower q c))) x) =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x) :=
  compHom_pure p q X b c x

#print axioms compIso
#print axioms compIso_pure

end WordComposition
end DiagramFunctorProof
