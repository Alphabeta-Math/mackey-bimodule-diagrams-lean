
namespace DiagramFunctorProof

open CategoryTheory

universe u v w i j

private abbrev StrandBalanced {R S : Type u} [Ring R] [Ring S]
    {N : Type i} [AddCommGroup N] (left : S → N → N) (right : R → N → N)
    (X : ModuleCat.{w} R) (Y : ModuleCat.{w} S) (t : N → X → Y) : Prop :=
  (∀ n m x, t (n + m) x = t n x + t m x) ∧
  (∀ n x y, t n (x + y) = t n x + t n y) ∧
  (∀ s n x, t (left s n) x = s • t n x) ∧
  (∀ r n x, t (right r n) x = t n (r • x))

private abbrev StrandPresentation {R S : Type u} [Ring R] [Ring S]
    {N : Type i} [AddCommGroup N] (left : S → N → N) (right : R → N → N)
    {F : ModuleCat.{w} R ⥤ ModuleCat.{w} S}
    (τ : ∀ X : ModuleCat.{w} R, N → X → F.obj X) : Prop :=
  (∀ X, StrandBalanced left right X (F.obj X) (τ X)) ∧
  (∀ (X : ModuleCat.{w} R) (Y : ModuleCat.{w} S) (t : N → X → Y),
     StrandBalanced left right X Y t →
       ∃! f : F.obj X →ₗ[S] Y, ∀ n x, f (τ X n x) = t n x) ∧
  (∀ (X Y : ModuleCat.{w} R) (f : X ⟶ Y) n x,
    (F.map f).hom (τ X n x) = τ Y n (f.hom x))

section Compare

variable {R S : Type u} [Ring R] [Ring S]
  {N : Type i} [AddCommGroup N] [Module Complex N]
  {P : Type j} [AddCommGroup P] [Module Complex P]
  {lN : S → N → N} {rN : R → N → N}
  {lP : S → P → P} {rP : R → P → P}
  {F G : ModuleCat.{w} R ⥤ ModuleCat.{w} S}
  {σ : ∀ X : ModuleCat.{w} R, N → X → F.obj X}
  {τ : ∀ X : ModuleCat.{w} R, P → X → G.obj X}

omit [Module Complex N] in
private theorem strand_hom_ext (hσ : StrandPresentation lN rN σ)
    {X : ModuleCat.{w} R} {Y : ModuleCat.{w} S} {f g : F.obj X ⟶ Y}
    (h : ∀ n x, f.hom (σ X n x) = g.hom (σ X n x)) : f = g := by
  have hb := hσ.1 X
  have hg : StrandBalanced lN rN X Y (fun n x => g.hom (σ X n x)) :=
    ⟨fun n m x => (congrArg g.hom (hb.1 n m x)).trans (g.hom.map_add _ _),
     fun n x y => (congrArg g.hom (hb.2.1 n x y)).trans (g.hom.map_add _ _),
     fun s n x => (congrArg g.hom (hb.2.2.1 s n x)).trans (g.hom.map_smul s _),
     fun r n x => congrArg g.hom (hb.2.2.2 r n x)⟩
  obtain ⟨lift, _, uniq⟩ := hσ.2.1 X Y _ hg
  exact ModuleCat.hom_injective ((uniq f.hom h).trans (uniq g.hom (fun _ _ => rfl)).symm)

variable (e : N ≃ₗ[Complex] P)
    (el : ∀ s n, e (lN s n) = lP s (e n))
    (er : ∀ r n, e (rN r n) = rP r (e n))
    (hσ : StrandPresentation lN rN σ) (hτ : StrandPresentation lP rP τ)

include el er hσ hτ in
private theorem strand_component_exists (X : ModuleCat.{w} R) :
    ∃! f : F.obj X →ₗ[S] G.obj X, ∀ n x, f (σ X n x) = τ X (e n) x := by
  have hb := hτ.1 X
  apply hσ.2.1 X (G.obj X) (fun n x => τ X (e n) x)
  refine ⟨?_, fun n x y => hb.2.1 (e n) x y, ?_, ?_⟩
  · intro n m x
    simpa only [e.map_add] using hb.1 (e n) (e m) x
  · intro s n x
    simpa only [el] using hb.2.2.1 s (e n) x
  · intro r n x
    simpa only [er] using hb.2.2.2 r (e n) x

private noncomputable def strand_component (X : ModuleCat.{w} R) : F.obj X ⟶ G.obj X :=
  ModuleCat.ofHom (Classical.choose (strand_component_exists e el er hσ hτ X))

private theorem strand_component_pure (X : ModuleCat.{w} R) (n : N) (x : X) :
    (strand_component e el er hσ hτ X).hom (σ X n x) = τ X (e n) x :=
  (Classical.choose_spec (strand_component_exists e el er hσ hτ X)).1 n x

private noncomputable def strand_hom : F ⟶ G where
  app := strand_component e el er hσ hτ
  naturality {X Y} f := by
    apply strand_hom_ext hσ
    intro n x
    change (strand_component e el er hσ hτ Y).hom ((F.map f).hom (σ X n x)) =
      (G.map f).hom ((strand_component e el er hσ hτ X).hom (σ X n x))
    rw [hσ.2.2, strand_component_pure, strand_component_pure, hτ.2.2]

private theorem strand_hom_pure (X : ModuleCat.{w} R) (n : N) (x : X) :
    ((strand_hom e el er hσ hτ).app X).hom (σ X n x) = τ X (e n) x :=
  strand_component_pure e el er hσ hτ X n x

include el in
private theorem strand_symm_left (s : S) (p : P) :
    e.symm (lP s p) = lN s (e.symm p) :=
  e.injective (by rw [e.apply_symm_apply, el, e.apply_symm_apply])

include er in
private theorem strand_symm_right (r : R) (p : P) :
    e.symm (rP r p) = rN r (e.symm p) :=
  e.injective (by rw [e.apply_symm_apply, er, e.apply_symm_apply])

private noncomputable def strand_iso : F ≅ G where
  hom := strand_hom e el er hσ hτ
  inv := strand_hom e.symm (strand_symm_left e el) (strand_symm_right e er) hτ hσ
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    apply strand_hom_ext hσ
    intro n x
    change ((strand_hom e.symm _ _ hτ hσ).app X).hom
        (((strand_hom e el er hσ hτ).app X).hom (σ X n x)) = σ X n x
    rw [strand_hom_pure, strand_hom_pure, e.symm_apply_apply]
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    apply strand_hom_ext hτ
    intro p x
    change ((strand_hom e el er hσ hτ).app X).hom
        (((strand_hom e.symm _ _ hτ hσ).app X).hom (τ X p x)) = τ X p x
    rw [strand_hom_pure, strand_hom_pure, e.apply_symm_apply]

private theorem strand_iso_pure (X : ModuleCat.{w} R) (n : N) (x : X) :
    ((strand_iso e el er hσ hτ).hom.app X).hom (σ X n x) = τ X (e n) x :=
  strand_hom_pure e el er hσ hτ X n x

end Compare

end DiagramFunctorProof

namespace DiagramFunctorProof

open CategoryTheory

universe u v

variable {U : Type u} [Group U]

private noncomputable def wordCoeffIso {K H G : Subgroup U} (p : Word K H)
    (h : p.basis.carrier = G) : wordBimod.{u,v} p ≃ₗ[Complex] MonoidAlgebra Complex G :=
  let coeff : (G →₀ Complex) ≃ₗ[Complex] MonoidAlgebra Complex G :=
    (MonoidAlgebra.coeffLinearEquiv Complex).symm
  (lower p).trans (cast (congrArg (fun C : Type u =>
    (C →₀ Complex) ≃ₗ[Complex] MonoidAlgebra Complex G) h.symm) coeff)

private theorem wordPresentation {K H : Subgroup U} (p : Word K H) :
    StrandPresentation (fun s b => leftHom (wordBimod.{u,v} p) s b)
      (fun r => rightHom (wordBimod.{u,v} p) (MulOpposite.op r))
      (rawPure (wordBimod.{u,v} p)) :=
  ⟨fun X => (rawUniversal (wordBimod p) X).1,
   fun X => (rawUniversal (wordBimod p) X).2,
   fun _ _ => rawMapInput (wordBimod p)⟩

private theorem strandActions {K H : Type u} [Group K] [Group H]
    {B : BM.{u,v} K H} {A : Type u} [Ring A] [Algebra Complex A]
    (e : B ≃ₗ[Complex] A) (L : MonoidAlgebra Complex K →ₐ[Complex] A)
    (R : MonoidAlgebra Complex H →ₐ[Complex] A)
    (h : ∀ k h b, e (B.ρ (k, h⁻¹) b) =
      L (MonoidAlgebra.of Complex K k) * (e b * R (MonoidAlgebra.of Complex H h))) :
    (∀ s b, e (leftHom B s b) = L s * e b) ∧
    (∀ r b, e (rightHom B (MulOpposite.op r) b) = e b * R r) := by
  constructor
  · intro s b
    induction s using MonoidAlgebra.induction_on with
    | of k =>
        rw [left_of]
        simpa only [inv_one, map_one, mul_one] using h k 1 b
    | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, add_mul, ha, ha']
    | smul z a ha => simp only [map_smul, LinearMap.smul_apply, smul_mul_assoc, ha]
  · intro r b
    induction r using MonoidAlgebra.induction_on with
    | of h' =>
        rw [right_of]
        simpa only [map_one, one_mul] using h 1 h' b
    | add a a' ha ha' =>
        simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, mul_add, ha, ha']
    | smul z a ha =>
        simp only [MulOpposite.op_smul, map_smul, LinearMap.smul_apply, mul_smul_comm, ha]

private theorem regularWord_group (H : Subgroup U) (k h : H)
    (x : MonoidAlgebra Complex H) :
    MonoidAlgebra.ofCoeff
      (Finsupp.lmapDomain Complex Complex (fun z : H => k * z * h) x.coeff) =
      MonoidAlgebra.single k 1 * (x * MonoidAlgebra.single h 1) := by
  induction x using MonoidAlgebra.induction_on with
  | of z =>
      simp [MonoidAlgebra.of_apply, Finsupp.lmapDomain_apply,
        MonoidAlgebra.single_mul_single, mul_assoc]
  | add x y hx hy =>
      simp only [MonoidAlgebra.coeff_add, map_add, MonoidAlgebra.ofCoeff_add, add_mul,
        mul_add, hx, hy]
  | smul r x hx =>
      simp only [MonoidAlgebra.coeff_smul, map_smul, MonoidAlgebra.ofCoeff_smul,
        smul_mul_assoc, mul_smul_comm, hx]

private theorem regularWord_actions (H : Subgroup U) :
    let e := wordCoeffIso.{u,v} (G := H) (Word.empty H) rfl
    (∀ s b, e (leftHom (wordBimod (Word.empty H)) s b) = s * e b) ∧
    (∀ r b, e (rightHom (wordBimod (Word.empty H)) (MulOpposite.op r) b) = e b * r) := by
  let p := Word.empty H
  let e := wordCoeffIso.{u,v} (G := H) p rfl
  apply strandActions e (AlgHom.id _ _) (AlgHom.id _ _)
  intro k h b
  change MonoidAlgebra.ofCoeff
      (Finsupp.lmapDomain Complex Complex (fun z : H => k * z * (h⁻¹)⁻¹) (lower p b)) =
    MonoidAlgebra.single k 1 * ((e b) * MonoidAlgebra.single h 1)
  rw [inv_inv]
  exact regularWord_group H k h (e b)

private theorem identityPresentation (H : Subgroup U) :
    StrandPresentation (F := 𝟭 (Mod.{u,v} H))
      (fun (s b : MonoidAlgebra Complex H) => s * b) (fun r b => b * r)
      (fun X b x => b • x) := by
  refine ⟨fun X => ⟨fun n m x => add_smul n m x, fun n x y => smul_add n x y,
    fun s n x => mul_smul s n x, fun r n x => mul_smul n r x⟩, ?_, ?_⟩
  · intro X Y t ht
    have at_one (b : MonoidAlgebra Complex H) (x : X) : t b x = t 1 (b • x) := by
      simpa only [one_mul] using ht.2.2.2 b 1 x
    let f : X →ₗ[MonoidAlgebra Complex H] Y :=
      { toFun := t 1
        map_add' := ht.2.1 1
        map_smul' := fun r x => by
          change t 1 (r • x) = r • t 1 x
          rw [← at_one]
          simpa only [mul_one] using ht.2.2.1 r 1 x }
    refine ⟨f, fun b x => (at_one b x).symm, ?_⟩
    intro g hg
    apply LinearMap.ext
    intro x
    change g x = t 1 x
    simpa only [one_smul] using hg 1 x
  · intro X Y f b x
    exact f.hom.map_smul b x

private noncomputable def emptyIso (H : Subgroup U) :
    T.{u,v} (Word.empty H) ≅ 𝟭 (Mod.{u,v} H) :=
  strand_iso (wordCoeffIso (G := H) (Word.empty H) rfl)
    (regularWord_actions H).1 (regularWord_actions H).2
    (wordPresentation (Word.empty H)) (identityPresentation H)

private theorem emptyIso_pure (H : Subgroup U) (X : Mod.{u,v} H)
    (b : wordBimod.{u,v} (Word.empty H)) (x : V X) :
    VMap ((emptyIso H).hom.app X) (DiagramFunctorProof.pure (wordBimod (Word.empty H)) X b x) =
      (MonoidAlgebra.ofCoeff (lower (Word.empty H) b) : MonoidAlgebra Complex H) • (show X from x) :=
  strand_iso_pure (wordCoeffIso (G := H) (Word.empty H) rfl)
    (regularWord_actions H).1 (regularWord_actions H).2
    (wordPresentation (Word.empty H)) (identityPresentation H) X b x

private noncomputable abbrev strandPhi {H G : Subgroup U} (a : ConjEmbedding H G) :=
  MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom

private noncomputable abbrev strandInd {H G : Subgroup U} (a : ConjEmbedding H G) :
    Func.{u,v} G H :=
  (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H) ⋙ Rep.indFunctor Complex a.toHom) ⋙
    Rep.toModuleMonoidAlgebra (k := Complex) (G := G)

private noncomputable abbrev strandRes {H G : Subgroup U} (a : ConjEmbedding H G) :
    Func.{u,v} H G :=
  ModuleCat.restrictScalars (strandPhi a).toRingHom

private theorem strandIsos {H G : Subgroup U} (a : ConjEmbedding H G) :
    Nonempty (T.{u,v} (Word.up a) ≅ strandInd a) ∧
    Nonempty (T.{u,v} (Word.down a) ≅ strandRes a) := by
  obtain ⟨α, hα⟩ := a.hasRepresentative
  have hmem (h : H) : α * (h : U) * α⁻¹ ∈ G := hα h ▸ (a.toHom h).property
  have ha : a = ConjEmbedding.ofConjugator α hmem :=
    ConjEmbedding.ext (MonoidHom.ext fun h => Subtype.ext (hα h))
  rw [ha]
  let a := ConjEmbedding.ofConjugator α hmem
  obtain ⟨I, D, hIleft, hIright, hDleft, hDright, hIgroup, hDgroup, hInd, hRes⟩ :=
    (InductionRestrictionBimoduleStrands.{u,v,u}).1 H G α hmem |>.2.2
  let eu := wordCoeffIso.{u,v} (G := G) (Word.up a) rfl
  let ed := wordCoeffIso.{u,v} (G := G) (Word.down a) rfl
  have upGroup (k : G) (h : H) (b : wordBimod.{u,v} (Word.up a)) :
      eu ((wordBimod (Word.up a)).ρ (k, h⁻¹) b) =
        AlgHom.id Complex (MonoidAlgebra Complex G) (MonoidAlgebra.of Complex G k) *
          (eu b * strandPhi a (MonoidAlgebra.of Complex H h)) := by
    change MonoidAlgebra.ofCoeff
        (Biset.actLinear Complex (Word.up a).basis (k, h⁻¹) (lower (Word.up a) b)) =
      MonoidAlgebra.single k 1 * (eu b * strandPhi a (MonoidAlgebra.single h 1))
    have hcoeff : (eu b).coeff = lower (Word.up a) b := rfl
    have hg := hIgroup k h (eu b)
    rw [hIleft, hIright, hcoeff] at hg
    exact hg
  have downGroup (h : H) (k : G) (b : wordBimod.{u,v} (Word.down a)) :
      ed ((wordBimod (Word.down a)).ρ (h, k⁻¹) b) =
        strandPhi a (MonoidAlgebra.of Complex H h) *
          (ed b * AlgHom.id Complex (MonoidAlgebra Complex G) (MonoidAlgebra.of Complex G k)) := by
    change MonoidAlgebra.ofCoeff
        (Biset.actLinear Complex (Word.down a).basis (h, k⁻¹) (lower (Word.down a) b)) =
      strandPhi a (MonoidAlgebra.single h 1) * (ed b * MonoidAlgebra.single k 1)
    have hcoeff : (ed b).coeff = lower (Word.down a) b := rfl
    have hg := hDgroup h k (ed b)
    rw [hDleft, hDright, hcoeff] at hg
    exact hg
  obtain ⟨ul, ur⟩ := strandActions eu (AlgHom.id _ _) (strandPhi a) upGroup
  obtain ⟨dl, dr⟩ := strandActions ed (strandPhi a) (AlgHom.id _ _) downGroup
  obtain ⟨σ, hσ⟩ := hInd
  obtain ⟨τ, hτ⟩ := hRes
  have hu : StrandPresentation (F := strandInd.{u,v} a)
      (fun s b => s * b) (fun r b => b * strandPhi a r) σ := by
    simpa only [StrandPresentation, StrandBalanced, hIleft, hIright] using hσ
  have hd : StrandPresentation (F := strandRes.{u,v} a)
      (fun r b => strandPhi a r * b) (fun s b => b * s) τ := by
    simpa only [StrandPresentation, StrandBalanced, hDleft, hDright] using hτ
  exact ⟨⟨strand_iso eu ul ur (wordPresentation (Word.up a)) hu⟩,
         ⟨strand_iso ed dl dr (wordPresentation (Word.down a)) hd⟩⟩

end DiagramFunctorProof

#print axioms DiagramFunctorProof.emptyIso
#print axioms DiagramFunctorProof.emptyIso_pure
#print axioms DiagramFunctorProof.strandIsos
