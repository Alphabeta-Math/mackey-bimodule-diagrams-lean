
namespace GeneralizedMackeySupport

open CategoryTheory CategoryTheory.Limits Representation
open scoped TensorProduct MonoidAlgebra
universe u v
noncomputable section

set_option maxHeartbeats 2000000

variable {H K G L : Type u} [Group H] [Group K] [Group G] [Group L]

private abbrev pure (b : H →* G) (X : Rep.{v} Complex H) (g : G) :=
  IndV.mk b X.ρ g⁻¹

private theorem pure_balance (b : H →* G) (X : Rep.{v} Complex H) (g : G) (h : H)
    (x : X) : pure b X (g * b h) x = pure b X g (X.ρ h x) := by
  change Coinvariants.mk (Representation.tprod ((leftRegular Complex G).comp b) X.ρ) ((MonoidAlgebra.single ((g * b h)⁻¹) (1 : Complex)) ⊗ₜ[Complex] x) = _
  rw [mul_inv_rev]
  simpa [ofMulAction_single] using Coinvariants.mk_inv_tmul ((leftRegular Complex G).comp b) X.ρ
    (.single g⁻¹ 1) x h

private theorem pure_act (b : H →* G) (X : Rep.{v} Complex H) (g t : G) (x : X) :
    ind b X.ρ t (pure b X g x) = pure b X (t * g) x := by
  simp [pure, mul_inv_rev]

private theorem pure_map (b : H →* G) {X Y : Rep.{v} Complex H} (f : X ⟶ Y)
    (g : G) (x : X) :
    (Rep.indMap b f).hom (pure b X g x) = pure b Y g (f.hom x) := rfl

private theorem pure_ext (b : H →* G) (X : Rep.{v} Complex H)
    {Y : Type v} [AddCommGroup Y] [Module Complex Y]
    {f f' : IndV b X.ρ →ₗ[Complex] Y}
    (h : ∀ g x, f (pure b X g x) = f' (pure b X g x)) : f = f' := by
  apply IndV.hom_ext
  intro g
  exact LinearMap.ext (fun x => by simpa only [pure, inv_inv, LinearMap.coe_comp, Function.comp_apply] using h g⁻¹ x)

private def liftPure (b : H →* G) (X : Rep.{v} Complex H)
    {Y : Type v} [AddCommGroup Y] [Module Complex Y]
    (F : G → X →ₗ[Complex] Y)
    (bal : ∀ g h x, F (g * b h) x = F g (X.ρ h x)) :
    IndV b X.ρ →ₗ[Complex] Y :=
  Coinvariants.lift _
    (TensorProduct.lift ((Finsupp.lift _ _ _ fun g => F g⁻¹) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap)) (by
    intro h
    ext g x
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
    simp [ofMulAction_single, mul_inv_rev, ← map_inv, bal, ← mul_apply_eq_comp,
      ← map_mul])

private theorem liftPure_apply (b : H →* G) (X : Rep.{v} Complex H)
    {Y : Type v} [AddCommGroup Y] [Module Complex Y]
    (F : G → X →ₗ[Complex] Y) (bal : ∀ g h x, F (g * b h) x = F g (X.ρ h x))
    (g : G) (x : X) :
    liftPure b X F bal (pure b X g x) = F g x := by
  simp [liftPure, pure, IndV.mk]

section Cofan

variable {J : Type u} {S : J → Type u} [∀ j, Group (S j)]
variable (a : K →* G) (b : H →* G)
variable (l : ∀ j, S j →* K) (r : ∀ j, S j →* H) (s : J → G)
variable (intertwines : ∀ j t, a (l j t) * s j = s j * b (r j t))

private abbrev mainRep : Rep.{max u v} Complex H ⥤ Rep.{max u v} Complex K :=
  Rep.indFunctor Complex b ⋙ Rep.resFunctor a

private abbrev summandRep (j : J) : Rep.{max u v} Complex H ⥤ Rep.{max u v} Complex K :=
  Rep.resFunctor (r j) ⋙ Rep.indFunctor Complex (l j)

include intertwines in
private theorem inclusionBalance (j : J) (X : Rep.{max u v} Complex H) (k : K) (t : S j)
    (x : X) : pure b X (a (k * l j t) * s j) x = pure b X (a k * s j) (X.ρ (r j t) x) := by
  rw [map_mul, mul_assoc, intertwines, ← mul_assoc]
  exact pure_balance b X _ _ x

private def inclusionAt (j : J) (X : Rep.{max u v} Complex H) :
    (summandRep l r j).obj X ⟶ (mainRep a b).obj X := by
  let Z := Rep.res (r j) X
  let F := liftPure (l j) Z (fun k => pure b X (a k * s j))
    (inclusionBalance a b l r s intertwines j X)
  refine Rep.ofHom ⟨F, ?_⟩
  intro t
  apply pure_ext (l j) Z
  intro k x
  change F (ind (l j) Z.ρ t (pure (l j) Z k x)) =
    ind b X.ρ (a t) (F (pure (l j) Z k x))
  dsimp only [F]
  rw [pure_act, liftPure_apply, liftPure_apply, pure_act, map_mul, mul_assoc]
private theorem inclusionAt_pure (j : J) (X : Rep.{max u v} Complex H) (k : K) (x : X) :
    (inclusionAt a b l r s intertwines j X).hom
      (pure (l j) (Rep.res (r j) X) k x) = pure b X (a k * s j) x := by
  unfold inclusionAt
  rw [Rep.hom_ofHom]
  exact liftPure_apply (l j) (Rep.res (r j) X) (fun k' => pure b X (a k' * s j))
    (inclusionBalance a b l r s intertwines j X) k x

private def inclusionRep (j : J) : summandRep.{u,v} l r j ⟶ mainRep.{u,v} a b where
  app := inclusionAt a b l r s intertwines j
  naturality X Y f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply pure_ext (l j) (Rep.res (r j) X)
    intro k x
    change (inclusionAt a b l r s intertwines j Y).hom
        ((Rep.indMap (l j) (Rep.resMap (r j) f)).hom (pure (l j) (Rep.res (r j) X) k x)) =
      (Rep.indMap b f).hom ((inclusionAt a b l r s intertwines j X).hom
        (pure (l j) (Rep.res (r j) X) k x))
    rw [pure_map, inclusionAt_pure, inclusionAt_pure, pure_map, Rep.resMap_hom_apply]

-- Work with balanced pairs of group elements, before linearization.
private def summandBasis (j : J) : Setoid (K × H) where
  r p q := ∃ t : S j, p.1 * (l j t)⁻¹ = q.1 ∧ r j t * p.2 = q.2
  iseqv := by
    constructor
    · intro p
      exact ⟨1, by simp, by simp⟩
    · rintro p q ⟨t, ht, hr⟩
      exact ⟨t⁻¹, by rw [← ht]; simp, by rw [← hr]; simp⟩
    · rintro p q w ⟨t, ht, hr⟩ ⟨t', ht', hr'⟩
      exact ⟨t' * t, by rw [← ht', ← ht]; simp [mul_assoc],
        by rw [← hr', ← hr]; simp [mul_assoc]⟩

private def toGroup (q : Σ j, Quotient (summandBasis l r j)) : G :=
  Quotient.liftOn q.2 (fun p => a p.1 * s q.1 * b p.2) (by
    rintro p w ⟨t, ht, hr⟩
    rw [← ht, ← hr, map_mul, map_inv, map_mul]
    have ht' := intertwines q.1 t
    symm
    calc
      _ = a p.1 * ((a (l q.1 t))⁻¹ * (s q.1 * b (r q.1 t))) * b p.2 := by
        simp only [mul_assoc]
      _ = _ := by rw [← ht', inv_mul_cancel_left])

variable (bijective : Function.Bijective (toGroup a b l r s intertwines))

private def descentOnPair (X : Rep.{max u v} Complex H) (Y : Rep.{max u v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y)
    (q : Σ j, Quotient (summandBasis l r j)) : X →ₗ[Complex] Y :=
  Quotient.liftOn q.2 (fun p => (f q.1).hom.toLinearMap ∘ₗ
    pure (l q.1) (Rep.res (r q.1) X) p.1 ∘ₗ X.ρ p.2) (by
    rintro p w ⟨t, ht, hr⟩
    rw [← ht, ← hr, ← map_inv]
    apply LinearMap.ext
    intro x
    change (f q.1).hom
        (pure (l q.1) (Rep.res (r q.1) X) p.1 (X.ρ p.2 x)) =
      (f q.1).hom
        (pure (l q.1) (Rep.res (r q.1) X) (p.1 * l q.1 t⁻¹)
          (X.ρ (r q.1 t * p.2) x))
    rw [pure_balance]
    congr 2
    change X.ρ p.2 x =
      X.ρ (r q.1 t⁻¹) (X.ρ (r q.1 t * p.2) x)
    rw [← mul_apply_eq_comp, ← map_mul, ← mul_assoc, ← map_mul, inv_mul_cancel,
      map_one, one_mul])

private def descentOnGroup (X : Rep.{max u v} Complex H) (Y : Rep.{max u v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) : G → X →ₗ[Complex] Y :=
  fun g => descentOnPair l r X Y f ((Equiv.ofBijective _ bijective).symm g)

private theorem descentOnGroup_apply (X : Rep.{max u v} Complex H) (Y : Rep.{max u v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (j : J) (k : K) (h : H) (x : X) :
    descentOnGroup a b l r s intertwines bijective X Y f (a k * s j * b h) x =
      (f j).hom (pure (l j) (Rep.res (r j) X) k (X.ρ h x)) := by
  let q : Σ j, Quotient (summandBasis l r j) := ⟨j, Quotient.mk _ (k,h)⟩
  change descentOnPair l r X Y f
    ((Equiv.ofBijective _ bijective).symm ((Equiv.ofBijective _ bijective) q)) x = _
  rw [Equiv.symm_apply_apply]
  rfl

include bijective in
private theorem exists_factor (g : G) : ∃ j k h, a k * s j * b h = g := by
  obtain ⟨⟨j,q⟩, rfl⟩ := bijective.2 g
  refine Quotient.inductionOn q (fun p => ?_)
  exact ⟨j,p.1,p.2,rfl⟩

private theorem descentOnGroup_balance (X : Rep.{max u v} Complex H) (Y : Rep.{max u v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (g : G) (h : H) (x : X) :
    descentOnGroup a b l r s intertwines bijective X Y f (g * b h) x =
      descentOnGroup a b l r s intertwines bijective X Y f g (X.ρ h x) := by
  obtain ⟨j,k,h',rfl⟩ := exists_factor a b l r s intertwines bijective g
  rw [mul_assoc (a k * s j), ← map_mul, descentOnGroup_apply, descentOnGroup_apply,
    map_mul, mul_apply_eq_comp]

private theorem descentOnGroup_equivariant (X : Rep.{max u v} Complex H) (Y : Rep.{max u v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (k : K) (g : G) (x : X) :
    descentOnGroup a b l r s intertwines bijective X Y f (a k * g) x =
      Y.ρ k (descentOnGroup a b l r s intertwines bijective X Y f g x) := by
  obtain ⟨j,k',h,rfl⟩ := exists_factor a b l r s intertwines bijective g
  rw [← mul_assoc (a k), ← mul_assoc (a k), ← map_mul,
    descentOnGroup_apply, descentOnGroup_apply, ← Rep.hom_comm_apply]
  congr 1
  exact (pure_act (l j) (Rep.res (r j) X) k' k (X.ρ h x)).symm

private def descentAt (X : Rep.{max u v} Complex H) (Y : Rep.{max u v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) : (mainRep a b).obj X ⟶ Y := by
  let F := liftPure b X (descentOnGroup a b l r s intertwines bijective X Y f)
    (descentOnGroup_balance a b l r s intertwines bijective X Y f)
  refine Rep.ofHom ⟨F, ?_⟩
  intro k
  apply pure_ext b X
  intro g x
  change F (ind b X.ρ (a k) (pure b X g x)) = Y.ρ k (F (pure b X g x))
  dsimp only [F]
  rw [pure_act, liftPure_apply, liftPure_apply]
  exact descentOnGroup_equivariant a b l r s intertwines bijective X Y f k g x
private theorem descentAt_pure (X : Rep.{max u v} Complex H) (Y : Rep.{max u v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (g : G) (x : X) :
    (descentAt a b l r s intertwines bijective X Y f).hom (pure b X g x) =
      descentOnGroup a b l r s intertwines bijective X Y f g x := by
  unfold descentAt
  rw [Rep.hom_ofHom]
  exact liftPure_apply b X _ (descentOnGroup_balance a b l r s intertwines bijective X Y f) g x

private def repCofan : Cofan (summandRep.{u,v} l r) :=
  Cofan.mk (mainRep a b) (inclusionRep a b l r s intertwines)

private def repCofanIsColimit :
    IsColimit (repCofan.{u,v} a b l r s intertwines) := by
  apply evaluationJointlyReflectsColimits
  intro X
  refine ⟨fun c => descentAt a b l r s intertwines bijective X c.pt
    (fun j => c.ι.app ⟨j⟩), ?_, ?_⟩
  · rintro c ⟨j⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply pure_ext (l j) (Rep.res (r j) X)
    intro k x
    change (descentAt a b l r s intertwines bijective X c.pt _).hom
        ((inclusionAt a b l r s intertwines j X).hom (pure (l j) (Rep.res (r j) X) k x)) =
      (c.ι.app ⟨j⟩).hom (pure (l j) (Rep.res (r j) X) k x)
    rw [inclusionAt_pure, descentAt_pure, ← mul_one (a k * s j), ← map_one b,
      descentOnGroup_apply, map_one]
    rfl
  · intro c f hf
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply pure_ext b X
    intro g x
    obtain ⟨j,k,h,rfl⟩ := exists_factor a b l r s intertwines bijective g
    change f.hom (pure b X (a k * s j * b h) x) =
      (descentAt a b l r s intertwines bijective X c.pt _).hom
        (pure b X (a k * s j * b h) x)
    rw [descentAt_pure, descentOnGroup_apply, pure_balance, ← inclusionAt_pure a b l r s intertwines]
    have hj := hf (Discrete.mk j)
    exact congrArg (fun z : (summandRep l r j).obj X ⟶ c.pt =>
      z.hom (pure (l j) (Rep.res (r j) X) k (X.ρ h x))) hj

end Cofan

section Modules

private abbrev Mod (G : Type u) [Group G] := ModuleCat.{max u v} (MonoidAlgebra Complex G)
private abbrev ofMod (G : Type u) [Group G] : Mod.{u,v} G ⥤ Rep.{max u v} Complex G :=
  Rep.ofModuleMonoidAlgebra
private abbrev toMod (G : Type u) [Group G] : Rep.{max u v} Complex G ⥤ Mod.{u,v} G :=
  Rep.toModuleMonoidAlgebra
private abbrev indMod (f : H →* G) : Mod.{u,v} H ⥤ Mod.{u,v} G :=
  (ofMod H ⋙ Rep.indFunctor Complex f) ⋙ toMod G
private abbrev resMod (f : H →* G) : Mod.{u,v} G ⥤ Mod.{u,v} H :=
  ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex f).toRingHom
private abbrev repEquiv (G : Type u) [Group G] : Rep.{max u v} Complex G ≌ Mod.{u,v} G :=
  Rep.equivalenceModuleMonoidAlgebra

private def adjointRestriction (f : H →* G) (adj : indMod.{u,v} f ⊣ resMod.{u,v} f) :
    (ofMod G ⋙ Rep.resFunctor f ⋙ toMod H) ≅ resMod.{u,v} f :=
  Adjunction.rightAdjointUniq
    (((repEquiv.{u,v} H).symm.toAdjunction.comp (Rep.indResAdjunction Complex f)).comp
      (repEquiv.{u,v} G).toAdjunction) adj

private theorem existsModuleAdjunction {U : Type u} [Group U] {S T : Subgroup U}
    (f : MackeyDiagrams.ConjEmbedding S T) :
    Nonempty (indMod.{u,v} f.toHom ⊣ resMod.{u,v} f.toHom) := by
  obtain ⟨a, ha⟩ := f.hasRepresentative
  have hm (x : S) : a * (x : U) * a⁻¹ ∈ T := ha x ▸ (f.toHom x).property
  have hf : f = MackeyDiagrams.ConjEmbedding.ofConjugator a hm := by
    apply MackeyDiagrams.ConjEmbedding.ext
    exact MonoidHom.ext (fun x => Subtype.ext (ha x))
  rw [hf]
  obtain ⟨_, _, _, _, _, adj, _, _⟩ := InductionRestrictionAdjunction.{u,v} S T a hm
  exact ⟨adj⟩

private def insertModuleEquiv (P : Mod.{u,v} H ⥤ Rep.{max u v} Complex G)
    (Q : Rep.{max u v} Complex G ⥤ Mod.{u,v} K) :
    (P ⋙ Q) ≅ (P ⋙ toMod G) ⋙ (ofMod G ⋙ Q) :=
  Functor.isoWhiskerLeft P ((Functor.leftUnitor Q).symm ≪≫
    Functor.isoWhiskerRight (repEquiv.{u,v} G).unitIso Q)

private def moduleMackey {J : Type u} {S : J → Type u} [∀ j, Group (S j)]
    (a : K →* G) (b : H →* G) (l : ∀ j, S j →* K) (r : ∀ j, S j →* H)
    (s : J → G) (intertwines : ∀ j t, a (l j t) * s j = s j * b (r j t))
    (bijective : Function.Bijective (toGroup a b l r s intertwines))
    (adjA : indMod.{u,v} a ⊣ resMod.{u,v} a)
    (adjR : ∀ j, indMod.{u,v} (r j) ⊣ resMod.{u,v} (r j)) :
    (indMod.{u,v} b ⋙ resMod.{u,v} a) ≅
      sigmaObj (fun j => resMod.{u,v} (r j) ⋙ indMod.{u,v} (l j)) := by
  let P := (Functor.whiskeringLeft _ _ (Rep.{max u v} Complex K)).obj (ofMod.{u,v} H)
  let Q := (Functor.whiskeringRight (Mod.{u,v} H) _ _).obj (toMod.{u,v} K)
  let c := repCofan.{u,v} a b l r s intertwines
  let F := Discrete.functor (summandRep.{u,v} l r)
  have hc : IsColimit c := repCofanIsColimit a b l r s intertwines bijective
  have hm : IsColimit ((P ⋙ Q).mapCocone c) := by
    letI : (toMod.{u,v} K).IsEquivalence := (repEquiv.{u,v} K).isEquivalence_functor
    exact isColimitOfPreserves (P ⋙ Q) hc
  let diagram := Discrete.functor (fun j => resMod.{u,v} (r j) ⋙ indMod.{u,v} (l j))
  have hmain : (P ⋙ Q).obj c.pt ≅ indMod.{u,v} b ⋙ resMod.{u,v} a := by
    exact (insertModuleEquiv (ofMod H ⋙ Rep.indFunctor Complex b)
      (Rep.resFunctor a ⋙ toMod K)) ≪≫
      Functor.isoWhiskerLeft (indMod b) (adjointRestriction a adjA)
  have hsummand : F ⋙ (P ⋙ Q) ≅ diagram := by
    apply Discrete.natIso
    intro j
    exact (insertModuleEquiv (ofMod H ⋙ Rep.resFunctor (r j.as))
      (Rep.indFunctor Complex (l j.as) ⋙ toMod K)) ≪≫
      Functor.isoWhiskerRight (adjointRestriction (r j.as) (adjR j.as)) (indMod (l j.as))
  exact hmain.symm ≪≫ hm.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    HasColimit.isoOfNatIso hsummand

end Modules

section Biset

open MackeyDiagrams

variable {U : Type u} [Group U] {K H G : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)

private theorem mixedProduct_action (g : K × H)
    (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    Generator.mixedProduct a b (((Biset.restriction a).tensor (Biset.induction b)).act g z) =
      a.toHom g.1 * Generator.mixedProduct a b z * (b.toHom g.2)⁻¹ := by
  refine Quotient.inductionOn z (fun p => ?_)
  change (a.toHom g.1 * p.1 * (1 : G)⁻¹) * (1 * p.2 * (b.toHom g.2)⁻¹) =
    a.toHom g.1 * (p.1 * p.2) * (b.toHom g.2)⁻¹
  simp [mul_assoc]

private theorem mixedCoordinates_action (g : K × H)
    (x : Finsupp ((Biset.restriction a).tensor (Biset.induction b)).carrier Complex) :
    let coord := (Finsupp.domLCongr (Generator.mixedEquiv a b)).trans
      (MonoidAlgebra.coeffLinearEquiv Complex).symm
    coord ((Biset.restriction a |>.tensor (Biset.induction b)).actLinear Complex g x) =
      MonoidAlgebra.of Complex G (a.toHom g.1) * coord x *
        MonoidAlgebra.of Complex G ((b.toHom g.2)⁻¹) := by
  intro coord
  have single (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) (c : Complex) :
      coord (Finsupp.single z c) = MonoidAlgebra.single (Generator.mixedProduct a b z) c := by
    change (MonoidAlgebra.coeffLinearEquiv Complex).symm
      (Finsupp.domLCongr (Generator.mixedEquiv a b) (Finsupp.single z c)) = _
    rw [Finsupp.domLCongr_single]
    rfl
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]
  | single z c =>
    rw [Biset.actLinear_single, single, single, mixedProduct_action]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul, mul_one]

private def sharedBasis {J : Type u} {S : J → Subgroup U}
    (l : ∀ j, ConjEmbedding (S j) K) (r : ∀ j, ConjEmbedding (S j) H) (j : J) :
    Quotient (summandBasis (fun i => (l i).toHom) (fun i => (r i).toHom) j) ≃
      ((Biset.induction (l j)).tensor (Biset.restriction (r j))).carrier :=
  Quotient.congrRight (fun p q => by
    change (∃ t : S j, p.1 * ((l j).toHom t)⁻¹ = q.1 ∧ (r j).toHom t * p.2 = q.2) ↔
      (∃ t : S j, (1 : K) * p.1 * ((l j).toHom t)⁻¹ = q.1 ∧
        (r j).toHom t * p.2 * (1 : H)⁻¹ = q.2)
    simp)
private theorem multiplication_bijective {J : Type u} {S : J → Subgroup U}
    (l : ∀ j, ConjEmbedding (S j) K) (r : ∀ j, ConjEmbedding (S j) H)
    (s : J → G) (ht : ∀ j t, a.toHom ((l j).toHom t) * s j = s j * b.toHom ((r j).toHom t))
    (index : G → J) (index_mul : ∀ j k h, index (a.toHom k * s j * b.toHom h) = j)
    (factor : ∀ g : G, ∃ j k h, a.toHom k * s j * b.toHom h = g)
    (intersection : ∀ j (k : K) (h : H),
      a.toHom k = s j * b.toHom h * (s j)⁻¹ → ∃ t, (l j).toHom t = k) :
    Function.Bijective
      (toGroup a.toHom b.toHom (fun j => (l j).toHom) (fun j => (r j).toHom) s ht) := by
  let f := toGroup a.toHom b.toHom (fun j => (l j).toHom) (fun j => (r j).toHom) s ht
  let d (j : J) : Dot (a.comp (l j)) (b.comp (r j)) := ⟨s j, ht j⟩
  have factorIndex (j : J) (q : Quotient (summandBasis
      (fun j => (l j).toHom) (fun j => (r j).toHom) j)) :
      index (f ⟨j,q⟩) = j := Quotient.inductionOn q (fun p => index_mul j p.1 p.2)
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hij : i = j := (factorIndex i x).symm.trans ((congrArg index he).trans (factorIndex j y))
    subst j
    apply congrArg (Sigma.mk i)
    apply (sharedBasis l r i).injective
    apply Generator.injective_mixedMultiplicationBasis a b (l i) (r i) (d i) (intersection i)
    apply (Generator.mixedEquiv a b).injective
    revert he
    refine Quotient.inductionOn₂ x y (fun p q he => ?_)
    change Generator.mixedProduct a b (Generator.mixedPair a b
        (a.toHom p.1 * s i * b.toHom p.2)) =
      Generator.mixedProduct a b (Generator.mixedPair a b
        (a.toHom q.1 * s i * b.toHom q.2))
    change a.toHom p.1 * s i * b.toHom p.2 = a.toHom q.1 * s i * b.toHom q.2 at he
    simpa only [Generator.mixedProduct_mixedPair] using he
  · intro g
    obtain ⟨j,k,h,hg⟩ := factor g
    exact ⟨⟨j, Quotient.mk _ (k,h)⟩, hg⟩

end Biset

end
end GeneralizedMackeySupport
