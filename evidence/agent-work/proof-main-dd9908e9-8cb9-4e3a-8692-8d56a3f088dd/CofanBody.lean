
section Cofan

variable {J : Type u} {S : J → Type u} [∀ j, Group (S j)]
variable (a : K →* G) (b : H →* G)
variable (l : ∀ j, S j →* K) (r : ∀ j, S j →* H) (s : J → G)
variable (intertwines : ∀ j t, a (l j t) * s j = s j * b (r j t))

private abbrev mainRep : Rep.{v} Complex H ⥤ Rep.{v} Complex K :=
  Rep.indFunctor Complex b ⋙ Rep.resFunctor a

private abbrev summandRep (j : J) : Rep.{v} Complex H ⥤ Rep.{v} Complex K :=
  Rep.resFunctor (r j) ⋙ Rep.indFunctor Complex (l j)

private def inclusionAt (j : J) (X : Rep.{v} Complex H) :
    (summandRep l r j).obj X ⟶ (mainRep a b).obj X :=
  Rep.ofHom ⟨liftPure (l j) (Rep.res (r j) X)
    (fun k => pure b X (a k * s j)) (by
      intro k t x
      rw [map_mul, mul_assoc, intertwines, ← mul_assoc]
      exact pure_balance b X _ (r j t) x), by
    intro t
    apply pure_ext (l j) (Rep.res (r j) X)
    intro k x
    change liftPure (l j) (Rep.res (r j) X) _ _
        (ind (l j) (Rep.res (r j) X).ρ t (pure (l j) (Rep.res (r j) X) k x)) =
      ind b X.ρ (a t) (liftPure (l j) (Rep.res (r j) X) _ _
        (pure (l j) (Rep.res (r j) X) k x))
    rw [pure_act, liftPure_apply, liftPure_apply, pure_act, map_mul, mul_assoc]⟩

private theorem inclusionAt_pure (j : J) (X : Rep.{v} Complex H) (k : K) (x : X) :
    (inclusionAt a b l r s intertwines j X).hom
      (pure (l j) (Rep.res (r j) X) k x) = pure b X (a k * s j) x :=
  liftPure_apply .. 

private def inclusionRep (j : J) : summandRep.{u,v} l r j ⟶ mainRep.{u,v} a b where
  app := inclusionAt a b l r s intertwines j
  naturality X Y f := by
    apply Rep.hom_ext
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
    calc
      _ = a p.1 * (a (l q.1 t))⁻¹ * (s q.1 * b (r q.1 t)) * b p.2 := by group
      _ = _ := by rw [← ht']; group)

variable (bijective : Function.Bijective (toGroup a b l r s intertwines))

private def descentOnPair (X : Rep.{v} Complex H) (Y : Rep.{v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y)
    (q : Σ j, Quotient (summandBasis l r j)) : X →ₗ[Complex] Y :=
  Quotient.liftOn q.2 (fun p => (f q.1).hom.toLinearMap ∘ₗ
    pure (l q.1) (Rep.res (r q.1) X) p.1 ∘ₗ X.ρ p.2) (by
    rintro p w ⟨t, ht, hr⟩
    rw [← ht, ← hr, ← map_inv, map_mul]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul_apply]
    rw [pure_balance]
    change (f q.1).hom.toLinearMap
        (pure (l q.1) (Rep.res (r q.1) X) p.1
          (X.ρ (r q.1 t⁻¹) (X.ρ (r q.1 t) (X.ρ p.2 x)))) = _
    rw [← LinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one]
    rfl)

private def descentOnGroup (X : Rep.{v} Complex H) (Y : Rep.{v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) : G → X →ₗ[Complex] Y :=
  fun g => descentOnPair l r X Y f ((Equiv.ofBijective _ bijective).symm g)

private theorem descentOnGroup_apply (X : Rep.{v} Complex H) (Y : Rep.{v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (j : J) (k : K) (h : H) (x : X) :
    descentOnGroup a b l r s intertwines bijective X Y f (a k * s j * b h) x =
      (f j).hom (pure (l j) (Rep.res (r j) X) k (X.ρ h x)) := by
  let q : Σ j, Quotient (summandBasis l r j) := ⟨j, Quotient.mk _ (k,h)⟩
  change descentOnPair l r X Y f
    ((Equiv.ofBijective _ bijective).symm ((Equiv.ofBijective _ bijective) q)) x = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem exists_factor (g : G) : ∃ j k h, a k * s j * b h = g := by
  obtain ⟨⟨j,q⟩, rfl⟩ := bijective.2 g
  refine Quotient.inductionOn q (fun p => ?_)
  exact ⟨j,p.1,p.2,rfl⟩

private theorem descentOnGroup_balance (X : Rep.{v} Complex H) (Y : Rep.{v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (g : G) (h : H) (x : X) :
    descentOnGroup a b l r s intertwines bijective X Y f (g * b h) x =
      descentOnGroup a b l r s intertwines bijective X Y f g (X.ρ h x) := by
  obtain ⟨j,k,h',rfl⟩ := exists_factor a b l r s intertwines bijective g
  rw [mul_assoc (a k * s j), ← map_mul, descentOnGroup_apply, descentOnGroup_apply,
    map_mul, LinearMap.mul_apply]

private theorem descentOnGroup_equivariant (X : Rep.{v} Complex H) (Y : Rep.{v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (k : K) (g : G) (x : X) :
    descentOnGroup a b l r s intertwines bijective X Y f (a k * g) x =
      Y.ρ k (descentOnGroup a b l r s intertwines bijective X Y f g x) := by
  obtain ⟨j,k',h,rfl⟩ := exists_factor a b l r s intertwines bijective g
  rw [← mul_assoc (a k), ← mul_assoc (a k), ← map_mul,
    descentOnGroup_apply, descentOnGroup_apply, ← Rep.hom_comm_apply]
  congr 1
  exact (pure_act (l j) (Rep.res (r j) X) k' k (X.ρ h x)).symm

private def descentAt (X : Rep.{v} Complex H) (Y : Rep.{v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) : (mainRep a b).obj X ⟶ Y :=
  Rep.ofHom ⟨liftPure b X (descentOnGroup a b l r s intertwines bijective X Y f)
    (descentOnGroup_balance a b l r s intertwines bijective X Y f), by
    intro k
    apply pure_ext b X
    intro g x
    change liftPure b X _ _ (ind b X.ρ (a k) (pure b X g x)) =
      Y.ρ k (liftPure b X _ _ (pure b X g x))
    rw [pure_act, liftPure_apply, liftPure_apply]
    exact descentOnGroup_equivariant a b l r s intertwines bijective X Y f k g x⟩

private theorem descentAt_pure (X : Rep.{v} Complex H) (Y : Rep.{v} Complex K)
    (f : ∀ j, (summandRep l r j).obj X ⟶ Y) (g : G) (x : X) :
    (descentAt a b l r s intertwines bijective X Y f).hom (pure b X g x) =
      descentOnGroup a b l r s intertwines bijective X Y f g x :=
  liftPure_apply ..

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
