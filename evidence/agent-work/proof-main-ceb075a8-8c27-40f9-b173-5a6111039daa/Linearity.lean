
section Linearity

variable {R : Type v} [CommSemiring R]

private theorem lift_map {ι : Type*} {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (L : M →ₗ[R] N) (f : ι → M) (z : ι →₀ R) :
    L (freeLift R f z) = freeLift R (fun d => L (f d)) z := by
  have h : L.comp (freeLift R f) = freeLift R (fun d => L (f d)) := by
    apply extOnBasis
    intro i
    simp only [LinearMap.comp_apply, freeLift_single, one_smul]
  exact LinearMap.congr_fun h z

private theorem lift_dual {ι κ : Type u} {M : Type*} [AddCommMonoid M] [Module R M]
    (rev : ι → κ) (f : κ → M) (z : ι →₀ R) :
    freeLift R f (Finsupp.mapDomain rev z) = freeLift R (fun d => f (rev d)) z := by
  have h : (freeLift R f).comp (Finsupp.lmapDomain R R rev) =
      freeLift R (fun d => f (rev d)) := by
    apply extOnBasis
    intro i
    simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      freeLift_single, one_smul]
  exact LinearMap.congr_fun h z

variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {X X' : Biset K H} {Y Y' : Biset H J}

private theorem lift_horizontal_left {ι : Type u}
    (z : ι →₀ R) (f : ι → Biset.Hom R X X') (F : Biset.Hom R X X')
    (hF : ∀ x, F.toLinearMap x = freeLift R (fun d => (f d).toLinearMap x) z)
    (g : Biset.Hom R Y Y') (w : (X.tensor Y).carrier →₀ R) :
    (F.horizontal g).toLinearMap w =
      freeLift R (fun d => ((f d).horizontal g).toLinearMap w) z := by
  let maps := fun d => ((f d).horizontal g).toLinearMap
  have h : (F.horizontal g).toLinearMap = freeLift R maps z := by
    apply extOnBasis
    intro t
    refine Quotient.inductionOn t (fun xy => ?_)
    obtain ⟨x,y⟩ := xy
    let w₀ := Finsupp.single (X.pair Y x y) (1 : R)
    change (F.horizontal g).toLinearMap w₀ = (freeLift R maps z) w₀
    have he := lift_map (LinearMap.applyₗ (R := R) w₀) maps z
    change (freeLift R maps z) w₀ = freeLift R (fun d => (maps d) w₀) z at he
    rw [he, Biset.Hom.horizontal_single F g x y 1, one_smul, hF]
    let L := (Biset.pairLinear R X' Y').flip (g.toLinearMap (Finsupp.single y 1))
    change L (freeLift R (fun d => (f d).toLinearMap (Finsupp.single x 1)) z) = _
    rw [lift_map]
    congr 1
    funext d
    symm
    change ((f d).horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) 1) = _
    rw [Biset.Hom.horizontal_single (f d) g x y 1, one_smul]
    rfl
  calc
    (F.horizontal g).toLinearMap w = (freeLift R maps z) w := LinearMap.congr_fun h w
    _ = _ := lift_map (LinearMap.applyₗ (R := R) w) maps z

private theorem lift_horizontal_right {ι : Type u}
    (z : ι →₀ R) (g : Biset.Hom R X X') (f : ι → Biset.Hom R Y Y')
    (F : Biset.Hom R Y Y')
    (hF : ∀ y, F.toLinearMap y = freeLift R (fun d => (f d).toLinearMap y) z)
    (w : (X.tensor Y).carrier →₀ R) :
    (g.horizontal F).toLinearMap w =
      freeLift R (fun d => (g.horizontal (f d)).toLinearMap w) z := by
  let maps := fun d => (g.horizontal (f d)).toLinearMap
  have h : (g.horizontal F).toLinearMap = freeLift R maps z := by
    apply extOnBasis
    intro t
    refine Quotient.inductionOn t (fun xy => ?_)
    obtain ⟨x,y⟩ := xy
    let w₀ := Finsupp.single (X.pair Y x y) (1 : R)
    change (g.horizontal F).toLinearMap w₀ = (freeLift R maps z) w₀
    have he := lift_map (LinearMap.applyₗ (R := R) w₀) maps z
    change (freeLift R maps z) w₀ = freeLift R (fun d => (maps d) w₀) z at he
    rw [he, Biset.Hom.horizontal_single g F x y 1, one_smul, hF]
    let L := Biset.pairLinear R X' Y' (g.toLinearMap (Finsupp.single x 1))
    change L (freeLift R (fun d => (f d).toLinearMap (Finsupp.single y 1)) z) = _
    rw [lift_map]
    congr 1
    funext d
    symm
    change (g.horizontal (f d)).toLinearMap (Finsupp.single (X.pair Y x y) 1) = _
    rw [Biset.Hom.horizontal_single g (f d) x y 1, one_smul]
  calc
    (g.horizontal F).toLinearMap w = (freeLift R maps z) w := LinearMap.congr_fun h w
    _ = _ := lift_map (LinearMap.applyₗ (R := R) w) maps z

end Linearity
