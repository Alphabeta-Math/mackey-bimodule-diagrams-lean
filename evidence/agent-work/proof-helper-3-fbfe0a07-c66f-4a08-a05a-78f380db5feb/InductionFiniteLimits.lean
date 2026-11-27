import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.GroupTheory.QuotientGroup.Defs
import MackeyDiagrams.Embedding

open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct

namespace DiagramFunctorProof

universe u v
noncomputable section

variable {H G : Type u} [Group H] [Group G] (f : H →* G)

-- This is the coset key bijection used in freeRight. Invert the labels
-- in IndV, whose coinvariant presentation uses the left regular action.
private def cosetKeys (hf : Function.Injective f) : (Σ _ : G ⧸ f.range, H) ≃ G :=
  Equiv.ofBijective (fun ih => Quotient.out ih.1 * f ih.2) (by
    have quotient_eq (i : G ⧸ f.range) (h : H) :
        ((Quotient.out i * f h : G) : G ⧸ f.range) = i := by
      refine (QuotientGroup.eq.mpr ?_).trans (Quotient.out_eq' i)
      exact ⟨h⁻¹, by simp [mul_inv_rev, mul_assoc]⟩
    constructor
    · rintro ⟨i, h⟩ ⟨j, k⟩ (e : Quotient.out i * f h = Quotient.out j * f k)
      have eqij : i = j := (quotient_eq i h).symm.trans
        ((congrArg (fun x : G => (x : G ⧸ f.range)) e).trans (quotient_eq j k))
      subst j
      congr 1
      exact hf (mul_left_cancel e)
    · intro g
      let i : G ⧸ f.range := (g : G ⧸ f.range)
      have eqi : ((Quotient.out i : G) : G ⧸ f.range) = (g : G ⧸ f.range) :=
        Quotient.out_eq' i
      obtain ⟨h, hh⟩ := QuotientGroup.eq.mp eqi
      exact ⟨⟨i, h⟩, by change Quotient.out i * f h = g; rw [hh, mul_inv_cancel_left]⟩)

private theorem cosetKeys_apply (hf : Function.Injective f) (i : G ⧸ f.range) (h : H) :
    cosetKeys f hf ⟨i, h⟩ = Quotient.out i * f h := rfl

variable (hf : Function.Injective f) (A : Rep.{max u v} ℂ H)

private def indCoordinate (g : G) : A →ₗ[ℂ] (G ⧸ f.range →₀ A) :=
  let ih := (cosetKeys f hf).symm g⁻¹
  Finsupp.lsingle ih.1 ∘ₗ A.ρ ih.2

private theorem indCoordinate_onKey (i : G ⧸ f.range) (h : H) (x : A) :
    indCoordinate f hf A (Quotient.out i * f h)⁻¹ x =
      Finsupp.single i (A.ρ h x) := by
  simp [indCoordinate, ← cosetKeys_apply f hf]

private theorem indCoordinate_balance (s : H) (g : G) (x : A) :
    indCoordinate f hf A (f s * g) (A.ρ s x) = indCoordinate f hf A g x := by
  obtain ⟨⟨i, h⟩, hg⟩ := (cosetKeys f hf).surjective g⁻¹
  have hg' : g = (Quotient.out i * f h)⁻¹ := by
    simpa [cosetKeys_apply] using (congrArg Inv.inv hg).symm
  rw [hg', indCoordinate_onKey]
  have ha : f s * (Quotient.out i * f h)⁻¹ = (Quotient.out i * f (h * s⁻¹))⁻¹ := by
    simp [mul_inv_rev, mul_assoc]
  rw [ha, indCoordinate_onKey]
  simp

private def indToCoordinates : IndV f A.ρ →ₗ[ℂ] (G ⧸ f.range →₀ A) :=
  Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift (A →ₗ[ℂ] (G ⧸ f.range →₀ A)) ℂ G (indCoordinate f hf A)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) (by
        intro s
        ext g x i
        simpa [ofMulAction_single] using
          DFunLike.congr_fun (indCoordinate_balance f hf A s g x) i)

private theorem indToCoordinates_mk (g : G) (x : A) :
    indToCoordinates f hf A (IndV.mk f A.ρ g x) = indCoordinate f hf A g x := by
  simp [indToCoordinates, IndV.mk]

private def indFromCoordinates : (G ⧸ f.range →₀ A) →ₗ[ℂ] IndV f A.ρ :=
  Finsupp.lsum ℂ fun i => IndV.mk f A.ρ (Quotient.out i)⁻¹

private theorem indFromCoordinates_single (i : G ⧸ f.range) (x : A) :
    indFromCoordinates f A (Finsupp.single i x) = IndV.mk f A.ρ (Quotient.out i)⁻¹ x := by
  exact Finsupp.lsum_single _ _ i x

private theorem indMk_onKey (i : G ⧸ f.range) (h : H) (x : A) :
    IndV.mk f A.ρ (Quotient.out i * f h)⁻¹ x =
      IndV.mk f A.ρ (Quotient.out i)⁻¹ (A.ρ h x) := by
  simpa [IndV.mk, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply, mul_inv_rev]
    using Coinvariants.mk_inv_tmul ((leftRegular ℂ G).comp f) A.ρ
      (MonoidAlgebra.single (Quotient.out i)⁻¹ 1) x h

private theorem indFromTo :
    (indFromCoordinates f A).comp (indToCoordinates f hf A) = LinearMap.id := by
  apply IndV.hom_ext f A.ρ
  intro g
  apply LinearMap.ext
  intro x
  change indFromCoordinates f A (indToCoordinates f hf A (IndV.mk f A.ρ g x)) =
    IndV.mk f A.ρ g x
  obtain ⟨⟨i, h⟩, hg⟩ := (cosetKeys f hf).surjective g⁻¹
  have hg' : g = (Quotient.out i * f h)⁻¹ := by
    simpa [cosetKeys_apply] using (congrArg Inv.inv hg).symm
  rw [hg', indToCoordinates_mk, indCoordinate_onKey, indFromCoordinates_single, indMk_onKey]

private theorem indToFrom :
    (indToCoordinates f hf A).comp (indFromCoordinates f A) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i x
  change indToCoordinates f hf A (indFromCoordinates f A (Finsupp.single i x)) =
    Finsupp.single i x
  rw [indFromCoordinates_single, indToCoordinates_mk]
  simpa using indCoordinate_onKey.{u,v} f hf A i 1 x

private def indCoordinates : IndV f A.ρ ≃ₗ[ℂ] (G ⧸ f.range →₀ A) :=
  LinearEquiv.ofLinearMap (indToCoordinates f hf A) (indFromCoordinates f A)
    (indToFrom f hf A) (indFromTo f hf A)

private theorem indCoordinates_natural {A B : Rep.{max u v} ℂ H} (a : A ⟶ B) :
    (indCoordinates f hf B).toLinearMap.comp (Rep.indMap f a).hom.toLinearMap =
      (Finsupp.mapRange.linearMap (Rep.Hom.hom a).toLinearMap).comp
        (indCoordinates f hf A).toLinearMap := by
  apply IndV.hom_ext f A.ρ
  intro g
  apply LinearMap.ext
  intro x
  change indToCoordinates f hf B ((Rep.indMap f a).hom (IndV.mk f A.ρ g x)) =
    Finsupp.mapRange.linearMap a.hom.toLinearMap (indToCoordinates f hf A (IndV.mk f A.ρ g x))
  have he : (Rep.indMap f a).hom (IndV.mk f A.ρ g x) = IndV.mk f B.ρ g (a.hom x) := by
    simp [Rep.indMap, IndV.mk]
  rw [he, indToCoordinates_mk, indToCoordinates_mk]
  simp [indCoordinate, Rep.hom_comm_apply]

private abbrev GroupAlgebra (S : Type u) [Group S] := MonoidAlgebra ℂ S

private def moduleInduction : ModuleCat.{max u v} (GroupAlgebra H) ⥤
    ModuleCat.{max u v} (GroupAlgebra G) :=
  (Rep.ofModuleMonoidAlgebra ⋙ Rep.indFunctor ℂ f) ⋙ Rep.toModuleMonoidAlgebra

private def moduleIndCoordinate (X : ModuleCat.{max u v} (GroupAlgebra H)) :
    (moduleInduction f).obj X ≃+ (G ⧸ f.range →₀ X) :=
  (indCoordinates f hf (Rep.ofModuleMonoidAlgebra.obj X)).toAddEquiv

private theorem moduleIndCoordinate_natural {X Y : ModuleCat.{max u v} (GroupAlgebra H)}
    (a : X ⟶ Y) (z : (moduleInduction f).obj X) (i : G ⧸ f.range) :
    moduleIndCoordinate f hf Y ((moduleInduction f).map a z) i =
      a (moduleIndCoordinate f hf X z i) := by
  have he := indCoordinates_natural f hf (Rep.ofModuleMonoidAlgebra.map a)
  exact DFunLike.congr_fun (LinearMap.congr_fun he z) i

include hf in
private theorem moduleInduction_additive : (moduleInduction.{u,v} f).Additive where
  map_add {X Y} a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (moduleIndCoordinate f hf Y).injective
    change moduleIndCoordinate f hf Y ((moduleInduction f).map (a + b) z) =
      moduleIndCoordinate f hf Y (((moduleInduction f).map a z) + ((moduleInduction f).map b z))
    rw [map_add]
    apply Finsupp.ext
    intro i
    rw [Finsupp.add_apply, moduleIndCoordinate_natural, moduleIndCoordinate_natural,
      moduleIndCoordinate_natural]
    rfl

include hf in
private theorem moduleInduction_map_exact (S : ShortComplex (ModuleCat.{max u v} (GroupAlgebra H)))
    (hS : S.Exact) :
    letI := moduleInduction_additive.{u,v} f hf
    (S.map (moduleInduction f)).Exact := by
  haveI := moduleInduction_additive.{u,v} f hf
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  intro z
  change (moduleInduction f).map S.g z = 0 ↔
    z ∈ Set.range (fun w => (moduleInduction f).map S.f w)
  constructor
  · intro hz
    have hr : moduleIndCoordinate f hf S.X₂ z ∈
        Set.range (Finsupp.mapRange (fun x => S.f x) S.f.hom.map_zero) := by
      rw [Finsupp.range_mapRange]
      intro i
      apply (hS _).mp
      rw [← moduleIndCoordinate_natural, hz, map_zero, Finsupp.zero_apply]
    obtain ⟨w, hw⟩ := hr
    refine ⟨(moduleIndCoordinate f hf S.X₁).symm w, ?_⟩
    apply (moduleIndCoordinate f hf S.X₂).injective
    apply Finsupp.ext
    intro i
    rw [moduleIndCoordinate_natural, AddEquiv.apply_symm_apply, ← hw, Finsupp.mapRange_apply]
  · rintro ⟨w, rfl⟩
    apply (moduleIndCoordinate f hf S.X₃).injective
    rw [map_zero]
    apply Finsupp.ext
    intro i
    rw [moduleIndCoordinate_natural, moduleIndCoordinate_natural, Finsupp.zero_apply]
    exact (hS _).mpr ⟨_, rfl⟩

include hf in
private theorem moduleInduction_preservesFiniteLimits :
    PreservesFiniteLimits (moduleInduction.{u,v} f) := by
  haveI := moduleInduction_additive.{u,v} f hf
  have h : PreservesFiniteLimits (moduleInduction.{u,v} f) ∧
      PreservesFiniteColimits (moduleInduction.{u,v} f) :=
    ((Functor.exact_tfae (moduleInduction.{u,v} f)).out 2 4).mp
      (moduleInduction_map_exact.{u,v} f hf)
  exact h.1

private theorem induction_preservesFiniteLimits {U : Type u} [Group U]
    {H G : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H G) :
    PreservesFiniteLimits
      ((Rep.ofModuleMonoidAlgebra (k := ℂ) (G := H) ⋙ Rep.indFunctor ℂ a.toHom) ⋙
        (Rep.toModuleMonoidAlgebra (k := ℂ) (G := G)) :
        ModuleCat.{max u v} (GroupAlgebra H) ⥤ ModuleCat.{max u v} (GroupAlgebra G)) := by
  exact moduleInduction_preservesFiniteLimits.{u,v} a.toHom a.injective

#print axioms induction_preservesFiniteLimits

end

end DiagramFunctorProof
