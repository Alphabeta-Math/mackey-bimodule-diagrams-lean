open CategoryTheory CategoryTheory.Limits in
by
  intro C _ _ _ _ P _ hGenerator hSmall
  dsimp only
  let R := (End P)ᵐᵒᵖ
  let H := preadditiveCoyonedaObj P
  change ∀ X Y, Function.Bijective (H.map (X := X) (Y := Y))
  -- Alphabeta Math's Hom functor step 1.2 uses separation for
  -- faithfulness. Lemma 8.3 supplies it for this projective separator
  -- and the given smallness hypothesis in the lecture notes' setting.
  have hExact := GeneratorHomExactnessAndDetection C P hGenerator hSmall
  let _ : H.Faithful := hExact.2.2.2.1
  intro X Y
  refine ⟨H.map_injective, ?_⟩
  intro t
  -- Lemma 8.5 uses the presentation in Lemma 8.4. The checked supplier
  -- uses local smallness to take I and J in the coproduct index universe.
  obtain ⟨I, J, d, q, hdq, ⟨hq⟩⟩ :=
    GeneratorCokernelPresentations C P hGenerator hSmall X
  let _ : DecidableEq I := Classical.decEq I
  let A : I → C := fun _ => P
  let leg (i : I) : H.obj P ⟶ H.obj (sigmaObj A) := H.map (Sigma.ι A i)
  -- Lemma 8.5 first identifies H(P) with the regular left R-module.
  -- The regular-module supplier concerns endomorphisms *in ModuleCat*.
  -- Here P is an arbitrary object, so use unop and check linearity for
  -- the actual precomposition action.
  let unopAdd : R ≃+ H.obj P := MulOpposite.opAddEquiv.symm.trans End.addEquiv
  let regular : R ≃ₗ[R] H.obj P :=
    { unopAdd with map_smul' := fun _ _ => rfl }
  -- Alphabeta Math's Hom functor step 2.1 uses smallness of P for
  -- the underlying additive map. The linear map below has that same
  -- underlying map because the legs act by postcomposition.
  -- Following the free-module steps 1.1, 2.1 and 3.1, assemble the
  -- maps on copies of R and evaluate them at coefficient one. The
  -- direct-sum equivalences implement the proposed Finsupp comparison
  -- without expanding a finite linear combination. Its source carrier
  -- can be larger than the target ModuleCat universe.
  let sumComparison : DirectSum I (fun _ => ↥(H.obj P)) →ₗ[R] H.obj (sigmaObj A) :=
    DirectSum.toModule R I (H.obj (sigmaObj A)) (fun i => (leg i).hom)
  have hSum : Function.Bijective sumComparison := hSmall I A
  let freeSum : (I →₀ R) ≃ₗ[R] DirectSum I (fun _ => ↥(H.obj P)) :=
    (finsuppLEquivDirectSum R R I).trans (DirectSum.congrLinearEquiv fun _ => regular)
  let θ : (I →₀ R) →ₗ[R] H.obj (sigmaObj A) := sumComparison.comp freeSum.toLinearMap
  have hθ : Function.Bijective θ := hSum.comp freeSum.bijective
  have hBasis (i : I) : θ (Finsupp.single i 1) = Sigma.ι A i := by
    change sumComparison (freeSum (Finsupp.single i 1)) = _
    simp only [freeSum, LinearEquiv.trans_apply, finsuppLEquivDirectSum_single,
      DirectSum.congrLinearEquiv_toLinearMap, ← LinearEquiv.coe_coe, DirectSum.lmap_lof,
      sumComparison, DirectSum.toModule_lof]
    change CategoryStruct.comp (CategoryStruct.id P) (Sigma.ι A i) = Sigma.ι A i
    exact Category.id_comp _
  -- Lift H(q) ≫ t on the individual generators. Alphabeta Math's
  -- free-module step 4.1 gives equality on the whole free module,
  -- via the first clause of the checked free-module supplier.
  let s : H.obj (sigmaObj A) ⟶ H.obj Y := CategoryStruct.comp (H.map q) t
  let images (i : I) : P ⟶ Y := s.hom (Sigma.ι A i)
  let g : sigmaObj A ⟶ Y := Sigma.desc images
  have hg : H.map g = s := by
    have hgBasis (i : I) : (H.map g).hom (θ (Finsupp.single i 1)) = images i := by
      rw [hBasis]
      exact Sigma.ι_comp_desc images i
    have hsBasis (i : I) : s.hom (θ (Finsupp.single i 1)) = images i := by
      rw [hBasis]
    obtain ⟨f, _, hf⟩ := (FreeModulesAndPresentations.{v, v, w, 0, 0} R (H.obj Y)).1 images
    have heq : (H.map g).hom.comp θ = s.hom.comp θ :=
      (hf _ hgBasis).trans (hf _ hsBasis).symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := hθ.2 z
    exact DFunLike.congr_fun heq a
  have hdg : CategoryStruct.comp d g = 0 := by
    apply H.map_injective
    rw [H.map_comp, hg, H.map_zero]
    simp only [s, ← Category.assoc, ← H.map_comp, hdq, H.map_zero, zero_comp]
  obtain ⟨f, hf⟩ := CokernelCofork.IsColimit.desc' hq g hdg
  change CategoryStruct.comp q f = g at hf
  have hqf : CategoryStruct.comp (H.map q) (H.map f) = CategoryStruct.comp (H.map q) t := by
    rw [← H.map_comp, hf]
    exact hg
  -- Alphabeta Math's Hom functor steps 3.1 and 4.1 use cokernel
  -- preservation. Lemma 8.3 supplies it for the parallel pair (d, 0).
  -- The mapped cofork is a cokernel, so its projection is epic and
  -- therefore surjective in ModuleCat. The construction uses the
  -- lecture notes' ordinary choice for the chosen coproducts and
  -- cokernels, and Classical.decEq for finitely supported coordinates.
  let _ : PreservesColimit (parallelPair d 0) H := hExact.2.1 d
  have hMapQ := isColimitCoforkMapOfIsColimit' H hdq hq
  have hEpi : Epi (H.map q) := epi_of_isColimit_cofork hMapQ
  have hSurj := (ModuleCat.epi_iff_surjective (H.map q)).mp hEpi
  refine ⟨f, ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
  obtain ⟨a, rfl⟩ := hSurj z
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hqf) a
