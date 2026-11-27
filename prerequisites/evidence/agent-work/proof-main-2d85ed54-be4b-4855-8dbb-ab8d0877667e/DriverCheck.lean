import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.ModuleProductsAndCoproducts
import NotesProofs.ModuleKernelsCokernelsAndImages
import NotesProofs.ModuleCategoriesAreAbelian
import NotesProofs.ExactPresentationsAreCokernels

set_option maxHeartbeats 2000000

theorem FreeModulesAndPresentations : (
∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
  (∀ {I : Type w} (m : I → M),
    ∃! f : LinearMap (RingHom.id R) (Finsupp I R) M,
      ∀ i : I, f (Finsupp.single i 1) = m i) ∧
  (∃ (I : Type v) (J : Type (max u v))
      (d : LinearMap (RingHom.id R) (Finsupp J R) (Finsupp I R))
      (q : LinearMap (RingHom.id R) (Finsupp I R) M),
    LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) ∧
  (∀ {I : Type w} {J : Type x}
      (d : LinearMap (RingHom.id R) (Finsupp J R) (Finsupp I R))
      (q : LinearMap (RingHom.id R) (Finsupp I R) M),
    (LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) ↔
      (LinearMap.comp q d = 0 ∧
        ∀ (N : Type (max u v w x y)) [AddCommGroup N] [Module R N]
          (g : LinearMap (RingHom.id R) (Finsupp I R) N),
          LinearMap.comp g d = 0 →
            ∃! h : LinearMap (RingHom.id R) M N, LinearMap.comp h q = g))
) :=
(by
  intro R _ M _ _
  refine ⟨?_, ?_, ?_⟩
  · intro I m
    -- Theorem 5.8 uses finite-support tuples. In Alphabeta Math's
    -- free-module proof, steps 1.1 and 2.1 use the maps r ↦ r • m i
    -- and the direct sum of the copies of R. Finsupp.linearCombination
    -- packages that finite sum directly and allows independent universes
    -- for the ring, the indices, and the target module. The checked
    -- ModuleProductsAndCoproducts uses the dependent DirectSum model.
    -- The constant-family equivalence finsuppLEquivDirectSum identifies
    -- its coordinate inclusions with Finsupp.single.
    let f := Finsupp.linearCombination R m
    have hgen (i : I) : f (Finsupp.single i 1) = m i := by
      -- Step 3.1 evaluates the sum on a generator at coefficient one.
      exact (Finsupp.linearCombination_single R 1 i).trans (one_smul R (m i))
    refine ⟨f, hgen, ?_⟩
    intro g hg
    -- Step 4.1: rescale each generator to test all singletons; lhom_ext
    -- then tests their finite sums. This works also for the empty index
    -- type in step 5.1, since the singleton tests are vacuous there.
    apply Finsupp.lhom_ext
    intro i r
    rw [← Finsupp.smul_single_one i r, map_smul, map_smul, hg i, hgen i]
  · -- The presentation clause of Theorem 5.8 uses the entire underlying
    -- types of M and ker q. Each evaluation onto its indexing module is
    -- surjective by the coefficient-one generator calculation.
    let q := Finsupp.linearCombination R (id : M → M)
    let K := LinearMap.ker q
    let rel := Finsupp.linearCombination R (id : K → K)
    let d := K.subtype.comp rel
    have hq : Function.Surjective q := Finsupp.linearCombination_id_surjective R M
    have hrel : Function.Surjective rel := Finsupp.linearCombination_id_surjective R K
    refine ⟨M, K, d, q, le_antisymm ?_ ?_, hq⟩
    · rintro _ ⟨z, rfl⟩
      exact (rel z).property
    · intro z hz
      obtain ⟨a, ha⟩ := hrel ⟨z, hz⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  · intro I J d q
    -- Proposition 4.9 gives the categorical equivalence in an abelian
    -- category. The reviewed module suppliers use one carrier universe.
    -- Here the free modules and M have independent universes, so we
    -- carry out the quotient argument of Propositions 5.4–5.5 directly.
    constructor
    · rintro ⟨hexact, hsurj⟩
      refine ⟨LinearMap.range_le_ker_iff.mp hexact.le, ?_⟩
      intro N _ _ g hg
      have hk : LinearMap.ker q ≤ LinearMap.ker g :=
        hexact.ge.trans (LinearMap.range_le_ker_iff.mpr hg)
      -- Since g kills ker q, it descends to the quotient. Surjectivity
      -- identifies that quotient with M and gives uniqueness on M.
      let e := q.quotKerEquivOfSurjective hsurj
      let h := ((LinearMap.ker q).liftQ g hk).comp e.symm.toLinearMap
      have hh : h.comp q = g := by
        apply LinearMap.ext
        intro z
        change (LinearMap.ker q).liftQ g hk (e.symm (q z)) = g z
        rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
        exact Submodule.liftQ_apply _ _ _
      refine ⟨h, hh, ?_⟩
      intro h' hh'
      apply LinearMap.ext
      intro m
      obtain ⟨z, rfl⟩ := hsurj m
      exact DFunLike.congr_fun (hh'.trans hh.symm) z
    · rintro ⟨hzero, hfactor⟩
      -- The checked NotesProofs.cokernel_universal_exact tests the quotient
      -- by range d in a common universe. Lift this quotient into the target
      -- universe of hfactor so that the same test works for mixed carriers.
      have hker : LinearMap.ker q ≤ LinearMap.range d := by
        let S := LinearMap.range d
        let lift : ((I →₀ R) ⧸ S) ≃ₗ[R] ULift.{max v x y} ((I →₀ R) ⧸ S) :=
          ULift.moduleEquiv.symm
        let p := lift.toLinearMap.comp S.mkQ
        have hp : p.comp d = 0 := by
          change (lift.toLinearMap.comp S.mkQ).comp d = 0
          rw [LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
        obtain ⟨h, hh, _⟩ := hfactor _ p hp
        intro z hz
        change q z = 0 at hz
        have hpz : p z = 0 := by
          rw [← DFunLike.congr_fun hh z, LinearMap.comp_apply, hz, map_zero]
        change z ∈ S
        rw [← Submodule.ker_mkQ S]
        exact lift.injective (hpz.trans (map_zero lift).symm)
      refine ⟨le_antisymm (LinearMap.range_le_ker_iff.mpr hzero) hker, ?_⟩
      -- The quotient of M by range q also lifts into the specified target
      -- universe. Its quotient map and the zero map both factor the zero
      -- map through q. Uniqueness forces the quotient map to vanish.
      let T := LinearMap.range q
      let lift : (M ⧸ T) ≃ₗ[R] ULift.{max u w x y} (M ⧸ T) :=
        ULift.moduleEquiv.symm
      let p := lift.toLinearMap.comp T.mkQ
      have hp : p.comp q = 0 := by
        change (lift.toLinearMap.comp T.mkQ).comp q = 0
        rw [LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
      obtain ⟨h, _, huniq⟩ :=
        hfactor (ULift.{max u w x y} (M ⧸ T)) 0 (LinearMap.zero_comp d)
      have hpzero : p = 0 :=
        (huniq p hp).trans (huniq 0 (LinearMap.zero_comp q)).symm
      intro m
      have hm : m ∈ T := by
        rw [← Submodule.ker_mkQ T]
        apply lift.injective
        exact (DFunLike.congr_fun hpzero m).trans (map_zero lift).symm
      exact hm)

#print axioms FreeModulesAndPresentations
