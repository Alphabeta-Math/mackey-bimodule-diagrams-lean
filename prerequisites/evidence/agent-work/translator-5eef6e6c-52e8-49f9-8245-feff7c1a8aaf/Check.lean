import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import NotesProofs.CokernelExact

universe u v w x y
section
variable (R : Type u) [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem freeGeneratorMap {I : Type w} (m : I → M) :
    ∃! f : (I →₀ R) →ₗ[R] M, ∀ i : I, f (Finsupp.single i 1) = m i := by
  have generator (i : I) :
      Finsupp.linearCombination R m (Finsupp.single i 1) = m i := by
    rw [Finsupp.linearCombination_single, one_smul]
  refine ⟨Finsupp.linearCombination R m, generator, ?_⟩
  intro f hf
  apply Finsupp.lhom_ext
  intro i r
  rw [← Finsupp.smul_single_one i r, map_smul, map_smul, hf i, generator i]

private theorem exactFreePresentation :
    ∃ (I : Type v) (J : Type (max u v))
      (d : (J →₀ R) →ₗ[R] (I →₀ R)) (q : (I →₀ R) →ₗ[R] M),
      LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q := by
  let q := Finsupp.linearCombination R (fun m : M => m)
  let K := LinearMap.ker q
  let d := Finsupp.linearCombination R (fun k : K => (k : M →₀ R))
  have hq : Function.Surjective q := fun m =>
    ⟨Finsupp.single m 1, (Finsupp.linearCombination_single R (v := fun m : M => m) 1 m).trans
      (one_smul R m)⟩
  refine ⟨M, K, d, q, ?_, hq⟩
  have hd : d = K.subtype.comp (Finsupp.linearCombination R (fun k : K => k)) := by
    apply Finsupp.lhom_ext
    intro k r
    simp [d, Finsupp.linearCombination_single]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [hd]
    exact Subtype.prop _
  · intro y hy
    refine ⟨Finsupp.single (⟨y, hy⟩ : K) 1, ?_⟩
    simp [d, Finsupp.linearCombination_single]

private theorem exactIffCokernel {I : Type w} {J : Type x}
    (d : (J →₀ R) →ₗ[R] (I →₀ R)) (q : (I →₀ R) →ₗ[R] M) :
    (LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) ↔
      (q.comp d = 0 ∧
        ∀ (N : Type (max u v w x y)) [AddCommGroup N] [Module R N]
          (g : (I →₀ R) →ₗ[R] N), g.comp d = 0 →
            ∃! h : M →ₗ[R] N, h.comp q = g) := by
  constructor
  · rintro ⟨hexact, hsurj⟩
    refine ⟨LinearMap.range_le_ker_iff.mp hexact.le, ?_⟩
    intro N _ _ g hg
    have hk : LinearMap.ker q ≤ LinearMap.ker g :=
      hexact.ge.trans (LinearMap.range_le_ker_iff.mpr hg)
    let e := q.quotKerEquivOfSurjective hsurj
    let h := ((LinearMap.ker q).liftQ g hk).comp e.symm.toLinearMap
    have hh : h.comp q = g := by
      apply LinearMap.ext
      intro p
      change (LinearMap.ker q).liftQ g hk (e.symm (q p)) = g p
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
      exact Submodule.liftQ_apply _ _ _
    refine ⟨h, hh, ?_⟩
    intro h' hh'
    apply LinearMap.ext
    intro m
    obtain ⟨p, rfl⟩ := hsurj m
    exact DFunLike.congr_fun (hh'.trans hh.symm) p
  · rintro ⟨hzero, hfactor⟩
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
      apply lift.injective
      exact hpz.trans (map_zero lift).symm
    refine ⟨le_antisymm (LinearMap.range_le_ker_iff.mpr hzero) hker, ?_⟩
    apply LinearMap.range_eq_top.mp
    apply LinearMap.range_eq_top_of_cancel
    let lift : (M ⧸ LinearMap.range q) ≃ₗ[R] ULift.{max u w x y} (M ⧸ LinearMap.range q) :=
      ULift.moduleEquiv.symm
    intro f g hfg
    let F := lift.toLinearMap.comp f
    let G := lift.toLinearMap.comp g
    have heq : F.comp q = G.comp q := by
      change (lift.toLinearMap.comp f).comp q = (lift.toLinearMap.comp g).comp q
      simp only [LinearMap.comp_assoc, hfg]
    have hF : (F.comp q).comp d = 0 := by
      rw [LinearMap.comp_assoc, hzero, LinearMap.comp_zero]
    obtain ⟨h, hh, huniq⟩ := hfactor _ (F.comp q) hF
    have hFG := (huniq F rfl).trans (huniq G heq.symm).symm
    exact LinearMap.ext fun z => lift.injective (DFunLike.congr_fun hFG z)
end

theorem FreeModulesAndPresentations :
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
:= by
  intro R _ M _ _
  exact ⟨freeGeneratorMap R, exactFreePresentation R, exactIffCokernel R⟩

#check finsuppLEquivDirectSum
#check finsuppLEquivDirectSum_single
#print axioms FreeModulesAndPresentations

private theorem checkProjectCokernelInterface (R M I J : Type u) [Ring R]
    [AddCommGroup M] [Module R M]
    (d : (J →₀ R) →ₗ[R] (I →₀ R)) (q : (I →₀ R) →ₗ[R] M)
    (hexact : LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) :
    ∀ p, q p = 0 → ∃ l, d l = p := by
  have hc := ((FreeModulesAndPresentations.{u, u, u, u, u} R M).2.2 d q).mp hexact
  apply NotesProofs.cokernel_universal_exact d q
  intro N _ _ g hg
  have hzero : g.comp d = 0 := LinearMap.ext hg
  obtain ⟨h, hh, _⟩ := hc.2 N g hzero
  exact ⟨h, DFunLike.congr_fun hh⟩
