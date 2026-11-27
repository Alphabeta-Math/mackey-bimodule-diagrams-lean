import MackeyDiagrams
import WattsFoundation.ConcreteTensorBimoduleMap
import WattsFoundation.WattsMathlibReverse
import WattsFoundation.General.OriginalBimoduleAdapter
import WattsFoundation.ClassicalReconstruction
import WattsFoundation.ModuleProductsAndCoproducts

set_option maxHeartbeats 2000000

theorem RegularModuleSmallProjectiveGenerator : (
∀ (R : Type u) [Ring R],
  let A := ModuleCat.of R (ULift.{max v w} R)
  (∃ e : ∀ M : ModuleCat.{max u v w} R, AddEquiv (Quiver.Hom A M) ↥M,
    (∀ (M : ModuleCat.{max u v w} R) (f : Quiver.Hom A M),
      e M f = ModuleCat.Hom.hom f (ULift.up (1 : R))) ∧
    (∀ {M N : ModuleCat.{max u v w} R} (g : Quiver.Hom M N) (f : Quiver.Hom A M),
      e N (CategoryTheory.CategoryStruct.comp f g) = ModuleCat.Hom.hom g (e M f))) ∧
  CategoryTheory.Projective A ∧
  CategoryTheory.IsSeparator A ∧
  (∀ (I : Type v) (M : I → ModuleCat.{max u v w} R),
    letI : DecidableEq I := Classical.decEq I
    let D := ModuleCat.of R (DirectSum I (fun i => ↥(M i)))
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom A (M i)) (γ := Quiver.Hom A D)
        (fun i => CategoryTheory.Preadditive.rightComp A
          (ModuleCat.ofHom (DirectSum.lof R I (fun j => ↥(M j)) i))))) ∧
  (∃ e : RingEquiv (CategoryTheory.End A) (MulOpposite R),
    ∀ f : CategoryTheory.End A,
      e f = MulOpposite.op
        (ULift.down (ModuleCat.Hom.hom (CategoryTheory.End.asHom f) (ULift.up (1 : R)))))
) :=
(by
  intro R _
  dsimp only
  let A : ModuleCat.{max u v w} R := ModuleCat.of R (ULift.{max v w} R)
  let liftEquiv : ULift.{max v w} R ≃ₗ[R] R := ULift.moduleEquiv
  -- Alphabeta Math steps 1.1 and 2.1 evaluate endomorphisms at one and
  -- recover them by linearity. Theorem 5.9 first does this for arbitrary
  -- codomains. Integer scalars commute with the R-action, so evaluation is
  -- additive. Transport this equivalence along the lifted domain.
  let e (M : ModuleCat.{max u v w} R) : (Quiver.Hom A M) ≃+ M :=
    (ModuleCat.homAddEquiv (M := A) (N := M)).trans
      ((liftEquiv.arrowCongrAddEquiv (LinearEquiv.refl R M)).trans
        (LinearMap.ringLmapEquivSelf R ℤ M).toAddEquiv)
  have eval (M : ModuleCat.{max u v w} R) (f : Quiver.Hom A M) :
      e M f = f.hom (ULift.up (1 : R)) := rfl
  have natural {M N : ModuleCat.{max u v w} R} (g : Quiver.Hom M N) (f : Quiver.Hom A M) :
      e N (CategoryTheory.CategoryStruct.comp f g) = g.hom (e M f) := rfl
  refine ⟨⟨e, eval, natural⟩, ?_, ?_, ?_, ?_⟩
  · -- In the article's lifting argument, epimorphisms are surjective by
    -- the module-category criterion. Lift the value at one and use naturality.
    constructor
    intro E X f p _
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective p).mp inferInstance (e X f)
    refine ⟨(e E).symm x, (e X).injective ?_⟩
    rw [natural, AddEquiv.apply_symm_apply]
    exact hx
  · -- Test equality of morphisms on the map corresponding to each element.
    apply (CategoryTheory.isSeparator_def A).mpr
    intro M N f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (e N) (h ((e M).symm x))
    simpa only [natural, AddEquiv.apply_symm_apply] using hx
  · -- The registered ModuleProductsAndCoproducts proves the universal property
    -- of this direct sum. To identify the specified comparison, the article's
    -- finite-support argument checks evaluation on the inclusion generators.
    intro I M
    let _ : DecidableEq I := Classical.decEq I
    let D := ModuleCat.of R (DirectSum I (fun i => ↥(M i)))
    let inc (i : I) : Quiver.Hom (M i) D :=
      ModuleCat.ofHom (DirectSum.lof R I (fun j => ↥(M j)) i)
    let compare : DirectSum I (fun i => Quiver.Hom A (M i)) →+ (Quiver.Hom A D) :=
      DirectSum.toAddMonoid (fun i => CategoryTheory.Preadditive.rightComp A (inc i))
    let sumEval := DirectSum.congrAddEquiv (fun i => e (M i))
    have commutes : (e D).toAddMonoidHom.comp compare = sumEval.toAddMonoidHom := by
      apply DirectSum.addHom_ext
      intro i f
      change e D (compare (DirectSum.of (fun j => Quiver.Hom A (M j)) i f)) =
        DirectSum.map (fun j => (e (M j)).toAddMonoidHom)
          (DirectSum.of (fun j => Quiver.Hom A (M j)) i f)
      rw [DirectSum.map_of]
      change e D (DirectSum.toAddMonoid
        (fun j => CategoryTheory.Preadditive.rightComp A (inc j))
        (DirectSum.of (fun j => Quiver.Hom A (M j)) i f)) = DirectSum.of (fun j => ↥(M j)) i (e (M i) f)
      rw [DirectSum.toAddMonoid_of]
      exact natural (inc i) f
    have heq : (e D : (Quiver.Hom A D) → D) ∘ compare = (sumEval : _ → _) :=
      congrArg (fun (k : DirectSum I (fun i => Quiver.Hom A (M i)) →+ D) => ⇑k) commutes
    change Function.Bijective compare
    rw [← (e D).bijective.of_comp_iff' compare, heq]
    exact sumEval.bijective
  · -- Alphabeta Math steps 2.1 and 3.1 identify the reversed multiplication
    -- and the inverse given by right multiplication. The bundled endomorphism
    -- equivalence respects this composition, and conjugation by liftEquiv
    -- removes the universe lift. Invert the right-multiplication equivalence
    -- to obtain the stated evaluation map. The historical SmallProjectiveGenerator_regular
    -- supplies a categorical smallness statement in the same-universe case.
    -- Here the construction gives the evaluation formula in the mixed universes.
    refine ⟨(ModuleCat.endRingEquiv A).trans
      (liftEquiv.conjRingEquiv.trans (RingEquiv.moduleEndSelf R).symm), ?_⟩
    intro f
    rfl)
