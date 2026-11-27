import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.RegularEvaluationRightAction
import NotesProofs.BimoduleTensorFunctoriality

set_option maxHeartbeats 2000000

theorem CanonicalWattsNaturalTransformation : (
∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{w} S))
  [CategoryTheory.Functor.Additive F],
  let A := ModuleCat.of R (ULift.{z} R)
  let B := CategoryTheory.Functor.obj F A
  let down : LinearEquiv (RingHom.id R) (ULift.{z} R) R := ULift.moduleEquiv
  let right : R → B → B := fun r b =>
    ModuleCat.Hom.hom (CategoryTheory.Functor.map F
      (ModuleCat.ofHom (LinearEquiv.conjRingEquiv (LinearEquiv.symm down)
        (LinearMap.mulRight R r)))) b
  let lambda : ∀ M : ModuleCat.{max u z} R, M → Quiver.Hom A M :=
    fun _ m => ModuleCat.ofHom (LinearMap.smulRight (LinearEquiv.toLinearMap down) m)
  let Balanced := fun (M : ModuleCat.{max u z} R)
      (G : AddCommGrpCat.{max u z w}) (p : B → M → G) =>
    (∀ (b b' : B) (m : M), p (b + b') m = p b m + p b' m) ∧
    (∀ (b : B) (m m' : M), p b (m + m') = p b m + p b m') ∧
    (∀ (r : R) (b : B) (m : M), p (right r b) m = p b (r • m))
  ∀ (T : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{max u z w} S))
    (pure : ∀ M : ModuleCat.{max u z} R, B → M → ModuleCat.carrier (CategoryTheory.Functor.obj T M)),
    (∀ M : ModuleCat.{max u z} R,
      Balanced M (AddCommGrpCat.of (ModuleCat.carrier (CategoryTheory.Functor.obj T M))) (pure M) ∧
      (∀ (G : AddCommGrpCat.{max u z w}) (p : B → M → G),
        Balanced M G p →
          ∃! h : AddMonoidHom (ModuleCat.carrier (CategoryTheory.Functor.obj T M)) G,
            ∀ (b : B) (m : M), h (pure M b m) = p b m) ∧
      (∀ (s : S) (b : B) (m : M), s • pure M b m = pure M (s • b) m)) →
    (∀ {M N : ModuleCat.{max u z} R} (f : Quiver.Hom M N) (b : B) (m : M),
      ModuleCat.Hom.hom (CategoryTheory.Functor.map T f) (pure M b m) =
        pure N b (ModuleCat.Hom.hom f m)) →
    ∃ τ : CategoryTheory.NatTrans T
        (CategoryTheory.Functor.comp F (ModuleCat.uliftFunctor.{max u z, w} S)),
      ∀ (M : ModuleCat.{max u z} R) (b : B) (m : M),
        ModuleCat.Hom.hom (CategoryTheory.NatTrans.app τ M) (pure M b m) =
          ULift.up (ModuleCat.Hom.hom (CategoryTheory.Functor.map F (lambda M m)) b)
) :=
(by
  intro R S _ _ F _ A B down right lambda Balanced T pure hT hMap
  -- Ian X, Lemma 9.3 (p. 29), env-9-3 in the cached TeX and PDF.
  -- https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=29
  -- Alphabeta Math, steps 1.1, 2.1 and 3.1.
  -- https://alphabetamath.cc/item/lem-canonical-eilenberg-watts-comparison-is-balanced-and-natural
  -- The reviewed endpoint supplies T, its pure tensors, and their universal,
  -- scalar and morphism formulas. The checked CanonicalWattsComparison builds
  -- a comparison for a specific Finsupp quotient. Here the supplied universal
  -- property constructs the components for the given T.
  -- The pairing and composition lemmas below come from NotesProofs/WattsSupport.lean,
  -- source SHA-256 853d1dd0016bf0735f7a84559e2f1cbbb701fc3cb0e00395a0e138ffecb1f967
  -- (beta_balanced at line 237 and ell_comp at line 231).
  let G := F.comp (ModuleCat.uliftFunctor.{max u z, w} S)
  let beta : ∀ M : ModuleCat.{max u z} R, B → M → G.obj M :=
    fun M b m => ULift.up ((F.map (lambda M m)).hom b)
  -- Step 1.1. The supplier uses the same lifted regular module, conjugated
  -- right multiplication and evaluation map. Carry its balance through ULift.
  have beta_balanced (M : ModuleCat.{max u z} R) : Balanced M (AddCommGrpCat.of (G.obj M)) (beta M) := by
    have h := ChoiceFreeWatts.beta_balanced F M
    exact ⟨fun b b' m => congrArg ULift.up (h.1 b b' m),
      fun b m m' => congrArg ULift.up (h.2.1 b m m'),
      fun r b m => congrArg ULift.up (h.2.2 r b m)⟩
  have beta_smul (M : ModuleCat.{max u z} R) (s : S) (b : B) (m : M) :
      beta M (s • b) m = s • beta M b m :=
    congrArg ULift.up ((F.map (lambda M m)).hom.map_smul s b)
  -- Step 2.1. Derive the pure-tensor equality test from the supplied
  -- uniqueness clause, which also works for the two naturality composites.
  have pure_ext (M : ModuleCat.{max u z} R) (Y : AddCommGrpCat.{max u z w}) (f g : T.obj M →+ Y)
      (h : ∀ b m, f (pure M b m) = g (pure M b m)) : f = g := by
    let p : B → M → Y := fun b m => g (pure M b m)
    have hb := (hT M).1
    have hp : Balanced M Y p := by
      refine ⟨?_, ?_, ?_⟩
      · intro b b' m
        change g (pure M (b + b') m) = g (pure M b m) + g (pure M b' m)
        rw [hb.1, map_add]
      · intro b m m'
        change g (pure M b (m + m')) = g (pure M b m) + g (pure M b m')
        rw [hb.2.1, map_add]
      · intro r b m
        exact congrArg (fun x => g x) (hb.2.2 r b m)
    obtain ⟨k, _, hk⟩ := (hT M).2.1 Y p hp
    exact (hk f h).trans (hk g (fun _ _ => rfl)).symm
  have exists_lift (M : ModuleCat.{max u z} R) :
      ∃ h : T.obj M →+ G.obj M, ∀ b m, h (pure M b m) = beta M b m := by
    obtain ⟨h, hh, _⟩ :=
      (hT M).2.1 (AddCommGrpCat.of (G.obj M)) (beta M) (beta_balanced M)
    exact ⟨h, hh⟩
  -- Use the unique additive lifts in the article's ordinary-choice setting.
  let lift (M : ModuleCat.{max u z} R) : T.obj M →+ G.obj M := Classical.choose (exists_lift M)
  have lift_pure (M : ModuleCat.{max u z} R) (b : B) (m : M) : lift M (pure M b m) = beta M b m :=
    Classical.choose_spec (exists_lift M) b m
  let appLin (M : ModuleCat.{max u z} R) : T.obj M →ₗ[S] G.obj M :=
    { lift M with
      map_smul' := by
        intro s x
        change lift M (s • x) = s • lift M x
        let actT : T.obj M →+ T.obj M := DistribSMul.toAddMonoidHom (T.obj M) s
        let actG : G.obj M →+ G.obj M := DistribSMul.toAddMonoidHom (G.obj M) s
        have hs : (lift M).comp actT = actG.comp (lift M) := by
          apply pure_ext M (AddCommGrpCat.of (G.obj M))
          intro b m
          change lift M (s • pure M b m) = s • lift M (pure M b m)
          rw [(hT M).2.2, lift_pure, lift_pure, beta_smul]
        exact DFunLike.congr_fun hs x }
  have app_pure (M : ModuleCat.{max u z} R) (b : B) (m : M) : appLin M (pure M b m) = beta M b m :=
    lift_pure M b m
  let τ : CategoryTheory.NatTrans T G :=
    { app := fun M => ModuleCat.ofHom (appLin M)
      naturality := by
        intro M N f
        apply ModuleCat.hom_ext
        apply LinearMap.toAddMonoidHom_injective
        apply pure_ext M (AddCommGrpCat.of (G.obj N))
        intro b m
        -- Step 3.1. Evaluate the supplied tensor map on generators and
        -- use the regular-module identity for the composite with f.
        change appLin N ((T.map f).hom (pure M b m)) =
          (G.map f).hom (appLin M (pure M b m))
        rw [hMap, app_pure, app_pure]
        change ULift.up ((F.map (lambda N (f.hom m))).hom b) =
          ULift.up ((F.map f).hom ((F.map (lambda M m)).hom b))
        congr 1
        calc
          _ = _ := congrArg (fun k => (F.map k).hom b) (ChoiceFreeWatts.ell_comp f m).symm
          _ = _ := congrArg (fun k => k.hom b) (F.map_comp (lambda M m) f) }
  exact ⟨τ, app_pure⟩)
