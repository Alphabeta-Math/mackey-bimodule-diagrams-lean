import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BimoduleTensorFunctoriality
import NotesProofs.ModuleProductsAndCoproducts

theorem TensorPreservesCoproducts : (
∀ {R : Type r} [Ring R] {S : Type s} [Ring S],
    let Bimod := CategoryTheory.AdditiveFunctor
      (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{b} S)
    let star := CategoryTheory.SingleObj.star (MulOpposite R)
    ∀ (B : Bimod),
      let carrier := B.obj.obj star
      let right := fun (a : R) (x : carrier) =>
        (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) x
      let Balanced := fun (X : ModuleCat.{max i m} R)
          (A : Type (max b i m t)) [AddCommGroup A] (p : carrier → X → A) =>
        (∀ x x' y, p (x + x') y = p x y + p x' y) ∧
        (∀ x y y', p x (y + y') = p x y + p x y') ∧
        (∀ a x y, p (right a x) y = p x (a • y))
      ∀ (T : ModuleCat.{max i m} R → ModuleCat.{max b i m t} S)
        (pure : ∀ (X : ModuleCat.{max i m} R), carrier → X → T X),
        (∀ (X : ModuleCat.{max i m} R),
          Balanced X (T X) (pure X) ∧
          (∀ (A : AddCommGrpCat.{max b i m t}) (p : carrier → X → A),
            Balanced X A p →
              ∃! h : AddMonoidHom (T X) A, ∀ x y, h (pure X x y) = p x y) ∧
          (∀ (c : S) (x : carrier) (y : X), c • pure X x y = pure X (c • x) y)) →
        ∀ {I : Type i} (M : I → ModuleCat.{max i m} R),
          letI : DecidableEq I := Classical.decEq I
          let sum := ModuleCat.of R (DirectSum I (fun j => ↥(M j)))
          ∃ e : LinearEquiv (RingHom.id S) (DirectSum I (fun j => ↥(T (M j)))) (T sum),
            ∀ (j : I) (x : carrier) (y : M j),
              e (DirectSum.lof S I (fun k => ↥(T (M k))) j (pure (M j) x y)) =
                pure sum x (DirectSum.lof R I (fun k => ↥(M k)) j y)
) :=
(by
  intro R _ S _ Bimod star B carrier right Balanced T pure hT I M
  -- This is the lecture notes' ordinary-choice endpoint. The reviewed
  -- inclusions use Classical.decEq and the family of lifts is selected below.
  let _ : DecidableEq I := Classical.decEq I
  let X (j : I) : Type _ := M j
  let Y (j : I) : Type _ := T (M j)
  let A := ModuleCat.of R (DirectSum I X)
  let D := ModuleCat.of S (DirectSum I Y)
  let inX (j : I) := DirectSum.lof R I X j
  let inY (j : I) := DirectSum.lof S I Y j
  change ∃ e : D ≃ₗ[S] T A, ∀ j x y, e (inY j (pure (M j) x y)) = pure A x (inX j y)
  -- BimoduleTensorFunctoriality supplies one model of the tensor functor.
  -- The checked concrete_tensor_direct_sum_iso uses a single carrier universe
  -- and its own tensor and sum models. The endpoint has arbitrary T and
  -- independent carrier universes, so construct the maps from hT.
  -- Use uniqueness in hT for pure-tensor extensionality (Alphabeta Math F1 and F3).
  have pureExt (N : ModuleCat R) (E : AddCommGrpCat)
      (f g : T N →+ E) (agree : ∀ x y, f (pure N x y) = g (pure N x y)) : f = g := by
    have balanced : Balanced N E (fun x y => g (pure N x y)) := by
      obtain ⟨addLeft, addRight, balance⟩ := (hT N).1
      exact ⟨fun x x' y => (congrArg g (addLeft x x' y)).trans (map_add g _ _),
        fun x y y' => (congrArg g (addRight x y y')).trans (map_add g _ _),
        fun a x y => congrArg g (balance a x y)⟩
    obtain ⟨_, _, unique⟩ := (hT N).2.1 E (fun x y => g (pure N x y)) balanced
    exact (unique f agree).trans (unique g (fun _ _ => rfl)).symm
  -- Step 2.1. Compare the two additive maps obtained by putting a scalar on
  -- either side of the lift. The specified action on pure tensors proves equality.
  have liftLinear (N : ModuleCat R) (E : ModuleCat S) (p : carrier → N → E)
      (hp : Balanced N E p) (outer : ∀ (c : S) x y, p (c • x) y = c • p x y) :
      ∃ f : T N →ₗ[S] E, ∀ x y, f (pure N x y) = p x y := by
    obtain ⟨f, hf, _⟩ := (hT N).2.1 (AddCommGrpCat.of E) p hp
    refine ⟨{ f with map_smul' := ?_ }, hf⟩
    intro c z
    change f (c • z) = c • f z
    have commute : f.comp (DistribSMul.toAddMonoidHom (T N) c) =
        (DistribSMul.toAddMonoidHom E c).comp f := by
      apply pureExt N (AddCommGrpCat.of E)
      intro x y
      change f (c • pure N x y) = c • f (pure N x y)
      rw [(hT N).2.2, hf, hf, outer]
    exact DFunLike.congr_fun commute z
  -- Step 1.2. Lift each inclusion using the balancing and outer action of
  -- pure A, then assemble the lifts via the linear direct-sum universal
  -- property underlying ModuleProductsAndCoproducts.
  have existsLeg (j : I) :
      ∃ f : T (M j) →ₗ[S] T A, ∀ x y, f (pure (M j) x y) = pure A x (inX j y) := by
    apply liftLinear (M j) (T A)
    · obtain ⟨addLeft, addRight, balance⟩ := (hT A).1
      exact ⟨fun x x' y => addLeft x x' (inX j y),
        fun x y y' => (congrArg (pure A x) (map_add (inX j) y y')).trans (addRight x _ _),
        fun a x y => (balance a x (inX j y)).trans
          (congrArg (pure A x) ((inX j).map_smul a y).symm)⟩
    · intro c x y
      exact ((hT A).2.2 c x (inX j y)).symm
  choose leg legPure using existsLeg
  let forward : D →ₗ[S] T A := DirectSum.toModule S I (T A) leg
  have forwardPure (j : I) (x : carrier) (y : M j) :
      forward (inY j (pure (M j) x y)) = pure A x (inX j y) := by
    exact (DirectSum.toModule_lof S j _).trans (legPure j x y)
  -- Step 1.3. Assemble the coordinate pairing via the additive direct-sum
  -- universal property. This handles finite support internally, and gives the
  -- same inverse formula as the coordinatewise construction in the source.
  let pureRight (N : ModuleCat R) (x : carrier) : N →+ T N :=
    AddMonoidHom.mk' (pure N x) ((hT N).1.2.1 x)
  let pair (x : carrier) : A →+ D :=
    DirectSum.toAddMonoid (fun j => (inY j).toAddMonoidHom.comp (pureRight (M j) x))
  have pairIn (x : carrier) (j : I) (y : M j) :
      pair x (inX j y) = inY j (pure (M j) x y) :=
    DirectSum.toAddMonoid_of (fun k => (inY k).toAddMonoidHom.comp (pureRight (M k) x)) j y
  have sumExt (E : AddCommGrpCat) (f g : A →+ E)
      (agree : ∀ j y, f (inX j y) = g (inX j y)) : f = g :=
    DirectSum.addHom_ext agree
  have pairAdd (x x' : carrier) : pair (x + x') = pair x + pair x' := by
    apply sumExt (AddCommGrpCat.of D)
    intro j y
    change pair (x + x') (inX j y) = pair x (inX j y) + pair x' (inX j y)
    rw [pairIn, pairIn, pairIn, (hT (M j)).1.1, map_add]
  have pairBalance (a : R) (x : carrier) :
      pair (right a x) = (pair x).comp (DistribSMul.toAddMonoidHom A a) := by
    apply sumExt (AddCommGrpCat.of D)
    intro j y
    change pair (right a x) (inX j y) = pair x (a • inX j y)
    rw [← map_smul (inX j), pairIn, pairIn, (hT (M j)).1.2.2]
  have pairOuter (c : S) (x : carrier) :
      pair (c • x) = (DistribSMul.toAddMonoidHom D c).comp (pair x) := by
    apply sumExt (AddCommGrpCat.of D)
    intro j y
    change pair (c • x) (inX j y) = c • pair x (inX j y)
    rw [pairIn, pairIn, ← (hT (M j)).2.2]
    exact (inY j).map_smul c _
  obtain ⟨backward, backwardPure⟩ := liftLinear A D (fun x y => pair x y)
    ⟨fun x x' y => DFunLike.congr_fun (pairAdd x x') y,
      fun x y y' => map_add (pair x) y y',
      fun a x y => DFunLike.congr_fun (pairBalance a x) y⟩
    (fun c x y => DFunLike.congr_fun (pairOuter c x) y)
  -- Step 2.2. Compare the composites with the identities on the two kinds
  -- of generators. The universal properties apply to the empty family too.
  have forwardBackward : forward.comp backward = LinearMap.id := by
    apply LinearMap.toAddMonoidHom_injective
    apply pureExt A (AddCommGrpCat.of (T A))
    intro x y
    change forward (backward (pure A x y)) = pure A x y
    rw [backwardPure]
    have agree : forward.toAddMonoidHom.comp (pair x) = pureRight A x := by
      apply sumExt (AddCommGrpCat.of (T A))
      intro j z
      change forward (pair x (inX j z)) = pure A x (inX j z)
      rw [pairIn, forwardPure]
    exact DFunLike.congr_fun agree y
  have backwardForward : backward.comp forward = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.toAddMonoidHom_injective
    apply pureExt (M j) (AddCommGrpCat.of D)
    intro x y
    change backward (forward (inY j (pure (M j) x y))) = inY j (pure (M j) x y)
    rw [forwardPure, backwardPure, pairIn]
  exact ⟨LinearEquiv.ofLinearMap forward backward forwardBackward backwardForward, forwardPure⟩)

#print axioms TensorPreservesCoproducts
