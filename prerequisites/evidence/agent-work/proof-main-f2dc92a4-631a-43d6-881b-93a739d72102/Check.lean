import Mathlib.CategoryTheory.Preadditive.SingleObj
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BalancedTensorUniversalProperty

set_option maxHeartbeats 2000000

namespace BimoduleTensorFunctorialityAux

open CategoryTheory

universe r s v w t

variable {R : Type r} [Ring R] {S : Type s} [Ring S]

private abbrev Bimod (R : Type r) [Ring R] (S : Type s) [Ring S] :=
  AdditiveFunctor (SingleObj (MulOpposite R)) (ModuleCat.{v} S)

local notation "★" => SingleObj.star (MulOpposite R)

private abbrev carrier (B : Bimod.{r,s,v} R S) := B.obj.obj ★

-- SingleObj composes f ≫ g as g * f. In the opposite ring this makes
-- the arrow for a * a' act by first applying a and then a'. Functoriality
-- gives the unit and product laws, and additivity gives the scalar sum law.
private abbrev action (B : Bimod.{r,s,v} R S) (a : R) (b : carrier B) : carrier B :=
  (B.obj.map (show ★ ⟶ ★ from MulOpposite.op a)) b

private theorem action_commutes (B : Bimod.{r,s,v} R S) (a : R) (c : S) (b : carrier B) :
    action B a (c • b) = c • action B a b :=
  map_smul (B.obj.map (show ★ ⟶ ★ from MulOpposite.op a)).hom c b

private theorem map_action {B B' : Bimod.{r,s,v} R S} (u : B ⟶ B') (a : R)
    (b : carrier B) :
    (u.hom.app ★) (action B a b) = action B' a ((u.hom.app ★) b) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (u.hom.naturality (show ★ ⟶ ★ from MulOpposite.op a))) b

-- Ian X, Proposition 6.3, p. 19.
-- https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19
-- Alphabeta Math, steps 1.2, 2.1, 3.1 and 5.1.
-- https://alphabetamath.cc/item/thm-bimodule-actions-induced-on-tensor-products
-- Step 1.2 gives the left-handed pairing. The S-linearity of the right
-- action gives the commuting-action hypothesis, so outerModule implements
-- the left-handed descent of steps 2.1 and 3.1, and scale_pure evaluates it.
-- We use the concrete quotient of BalancedTensorUniversalProperty so the
-- same chosen tensor objects carry the actions and all the induced maps.
-- The checked supplier is NotesProofs/WattsSupport.lean, SHA-256
-- 853d1dd0016bf0735f7a84559e2f1cbbb701fc3cb0e00395a0e138ffecb1f967.
-- ULift supplies the additional carrier universe in the reviewed endpoint.
private abbrev Tensor (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R) :=
  ChoiceFreeWatts.Tensor (action B) M

local instance (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R) :
    AddCommGroup (Tensor B M) :=
  ChoiceFreeWatts.tensorAddCommGroup (action B)

local instance (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R) :
    Module S (Tensor B M) :=
  ChoiceFreeWatts.outerModule (action B) (action_commutes B)

private abbrev obj (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R) :
    ModuleCat.{max v w t} S :=
  ModuleCat.of S (ULift.{t} (Tensor B M))

private abbrev pure (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R)
    (b : carrier B) (m : M) : obj.{r,s,v,w,t} B M :=
  ULift.up (ChoiceFreeWatts.pure (action B) b m)

private theorem pure_balanced (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R) :
    ChoiceFreeWatts.Balanced (action B) (pure.{r,s,v,w,t} B M) := by
  have h := ChoiceFreeWatts.pureBalanced (X := M) (action B)
  exact ⟨fun b b' m => congrArg ULift.up (h.1 b b' m),
    fun b m m' => congrArg ULift.up (h.2.1 b m m'),
    fun a b m => congrArg ULift.up (h.2.2 a b m)⟩

private theorem smul_pure (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R)
    (c : S) (b : carrier B) (m : M) :
    c • pure.{r,s,v,w,t} B M b m = pure.{r,s,v,w,t} B M (c • b) m :=
  congrArg ULift.up (ChoiceFreeWatts.scale_pure (action B) (action_commutes B) c b m)

-- Step 5.1 uses uniqueness on pure tensors. Transport tensorLift and
-- tensorLift_pure through the lift, and use tensorExt for uniqueness.
private theorem unique_lift (B : Bimod.{r,s,v} R S) (M : ModuleCat.{w} R)
    (A : AddCommGrpCat.{max v w t}) (p : carrier B → M → A)
    (hp : ChoiceFreeWatts.Balanced (action B) p) :
    ∃! h : obj.{r,s,v,w,t} B M →+ A, ∀ b m, h (pure.{r,s,v,w,t} B M b m) = p b m := by
  let up : Tensor B M ≃+ ULift.{t} (Tensor B M) := AddEquiv.ulift.symm
  let h := ChoiceFreeWatts.tensorLift (action B) p hp
  have eval (b : carrier B) (m : M) : h (ChoiceFreeWatts.pure (action B) b m) = p b m :=
    ChoiceFreeWatts.tensorLift_pure (action B) p hp b m
  refine ⟨h.comp up.symm.toAddMonoidHom, eval, ?_⟩
  intro g hg
  have eq : g.comp up.toAddMonoidHom = h :=
    ChoiceFreeWatts.tensorExt (action B) _ _ (fun b m => (hg b m).trans (eval b m).symm)
  ext x
  exact DFunLike.congr_fun eq x.down

private theorem hom_ext {B : Bimod.{r,s,v} R S} {M : ModuleCat.{w} R}
    {Y : ModuleCat.{max v w t} S} {f g : obj.{r,s,v,w,t} B M ⟶ Y}
    (h : ∀ b m, f (pure.{r,s,v,w,t} B M b m) = g (pure.{r,s,v,w,t} B M b m)) : f = g := by
  let up : Tensor B M ≃+ ULift.{t} (Tensor B M) := AddEquiv.ulift.symm
  have eq : f.hom.toAddMonoidHom.comp up.toAddMonoidHom =
      g.hom.toAddMonoidHom.comp up.toAddMonoidHom :=
    ChoiceFreeWatts.tensorExt (action B) _ _ h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun eq x.down

-- Proposition 6.3 extends the portal's descent argument to morphisms.
-- Naturality supplies right equivariance of u. The linearity of f supplies
-- left equivariance on the second factor. Left equivariance of u then
-- supplies the outer-linearity hypothesis of tensorLinearLift.
private theorem map_balanced {B B' : Bimod.{r,s,v} R S} {M M' : ModuleCat.{w} R}
    (u : B ⟶ B') (f : M ⟶ M') :
    ChoiceFreeWatts.Balanced (action B)
      (fun b m => pure.{r,s,v,w,t} B' M' ((u.hom.app ★) b) (f m)) := by
  have hp := pure_balanced.{r,s,v,w,t} B' M'
  refine ⟨?_, ?_, ?_⟩
  · intro b b' m
    simp only [map_add, hp.1]
  · intro b m m'
    simp only [map_add, hp.2.1]
  · intro a b m
    dsimp only
    rw [map_action, hp.2.2, map_smul]

private theorem map_outer_linear {B B' : Bimod.{r,s,v} R S} {M M' : ModuleCat.{w} R}
    (u : B ⟶ B') (f : M ⟶ M') (c : S) (b : carrier B) (m : M) :
    pure.{r,s,v,w,t} B' M' ((u.hom.app ★) (c • b)) (f m) =
      c • pure.{r,s,v,w,t} B' M' ((u.hom.app ★) b) (f m) := by
  rw [map_smul, smul_pure.{r,s,v,w,t}]

private def map {B B' : Bimod.{r,s,v} R S} {M M' : ModuleCat.{w} R}
    (u : B ⟶ B') (f : M ⟶ M') :
    obj.{r,s,v,w,t} B M ⟶ obj.{r,s,v,w,t} B' M' :=
  ModuleCat.ofHom <|
    (ChoiceFreeWatts.tensorLinearLift (action B) (action_commutes B)
      (fun b m => pure.{r,s,v,w,t} B' M' ((u.hom.app ★) b) (f m))
      (map_balanced.{r,s,v,w,t} u f) (map_outer_linear.{r,s,v,w,t} u f)).comp
        ULift.moduleEquiv.toLinearMap

private theorem map_pure {B B' : Bimod.{r,s,v} R S} {M M' : ModuleCat.{w} R}
    (u : B ⟶ B') (f : M ⟶ M') (b : carrier B) (m : M) :
    map.{r,s,v,w,t} u f (pure.{r,s,v,w,t} B M b m) =
      pure.{r,s,v,w,t} B' M' ((u.hom.app ★) b) (f m) :=
  ChoiceFreeWatts.tensorLinearLift_pure (action B) (action_commutes B)
    (fun b m => pure.{r,s,v,w,t} B' M' ((u.hom.app ★) b) (f m))
    (map_balanced.{r,s,v,w,t} u f) (map_outer_linear.{r,s,v,w,t} u f) b m

-- Use step 5.1's pure-tensor extensionality for identities, composition
-- and separate additivity. Fixing either factor keeps its identity map.
private def tensorFunctor :
    Bimod.{r,s,v} R S × ModuleCat.{w} R ⥤ ModuleCat.{max v w t} S where
  obj X := obj.{r,s,v,w,t} X.1 X.2
  map f := map.{r,s,v,w,t} f.1 f.2
  map_id X := by
    apply hom_ext
    intro b m
    change map.{r,s,v,w,t} (𝟙 X.1) (𝟙 X.2) (pure.{r,s,v,w,t} X.1 X.2 b m) =
      pure.{r,s,v,w,t} X.1 X.2 b m
    rw [map_pure.{r,s,v,w,t}]
    rfl
  map_comp f g := by
    apply hom_ext
    intro b m
    change map.{r,s,v,w,t} (f.1 ≫ g.1) (f.2 ≫ g.2) (pure.{r,s,v,w,t} _ _ b m) =
      map.{r,s,v,w,t} g.1 g.2 (map.{r,s,v,w,t} f.1 f.2 (pure.{r,s,v,w,t} _ _ b m))
    rw [map_pure.{r,s,v,w,t}, map_pure.{r,s,v,w,t}, map_pure.{r,s,v,w,t}]
    rfl

private theorem sectL_additive (M : ModuleCat.{w} R) :
    ((Prod.sectL (Bimod.{r,s,v} R S) M) ⋙ tensorFunctor.{r,s,v,w,t}).Additive := by
  constructor
  intro B B' u u'
  change map.{r,s,v,w,t} (u + u') (𝟙 M) =
    map.{r,s,v,w,t} u (𝟙 M) + map.{r,s,v,w,t} u' (𝟙 M)
  apply hom_ext.{r,s,v,w,t}
  intro b m
  change map.{r,s,v,w,t} (u + u') (𝟙 M) (pure.{r,s,v,w,t} B M b m) =
    map.{r,s,v,w,t} u (𝟙 M) (pure.{r,s,v,w,t} B M b m) +
      map.{r,s,v,w,t} u' (𝟙 M) (pure.{r,s,v,w,t} B M b m)
  rw [map_pure.{r,s,v,w,t}, map_pure.{r,s,v,w,t}, map_pure.{r,s,v,w,t}]
  exact (pure_balanced.{r,s,v,w,t} B' M).1 _ _ _

private theorem sectR_additive (B : Bimod.{r,s,v} R S) :
    ((Prod.sectR B (ModuleCat.{w} R)) ⋙ tensorFunctor.{r,s,v,w,t}).Additive := by
  constructor
  intro M M' f f'
  change map.{r,s,v,w,t} (𝟙 B) (f + f') =
    map.{r,s,v,w,t} (𝟙 B) f + map.{r,s,v,w,t} (𝟙 B) f'
  apply hom_ext.{r,s,v,w,t}
  intro b m
  change map.{r,s,v,w,t} (𝟙 B) (f + f') (pure.{r,s,v,w,t} B M b m) =
    map.{r,s,v,w,t} (𝟙 B) f (pure.{r,s,v,w,t} B M b m) +
      map.{r,s,v,w,t} (𝟙 B) f' (pure.{r,s,v,w,t} B M b m)
  rw [map_pure.{r,s,v,w,t}, map_pure.{r,s,v,w,t}, map_pure.{r,s,v,w,t}]
  exact (pure_balanced.{r,s,v,w,t} B M').2.1 _ _ _

end BimoduleTensorFunctorialityAux

theorem BimoduleTensorFunctoriality : (
∀ (R : Type r) [Ring R] (S : Type s) [Ring S],
  let Bimod := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{v} S)
  let star := CategoryTheory.SingleObj.star (MulOpposite R)
  let carrier := fun (B : Bimod) => B.obj.obj star
  let right := fun (B : Bimod) (a : R) (b : carrier B) =>
    (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) b
  let Balanced := fun (B : Bimod) (M : ModuleCat.{w} R)
      (A : Type (max v w t)) [AddCommGroup A] (p : carrier B → M → A) =>
    (∀ (b b' : carrier B) (m : M), p (b + b') m = p b m + p b' m) ∧
    (∀ (b : carrier B) (m m' : M), p b (m + m') = p b m + p b m') ∧
    (∀ (a : R) (b : carrier B) (m : M), p (right B a b) m = p b (a • m))
  ∃ (F : CategoryTheory.Functor (Prod Bimod (ModuleCat.{w} R)) (ModuleCat.{max v w t} S))
    (pure : ∀ (B : Bimod) (M : ModuleCat.{w} R), carrier B → M → F.obj (B, M)),
    (∀ (B : Bimod) (M : ModuleCat.{w} R),
      Balanced B M ((F.obj (B, M)) : Type (max v w t)) (pure B M) ∧
      (∀ (A : AddCommGrpCat.{max v w t}) (p : carrier B → M → A),
        Balanced B M A p →
        ∃! h : AddMonoidHom (F.obj (B, M)) A, ∀ b m, h (pure B M b m) = p b m) ∧
      (∀ (a : S) (b : carrier B) (m : M), a • pure B M b m = pure B M (a • b) m)) ∧
    (∀ {B B' : Bimod} {M M' : ModuleCat.{w} R}
        (u : Quiver.Hom B B') (f : Quiver.Hom M M') (b : carrier B) (m : M),
      (F.map (CategoryTheory.Prod.mkHom u f)) (pure B M b m) =
        pure B' M' ((u.hom.app star) b) (f m)) ∧
    (∀ M : ModuleCat.{w} R,
      CategoryTheory.Functor.Additive (CategoryTheory.Functor.comp
        (CategoryTheory.Prod.sectL Bimod M) F)) ∧
    (∀ B : Bimod,
      CategoryTheory.Functor.Additive (CategoryTheory.Functor.comp
        (CategoryTheory.Prod.sectR B (ModuleCat.{w} R)) F))
) :=
(by
  intro R _ S _ Bimod star carrier right Balanced
  exact ⟨BimoduleTensorFunctorialityAux.tensorFunctor.{r,s,v,w,t},
    BimoduleTensorFunctorialityAux.pure.{r,s,v,w,t},
    fun B M => ⟨BimoduleTensorFunctorialityAux.pure_balanced.{r,s,v,w,t} B M,
      BimoduleTensorFunctorialityAux.unique_lift.{r,s,v,w,t} B M,
      BimoduleTensorFunctorialityAux.smul_pure.{r,s,v,w,t} B M⟩,
    fun u f b m => BimoduleTensorFunctorialityAux.map_pure.{r,s,v,w,t} u f b m,
    BimoduleTensorFunctorialityAux.sectL_additive.{r,s,v,w,t},
    BimoduleTensorFunctorialityAux.sectR_additive.{r,s,v,w,t}⟩)

#print axioms BimoduleTensorFunctoriality
