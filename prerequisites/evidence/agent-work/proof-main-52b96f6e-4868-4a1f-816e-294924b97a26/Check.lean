import Mathlib.RepresentationTheory.Rep.Iso
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.GroupAlgebraRingLaws

set_option maxHeartbeats 2000000

universe u v w

section

open CategoryTheory

variable {k : Type u} [Field k] {G : Type v} [Group G]

local notation "A" => MonoidAlgebra k G
local notation "F" => Rep.toModuleMonoidAlgebra (k := k) (G := G)
local notation "H" => Rep.ofModuleMonoidAlgebra (k := k) (G := G)

-- Alphabeta Math step 6.1, starting from a group-algebra module.
-- The counit acts as the identity, and its linearity supplies agreement of
-- the recovered scalar action at every group-algebra element. The additive
-- group is unchanged, so equality of module structures suffices.
private theorem representationModule_roundTripModule (M : ModuleCat.{w} A) :
    (H ⋙ F).obj M = M := by
  have sameScalar := (Rep.counitIso (k := k) (G := G) (M := M)).hom.hom.map_smul
  let recovered : Module A M := ((H ⋙ F).obj M).isModule
  have sameModule : recovered = M.isModule := by
    apply Module.ext'
    intro a x
    exact sameScalar a x
  exact congrArg (@ModuleCat.of A _ M M.isAddCommGroup) sameModule

-- The representation field of the bundle depends on its module instance.
-- Transport along equality of those instances before using extensionality.
private theorem representationModule_repOf_eq {X : Type w} [AddCommGroup X]
    (P Q : Module k X)
    (ρ : @Representation k G X _ _ _ P) (σ : @Representation k G X _ _ _ Q)
    (sameModule : P = Q)
    (sameAction : ∀ (g : G) (x : X), (ρ g).toFun x = (σ g).toFun x) :
    @Rep.of k G _ _ X _ P ρ = @Rep.of k G _ _ X _ Q σ := by
  subst Q
  have h : ρ = σ := by
    ext g x
    exact sameAction g x
  rw [h]

-- Alphabeta Math step 6.1, starting from a representation.
-- Restriction along the scalar map recovers the original k-action. The
-- recovered action of each g is the action of [g], hence the original ρ g.
private theorem representationModule_roundTripRep (X : Rep.{w} k G) :
    (F ⋙ H).obj X = X := by
  have sameScalar := Representation.asModuleEquiv_symm_map_smul (k := k) (G := G) X.ρ
  have recoveredAction := Representation.ofModule_asModule_act (k := k) (G := G) X.ρ
  let recovered : Module k X := ((F ⋙ H).obj X).hV2
  let action : @Representation k G X _ _ _ recovered := ((F ⋙ H).obj X).ρ
  have sameModule : recovered = X.hV2 :=
    Module.ext' recovered X.hV2 fun a x => (sameScalar a x).symm
  have sameAction (g : G) (x : X) : (action g).toFun x = (X.ρ g).toFun x :=
    recoveredAction g x
  exact representationModule_repOf_eq recovered X.hV2 action X.ρ sameModule sameAction

end

theorem RepresentationModuleCorrespondence : (
∀ (k : Type u) [Field k] (G : Type v) [Group G],
  let U := CategoryTheory.Functor.comp
    (CategoryTheory.forget₂ (Rep.{w} k G) (ModuleCat.{w} k))
    (CategoryTheory.forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w})
  let V := CategoryTheory.forget₂ (ModuleCat.{w} (MonoidAlgebra k G)) AddCommGrpCat.{w}
  ∃ (F : CategoryTheory.Functor (Rep.{w} k G) (ModuleCat.{w} (MonoidAlgebra k G)))
    (H : CategoryTheory.Functor (ModuleCat.{w} (MonoidAlgebra k G)) (Rep.{w} k G)),
    CategoryTheory.Functor.comp F H = CategoryTheory.Functor.id (Rep.{w} k G) ∧
    CategoryTheory.Functor.comp H F =
      CategoryTheory.Functor.id (ModuleCat.{w} (MonoidAlgebra k G)) ∧
    CategoryTheory.Functor.comp F V = U ∧
    CategoryTheory.Functor.comp H U = V
) :=
(by
  intro k _ G _
  -- Theorem 7.4 in the lecture notes asks for inverse functors preserving the
  -- underlying groups. Alphabeta Math steps 1.1–3.1 extend the action by the
  -- monoid-algebra lift, and step 4.1 restricts along the scalar and basis
  -- maps. The pinned functors implement these constructions over a
  -- commutative ring and monoid. A field and group supply those instances.
  -- They use the canonical MonoidAlgebra whose convolution and scalar laws
  -- are recorded in GroupAlgebraRingLaws. Only algebra elements have finite
  -- support, so G and the representation carrier can be arbitrary.
  let equivalence := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  refine ⟨equivalence.functor, equivalence.inverse, ?_, ?_, ?_, ?_⟩
  -- Step 6.1 supplies equality of actions. The coordinator's retained check
  -- turns this into literal functor equalities by checking that the natural
  -- isomorphisms have precisely the maps induced by the object equalities.
  · refine CategoryTheory.Functor.ext_of_iso equivalence.unitIso.symm
      representationModule_roundTripRep ?_
    intro X
    have coeEqToHom (Y Z : Rep.{w} k G) (h : Y = Z) :
        ⇑(CategoryTheory.eqToHom h : Y ⟶ Z) =
          cast (congrArg Rep.V h) := by
      cases h
      rfl
    -- Both the unit inverse and the cast act as the identity on elements.
    ext x
    exact congrFun (coeEqToHom _ _ (representationModule_roundTripRep X)).symm x
  · refine CategoryTheory.Functor.ext_of_iso equivalence.counitIso
      representationModule_roundTripModule ?_
    intro M
    have coeEqToHom (N P : ModuleCat.{w} (MonoidAlgebra k G)) (h : N = P) :
        ⇑(CategoryTheory.eqToHom h : N ⟶ P) =
          cast (congrArg ModuleCat.carrier h) := by
      cases h
      rfl
    -- The counit also acts as the identity on elements.
    ext x
    exact congrFun (coeEqToHom _ _ (representationModule_roundTripModule M)).symm x
  -- Step 5.1 is implemented by the functor maps. Extension checks linearity
  -- by induction on group-algebra elements using the intertwining equation.
  -- Restriction checks linearity and equivariance at scalars and basis
  -- elements. Both maps retain the given additive map, and the underlying
  -- additive group objects are definitionally equal.
  · exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)
  · exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl))

#print axioms RepresentationModuleCorrespondence
