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
