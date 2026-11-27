import Mathlib.RepresentationTheory.Rep.Iso

open CategoryTheory

universe u v w

section
variable {k : Type u} [Field k] {G : Type v} [Group G]
local notation "A" => MonoidAlgebra k G
local notation "F" => Rep.toModuleMonoidAlgebra (k := k) (G := G)
local notation "H" => Rep.ofModuleMonoidAlgebra (k := k) (G := G)

private theorem check_module_obj (M : ModuleCat.{w} A) :
    (H ⋙ F).obj M = M := by
  have hS := (Rep.counitIso (k := k) (G := G) (M := M)).hom.hom.map_smul
  let Q : Module A M := ((H ⋙ F).obj M).isModule
  have hQ : Q = M.isModule := by
    apply Module.ext'
    intro r x
    exact hS r x
  exact congrArg (@ModuleCat.of A _ M M.isAddCommGroup) hQ

private theorem check_rep_pack {X : Type w} [AddCommGroup X] (P Q : Module k X)
    (ρ : @Representation k G X _ _ _ P) (σ : @Representation k G X _ _ _ Q)
    (hM : P = Q) (hρ : ∀ (g : G) (x : X), (ρ g).toFun x = (σ g).toFun x) :
    @Rep.of k G _ _ X _ P ρ = @Rep.of k G _ _ X _ Q σ := by
  subst Q
  have he : ρ = σ := by
    ext g x
    exact hρ g x
  rw [he]

private theorem check_rep_obj (V : Rep.{w} k G) :
    (F ⋙ H).obj V = V := by
  have hScalar := Representation.asModuleEquiv_symm_map_smul (k := k) (G := G) V.ρ
  have hAct := Representation.ofModule_asModule_act (k := k) (G := G) V.ρ
  let P : Module k V := ((F ⋙ H).obj V).hV2
  let ρ : @Representation k G V _ _ _ P := ((F ⋙ H).obj V).ρ
  have hM : P = V.hV2 :=
    Module.ext' P V.hV2 fun a x =>
      (hScalar a x).symm
  have hρ (g : G) (x : V) : (ρ g).toFun x = (V.ρ g).toFun x :=
    hAct g x
  exact check_rep_pack P V.hV2 ρ V.ρ hM hρ

private theorem check_module_iso (M N : ModuleCat.{w} A) (e : M = N)
    (h : (M : Type w) = N := congrArg ModuleCat.carrier e) :
    ⇑(eqToHom e : M ⟶ N) = cast h := by
  cases e
  rfl

private theorem check_rep_iso (V W : Rep.{w} k G) (e : V = W)
    (h : (V : Type w) = W := congrArg Rep.V e) :
    ⇑(eqToHom e : V ⟶ W) = cast h := by
  cases e
  rfl

end

theorem RepresentationModuleCorrespondence :
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
        CategoryTheory.Functor.comp H U = V := by
  intro k _ G _
  let e := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  refine ⟨e.functor, e.inverse, ?_, ?_, ?_, ?_⟩
  · refine Functor.ext_of_iso e.unitIso.symm check_rep_obj ?_
    intro V
    ext x
    exact congrFun (check_rep_iso _ _ (check_rep_obj V)).symm x
  · refine Functor.ext_of_iso e.counitIso check_module_obj ?_
    intro M
    ext x
    exact congrFun (check_module_iso _ _ (check_module_obj M)).symm x
  · exact Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)
  · exact Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

#print axioms RepresentationModuleCorrespondence
