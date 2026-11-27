import WattsFoundation.General.WattsFreeComparison
import WattsFoundation.PresentationFiveLemma
import WattsFoundation.CokernelExact

/-! The free-presentation step of Eilenberg–Watts for arbitrary rings, in a
single fixed Lean universe. -/

set_option backward.isDefEq.respectTransparency false

namespace WattsFoundation.General

universe u v
open CategoryTheory

variable {A B : Type u} [Ring A] [Ring B]
variable (F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B) [F.Additive]
local instance General_WattsAllComparison_local1 : Module (MulOpposite A) (ChoiceFreeWatts.M F) := wattsRightModule F
local instance General_WattsAllComparison_local2 : SMulCommClass (MulOpposite A) B (ChoiceFreeWatts.M F) := wattsRight_commutes F
local instance General_WattsAllComparison_local3 {X : Type (max u v)} [AddCommGroup X] [Module A X] :
    AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := A) (M := ChoiceFreeWatts.M F)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup _
local instance General_WattsAllComparison_local4 {X : Type (max u v)} [AddCommGroup X] [Module A X] :
    Module B (ChoiceFreeWatts.Tensor (rightAction (R := A) (M := ChoiceFreeWatts.M F)) X) :=
  ChoiceFreeWatts.outerModule _ right_commute

/-- Under the explicit cokernel and coproduct preservation hypotheses, the
canonical Eilenberg–Watts comparison is bijective on every module. -/
theorem watts_comparison_bijective
    (hcokern :
      ∀ (L P X : ModuleCat.{max u v} A) (f : L ⟶ P) (q : P ⟶ X),
      f ≫ q = ModuleCat.ofHom 0 →
      (∀ (Z : ModuleCat.{max u v} A) (g : P ⟶ Z),
        f ≫ g = ModuleCat.ofHom 0 → ∃! d : X ⟶ Z, q ≫ d = g) →
      F.map f ≫ F.map q = ModuleCat.ofHom 0 ∧
      ∀ (Z : ModuleCat.{max u v} B) (g : F.obj P ⟶ Z),
        F.map f ≫ g = ModuleCat.ofHom 0 → ∃! d : F.obj X ⟶ Z, F.map q ≫ d = g)
    (hcoprod :
      ∀ (I : Type (max u v)) (D : I → ModuleCat.{max u v} A) (P : ModuleCat.{max u v} A)
        (ι : ∀ i, D i ⟶ P),
      (∀ (Q : ModuleCat.{max u v} A) (legs : ∀ i, D i ⟶ Q),
        ∃! d : P ⟶ Q, ∀ i, ι i ≫ d = legs i) →
      ∀ (Q : ModuleCat.{max u v} B) (legs : ∀ i, F.obj (D i) ⟶ Q),
        ∃! d : F.obj P ⟶ Q, ∀ i, F.map (ι i) ≫ d = legs i)
    (X : ModuleCat.{max u v} A) : Function.Bijective (ChoiceFreeWatts.comparison F X) := by
  have free_bij (I : Type (max u v)) :
      Function.Bijective (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.freeObj (A := A) I)) :=
    watts_comparison_free_bijective F I
      (hcoprod I (fun _ => ChoiceFreeWatts.regular A) (ChoiceFreeWatts.freeObj I)
        (ChoiceFreeWatts.freeIncl I) (ChoiceFreeWatts.freeCoproduct I))
  let f := ChoiceFreeWatts.relationsMap X
  let q := ChoiceFreeWatts.cover X
  have qsurj : Function.Surjective q.hom := fun x =>
    ⟨ChoiceFreeWatts.sectionOnGenerators X x, ChoiceFreeWatts.cover_section X x⟩
  have qexact (n : ChoiceFreeWatts.freeObj (A := A) X) (hn : q.hom n = 0) :
      ∃ l, f.hom l = n := by
    let k : ChoiceFreeWatts.Relations X := ⟨n, hn⟩
    refine ⟨(ChoiceFreeWatts.freeIncl (ChoiceFreeWatts.Relations X) k).hom (⟨1⟩ : ULift.{v} A), ?_⟩
    exact ChoiceFreeWatts.freeDesc_gen (fun i : ChoiceFreeWatts.Relations X => i.val) k
  have qzero (l : ChoiceFreeWatts.freeObj (A := A) (ChoiceFreeWatts.Relations X)) :
      q.hom (f.hom l) = 0 :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (ChoiceFreeWatts.relations_zero X)) l
  have tf := concrete_tensor_preserves_cokernel (M := ChoiceFreeWatts.M F) (S := B)
    f.hom q.hom qsurj qexact qzero
  rw [watts_concrete_map F f, watts_concrete_map F q] at tf
  let tfmap := (ChoiceFreeWatts.tensorMap F f).hom
  let tqmap := (ChoiceFreeWatts.tensorMap F q).hom
  let ff := (F.map f).hom
  let fq := (F.map q).hom
  have tsurj : Function.Surjective tqmap :=
    cokernel_factorization_surjective tfmap tqmap tf.1 tf.2
  have hk := hcokern _ _ _ f q (ChoiceFreeWatts.relations_zero X) (ChoiceFreeWatts.cover_cokernel X)
  have fsurj : Function.Surjective fq := ChoiceFreeWatts.cokernelSurjective (F.map f) (F.map q) hk.1 hk.2
  have ffactor (Z : Type (max u v)) [AddCommGroup Z] [Module B Z]
      (g : F.obj (ChoiceFreeWatts.freeObj (A := A) X) →ₗ[B] Z)
      (gzero : ∀ l, g (ff l) = 0) :
      ∃ d : F.obj X →ₗ[B] Z, ∀ p, d (fq p) = g p := by
    have hz : F.map f ≫ ModuleCat.ofHom g = ModuleCat.ofHom 0 := by
      apply ModuleCat.hom_ext
      ext l
      exact gzero l
    obtain ⟨d, hd, _⟩ := hk.2 (ModuleCat.of B Z) (ModuleCat.ofHom g) hz
    exact ⟨d.hom, fun p => DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd) p⟩
  have fexact : ∀ p, fq p = 0 → ∃ l, ff l = p :=
    cokernel_universal_exact ff fq ffactor
  apply presentation_comparison_bijective tfmap tqmap ff fq
    (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.freeObj (ChoiceFreeWatts.Relations X)))
    (ChoiceFreeWatts.comparison F (ChoiceFreeWatts.freeObj X))
    (ChoiceFreeWatts.comparison F X)
  · intro l
    exact DFunLike.congr_fun (ChoiceFreeWatts.comparison_naturality F f) l
  · intro p
    exact DFunLike.congr_fun (ChoiceFreeWatts.comparison_naturality F q) p
  · exact tf.1
  · exact fexact
  · exact tsurj
  · exact fsurj
  · exact (free_bij (ChoiceFreeWatts.Relations X)).2
  · exact free_bij X

#print axioms watts_comparison_bijective

end WattsFoundation.General
