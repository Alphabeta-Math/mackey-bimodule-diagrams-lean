import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.RingTheory.Finiteness.Basic
import MackeyDiagrams

set_option maxHeartbeats 2000000

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace SmallProjectiveGeneratorProof

private noncomputable abbrev sumCocone {B : Type v} [Ring B] {I : Type v}
    (Y : Discrete I ⥤ ModuleCat.{v} B) : Cocone Y := by
  classical
  exact
    { pt := ModuleCat.of B (DFinsupp fun i : I => Y.obj ⟨i⟩)
      ι :=
        { app := fun j => ModuleCat.ofHom
            (DFinsupp.lsingle (R := B) (M := fun i : I => ↑(Y.obj ⟨i⟩)) j.as)
          naturality := by
            intro j k f
            have h : j = k := IsDiscrete.eq_of_hom f
            subst k
            have hf : f = 𝟙 j := Subsingleton.elim _ _
            simp [hf] } }

private noncomputable def sumIsColimit {B : Type v} [Ring B] {I : Type v}
    (Y : Discrete I ⥤ ModuleCat.{v} B) : IsColimit (sumCocone Y) := by
  classical
  let legs (s : Cocone Y) (i : I) : (Y.obj ⟨i⟩) →ₗ[B] s.pt := (s.ι.app ⟨i⟩).hom
  refine
    { desc := fun s => ModuleCat.ofHom (DFinsupp.lsum ℕ (legs s))
      fac := ?_
      uniq := ?_ }
  · rintro s ⟨i⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DFinsupp.lsum_single ℕ (legs s) i x
  · intro s f hf
    apply ModuleCat.hom_ext
    apply DFinsupp.lhom_ext
    intro i x
    calc
      f.hom (DFinsupp.single i x) = (legs s i) x :=
        congrArg (fun g : Y.obj ⟨i⟩ ⟶ s.pt => g.hom x) (hf ⟨i⟩)
      _ = _ := (DFinsupp.lsum_single ℕ (legs s) i x).symm

private noncomputable def comparison {B : Type v} [Ring B] {I : Type v}
    (P : ModuleCat.{v} B) (Y : Discrete I ⥤ ModuleCat.{v} B) :
    (sumCocone (Y ⋙ preadditiveCoyonedaObj P)).pt ⟶
      (preadditiveCoyonedaObj P).obj (sumCocone Y).pt :=
  (sumIsColimit (Y ⋙ preadditiveCoyonedaObj P)).desc
    ((preadditiveCoyonedaObj P).mapCocone (sumCocone Y))

private noncomputable def comparisonHom {B : Type v} [Ring B] {I : Type v}
    (P : ModuleCat.{v} B) (Y : Discrete I ⥤ ModuleCat.{v} B) :
    (DFinsupp fun i : I => P ⟶ Y.obj ⟨i⟩) →ₗ[(End P)ᵐᵒᵖ]
      (P ⟶ ModuleCat.of B (DFinsupp fun i : I => Y.obj ⟨i⟩)) :=
  (comparison P Y).hom

private theorem comparison_apply {B : Type v} [Ring B] {I : Type v}
    (P : ModuleCat.{v} B) (Y : Discrete I ⥤ ModuleCat.{v} B)
    (i : I) (a : DFinsupp fun j : I => P ⟶ Y.obj ⟨j⟩) (x : P) :
    (comparisonHom P Y a).hom x i = (a i).hom x := by
  classical
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha j f a hj hf ih =>
    have h := (sumIsColimit (Y ⋙ preadditiveCoyonedaObj P)).fac
      ((preadditiveCoyonedaObj P).mapCocone (sumCocone Y)) ⟨j⟩
    have hsingle : comparisonHom P Y (DFinsupp.single j f) =
        f ≫ (sumCocone Y).ι.app ⟨j⟩ :=
      congrArg (fun g =>
        (g : (preadditiveCoyonedaObj P).obj (Y.obj ⟨j⟩) ⟶ _).hom f) h
    rw [map_add]
    simp only [ModuleCat.hom_add, LinearMap.add_apply, DFinsupp.add_apply, ih]
    congr 1
    rw [hsingle]
    change DFinsupp.single (β := fun j : I => ↑(Y.obj ⟨j⟩)) j (f.hom x) i =
      (DFinsupp.single (β := fun j : I => P ⟶ Y.obj ⟨j⟩) j f i).hom x
    by_cases hij : j = i
    · subst j
      simp
    · rw [DFinsupp.single_eq_of_ne (Ne.symm hij), DFinsupp.single_eq_of_ne (Ne.symm hij)]
      simp

/- Alphabeta Math, Step 1.1.
   https://alphabetamath.cc/item/lem-small-projective-modules-are-exactly-finitely-generated-projective-modules
   Use the dependent direct sum both before and after taking Hom.
   We prove that the coproduct comparison is bijective, using its coordinate formula.
   Compute the comparison on modules over the opposite endomorphism ring. The additive
   forgetful functor preserves and reflects the coproducts, connecting this computation
   to the abelian-group-valued Hom functor in the statement.
   This direction uses only finite generation. -/
private theorem preservesCoproductsOfFinite {B : Type v} [Ring B] (P : ModuleCat.{v} B)
    (hP : Module.Finite B P) (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (Opposite.op P)) := by
  classical
  let F := preadditiveCoyonedaObj P
  have : PreservesColimitsOfShape (Discrete I) F := by
    constructor
    intro Y
    apply preservesColimit_of_preserves_colimit_cocone (sumIsColimit Y)
    have hbij : Function.Bijective (comparisonHom P Y) := by
      constructor
      · intro a b hab
        apply DFinsupp.ext
        intro i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rw [← comparison_apply P Y i a x, ← comparison_apply P Y i b x, hab]
      · intro f
        obtain ⟨g, hg⟩ := hP.fg_top
        let s : Finset I := g.biUnion fun x => (f.hom x).support
        let coord (i : I) : P ⟶ Y.obj ⟨i⟩ :=
          ModuleCat.ofHom ((DFinsupp.lapply (R := B) (M := fun j : I => ↑(Y.obj ⟨j⟩)) i).comp f.hom)
        have coord_eq_zero (i : I) (hi : i ∉ s) : coord i = 0 := by
          have hle : Submodule.span B (g : Set P) ≤ LinearMap.ker (coord i).hom := by
            apply Submodule.span_le.mpr
            intro x hx
            apply LinearMap.mem_ker.mpr
            change f.hom x i = 0
            apply DFinsupp.notMem_support_iff.mp
            intro hmem
            exact hi (Finset.mem_biUnion.mpr ⟨x, hx, hmem⟩)
          rw [hg, top_le_iff] at hle
          apply ModuleCat.hom_ext
          simpa only [ModuleCat.hom_zero] using LinearMap.ker_eq_top.mp hle
        let a : DFinsupp fun i : I => P ⟶ Y.obj ⟨i⟩ := DFinsupp.mk s (fun i => coord i)
        have ha (i : I) : a i = coord i := by
          by_cases hi : i ∈ s
          · exact DFinsupp.mk_of_mem hi
          · exact (DFinsupp.mk_of_notMem hi).trans (coord_eq_zero i hi).symm
        refine ⟨a, ?_⟩
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply DFinsupp.ext
        intro i
        rw [comparison_apply, ha]
        rfl
    have : IsIso ((sumIsColimit (Y ⋙ F)).desc (F.mapCocone (sumCocone Y))) :=
      (ConcreteCategory.isIso_iff_bijective (comparison P Y)).mpr hbij
    exact (sumIsColimit (Y ⋙ F)).ofPointIso
  let U := forget₂ (ModuleCat (End P)ᵐᵒᵖ) AddCommGrpCat
  have : PreservesColimitsOfShape (Discrete I) U :=
    ModuleCat.forget₂PreservesColimitsOfShape (End P)ᵐᵒᵖ (Discrete I)
  change PreservesColimitsOfShape (Discrete I) (F ⋙ U)
  infer_instance

/- Alphabeta Math Step 1.2. Use the direct sum of copies of the regular module as the
   free cover. The explicit injections give its generators and show the cover is onto.
   This realizes the free cover in the direct-sum model used by the projection formula.
   The section uses only projectivity of P.
   The comparison forces the section’s coordinates to vanish outside one finite set of
   indices, so the corresponding generators span P. -/
private theorem finiteOfPreservesCoproducts {B : Type v} [Ring B] (P : ModuleCat.{v} B)
    [Projective P] (h :
      ∀ I : Type v, PreservesColimitsOfShape (Discrete I)
        (preadditiveCoyoneda.obj (Opposite.op P))) : Module.Finite B P := by
  classical
  let F := preadditiveCoyonedaObj P
  let Y := Discrete.functor (fun _ : P => ModuleCat.of B B)
  let cover : (sumCocone Y).pt ⟶ P :=
    ModuleCat.ofHom (DFinsupp.lsum (R := B) (M := fun _ : P => B) ℕ
      (LinearMap.toSpanSingleton B P))
  have : Epi cover := (ModuleCat.epi_iff_surjective cover).mpr (by
    intro p
    refine ⟨DFinsupp.single (β := fun _ : P => B) p 1, ?_⟩
    change DFinsupp.lsum (R := B) (M := fun _ : P => B) ℕ
      (LinearMap.toSpanSingleton B P) (DFinsupp.single p 1) = p
    rw [DFinsupp.lsum_single, LinearMap.toSpanSingleton_apply_one])
  let sectionMap : P ⟶ (sumCocone Y).pt := Projective.factorThru (𝟙 P) cover
  have section_comp : sectionMap ≫ cover = 𝟙 P := Projective.factorThru_comp _ _
  let U := forget₂ (ModuleCat (End P)ᵐᵒᵖ) AddCommGrpCat
  have : PreservesColimitsOfShape (Discrete P) (F ⋙ U) := h P
  have : ReflectsColimit (Y ⋙ F) U :=
    (ModuleCat.reflectsColimitsOfShape (End P)ᵐᵒᵖ (Discrete P)).reflectsColimit
  have hmap : IsColimit (F.mapCocone (sumCocone Y)) :=
    isColimitOfReflects U (isColimitOfPreserves (F ⋙ U) (sumIsColimit Y))
  have : IsIso (comparison P Y) :=
    ((sumIsColimit (Y ⋙ F)).nonempty_isColimit_iff_isIso_desc).mp ⟨hmap⟩
  have hsurj : Function.Surjective (comparisonHom P Y) :=
    (ConcreteCategory.bijective_of_isIso (comparison P Y)).2
  obtain ⟨a, ha⟩ := hsurj sectionMap
  refine ⟨⟨a.support, top_unique ?_⟩⟩
  intro p _
  have hsplit : cover.hom (sectionMap.hom p) = p :=
    congrArg (fun f : P ⟶ P => f.hom p) section_comp
  rw [← hsplit]
  change DFinsupp.lsum (R := B) (M := fun _ : P => B) ℕ
    (LinearMap.toSpanSingleton B P) (sectionMap.hom p) ∈ _
  rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  have hai : i ∈ a.support := by
    apply DFinsupp.mem_support_iff.mpr
    intro hz
    have hcoord := comparison_apply P Y i a p
    rw [ha, hz, ModuleCat.hom_zero, LinearMap.zero_apply] at hcoord
    exact DFinsupp.mem_support_iff.mp hi hcoord
  exact Submodule.smul_mem _ _ (Submodule.subset_span hai)

end SmallProjectiveGeneratorProof

open SmallProjectiveGeneratorProof

/- Alphabeta Math Steps 2.1 and 3.1. The separator condition is shared.
   The projectivity bridge applies because the ring has the module universe. -/
theorem SmallProjectiveGenerator_module_iff (B : Type v) [Ring B] (P : ModuleCat.{v} B) :
    (Projective P ∧ IsSeparator P ∧ ∀ I : Type v,
      PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (Opposite.op P))) ↔
    (Module.Finite B P ∧ Module.Projective B P ∧ IsSeparator P) := by
  have hproj : Module.Projective B P ↔ Projective P :=
    IsProjective.iff_projective (R := B) P
  constructor
  · rintro ⟨hp, hs, hc⟩
    have : Projective P := hp
    exact ⟨finiteOfPreservesCoproducts P hc, hproj.mpr hp, hs⟩
  · rintro ⟨hf, hp, hs⟩
    exact ⟨hproj.mp hp, hs, preservesCoproductsOfFinite P hf⟩

/- Alphabeta Math Step 2.2. The regular module is finite and projective by its rank-one
   free module structure. Evaluation at 1 on maps from the regular module detects
   equality of morphisms. The reverse direction of the equivalence supplies smallness. -/
theorem SmallProjectiveGenerator_regular (B : Type v) [Ring B] :
    Projective (ModuleCat.of B B) ∧ IsSeparator (ModuleCat.of B B) ∧
      ∀ I : Type v, PreservesColimitsOfShape (Discrete I)
        (preadditiveCoyoneda.obj (Opposite.op (ModuleCat.of B B))) := by
  apply (SmallProjectiveGenerator_module_iff B (ModuleCat.of B B)).mpr
  refine ⟨inferInstance, inferInstance, (isSeparator_def _).mpr ?_⟩
  intro X Y f g h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := h (ModuleCat.ofHom (LinearMap.toSpanSingleton B X x))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] using
      congrArg (fun k : ModuleCat.of B B ⟶ Y => k.hom (1 : B)) hx

noncomputable def SmallProjectiveGenerator : ((∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.Limits.HasColimitsOfSize.{v,v} C], C → Prop) ×
  (Σ smallInModules : ∀ (B : Type v) [Ring B], ModuleCat.{v} B → Prop,
    { progenerator : ∀ (B : Type v) [Ring B], ModuleCat.{v} B → Prop //
      (∀ (B : Type v) [Ring B] (P : ModuleCat.{v} B),
        smallInModules B P ↔ progenerator B P) ∧
      (∀ (B : Type v) [Ring B], smallInModules B (ModuleCat.of B B)) })) := (let smallInModules := fun (B : Type v) [Ring B] (P : ModuleCat.{v} B) =>
  CategoryTheory.Projective P ∧ CategoryTheory.IsSeparator P ∧
    ∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Discrete I)
      (CategoryTheory.preadditiveCoyoneda.obj (Opposite.op P))
let progenerator := fun (B : Type v) [Ring B] (P : ModuleCat.{v} B) =>
  Module.Finite B P ∧ Module.Projective B P ∧ CategoryTheory.IsSeparator P
⟨(fun (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
      [CategoryTheory.Limits.HasColimitsOfSize.{v,v} C] (P : C) =>
    CategoryTheory.Projective P ∧ CategoryTheory.IsSeparator P ∧
      ∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape
        (CategoryTheory.Discrete I)
        (CategoryTheory.preadditiveCoyoneda.obj (Opposite.op P))),
  ⟨smallInModules, ⟨progenerator,
    ⟨(show ∀ (B : Type v) [Ring B] (P : ModuleCat.{v} B),
        smallInModules B P ↔ progenerator B P from
      SmallProjectiveGenerator_module_iff),
     (show ∀ (B : Type v) [Ring B], smallInModules B (ModuleCat.of B B) from
      SmallProjectiveGenerator_regular)⟩⟩⟩⟩)

#print axioms SmallProjectiveGenerator
