import MackeyDiagrams.DiagramComposition
import MackeyDiagrams.IndexedQuotient
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Hom

/-! A family of boundary words gives a unital quotient algebra of block maps.
Generators are diagram classes between any pair of selected boundaries. For
finitely many boundaries, the global identity is the sum of the diagrammatic
identity blocks; for an infinite family the construction adjoins a global unit. -/
namespace MackeyDiagrams.BlockAlgebra
universe u v w
variable {U : Type u} [Group U] {K H : Subgroup U}
variable (R : Type v) [CommRing R] {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (word : ι → Word K H)

abbrev Space (i : ι) := (word i).basis.carrier →₀ R
abbrev Total := ∀ i, Space R word i
abbrev Generator := Σ i, Σ j, DiagramVectorSpace.MapClasses R (word i) (word j)

noncomputable def evalBlock (g : Generator R word) : Module.End R (Total R word) :=
  (LinearMap.single R (Space R word) g.2.1).comp
    ((DiagramVectorSpace.classEval R (word g.1) (word g.2.1) g.2.2).comp (LinearMap.proj g.1))

omit [Fintype ι] in
theorem block_comp (i j k : ι)
    (x : DiagramVectorSpace.MapClasses R (word i) (word j))
    (y : DiagramVectorSpace.MapClasses R (word j) (word k)) :
    evalBlock R word ⟨j, k, y⟩ * evalBlock R word ⟨i, j, x⟩ =
      evalBlock R word ⟨i, k, DiagramVectorSpace.stack R (word i) (word j) (word k) x y⟩ := by
  apply LinearMap.ext
  intro z
  simp [evalBlock, DiagramVectorSpace.classEval_stack]

omit [Fintype ι] in
theorem block_comp_incompatible (i j k l : ι) (h : k ≠ j)
    (x : DiagramVectorSpace.MapClasses R (word i) (word j))
    (y : DiagramVectorSpace.MapClasses R (word k) (word l)) :
    evalBlock R word ⟨k, l, y⟩ * evalBlock R word ⟨i, j, x⟩ = 0 := by
  apply LinearMap.ext
  intro z
  simp [evalBlock, Pi.single_eq_of_ne h]

theorem sum_block_identity :
    (∑ i : ι, evalBlock R word ⟨i, i, DiagramVectorSpace.identityClass R (word i)⟩) = 1 := by
  apply LinearMap.ext
  intro z
  funext i
  simp [evalBlock, DiagramVectorSpace.classEval_identity, LinearMap.sum_apply]

noncomputable def evaluate : FreeAlgebra R (Generator R word) →ₐ[R] Module.End R (Total R word) :=
  FreeAlgebra.lift R (evalBlock R word)

abbrev Classes := (RingCon.ker (evaluate R word).toRingHom).Quotient

omit [Fintype ι] in
theorem classes_eq_iff (a b : FreeAlgebra R (Generator R word)) :
    (RingCon.ker (evaluate R word).toRingHom).mkₐ R a =
      (RingCon.ker (evaluate R word).toRingHom).mkₐ R b ↔
      evaluate R word a = evaluate R word b := by
  change (⟦a⟧ : Classes R word) = ⟦b⟧ ↔ _
  exact RingCon.eq _

noncomputable def blockClass (g : Generator R word) : Classes R word :=
  (RingCon.ker (evaluate R word).toRingHom).mkₐ R (FreeAlgebra.ι R g)

omit [Fintype ι] in
theorem blockClass_comp (i j k : ι)
    (x : DiagramVectorSpace.MapClasses R (word i) (word j))
    (y : DiagramVectorSpace.MapClasses R (word j) (word k)) :
    blockClass R word ⟨j, k, y⟩ * blockClass R word ⟨i, j, x⟩ =
      blockClass R word ⟨i, k, DiagramVectorSpace.stack R (word i) (word j) (word k) x y⟩ := by
  unfold blockClass
  rw [← map_mul]
  apply (classes_eq_iff R word _ _).2
  simp only [map_mul, evaluate, FreeAlgebra.lift_ι_apply]
  exact block_comp R word i j k x y

omit [Fintype ι] in
theorem blockClass_comp_incompatible (i j k l : ι) (h : k ≠ j)
    (x : DiagramVectorSpace.MapClasses R (word i) (word j))
    (y : DiagramVectorSpace.MapClasses R (word k) (word l)) :
    blockClass R word ⟨k, l, y⟩ * blockClass R word ⟨i, j, x⟩ = 0 := by
  unfold blockClass
  rw [← map_mul, ← map_zero ((RingCon.ker (evaluate R word).toRingHom).mkₐ R)]
  apply (classes_eq_iff R word _ _).2
  simp only [map_mul, map_zero, evaluate, FreeAlgebra.lift_ι_apply]
  exact block_comp_incompatible R word i j k l h x y

omit [Fintype ι] in
theorem blockClass_add (i j : ι)
    (x y : DiagramVectorSpace.MapClasses R (word i) (word j)) :
    blockClass R word ⟨i, j, x + y⟩ = blockClass R word ⟨i, j, x⟩ + blockClass R word ⟨i, j, y⟩ := by
  unfold blockClass
  rw [← map_add]
  apply (classes_eq_iff R word _ _).2
  simp only [map_add, evaluate, FreeAlgebra.lift_ι_apply]
  apply LinearMap.ext
  intro z
  simp only [evalBlock, DiagramVectorSpace.classEval_add, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.proj_apply]
  exact map_add (LinearMap.single R (Space R word) j) _ _

omit [Fintype ι] in
theorem blockClass_smul (i j : ι) (c : R)
    (x : DiagramVectorSpace.MapClasses R (word i) (word j)) :
    blockClass R word ⟨i, j, c • x⟩ = c • blockClass R word ⟨i, j, x⟩ := by
  unfold blockClass
  rw [← map_smul]
  apply (classes_eq_iff R word _ _).2
  simp only [map_smul, evaluate, FreeAlgebra.lift_ι_apply]
  apply LinearMap.ext
  intro z
  simp only [evalBlock, DiagramVectorSpace.classEval_smul, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.proj_apply]
  exact map_smul (LinearMap.single R (Space R word) j) _ _

omit [Fintype ι] in
theorem blockClass_injective (i j : ι) :
    Function.Injective (fun x : DiagramVectorSpace.MapClasses R (word i) (word j) =>
      blockClass R word ⟨i, j, x⟩) := by
  intro x y h
  apply DiagramVectorSpace.classEval_injective R (word i) (word j)
  apply LinearMap.ext
  intro z
  have h' : evalBlock R word ⟨i, j, x⟩ = evalBlock R word ⟨i, j, y⟩ := by
    unfold blockClass at h
    have hh := (classes_eq_iff R word _ _).1 h
    simpa only [evaluate, FreeAlgebra.lift_ι_apply] using hh
  have hh := congrArg (fun f : Module.End R (Total R word) =>
    f ((LinearMap.single R (Space R word) i) z) j) h'
  simpa [evalBlock] using hh

omit [Fintype ι] in
theorem blockSingleton_eq_iff (i j : ι) (d e : LabelledDrawing R (word i) (word j)) :
    blockClass R word ⟨i, j, Submodule.Quotient.mk (Finsupp.single d 1)⟩ =
      blockClass R word ⟨i, j, Submodule.Quotient.mk (Finsupp.single e 1)⟩ ↔
        d.interpret.eval = e.interpret.eval := by
  rw [(blockClass_injective R word i j).eq_iff]
  exact DiagramVectorSpace.singleton_classes_eq_iff R (word i) (word j) d e

omit [Fintype ι] in
theorem blockIndexed_eq_iff {α β : Type*} (i j : ι)
    (d : IndexedDrawing R (word i) (word j) α) (e : IndexedDrawing R (word i) (word j) β) :
    blockClass R word ⟨i, j, Submodule.Quotient.mk (DiagramVectorSpace.indexedExpressions R (word i) (word j) d)⟩ =
      blockClass R word ⟨i, j, Submodule.Quotient.mk (DiagramVectorSpace.indexedExpressions R (word i) (word j) e)⟩ ↔
        d.eval = e.eval := by
  rw [(blockClass_injective R word i j).eq_iff]
  exact DiagramVectorSpace.indexedClasses_eq_iff R (word i) (word j) d e

theorem sum_blockClass_identity :
    (∑ i : ι, blockClass R word ⟨i, i, DiagramVectorSpace.identityClass R (word i)⟩) = 1 := by
  unfold blockClass
  rw [← map_sum, ← map_one ((RingCon.ker (evaluate R word).toRingHom).mkₐ R)]
  apply (classes_eq_iff R word _ _).2
  simp only [map_sum, map_one, evaluate, FreeAlgebra.lift_ι_apply]
  exact sum_block_identity R word

noncomputable def classesEquivImage : Classes R word ≃ₐ[R] (evaluate R word).range :=
  RingCon.quotientKerEquivRangeₐ (evaluate R word)

end MackeyDiagrams.BlockAlgebra
