import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.RightOrbitDiagramFromProjectedStabilizer
namespace ExpansionIntoRightDiagramsAux

open MackeyDiagrams

private theorem basis_ext {X : Type*} {V : Type*} [AddCommMonoid V] [Module Complex V]
    {L M : (X →₀ Complex) →ₗ[Complex] V}
    (h : ∀ x, L (Finsupp.single x 1) = M (Finsupp.single x 1)) : L = M := by
  apply Finsupp.lhom_ext
  intro x c
  rw [← Finsupp.smul_single_one, map_smul, map_smul, h x]

private theorem assemble {X I V : Type*} [AddCommMonoid V] [Module Complex V]
    (M : (X →₀ Complex) →ₗ[Complex] V) (L : I → (X →₀ Complex) →ₗ[Complex] V)
    (finiteColumn : ∀ x, Set.Finite {i : I | L i (Finsupp.single x 1) ≠ 0})
    (columnSum : ∀ x, M (Finsupp.single x 1) =
      (finiteColumn x).toFinset.sum (fun i => L i (Finsupp.single x 1))) :
    ∃ finite : ∀ v, Set.Finite {i : I | L i v ≠ 0},
      ∀ v, M v = (finite v).toFinset.sum (fun i => L i v) := by
  classical
  -- Step 3. Collect each finite column over the orbit index. Linear extension
  -- gives one finitely supported vector of contributions for every finite input.
  let column (x : X) : I →₀ V :=
    Finsupp.ofSupportFinite (fun i => L i (Finsupp.single x 1)) (finiteColumn x)
  let collect := Finsupp.linearCombination Complex column
  have collect_basis (x : X) : collect (Finsupp.single x 1) = column x := by
    simp only [collect, Finsupp.linearCombination_single, one_smul]
  have entry (i : I) (v : X →₀ Complex) : collect v i = L i v := by
    have he : (Finsupp.lapply (R := Complex) i).comp collect = L i := by
      apply basis_ext
      intro x
      change collect (Finsupp.single x 1) i = _
      rw [collect_basis]
      rfl
    exact LinearMap.congr_fun he v
  let total := Finsupp.lsum Complex (fun _ : I => LinearMap.id (R := Complex) (M := V))
  have total_apply (w : I →₀ V) : total w = w.support.sum (fun i => w i) := by
    rw [Finsupp.lsum_apply]
    rfl
  have hM : M = total.comp collect := by
    apply basis_ext
    intro x
    change M (Finsupp.single x 1) = total (collect (Finsupp.single x 1))
    rw [columnSum x, collect_basis, total_apply]
    rfl
  have support_eq (v : X →₀ Complex) : (↑(collect v).support : Set I) = {i | L i v ≠ 0} := by
    ext i
    change i ∈ (collect v).support ↔ L i v ≠ 0
    rw [Finsupp.mem_support_iff, entry]
  let finite (v : X →₀ Complex) : Set.Finite {i : I | L i v ≠ 0} :=
    support_eq v ▸ (collect v).support.finite_toSet
  refine ⟨finite, fun v => ?_⟩
  have hfin : (finite v).toFinset = (collect v).support := by
    ext i
    rw [Set.Finite.mem_toFinset]
    exact (Set.ext_iff.mp (support_eq v) i).symm
  rw [hfin]
  calc
    M v = total (collect v) := LinearMap.congr_fun hM v
    _ = (collect v).support.sum (fun i => collect v i) := total_apply _
    _ = _ := Finset.sum_congr rfl (fun i _ => entry i v)

private theorem orbit_columns {X Y O : Type*} (orbit : X × Y → O)
    (M : (X →₀ Complex) →ₗ[Complex] (Y →₀ Complex))
    (I : Set O) (weight : I → Complex)
    (L : I → (X →₀ Complex) →ₗ[Complex] (Y →₀ Complex))
    (hit : ∀ x y, M (Finsupp.single x 1) y ≠ 0 → orbit (x, y) ∈ I)
    (weight_eq : ∀ (i : I) x y, orbit (x, y) = ↑i → weight i = M (Finsupp.single x 1) y)
    (matrix : ∀ (i : I) x y,
      L i (Finsupp.single x 1) y =
        @ite Complex (orbit (x, y) = ↑i) (Classical.propDecidable _) (weight i) 0) :
    ∃ finite : ∀ v, Set.Finite {i : I | L i v ≠ 0},
      ∀ v, M v = (finite v).toFinset.sum (fun i => L i v) := by
  classical
  have finiteColumn (x : X) : Set.Finite {i : I | L i (Finsupp.single x 1) ≠ 0} := by
    let column := M (Finsupp.single x 1)
    have hO := column.support.finite_toSet.image (fun y => orbit (x, y))
    apply (hO.preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
    intro i hi
    change L i (Finsupp.single x 1) ≠ 0 at hi
    have h : ∃ y, L i (Finsupp.single x 1) y ≠ 0 := by
      by_contra! hall
      exact hi (Finsupp.ext fun y => hall y)
    obtain ⟨y, hy⟩ := h
    have horbit : orbit (x, y) = ↑i := by
      by_contra hne
      exact hy ((matrix i x y).trans (if_neg hne))
    refine ⟨y, Finsupp.mem_support_iff.mpr ?_, horbit⟩
    rw [matrix, if_pos horbit, weight_eq i x y horbit] at hy
    exact hy
  apply assemble M L finiteColumn
  intro x
  ext y
  rw [Finsupp.finset_sum_apply]
  by_cases hc : M (Finsupp.single x 1) y = 0
  · rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases he : orbit (x, y) = ↑i
    · rw [matrix, if_pos he, weight_eq i x y he, hc]
    · rw [matrix, if_neg he]
  · let i : I := ⟨orbit (x, y), hit x y hc⟩
    have he : orbit (x, y) = ↑i := rfl
    have hval : L i (Finsupp.single x 1) y = M (Finsupp.single x 1) y := by
      rw [matrix, if_pos he, weight_eq i x y he]
    rw [Finset.sum_eq_single i]
    · exact hval.symm
    · intro j _ hj
      rw [matrix, if_neg (fun hj' => hj (Subtype.ext hj'))]
    · intro hi
      rw [Set.Finite.mem_toFinset] at hi
      have hzero : L i (Finsupp.single x 1) = 0 := by simpa using hi
      exact False.elim (hc (hval.symm.trans (congrArg (fun w : Y →₀ Complex => w y) hzero)))

private theorem fold_finset {U : Type*} [Group U] {G F : Subgroup U}
    {bottom top : Word G F} {I : Type*}
    (weight : I → Complex) (diagram : I → LabelledDrawing Complex bottom top)
    (s : Finset I) :
    ∃ terms : List (Complex × LabelledDrawing Complex bottom top),
      (∀ term ∈ terms, ∃ i, term = (weight i, diagram i)) ∧
      ∀ v : bottom.basis.carrier →₀ Complex,
        (terms.foldr (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
          (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))).interpret.eval.toLinearMap v =
          s.sum (fun i => weight i • (diagram i).interpret.eval.toLinearMap v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨[], by simp, fun v => ?_⟩
    change 0 = Finset.sum ∅ _
    simp
  | @insert i s hi ih =>
    obtain ⟨terms, hterms, hsum⟩ := ih
    refine ⟨(weight i, diagram i) :: terms, ?_, fun v => ?_⟩
    · intro term ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨i, rfl⟩
      · exact hterms term ht
    · let folded := terms.foldr
        (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
        (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))
      change weight i • (diagram i).interpret.eval.toLinearMap v +
        folded.interpret.eval.toLinearMap v = _
      rw [Finset.sum_insert hi]
      exact congrArg (_ + ·) (hsum v)

end ExpansionIntoRightDiagramsAux
