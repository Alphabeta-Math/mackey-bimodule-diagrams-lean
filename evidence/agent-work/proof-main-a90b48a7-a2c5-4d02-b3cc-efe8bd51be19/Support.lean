namespace CaseFivePointwiseAux

open MackeyDiagrams

private theorem finite_linear_support {X I V : Type*} [AddCommMonoid V] [Module Complex V]
    (L : I → (X →₀ Complex) →ₗ[Complex] V)
    (h : ∀ x, Set.Finite {i | L i (Finsupp.single x 1) ≠ 0})
    (v : X →₀ Complex) : Set.Finite {i | L i v ≠ 0} := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero, ne_eq, not_true_eq_false, Set.ofPred_false] using
      (Set.finite_empty : (∅ : Set I).Finite)
  | add v w hv hw =>
      refine (hv.union hw).subset ?_
      intro i hi
      change L i (v + w) ≠ 0 at hi
      rw [map_add] at hi
      by_cases hvi : L i v = 0
      · exact Or.inr (fun hwi => hi (by rw [hvi, hwi, add_zero]))
      · exact Or.inl hvi
  | single x c =>
      refine (h x).subset ?_
      intro i hi
      change L i (Finsupp.single x c) ≠ 0 at hi
      rw [← Finsupp.smul_single_one, map_smul] at hi
      exact fun hz => hi (by rw [hz, smul_zero])

private theorem sum_orbit_drawings {U : Type*} [Group U] {G F : Subgroup U}
    {bottom top : Word G F} {O : Type*}
    (orbit : bottom.basis.carrier × top.basis.carrier → O)
    (M : (bottom.basis.carrier →₀ Complex) →ₗ[Complex] (top.basis.carrier →₀ Complex))
    (I : Set O) (weight : I → Complex)
    (drawing : I → LabelledDrawing Complex bottom top)
    (hit : ∀ x y, M (Finsupp.single x 1) y ≠ 0 → orbit (x, y) ∈ I)
    (weight_eq : ∀ (i : I) x y, orbit (x, y) = i.val → weight i = M (Finsupp.single x 1) y)
    (finiteOrbits : ∀ x, Set.Finite {o : O |
      ∃ y, M (Finsupp.single x 1) y ≠ 0 ∧ o = orbit (x, y)})
    (matrix : ∀ (i : I) x y,
      (weight i • (drawing i).interpret.eval.toLinearMap (Finsupp.single x 1)) y =
        @ite Complex (orbit (x, y) = i.val) (Classical.propDecidable _) (weight i) 0) :
    ∃ (finite : ∀ v : bottom.basis.carrier →₀ Complex, Set.Finite
        {i : I | weight i • (drawing i).interpret.eval.toLinearMap v ≠ 0}),
      let sum : PointwiseIndexedDrawing Complex bottom top I :=
        ⟨fun i => LabelledDrawing.scale (weight i) (drawing i), finite⟩
      ∀ v, M v = sum.evalAt v := by
  classical
  let L (i : I) := weight i • (drawing i).interpret.eval.toLinearMap
  have entry (i : I) (x : bottom.basis.carrier) (y : top.basis.carrier) :
      L i (Finsupp.single x 1) y = if orbit (x, y) = i.val then weight i else 0 :=
    matrix i x y
  -- Step 3. The nonzero entries in a basis column bound the contributing
  -- orbits. Finite linear extension handles arbitrary inputs.
  have finiteColumn (x : bottom.basis.carrier) :
      Set.Finite {i : I | L i (Finsupp.single x 1) ≠ 0} := by
    apply ((finiteOrbits x).preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
    intro i hi
    change L i (Finsupp.single x 1) ≠ 0 at hi
    have h : ∃ y, L i (Finsupp.single x 1) y ≠ 0 := by
      by_contra! hall
      exact hi (Finsupp.ext fun y => hall y)
    obtain ⟨y, hy⟩ := h
    have he : orbit (x, y) = i.val := by
      by_contra hn
      exact hy ((entry i x y).trans (ite_eq_right hn))
    exact ⟨y, by rwa [entry, ite_eq_left he, weight_eq i x y he] at hy, he.symm⟩
  let finite := finite_linear_support L finiteColumn
  let sum : PointwiseIndexedDrawing Complex bottom top I :=
    ⟨fun i => LabelledDrawing.scale (weight i) (drawing i), finite⟩
  refine ⟨finite, ?_⟩
  suffices h : M = sum.eval from fun v => (LinearMap.congr_fun h v).trans (sum.eval_apply v)
  apply Finsupp.lhom_ext
  intro x c
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  congr 1
  rw [PointwiseIndexedDrawing.eval_apply, PointwiseIndexedDrawing.evalAt_def]
  change M (Finsupp.single x 1) = (finite (Finsupp.single x 1)).toFinset.sum
    (fun i => L i (Finsupp.single x 1))
  apply Finsupp.ext
  intro y
  rw [Finsupp.finsetSum_apply]
  by_cases hc : M (Finsupp.single x 1) y = 0
  · rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases he : orbit (x, y) = i.val
    · rw [entry, ite_eq_left he, weight_eq i x y he, hc]
    · rw [entry, ite_eq_right he]
  · let i : I := ⟨orbit (x, y), hit x y hc⟩
    have he : orbit (x, y) = i.val := rfl
    have hval : L i (Finsupp.single x 1) y = M (Finsupp.single x 1) y := by
      rw [entry, ite_eq_left he, weight_eq i x y he]
    rw [Finset.sum_eq_single i]
    · exact hval.symm
    · intro j _ hj
      have hne : orbit (x, y) ≠ j.val := fun he' => hj (Subtype.ext (he'.symm.trans he))
      rw [entry, ite_eq_right hne]
    · intro hi
      rw [Set.Finite.mem_toFinset] at hi
      have hz : L i (Finsupp.single x 1) = 0 := not_ne_iff.mp hi
      exact False.elim (hc (hval.symm.trans (congrArg (fun w => w y) hz)))

private theorem finite_eval {U : Type*} [Group U] {G F : Subgroup U}
    {bottom top : Word G F} (terms : List (Complex × LabelledDrawing Complex bottom top)) :
    let folded := terms.foldr
      (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
      (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))
    let indexed : IndexedDrawing Complex bottom top (Fin terms.length) :=
      ⟨Finset.univ, fun i => LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩
    folded.interpret.eval.toLinearMap = indexed.eval := by
  intro folded indexed
  apply LinearMap.ext
  intro v
  let termValue (term : Complex × LabelledDrawing Complex bottom top) :=
    term.1 • term.2.interpret.eval.toLinearMap v
  have hfold (l : List (Complex × LabelledDrawing Complex bottom top)) :
      (l.foldr (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
        (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))).interpret.eval.toLinearMap v =
        (l.map termValue).sum := by
    induction l with
    | nil => rfl
    | cons t l ih =>
        rw [List.map_cons, List.sum_cons]
        change termValue t + _ = termValue t + _
        exact congrArg (termValue t + ·) ih
  rw [IndexedDrawing.eval_apply]
  change folded.interpret.eval.toLinearMap v =
    Finset.univ.sum (fun i : Fin terms.length => termValue (terms.get i))
  exact (hfold terms).trans (Fin.sum_univ_fun_getElem terms termValue).symm

end CaseFivePointwiseAux
