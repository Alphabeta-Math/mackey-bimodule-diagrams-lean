namespace MixedMackeyCancellationSupport

open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {K H : Subgroup U}

private theorem eval_sum (M : Word K H) {J : Type u}
    (drawings : J → LabelledDrawing Complex M M) (indices : Finset J)
    (x : M.basis.carrier →₀ Complex) :
    ((List.foldr LabelledDrawing.add (.ordinary (Diagram.zero M M))
      (List.map drawings indices.toList)).interpret.eval).toLinearMap x =
        ∑ j ∈ indices, (drawings j).interpret.eval.toLinearMap x := by
  classical
  let term (j : J) := (drawings j).interpret.eval.toLinearMap x
  have evalList (L : List J) :
      ((List.foldr LabelledDrawing.add (.ordinary (Diagram.zero M M))
        (L.map drawings)).interpret.eval).toLinearMap x = (L.map term).sum := by
    induction L with
    | nil => rfl
    | cons j L ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons]
      change term j +
          (List.foldr LabelledDrawing.add (.ordinary (Diagram.zero M M))
            (L.map drawings)).interpret.eval.toLinearMap x = term j + (L.map term).sum
      rw [ih]
  rw [evalList]
  conv_rhs => rw [← indices.toList_toFinset, List.sum_toFinset _ indices.nodup_toList]

end MixedMackeyCancellationSupport

open MackeyDiagrams
universe u
