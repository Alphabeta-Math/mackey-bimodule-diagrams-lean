namespace MixedCrossingsThroughSmallerGroupAux

private theorem fiberCard {X Y : Type*} (f : X → Y) (y : Y)
    (hf : Set.Finite {x | f x = y}) :
    (hf.toFinset).card = Nat.card {x | f x = y} := by
  let := hf.fintype
  rw [Nat.card_eq_fintype_card, hf.card_toFinset]

private theorem sumSingleApply {X : Type*} [DecidableEq X] (S : Finset X) (w : X) :
    (S.sum (fun x => Finsupp.single x (1 : Complex))) w =
      if w ∈ S then 1 else 0 := by
  change (Finsupp.lapply w : (X →₀ Complex) →ₗ[Complex] Complex) _ = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply, Finset.sum_ite_eq']

end MixedCrossingsThroughSmallerGroupAux
