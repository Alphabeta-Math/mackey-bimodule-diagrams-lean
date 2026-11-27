by
  classical
  intro S R algS algR ew Bimod Good GoodFunctors EqualScalars ComplexLinear
  let : CategoryTheory.Category.{max u v} Bimod :=
    (fun (c : CategoryTheory.Category.{max u v} Bimod)
      (_ : @CategoryTheory.Equivalence Bimod GoodFunctors c inferInstance) => c) _ ew
  -- Xiao, § 1.1, p. 2, immediately after Theorem 1.1. Use the precise
  -- equivalence named in the statement and its tensor clauses.
  have h := Classical.choose_spec (_root_.EilenbergWatts.{u,v})
  obtain ⟨pure, hUniversal, hMap, _⟩ := h
  have scalarCriterion (B : Bimod) : EqualScalars B ↔ ComplexLinear (ew.functor.obj B) := by
    let : Module (MulOpposite R) B.1 := B.2.1.2.1
    let : SMulCommClass (MulOpposite R) S B.1 := by
      rcases B with ⟨M, ⟨⟨left, ⟨right, commute⟩⟩, sameLeft⟩⟩
      cases sameLeft
      exact commute
    exact complexWatts_linear_iff B.1 (ew.functor.obj B).obj
      (pure S R B) (hUniversal S R B) (hMap S R B)
  refine ⟨scalarCriterion, complexWatts_restrict ew _ _ scalarCriterion ?_⟩
  intro F G iso hF
  have : CategoryTheory.Functor.Linear Complex F.obj := hF
  have ambient : CategoryTheory.Iso F.obj G.obj :=
    (CategoryTheory.ObjectProperty.ι Good).mapIso iso
  exact CategoryTheory.Functor.linear_of_iso Complex ambient
