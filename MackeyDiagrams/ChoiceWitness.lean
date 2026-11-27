import Mathlib.Algebra.Category.ModuleCat.Ulift

namespace MackeyDiagrams
/-- A pointwise unique witness can be chosen as a coherent dependent family. -/
theorem existsUnique_family {ι : Type*} {K : ι → Type*} {P : ∀ i, K i → Prop} :
    (∀ i, ∃! k, P i k) ↔ ∃ f : ∀ i, K i, ∀ i, P i (f i) ∧ ∀ k, P i k → k = f i := by
  constructor
  · intro h
    let f := fun i => Classical.choose (h i).exists
    refine ⟨f, ?_⟩
    intro i
    exact ⟨Classical.choose_spec (h i).exists, fun k hk => (h i).unique hk (Classical.choose_spec (h i).exists)⟩
  · rintro ⟨f, hf⟩ i
    exact ⟨f i, (hf i).1, (hf i).2⟩
/-- A pointwise inhabited family has a dependent choice function classically. -/
theorem nonempty_family {ι : Type*} {K : ι → Type*} :
    (∀ i, Nonempty (K i)) ↔ Nonempty (∀ i, K i) := by
  constructor
  · intro h
    exact ⟨fun i => Classical.choice (h i)⟩
  · rintro ⟨f⟩ i
    exact ⟨f i⟩

end MackeyDiagrams
