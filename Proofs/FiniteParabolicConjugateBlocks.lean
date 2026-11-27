import Mathlib.GroupTheory.Perm.Support
import MackeyDiagrams

set_option maxHeartbeats 2000000

theorem FiniteParabolicConjugateBlocks : (∀ {ι : Type*} [Finite ι] (X : ι → Finset Nat),
  (∀ i, Finset.Nonempty (X i)) →
  Pairwise (fun i j => Disjoint (X i) (X j)) →
  ∀ α : ↥(Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}),
    let blockProduct : (ι → Finset Nat) → Subgroup (Equiv.Perm Nat) :=
      fun blocks => iSup (fun i =>
        MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ blocks i)))
    Subgroup.map
        (MulEquiv.toMonoidHom (MulAut.conj (α : Equiv.Perm Nat)))
        (blockProduct X) =
      blockProduct (fun i => Finset.image (α : Equiv.Perm Nat) (X i))) :=
(by
  intro ι finite X nonempty disjoint α
  dsimp only
  rw [Subgroup.map_iSup]
  congr 1
  funext i
  let σ : Equiv.Perm Nat := α
  let Y := (X i).image σ
  have mem_image (n : Nat) : n ∈ X i ↔ σ n ∈ Y := by
    simp [Y, Finset.mem_image]
  let e : {n // n ∈ X i} ≃ {n // n ∈ Y} := σ.subtypeEquiv mem_image
  have commute (f : Equiv.Perm {n // n ∈ X i}) :
      MulAut.conj σ (Equiv.Perm.ofSubtype f) =
        Equiv.Perm.ofSubtype (e.permCongr f) := by
    apply Equiv.ext
    intro n
    obtain ⟨m, rfl⟩ := σ.surjective n
    change σ (Equiv.Perm.ofSubtype f (σ.symm (σ m))) =
      Equiv.Perm.ofSubtype (e.permCongr f) (σ m)
    rw [σ.symm_apply_apply]
    by_cases hm : m ∈ X i
    · rw [Equiv.Perm.ofSubtype_apply_of_mem f hm,
        Equiv.Perm.ofSubtype_apply_of_mem _ ((mem_image m).mp hm)]
      change (e (f ⟨m, hm⟩) : Nat) = (e.permCongr f (e ⟨m, hm⟩) : Nat)
      simp
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem f hm,
        Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun h => hm ((mem_image m).mpr h))]
  apply Subgroup.ext
  intro τ
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨f, rfl⟩ := hg
    exact ⟨e.permCongr f, (commute f).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨f, rfl⟩ := e.permCongr.surjective g
    exact ⟨Equiv.Perm.ofSubtype f, ⟨f, rfl⟩, commute f⟩
)
