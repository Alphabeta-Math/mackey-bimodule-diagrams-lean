import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map

namespace OverlapBlocks

variable {U : Type} [Group U] (ambient : U →* Equiv.Perm Nat)

private theorem fixes {a b : Nat} (swap : U) (hswap : ambient swap = Equiv.swap a b)
    {x : U} (hx : x ∈ Subgroup.closure {swap}) {i : Nat} (hia : i ≠ a) (hib : i ≠ b) :
    ambient x i = i := by
  let fix := Subgroup.comap ambient (MulAction.stabilizer (Equiv.Perm Nat) i)
  have hle : Subgroup.closure {swap} ≤ fix := by
    apply (Subgroup.closure_le fix).2
    apply Set.singleton_subset_iff.mpr
    change ambient swap i = i
    rw [hswap, Equiv.swap_apply_of_ne_of_ne hia hib]
  exact hle hx

theorem overlap_inf_bot (hinj : Function.Injective ambient) (swap12 swap23 : U)
    (h12 : ambient swap12 = Equiv.swap 1 2) (h23 : ambient swap23 = Equiv.swap 2 3) :
    Subgroup.closure {swap12} ⊓ Subgroup.closure {swap23} = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hx12, hx23⟩ := hx
  apply Subgroup.mem_bot.mpr
  apply hinj
  rw [map_one]
  apply Equiv.ext
  have hfix : ∀ i : Nat, i ≠ 2 → ambient x i = i := by
    intro i hi
    by_cases h1 : i = 1
    · subst i
      exact fixes ambient swap23 h23 hx23 (by decide) (by decide)
    · exact fixes ambient swap12 h12 hx12 h1 hi
  intro i
  change ambient x i = i
  by_cases hi : i = 2
  · subst i
    by_contra hn
    exact hn ((ambient x).injective (hfix _ hn))
  · exact hfix i hi

end OverlapBlocks
