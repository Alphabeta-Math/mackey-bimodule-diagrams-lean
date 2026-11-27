import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.GroupAction.Defs

private theorem closure_swap_fixes {S : Subgroup (Equiv.Perm Nat)} {t x : S}
    {i j n : Nat} (ht : (t : Equiv.Perm Nat) = Equiv.swap i j)
    (hx : x ∈ Subgroup.closure {t}) (hni : n ≠ i) (hnj : n ≠ j) :
    (x : Equiv.Perm Nat) n = n := by
  let stab := (MulAction.stabilizer (Equiv.Perm Nat) n).comap (Subgroup.subtype S)
  have hle : Subgroup.closure {t} ≤ stab := (Subgroup.closure_le stab).mpr (by
    apply Set.singleton_subset_iff.mpr
    change (t : Equiv.Perm Nat) n = n
    rw [ht]
    exact Equiv.swap_apply_of_ne_of_ne hni hnj)
  exact hle hx

private theorem overlapping_swaps {S : Subgroup (Equiv.Perm Nat)} {t u x : S}
    (ht : (t : Equiv.Perm Nat) = Equiv.swap 1 2)
    (hu : (u : Equiv.Perm Nat) = Equiv.swap 2 3)
    (hx : x ∈ Subgroup.closure {t}) (hy : x ∈ Subgroup.closure {u}) : x = 1 := by
  have hfix (n : Nat) (hn : n ≠ 2) : (x : Equiv.Perm Nat) n = n := by
    by_cases h : n = 1
    · subst n
      exact closure_swap_fixes hu hy hn (by decide)
    · exact closure_swap_fixes ht hx h hn
  apply Subtype.ext
  apply Equiv.ext
  intro n
  change (x : Equiv.Perm Nat) n = n
  by_cases hn : n = 2
  · subst n
    by_contra h
    exact h ((x : Equiv.Perm Nat).injective (hfix ((x : Equiv.Perm Nat) 2) h))
  · exact hfix n hn

theorem overlap_group :
    let P := Equiv.Perm Nat
    let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
    let U := ↥finitary
    let T : Subgroup U := ⊥
    let swap := fun (i j : Nat) (hij : i ≠ j) =>
      (⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩ : U)
    let swap12 := swap 1 2 (by decide)
    let swap23 := swap 2 3 (by decide)
    let D : Subgroup U := Subgroup.closure {swap12}
    let E : Subgroup U := Subgroup.closure {swap23}
    let points : Finset Nat := {1, 2, 3}
    let extend := Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ points)
    let B : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) (MonoidHom.range extend)
    swap12 ∈ B ∧ swap23 ∈ B ∧ D ≤ B ∧ E ≤ B ∧ D ⊓ E = T := by
  intro P finitary U T swap swap12 swap23 D E points extend B
  have h12 : swap12 ∈ B := by
    change ∃ p, extend p = Equiv.swap 1 2
    exact ⟨Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  have h23 : swap23 ∈ B := by
    change ∃ p, extend p = Equiv.swap 2 3
    exact ⟨Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  have hDB : D ≤ B := (Subgroup.closure_le B).mpr (Set.singleton_subset_iff.mpr h12)
  have hEB : E ≤ B := (Subgroup.closure_le B).mpr (Set.singleton_subset_iff.mpr h23)
  have hdis : ∀ z : U, z ∈ D → z ∈ E → z = 1 :=
    fun _ hzD hzE => overlapping_swaps rfl rfl hzD hzE
  refine ⟨h12, h23, hDB, hEB, le_antisymm ?_ bot_le⟩
  intro z hz
  rcases Subgroup.mem_inf.mp hz with ⟨hzD, hzE⟩
  exact Subgroup.mem_bot.mpr (hdis z hzD hzE)

#print axioms overlap_group
