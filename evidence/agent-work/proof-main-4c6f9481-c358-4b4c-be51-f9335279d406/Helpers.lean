import MackeyDiagrams
import Proofs.ParabolicMackeyIntersectionBlocks
import Proofs.TwoBlockDoubleCosetMatrices
import Proofs.ParabolicDoubleCosetRepresentatives
private def twoBlockInterval (n lo hi : Nat) : Finset ↥(Finset.Icc 1 n) :=
  Finset.filter (fun x => lo ≤ x.val ∧ x.val ≤ hi) Finset.univ

private theorem twoBlockBounds {n : Nat} (x : ↥(Finset.Icc 1 n)) :
    1 ≤ x.val ∧ x.val ≤ n :=
  Finset.mem_Icc.mp x.property

private theorem twoBlockMemInterval {n lo hi : Nat} {x : ↥(Finset.Icc 1 n)} :
    x ∈ twoBlockInterval n lo hi ↔ lo ≤ x.val ∧ x.val ≤ hi := by
  simp [twoBlockInterval]

private theorem twoBlockCardInterval {n lo hi : Nat} (hlo : 1 ≤ lo) (hhi : hi ≤ n) :
    (twoBlockInterval n lo hi).card = hi + 1 - lo := by
  let val : ↥(Finset.Icc 1 n) ↪ Nat := ⟨Subtype.val, Subtype.val_injective⟩
  have himage : (twoBlockInterval n lo hi).map val = Finset.Icc lo hi := by
    ext z
    simp only [Finset.mem_map, Finset.mem_Icc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact twoBlockMemInterval.mp hx
    · intro hz
      have hz' : z ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr
        ⟨hlo.trans hz.1, hz.2.trans hhi⟩
      exact ⟨⟨z, hz'⟩, twoBlockMemInterval.mpr hz, rfl⟩
  rw [← Finset.card_map val, himage, Nat.card_Icc]

private def twoBlockPartition (n cut : Nat) (r : Fin 2) : Finset ↥(Finset.Icc 1 n) :=
  if r = 0 then twoBlockInterval n 1 cut else twoBlockInterval n (cut + 1) n

private theorem twoBlockPartitionFacts {n cut : Nat} (hc : 1 ≤ cut) (hcn : cut < n) :
    (∀ r, (twoBlockPartition n cut r).Nonempty) ∧
    Pairwise (fun r c => Disjoint (twoBlockPartition n cut r) (twoBlockPartition n cut c)) ∧
    ∀ x, ∃ r, x ∈ twoBlockPartition n cut r := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    by_cases h : r = 0
    · let x : ↥(Finset.Icc 1 n) := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      rw [twoBlockPartition, if_pos h]
      exact ⟨x, twoBlockMemInterval.mpr ⟨le_rfl, hc⟩⟩
    · let x : ↥(Finset.Icc 1 n) := ⟨cut + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      rw [twoBlockPartition, if_neg h]
      exact ⟨x, twoBlockMemInterval.mpr ⟨le_rfl, hcn⟩⟩
  · intro r c hrc
    have h : r = 0 ∨ c = 0 := by
      by_contra! hn
      have hr : r.val < 2 := r.isLt
      have hcv : c.val < 2 := c.isLt
      have hr0 : r.val ≠ 0 := fun h => hn.1 (Fin.ext h)
      have hc0 : c.val ≠ 0 := fun h => hn.2 (Fin.ext h)
      exact hrc (Fin.ext (by omega))
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases h with hr | hc'
    · have hc0 : c ≠ 0 := fun h => hrc (hr.trans h.symm)
      simp only [twoBlockPartition, if_pos hr, if_neg hc0, twoBlockMemInterval] at hx hy
      omega
    · have hr0 : r ≠ 0 := fun h => hrc (h.trans hc'.symm)
      simp only [twoBlockPartition, if_neg hr0, if_pos hc', twoBlockMemInterval] at hx hy
      omega
  · intro x
    obtain ⟨hx₁, hx₂⟩ := twoBlockBounds x
    by_cases hx : x.val ≤ cut
    · exact ⟨0, by simpa [twoBlockPartition, twoBlockMemInterval] using And.intro hx₁ hx⟩
    · refine ⟨1, ?_⟩
      simp only [twoBlockPartition, Fin.one_ne_zero, if_false, twoBlockMemInterval]
      exact ⟨by omega, hx₂⟩

private theorem twoBlockSwapImage {n d s t j : Nat}
    (hsd : s ≤ d) (hdt : d ≤ t) (hjs : j < s)
    (left right : ↥(Finset.Icc 1 n))
    (hl : left.val = s - j) (hr : right.val = t + j + 1)
    (f : Equiv.Perm ↥(Finset.Icc 1 n))
    (hf : ∀ x : ↥(Finset.Icc 1 n), (f.symm x).val ≤ d ↔
      x.val ≤ s - j ∨ (s < x.val ∧ x.val ≤ d) ∨ (t < x.val ∧ x.val ≤ t + j))
    (x : ↥(Finset.Icc 1 n)) :
    (((Equiv.swap left right) * f).symm x).val ≤ d ↔
      x.val ≤ s - (j + 1) ∨ (s < x.val ∧ x.val ≤ d) ∨
        (t < x.val ∧ x.val ≤ t + (j + 1)) := by
  change (f.symm ((Equiv.swap left right) x)).val ≤ d ↔ _
  rw [hf, Equiv.swap_apply_def]
  split_ifs with h h'
  · subst x
    omega
  · subst x
    omega
  · have hx₁ : x.val ≠ left.val := fun hv => h (Subtype.ext hv)
    have hx₂ : x.val ≠ right.val := fun hv => h' (Subtype.ext hv)
    omega

private theorem twoBlockCellIntervals {n n1 n2 s t k : Nat}
    (hs : s = min n1 n2) (ht : t = max n1 n2) (hk : k ≤ s)
    (σ : Equiv.Perm ↥(Finset.Icc 1 n))
    (hσ : ∀ x : ↥(Finset.Icc 1 n), (σ.symm x).val ≤ n2 ↔
      x.val ≤ s - k ∨ (s < x.val ∧ x.val ≤ n2) ∨ (t < x.val ∧ x.val ≤ t + k)) :
    let C := fun r c => twoBlockPartition n n1 r ∩
      (twoBlockPartition n n2 c).map σ.toEmbedding
    C 0 0 = twoBlockInterval n 1 (s - k) ∧
    C 0 1 = twoBlockInterval n (s - k + 1) n1 ∧
    C 1 0 = twoBlockInterval n (n1 + 1) (t + k) ∧
    C 1 1 = twoBlockInterval n (t + k + 1) n := by
  intro C
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext x <;>
    obtain ⟨hx₁, hx₂⟩ := twoBlockBounds x <;>
    obtain ⟨hy₁, hy₂⟩ := twoBlockBounds (σ.symm x) <;>
    simp only [C, Finset.mem_inter, Finset.mem_map_equiv, twoBlockPartition,
      if_pos rfl, Fin.one_ne_zero, if_false, twoBlockMemInterval] <;>
    have h := hσ x <;>
    omega

private theorem twoBlockOmitEmpty {α : Type*} [DecidableEq α] {ι κ : Type*}
    (C : ι → κ → Finset α) :
    let B := fun S : Finset α =>
      MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : α => x ∈ S))
    (⨆ r, ⨆ c, B (C r c)) =
      ⨆ p : {p : ι × κ // (C p.1 p.2).Nonempty}, B (C p.val.1 p.val.2) := by
  intro B
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun c => ?_
    by_cases h : (C r c).Nonempty
    · exact le_iSup (fun p : {p : ι × κ // (C p.1 p.2).Nonempty} =>
        B (C p.val.1 p.val.2)) ⟨(r, c), h⟩
    · have hb : B (C r c) ≤ ⊥ := by
        rintro _ ⟨g, rfl⟩
        apply Subgroup.mem_bot.mpr
        apply Equiv.ext
        intro x
        exact Equiv.Perm.ofSubtype_apply_of_not_mem g (fun hx => h ⟨x, hx⟩)
      exact hb.trans bot_le
  · refine iSup_le fun p => ?_
    exact (le_iSup (fun c => B (C p.val.1 c)) p.val.2).trans
      (le_iSup (fun r => ⨆ c, B (C r c)) p.val.1)
