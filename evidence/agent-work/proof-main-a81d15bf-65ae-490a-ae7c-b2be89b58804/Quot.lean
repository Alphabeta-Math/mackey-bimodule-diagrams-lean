import MackeyDiagrams
import Proofs.ParabolicDoubleCosetRepresentatives

-- Section 7.3's componentwise equality follows by applying Mathlib's DoubleCoset.eq
-- in both directions. The reverse direction assembles the chosen left and right
-- factors via split.symm and uses the two subgroup membership equivalences.
private theorem parBlockCoset_eq {G ι : Type*} [Group G] {P : ι → Type*}
    [∀ i, Group (P i)] (split : G ≃* ∀ i, P i)
    (K H : Subgroup G) (Kᵢ Hᵢ : ∀ i, Subgroup (P i))
    (hK : ∀ x, x ∈ K ↔ ∀ i, split x i ∈ Kᵢ i)
    (hH : ∀ x, x ∈ H ↔ ∀ i, split x i ∈ Hᵢ i) (x y : G) :
    DoubleCoset.mk K H x = DoubleCoset.mk K H y ↔
      ∀ i, DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split x i) =
        DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split y i) := by
  constructor
  · intro h i
    obtain ⟨k, hk, l, hl, rfl⟩ := DoubleCoset.eq.mp h
    refine DoubleCoset.eq.mpr ⟨split k i, (hK k).mp hk i, split l i, (hH l).mp hl i, ?_⟩
    rw [map_mul, map_mul]
    rfl
  · intro h
    have f i := DoubleCoset.eq.mp (h i)
    choose k hk l hl e using f
    refine DoubleCoset.eq.mpr ⟨split.symm k, (hK _).mpr (fun i => ?_),
      split.symm l, (hH _).mpr (fun i => ?_), ?_⟩
    · rw [split.apply_symm_apply]
      exact hk i
    · rw [split.apply_symm_apply]
      exact hl i
    · apply split.injective
      simp only [map_mul, split.apply_symm_apply]
      exact funext e

private noncomputable def parBlockQuotientSplit {G ι : Type*} [Group G] {P : ι → Type*}
    [∀ i, Group (P i)] (split : G ≃* ∀ i, P i)
    (K H : Subgroup G) (Kᵢ Hᵢ : ∀ i, Subgroup (P i))
    (hK : ∀ x, x ∈ K ↔ ∀ i, split x i ∈ Kᵢ i)
    (hH : ∀ x, x ∈ H ↔ ∀ i, split x i ∈ Hᵢ i) :
    DoubleCoset.Quotient (K : Set G) H ≃
      (∀ i, DoubleCoset.Quotient (Kᵢ i : Set (P i)) (Hᵢ i)) := by
  let f : DoubleCoset.Quotient (K : Set G) H → ∀ i, DoubleCoset.Quotient (Kᵢ i : Set (P i)) (Hᵢ i) :=
    Quotient.lift (fun x i => DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split x i))
      (fun x y h => funext ((parBlockCoset_eq split K H Kᵢ Hᵢ hK hH x y).mp (Quotient.sound h)))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂ q q' (fun x y h => ?_)
    exact (parBlockCoset_eq split K H Kᵢ Hᵢ hK hH x y).mpr (congrFun h)
  · intro q
    refine ⟨DoubleCoset.mk K H (split.symm fun i => (q i).out), funext fun i => ?_⟩
    change DoubleCoset.mk (Kᵢ i) (Hᵢ i) (split (split.symm fun i => (q i).out) i) = q i
    rw [split.apply_symm_apply]
    exact DoubleCoset.out_eq' (q i)

private theorem parBlockCoset_one {G : Type*} [Group G] (K H : Subgroup G)
    (h : K = ⊤ ∨ H = ⊤) (q : DoubleCoset.Quotient (K : Set G) H) :
    DoubleCoset.mk K H 1 = q := by
  rw [← DoubleCoset.out_eq' q]
  apply DoubleCoset.eq.mpr
  rcases h with hK | hH
  · exact ⟨q.out, (fun x : G => hK ▸ Subgroup.mem_top x) q.out, 1, H.one_mem, by simp⟩
  · exact ⟨1, K.one_mem, q.out, (fun x : G => hH ▸ Subgroup.mem_top x) q.out, by simp⟩
