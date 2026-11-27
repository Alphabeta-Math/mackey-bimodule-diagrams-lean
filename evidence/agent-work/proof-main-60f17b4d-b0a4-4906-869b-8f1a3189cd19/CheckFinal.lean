import MackeyDiagrams
import Proofs.ParabolicDoubleCosetRepresentatives

theorem OneSidedTableauCosetRepresentatives : (∀ (X : Finset Nat) (r c : Nat) (A : Fin r → Finset ↥X) (B : Fin c → Finset ↥X),
  (∀ i, Finset.Nonempty (A i)) →
  (∀ j, Finset.card (B j) = 1) →
  Pairwise (fun i i' => Disjoint (A i) (A i')) →
  Pairwise (fun j j' => Disjoint (B j) (B j')) →
  (∀ x : ↥X, ∃ i, x ∈ A i) →
  (∀ x : ↥X, ∃ j, x ∈ B j) →
  let G := Equiv.Perm ↥X
  let blockSym := fun S : Finset ↥X =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ S))
  let K : Subgroup G := iSup (fun i => blockSym (A i))
  let H : Subgroup G := iSup (fun j => blockSym (B j))
  H = ⊥ →
  let Mat := {R : Fin r → Fin c → Nat //
    (∀ i, Finset.sum Finset.univ (R i) = Finset.card (A i)) ∧
    (∀ j, Finset.sum Finset.univ (fun i => R i j) = Finset.card (B j))}
  let rank := fun (S : Finset ↥X) (x : ↥S) =>
    Fin.val (OrderIso.symm (Finset.orderIsoOfFin S rfl) x)
  ∃ rep : Mat → G,
    (∀ (R : Mat) (i : Fin r) (j : Fin c) (x : ↥(A i)) (y : ↥(B j)),
      rep R (Subtype.val y) = Subtype.val x ↔
        ∃ k : Fin (Subtype.val R i j),
          rank (A i) x = Finset.sum (Finset.Iio j) (fun j' => Subtype.val R i j') + Fin.val k ∧
          rank (B j) y = Finset.sum (Finset.Iio i) (fun i' => Subtype.val R i' j) + Fin.val k) ∧
    (∀ τ : G, ∃! R : Mat, ∃ k : K, τ = (Subtype.val k) * rep R) ∧
    (∀ τ : G, ∃! R : Mat, ∃ k : K, τ = (rep R)⁻¹ * (Subtype.val k))) :=
(by
  classical
  intro X r c A B hA hB hdA hdB hcA hcB G blockSym K H hH Mat rank
  -- Xiao, Example 7.3 (archived p. 30, 28 November revision p. 32).
  -- The ordered splitting and matching in Proposition 7.3 (steps 1 and 2)
  -- are supplied by ParabolicDoubleCosetRepresentatives. A column of size
  -- one is nonempty, so that theorem applies to both covering partitions.
  obtain ⟨classify, _, hrep⟩ := ParabolicDoubleCosetRepresentatives X r c A B hA
    (fun j => Finset.card_pos.mp (by rw [hB j]; exact Nat.zero_lt_one))
    hdA hdB hcA hcB
  choose rep hclass hrank using hrep
  -- With H = ⊥, the right factor in KσH is 1. Use the quotient equality
  -- criterion in both directions to identify the matrix of a right coset.
  have rightCoset (τ : G) (R : Mat) :
      (∃ k : K, τ = (k : G) * rep R) ↔ R = classify (DoubleCoset.mk K H τ) := by
    have hquot :
        DoubleCoset.mk K H (rep R) = DoubleCoset.mk K H τ ↔
          R = classify (DoubleCoset.mk K H τ) := by
      rw [hclass R, Equiv.symm_apply_eq]
    rw [← hquot]
    constructor
    · rintro ⟨k, hk⟩
      exact DoubleCoset.eq.mpr ⟨k, k.property, 1, H.one_mem, by simpa only [mul_one] using hk⟩
    · intro heq
      obtain ⟨k, hk, h, hh, he⟩ := DoubleCoset.eq.mp heq
      rw [hH, Subgroup.mem_bot] at hh
      exact ⟨⟨k, hk⟩, by simpa only [hh, mul_one] using he⟩
  refine ⟨rep, hrank, ?_, ?_⟩
  · intro τ
    refine ⟨classify (DoubleCoset.mk K H τ), (rightCoset τ _).mpr rfl, ?_⟩
    intro R hR
    exact (rightCoset τ R).mp hR
  · intro τ
    -- Inversion exchanges Kσ and σ⁻¹K and uses the same matrix R.
    have invert (R : Mat) :
        (∃ k : K, τ = (rep R)⁻¹ * (k : G)) ↔
          (∃ k : K, τ⁻¹ = (k : G) * rep R) := by
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k⁻¹, by
          simpa only [mul_inv_rev, inv_inv] using congrArg (fun g : G => g⁻¹) hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k⁻¹, by
          simpa only [mul_inv_rev, inv_inv] using congrArg (fun g : G => g⁻¹) hk⟩
    simp_rw [invert, rightCoset]
    exact ⟨_, rfl, fun _ h => h⟩
)

#print axioms OneSidedTableauCosetRepresentatives
