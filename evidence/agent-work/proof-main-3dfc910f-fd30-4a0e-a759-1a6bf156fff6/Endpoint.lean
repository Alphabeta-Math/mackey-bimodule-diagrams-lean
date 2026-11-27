import Mathlib.GroupTheory.Perm.ConjAct
import MackeyDiagrams
import Proofs.EqualTwoBlockSubgroups

set_option maxHeartbeats 2000000

theorem MackeyConjugationExchangesFactors : (
let X : Finset Nat := Finset.Icc 1 4
let G := Equiv.Perm ↥X
let interval := fun lo hi : Nat =>
  Finset.filter (fun x : ↥X => lo ≤ Subtype.val x ∧ Subtype.val x ≤ hi) Finset.univ
let blockSym := fun S : Finset ↥X =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ S))
let A : Subgroup G := blockSym (interval 1 2)
let B : Subgroup G := blockSym (interval 3 4)
let K : Subgroup G := A ⊔ B
let point := fun j : Nat => fun h : 1 ≤ j ∧ j ≤ 4 =>
  (⟨j, Finset.mem_Icc.mpr h⟩ : ↥X)
let σ : G :=
  Equiv.swap (point 1 (by decide)) (point 4 (by decide)) *
    Equiv.swap (point 2 (by decide)) (point 3 (by decide))
let L : Subgroup G := K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj σ)) K
let conjugate := MulEquiv.toMonoidHom (MulAut.conj (σ⁻¹))
L = K ∧
  Subgroup.map conjugate L = L ∧
  Subgroup.map conjugate A = B ∧
  Subgroup.map conjugate B = A
) :=
(by
  intro X G interval blockSym A B K point σ L conjugate
  -- Xiao, Example 7.5 (archived PDF p. 31, 28 November revision p. 33).
  -- Alphabeta Math §7.2, steps 1 and 2, split the row and column blocks
  -- into pieces of the matrix sizes and match corresponding pieces in order.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-double-cosets
  -- Here the row and column partitions are both (1–2, 3–4), each covering X
  -- with disjoint nonempty blocks. At i = 2 only the two off-diagonal cells
  -- remain. Section 7.3 uses the reverse-pairing representative for those
  -- cells. Specialize EqualTwoBlockSubgroups to certify that choice and L.
  have memInterval (lo hi : Nat) (x : ↥X) :
      x ∈ interval lo hi ↔ lo ≤ x.val ∧ x.val ≤ hi := by
    change x ∈ Finset.univ.filter (fun y : ↥X => lo ≤ y.val ∧ y.val ≤ hi) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have bounds (x : ↥X) : 1 ≤ x.val ∧ x.val ≤ 4 :=
    Finset.mem_Icc.mp x.property
  have hL : L = K := by
    obtain ⟨left, right, reps, labels, zero, step, _, intersections⟩ :=
      EqualTwoBlockSubgroups 2 2 (by decide) (by decide)
    have left0 : left 0 = point 2 (by decide) := Subtype.ext (labels 0).1
    have right0 : right 0 = point 3 (by decide) := Subtype.ext (labels 0).2
    have left1 : left 1 = point 1 (by decide) := Subtype.ext (labels 1).1
    have right1 : right 1 = point 4 (by decide) := Subtype.ext (labels 1).2
    have step0 : reps 1 = Equiv.swap (left 0) (right 0) * reps 0 := step 0
    have step1 : reps 2 = Equiv.swap (left 1) (right 1) * reps 1 := step 1
    have hrep : reps 2 = σ := by
      rw [step1, step0, zero, mul_one, left0, right0, left1, right1]
    let blocks : Fin 2 → Subgroup G := fun r =>
      blockSym (if r = 0 then interval 1 2 else interval 3 4)
    have hblocks : (⨆ r, blocks r) = K := by
      change (⨆ r, blocks r) = blocks 0 ⊔ blocks 1
      refine le_antisymm (iSup_le ?_) (sup_le (le_iSup blocks 0) (le_iSup blocks 1))
      intro r
      fin_cases r
      · exact le_sup_left
      · exact le_sup_right
    have emptyFactor (lo hi : Nat) (h : hi < lo) : blockSym (interval lo hi) = ⊥ := by
      apply le_antisymm ?_ bot_le
      rintro _ ⟨f, rfl⟩
      apply Subgroup.mem_bot.mpr
      apply Equiv.ext
      intro x
      apply Equiv.Perm.ofSubtype_apply_of_not_mem
      intro hx
      have := (memInterval lo hi x).mp hx
      omega
    have intersection := (intersections (2 : Fin 3)).1
    change (⨆ r, blocks r) ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (reps 2))) (⨆ r, blocks r) =
      ((blockSym (interval 1 0) ⊔ A) ⊔ B) ⊔ blockSym (interval 5 4) at intersection
    rw [hblocks, hrep, emptyFactor 1 0 (by decide), emptyFactor 5 4 (by decide),
      bot_sup_eq, sup_bot_eq] at intersection
    exact intersection
  -- Compute the action on the concrete factor inclusions by evaluating the
  -- representative and transporting the subgroup supported in each interval.
  let perm : Equiv.Perm ↥X := σ
  have reflect (x : ↥X) : (perm x).val = 5 - x.val := by
    have hx := bounds x
    have labels : x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 := by omega
    change ((Equiv.swap (point 1 (by decide)) (point 4 (by decide)) *
      Equiv.swap (point 2 (by decide)) (point 3 (by decide))) x).val = _
    rw [Equiv.Perm.mul_apply]
    simp only [Equiv.swap_apply_def]
    rcases labels with h | h | h | h
    · have hx' : x = point 1 (by decide) := Subtype.ext h
      rw [hx']
      decide
    · have hx' : x = point 2 (by decide) := Subtype.ext h
      rw [hx']
      decide
    · have hx' : x = point 3 (by decide) := Subtype.ext h
      rw [hx']
      decide
    · have hx' : x = point 4 (by decide) := Subtype.ext h
      rw [hx']
      decide
  have hinv : perm⁻¹ = perm := by
    apply inv_eq_of_mul_eq_one_right
    apply Equiv.ext
    intro x
    change perm (perm x) = x
    apply Subtype.ext
    rw [reflect, reflect]
    have := bounds x
    omega
  let _ : MulAction (Equiv.Perm ↥X) (Finset ↥X) := Finset.mulActionFinset
  have blockImage (lo hi : Nat) :
      perm • interval lo hi = interval (5 - hi) (5 - lo) := by
    ext x
    rw [← Finset.inv_smul_mem_iff, hinv, memInterval, memInterval]
    change lo ≤ (perm x).val ∧ (perm x).val ≤ hi ↔
      5 - hi ≤ x.val ∧ x.val ≤ 5 - lo
    rw [reflect]
    have := bounds x
    omega
  have transport (lo hi : Nat) :
      Subgroup.map conjugate (blockSym (interval lo hi)) =
        blockSym (interval (5 - hi) (5 - lo)) := by
    have h := Equiv.Perm.conj_smul_range_ofSubtype perm (interval lo hi)
    change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj perm))
      (blockSym (interval lo hi)) = blockSym (perm • interval lo hi) at h
    rw [blockImage] at h
    change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj perm⁻¹))
        (blockSym (interval lo hi)) = _
    rwa [hinv]
  have hAB : Subgroup.map conjugate A = B := transport 1 2
  have hBA : Subgroup.map conjugate B = A := transport 3 4
  refine ⟨hL, ?_, hAB, hBA⟩
  rw [hL]
  change Subgroup.map conjugate (A ⊔ B) = A ⊔ B
  -- The reviewed two-factor join is binary, so use map_sup here.
  rw [Subgroup.map_sup, hAB, hBA, sup_comm])

#print axioms MackeyConjugationExchangesFactors
