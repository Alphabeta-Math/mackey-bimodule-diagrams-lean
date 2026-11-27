import MackeyDiagrams
import Proofs.CommonMackeyIntersectionSum
import Proofs.MackeyIdentityDiagram
import Mathlib.Data.ZMod.QuotientGroup

namespace TwoMackeySummandsAux

private abbrev P := Equiv.Perm (Fin 3)
private abbrev C := Multiplicative (ZMod 2)
private abbrev U := P × C
private abbrev a : P := Equiv.swap 0 1
private abbrev b : P := Equiv.swap 0 2
private abbrev K : Subgroup U := (Subgroup.zpowers a).prod ⊤
private abbrev L : Subgroup U := (⊥ : Subgroup P).prod ⊤
private abbrev s : U := (b, 1)

private theorem perm_cases (p : P) :
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b ∨ p = b * a ∨ p = a * b * a :=
  (by decide : ∀ p : P,
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b ∨ p = b * a ∨ p = a * b * a) p

private theorem a_order : orderOf a = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, Equiv.swap_mul_self]
  · decide

private theorem mem_cyclic (p : P) : p ∈ Subgroup.zpowers a ↔ p = 1 ∨ p = a := by
  rw [mem_zpowers_iff_mem_range_orderOf, a_order]
  simp [Finset.range_succ]

private theorem cosets_ne : DoubleCoset.mk K K (1 : U) ≠ DoubleCoset.mk K K s := by
  intro h
  obtain ⟨x, hx, y, hy, he⟩ := DoubleCoset.eq.mp h
  have hs : s ∈ K := by rw [he, mul_one]; exact K.mul_mem hx hy
  have hp := (mem_cyclic b).mp hs.1
  exact (by decide : ¬ (b = 1 ∨ b = a)) hp

private theorem cosets_all (j : DoubleCoset.Quotient (K : Set U) (K : Set U)) :
    j = DoubleCoset.mk K K (1 : U) ∨ j = DoubleCoset.mk K K s := by
  induction j using Quotient.inductionOn' with
  | h g =>
    change DoubleCoset.mk K K g = DoubleCoset.mk K K 1 ∨
      DoubleCoset.mk K K g = DoubleCoset.mk K K s
    have km (x : P) (hx : x = 1 ∨ x = a) (z : C) : (x,z) ∈ K :=
      ⟨(mem_cyclic x).mpr hx, Subgroup.mem_top _⟩
    have left (x y : P) (hx : x = 1 ∨ x = a) (e : g.1 = x) :
        DoubleCoset.mk K K g = DoubleCoset.mk K K 1 := by
      symm
      apply DoubleCoset.eq.mpr
      refine ⟨(x,g.2), km x hx _, 1, K.one_mem, ?_⟩
      rw [mul_one, mul_one]
      exact Prod.ext e rfl
    have right (x y : P) (hx : x = 1 ∨ x = a) (hy : y = 1 ∨ y = a)
        (e : g.1 = x * b * y) : DoubleCoset.mk K K g = DoubleCoset.mk K K s := by
      symm
      apply DoubleCoset.eq.mpr
      exact ⟨(x,g.2), km x hx _, (y,1), km y hy _,
        Prod.ext e (by change g.2 = g.2 * 1 * 1; simp)⟩
    rcases perm_cases g.1 with h | h | h | h | h | h
    · exact Or.inl (left 1 1 (Or.inl rfl) h)
    · exact Or.inl (left a 1 (Or.inr rfl) h)
    · exact Or.inr (right 1 1 (Or.inl rfl) (Or.inl rfl) (by simpa using h))
    · exact Or.inr (right a 1 (Or.inr rfl) (Or.inl rfl) (by simpa using h))
    · exact Or.inr (right 1 a (Or.inl rfl) (Or.inr rfl) (by simpa using h))
    · exact Or.inr (right a a (Or.inr rfl) (Or.inr rfl) h)

private theorem conjugate_one {V : Type*} [Group V] (S : Subgroup V) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : V))) S = S := by
  have h : MulEquiv.toMonoidHom (MulAut.conj (1 : V)) = MonoidHom.id V := by
    ext x
    change (1 : V) * x * 1⁻¹ = x
    simp
  rw [h, Subgroup.map_id]

private theorem intersection_s :
    K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) K = L := by
  ext x
  change (x ∈ K ∧ x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) K) ↔ x ∈ L
  constructor
  · rintro ⟨hx, hm⟩
    obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp hm
    have he' : b * y.1 * b⁻¹ = x.1 := congrArg Prod.fst he
    refine ⟨Subgroup.mem_bot.mpr ?_, Subgroup.mem_top _⟩
    rcases (mem_cyclic x.1).mp hx.1 with h | h
    · exact h
    · rcases (mem_cyclic y.1).mp hy.1 with h' | h'
      · exact (by decide : b * 1 * b⁻¹ ≠ a) ((h' ▸ he').trans h)
      · exact (by decide : b * a * b⁻¹ ≠ a) ((h' ▸ he').trans h)
  · intro hx
    have hx' : x.1 = 1 := Subgroup.mem_bot.mp hx.1
    have hk : x ∈ K := ⟨(mem_cyclic _).mpr (Or.inl hx'), Subgroup.mem_top _⟩
    refine ⟨hk, Subgroup.mem_map.mpr ⟨x, hk, Prod.ext ?_ ?_⟩⟩
    · change b * x.1 * b⁻¹ = x.1
      simp [hx']
    · change (1 : C) * x.2 * 1⁻¹ = x.2
      simp

private theorem index_K : L.relIndex K = 2 := by
  have hk : Nat.card K = 4 := by
    change Nat.card ((Subgroup.zpowers a).prod (⊤ : Subgroup C)) = 4
    rw [Nat.card_congr ((Subgroup.zpowers a).prodEquiv (⊤ : Subgroup C)).toEquiv,
      Nat.card_prod, Nat.card_zpowers, a_order, Subgroup.card_top]
    change 2 * Nat.card (ZMod 2) = 4
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hl : Nat.card L = 2 := by
    change Nat.card ((⊥ : Subgroup P).prod (⊤ : Subgroup C)) = 2
    rw [Nat.card_congr ((⊥ : Subgroup P).prodEquiv (⊤ : Subgroup C)).toEquiv,
      Nat.card_prod, Subgroup.card_bot, Subgroup.card_top]
    change 1 * Nat.card (ZMod 2) = 2
    rw [Nat.card_eq_fintype_card, ZMod.card, one_mul]
  have h := Subgroup.relIndex_mul_card L K
  have hLK : L ≤ K := Subgroup.prod_mono bot_le le_rfl
  rw [inf_eq_left.mpr hLK, hl, hk] at h
  omega

end TwoMackeySummandsAux
