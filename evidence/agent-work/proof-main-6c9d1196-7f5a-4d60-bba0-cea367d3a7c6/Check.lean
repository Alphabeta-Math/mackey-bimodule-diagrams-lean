import MackeyDiagrams
import Proofs.StandardTwoBlockRepresentatives

set_option maxHeartbeats 2000000


theorem TwoBlockSplitGivesFourIntersections : (
let X : Finset Nat := Finset.Icc 1 4
let G := Equiv.Perm ↥X
let interval := fun lo hi : Nat =>
  Finset.filter (fun x : ↥X => lo ≤ Subtype.val x ∧ Subtype.val x ≤ hi) Finset.univ
let blocks : Fin 2 → Finset ↥X := fun r =>
  if r = 0 then interval 1 2 else interval 3 4
let blockSym := fun S : Finset ↥X =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ S))
let P : Subgroup G := iSup (fun r => blockSym (blocks r))
let point : Fin 4 → ↥X := fun i =>
  ⟨Fin.val i + 1, Iff.mpr Finset.mem_Icc
    ⟨Nat.succ_le_succ (Nat.zero_le (Fin.val i)), Nat.succ_le_of_lt (Fin.isLt i)⟩⟩
let σ : G := Equiv.swap (point 1) (point 2)
let representative : Fin 3 → G := fun i =>
  if i = 0 then 1 else if i = 1 then σ else Equiv.swap (point 0) (point 3) * σ
let C : Fin 2 → Fin 2 → Finset ↥X := fun r c =>
  blocks r ∩ Finset.map (Equiv.toEmbedding σ) (blocks c)
let L : Subgroup G := P ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj σ)) P
let binaryRefinements : Set (Subgroup G) :=
  {Q | ∃ U : Finset ↥X, Finset.card U = 2 ∧
    Q = blockSym U ⊔ blockSym (Finset.univ \ U)}
Function.Bijective (fun i => DoubleCoset.mk P P (representative i)) ∧
  (∀ r c, Finset.card (C r c) = 1) ∧
  L = ⊥ ∧
  L ∉ binaryRefinements
) :=
(by
  intro X G interval blocks blockSym P point σ representative C L binaryRefinements
  -- Xiao, Example 7.8 (archived p. 31, published 28 November revision p. 33).
  -- Alphabeta Math's §7.2 steps 1–2 split ordered row blocks and match the
  -- ordered column pieces with the same matrix sizes. We use the registered
  -- StandardTwoBlockRepresentatives result for §7.3's alternative
  -- transposition construction and its matrix and Mackey intersection
  -- formulas. The two cuts are both 2, strictly between 0 and 4.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-double-cosets
  have standard := StandardTwoBlockRepresentatives 4 2 2 (by decide) (by decide)
    (by decide) (by decide)
  dsimp only at standard
  obtain ⟨left, right, rep, hlabels, hzero, hsucc, _, hbij, _, hcells⟩ := standard
  -- The supplier indexes its two transpositions by Fin 2. Identify their
  -- endpoints by their Nat labels in Icc 1 4.
  have hleft₀ : left (0 : Fin 2) = point 1 := Subtype.ext (hlabels (0 : Fin 2)).1
  have hright₀ : right (0 : Fin 2) = point 2 := Subtype.ext (hlabels (0 : Fin 2)).2
  have hleft₁ : left (1 : Fin 2) = point 0 := Subtype.ext (hlabels (1 : Fin 2)).1
  have hright₁ : right (1 : Fin 2) = point 3 := Subtype.ext (hlabels (1 : Fin 2)).2
  have hmid : rep (1 : Fin 3) = σ := by
    have step := hsucc (0 : Fin 2)
    change rep (1 : Fin 3) = Equiv.swap (left (0 : Fin 2)) (right (0 : Fin 2)) *
      rep (0 : Fin 3) at step
    rw [hleft₀, hright₀, hzero, mul_one] at step
    exact step
  have hlast : rep (2 : Fin 3) = Equiv.swap (point 0) (point 3) * σ := by
    have step := hsucc (1 : Fin 2)
    change rep (2 : Fin 3) = Equiv.swap (left (1 : Fin 2)) (right (1 : Fin 2)) *
      rep (1 : Fin 3) at step
    rw [hleft₁, hright₁, hmid] at step
    exact step
  have hrep : rep = representative := by
    funext i
    fin_cases i
    · exact hzero
    · exact hmid
    · exact hlast
  have hclasses : Function.Bijective (fun i => DoubleCoset.mk P P (representative i)) := by
    rw [← hrep]
    exact hbij
  -- The middle matrix parameter is a = 2 - 1. The four cardinality
  -- formulas apply to the actual interval filters and transported blocks.
  obtain ⟨h00, h01, h10, h11, _, hintersection⟩ := hcells (1 : Fin 3)
  rw [hmid] at h00 h01 h10 h11 hintersection
  change Int.ofNat (C 0 0).card = (1 : Int) at h00
  change Int.ofNat (C 0 1).card = (1 : Int) at h01
  change Int.ofNat (C 1 0).card = (1 : Int) at h10
  change Int.ofNat (C 1 1).card = (1 : Int) at h11
  have hsizes (r c : Fin 2) : (C r c).card = 1 := by
    fin_cases r <;> fin_cases c
    · exact Int.ofNat.inj h00
    · exact Int.ofNat.inj h01
    · exact Int.ofNat.inj h10
    · exact Int.ofNat.inj h11
  -- Each one-point permutation group is trivial. Hence so is the
  -- supremum of the actual nonempty Mackey block factors.
  have hsingle (S : Finset ↥X) (hS : S.card = 1) : blockSym S ≤ (⊥ : Subgroup G) := by
    have hsub : Subsingleton ↥S := Finset.card_le_one_iff_subsingleton_coe.mp hS.le
    rintro _ ⟨g, rfl⟩
    rw [show g = 1 from Subsingleton.elim _ _, map_one]
    exact Subgroup.one_mem _
  change L = ⨆ p : {p : Fin 2 × Fin 2 // (C p.1 p.2).Nonempty},
    blockSym (C p.val.1 p.val.2) at hintersection
  have htrivial : L = ⊥ := by
    rw [hintersection]
    exact le_antisymm (iSup_le fun p => hsingle _ (hsizes p.val.1 p.val.2)) bot_le
  refine ⟨hclasses, hsizes, htrivial, ?_⟩
  -- For the exclusion, select both points of the prescribed two-point
  -- block. Their subtype swap extends to a nonidentity permutation.
  change ¬ ∃ U : Finset ↥X, U.card = 2 ∧ L = blockSym U ⊔ blockSym (Finset.univ \ U)
  rintro ⟨U, hU, hsplit⟩
  obtain ⟨x, y, hxy, hpair⟩ := Finset.card_eq_two.mp hU
  have hx : x ∈ U := by rw [hpair]; simp
  have hy : y ∈ U := by rw [hpair]; simp
  have hswap : Equiv.swap x y ∈ blockSym U := by
    exact ⟨Equiv.swap (⟨x, hx⟩ : ↥U) ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  have hmem : Equiv.swap x y ∈ L := by
    rw [hsplit]
    exact (le_sup_left : blockSym U ≤ blockSym U ⊔ blockSym (Finset.univ \ U)) hswap
  have heq : Equiv.swap x y = (1 : G) := Subgroup.mem_bot.mp (htrivial ▸ hmem)
  exact hxy ((congrArg (fun g : G => g x) heq).symm.trans (Equiv.swap_apply_left x y))
)

#print axioms TwoBlockSplitGivesFourIntersections
