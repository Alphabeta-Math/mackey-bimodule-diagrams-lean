import MackeyDiagrams
import Proofs.ParabolicMackeyIntersectionBlocks
import Proofs.TwoBlockDoubleCosetMatrices
import Proofs.ParabolicDoubleCosetRepresentatives

set_option maxHeartbeats 2000000

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
      rw [twoBlockPartition, ite_eq_left h]
      exact ⟨x, twoBlockMemInterval.mpr ⟨le_rfl, hc⟩⟩
    · let x : ↥(Finset.Icc 1 n) := ⟨cut + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      rw [twoBlockPartition, ite_eq_right h]
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
      simp only [twoBlockPartition, ite_eq_left hr, ite_eq_right hc0, twoBlockMemInterval] at hx hy
      omega
    · have hr0 : r ≠ 0 := fun h => hrc (h.trans hc'.symm)
      simp only [twoBlockPartition, ite_eq_right hr0, ite_eq_left hc', twoBlockMemInterval] at hx hy
      omega
  · intro x
    obtain ⟨hx₁, hx₂⟩ := twoBlockBounds x
    by_cases hx : x.val ≤ cut
    · exact ⟨0, by simpa [twoBlockPartition, twoBlockMemInterval] using And.intro hx₁ hx⟩
    · refine ⟨1, ?_⟩
      simp only [twoBlockPartition, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), twoBlockMemInterval]
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
      ite_eq_left (rfl : (0 : Fin 2) = 0), ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
      twoBlockMemInterval] <;>
    have h := hσ x
  all_goals
    rcases le_total n1 n2 with hle | hle
    · rw [min_eq_left hle] at hs
      rw [max_eq_right hle] at ht
      omega
    · rw [min_eq_right hle] at hs
      rw [max_eq_left hle] at ht
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

private theorem twoBlockParameter {n n1 n2 s t m : Nat}
    (hst : s + t = n1 + n2) (htn : t ≤ n) (hm : m = min s (n - t)) :
    Set.BijOn (fun i : Fin (m + 1) => (s : Int) - (i.val : Int)) Set.univ
      (Set.Icc (max 0 ((n1 : Int) + (n2 : Int) - (n : Int))) (s : Int)) := by
  have hms : m ≤ s := by rw [hm]; exact min_le_left ..
  have hmt : m ≤ n - t := by rw [hm]; exact min_le_right ..
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    have hi := i.isLt
    apply Set.mem_Icc.mpr
    change _ ≤ (s : Int) - (i.val : Int) ∧ (s : Int) - (i.val : Int) ≤ _
    exact ⟨max_le (by omega) (by omega), by omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    change (s : Int) - (i.val : Int) = (s : Int) - (j.val : Int) at hij
    omega
  · intro z hz
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hz
    have hz0 : 0 ≤ z := (le_max_left _ _).trans hlo
    have hzl : (n1 : Int) + (n2 : Int) - (n : Int) ≤ z := (le_max_right _ _).trans hlo
    let k := ((s : Int) - z).toNat
    have hk : (k : Int) = (s : Int) - z :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hhi)
    have hkm : k ≤ m := by
      rw [hm]
      exact le_min (by omega) (by omega)
    refine ⟨⟨k, Nat.lt_succ_of_le hkm⟩, Set.mem_univ _, ?_⟩
    change (s : Int) - (k : Int) = z
    omega

private theorem twoBlockCellSizes {n n1 n2 s t k : Nat}
    (hn₁ : n1 ≤ n) (hk : k ≤ s) (hs₁ : s ≤ n1) (ht₁ : n1 ≤ t)
    (htk : t + k ≤ n) (hsum : s + t = n1 + n2)
    (C : Fin 2 → Fin 2 → Finset ↥(Finset.Icc 1 n))
    (h00 : C 0 0 = twoBlockInterval n 1 (s - k))
    (h01 : C 0 1 = twoBlockInterval n (s - k + 1) n1)
    (h10 : C 1 0 = twoBlockInterval n (n1 + 1) (t + k))
    (h11 : C 1 1 = twoBlockInterval n (t + k + 1) n) :
    let a := (s : Int) - (k : Int)
    ((C 0 0).card : Int) = a ∧
    ((C 0 1).card : Int) = (n1 : Int) - a ∧
    ((C 1 0).card : Int) = (n2 : Int) - a ∧
    ((C 1 1).card : Int) = (n : Int) - (n1 : Int) - (n2 : Int) + a := by
  rw [h00, h01, h10, h11, twoBlockCardInterval le_rfl (by omega),
    twoBlockCardInterval (by omega) hn₁,
    twoBlockCardInterval (by omega) htk,
    twoBlockCardInterval (by omega) le_rfl]
  dsimp
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem StandardTwoBlockRepresentatives : (∀ (n n1 n2 : Nat), 1 ≤ n1 → n1 < n → 1 ≤ n2 → n2 < n →
  let X : Finset Nat := Finset.Icc 1 n
  let G := Equiv.Perm ↥X
  let interval := fun lo hi : Nat =>
    Finset.filter (fun x : ↥X => lo ≤ x.val ∧ x.val ≤ hi) Finset.univ
  let XBlock : Fin 2 → Finset ↥X := fun r =>
    if r = 0 then interval 1 n1 else interval (n1 + 1) n
  let YBlock : Fin 2 → Finset ↥X := fun c =>
    if c = 0 then interval 1 n2 else interval (n2 + 1) n
  let blockSym := fun S : Finset ↥X =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ S))
  let K : Subgroup G := iSup (fun r => blockSym (XBlock r))
  let H : Subgroup G := iSup (fun c => blockSym (YBlock c))
  let s := Nat.min n1 n2
  let t := Nat.max n1 n2
  let m := Nat.min s (n - t)
  let a : Fin (m + 1) → Int := fun i => Int.ofNat s - Int.ofNat i.val
  ∃ (left right : Fin m → ↥X) (σ : Fin (m + 1) → G),
    (∀ j : Fin m, (left j).val = s - j.val ∧ (right j).val = t + j.val + 1) ∧
    let τ : Fin m → G := fun j => Equiv.swap (left j) (right j)
    σ 0 = 1 ∧
    (∀ j : Fin m, σ (Fin.succ j) = τ j * σ (Fin.castSucc j)) ∧
    Pairwise (fun j k => Disjoint (Equiv.Perm.support (τ j)) (Equiv.Perm.support (τ k))) ∧
    Function.Bijective (fun i => DoubleCoset.mk K H (σ i)) ∧
    Set.BijOn a Set.univ
      (Set.Icc (max 0 (Int.ofNat n1 + Int.ofNat n2 - Int.ofNat n)) (Int.ofNat s)) ∧
    ∀ i : Fin (m + 1),
      let C : Fin 2 → Fin 2 → Finset ↥X := fun r c =>
        XBlock r ∩ Finset.map (Equiv.toEmbedding (σ i)) (YBlock c)
      let size := fun r c => Int.ofNat (Finset.card (C r c))
      size 0 0 = a i ∧
      size 0 1 = Int.ofNat n1 - a i ∧
      size 1 0 = Int.ofNat n2 - a i ∧
      size 1 1 = Int.ofNat n - Int.ofNat n1 - Int.ofNat n2 + a i ∧
      (∀ r c, ∃ lo hi : Nat, C r c = interval lo hi) ∧
      K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (σ i))) H =
        iSup (fun p : {p : Fin 2 × Fin 2 // Finset.Nonempty (C p.1 p.2)} =>
          blockSym (C p.val.1 p.val.2))) :=
(by
  intro n n1 n2 hn1 h1n hn2 h2n X G interval XBlock YBlock blockSym K H s t m a
  have hs₁ : s ≤ n1 := min_le_left ..
  have hs₂ : s ≤ n2 := min_le_right ..
  have ht₁ : n1 ≤ t := le_max_left ..
  have ht₂ : n2 ≤ t := le_max_right ..
  have hst : s ≤ t := hs₁.trans ht₁
  have htn : t ≤ n := max_le h1n.le h2n.le
  have hms : m ≤ s := min_le_left ..
  have hmt : m ≤ n - t := min_le_right ..
  have hsum : s + t = n1 + n2 := by
    rcases le_total n1 n2 with h | h
    · simp [s, t, min_eq_left h, max_eq_right h]
    · simp [s, t, min_eq_right h, max_eq_left h, Nat.add_comm]
  -- Xiao, §7.3 (archived pp. 30–31, revised published pp. 32–33),
  -- specifies a recursive family of actual transpositions. In Lean the
  -- article's step j+1 is indexed by j : Fin m.
  let left (j : Fin m) : ↥X :=
    ⟨s - j.val, Finset.mem_Icc.mpr ⟨by have := j.isLt; omega, by omega⟩⟩
  let right (j : Fin m) : ↥X :=
    ⟨t + j.val + 1, Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩⟩
  let τ (j : Fin m) : G := Equiv.swap (left j) (right j)
  let σ : Fin (m + 1) → G :=
    Fin.induction (motive := fun _ => G) 1 (fun j prev => τ j * prev)
  have hzero : σ 0 = 1 := by simp only [σ, Fin.induction_zero]
  have hsucc (j : Fin m) : σ j.succ = τ j * σ j.castSucc := by
    simp only [σ, Fin.induction_succ]
  have himage (i : Fin (m + 1)) (x : ↥X) :
      ((σ i).symm x).val ≤ n2 ↔
        x.val ≤ s - i.val ∨ (s < x.val ∧ x.val ≤ n2) ∨
          (t < x.val ∧ x.val ≤ t + i.val) := by
    induction i using Fin.induction generalizing x with
    | zero =>
        rw [hzero]
        change x.val ≤ n2 ↔
          x.val ≤ s - 0 ∨ (s < x.val ∧ x.val ≤ n2) ∨ (t < x.val ∧ x.val ≤ t + 0)
        omega
    | succ j ih =>
        rw [hsucc]
        have hj := j.isLt
        exact twoBlockSwapImage hs₂ ht₂ (by omega) (left j) (right j) rfl rfl
          (σ j.castSucc) ih x
  let C (f : G) (r c : Fin 2) := XBlock r ∩ (YBlock c).map f.toEmbedding
  have hcells (i : Fin (m + 1)) :
      C (σ i) 0 0 = twoBlockInterval n 1 (s - i.val) ∧
      C (σ i) 0 1 = twoBlockInterval n (s - i.val + 1) n1 ∧
      C (σ i) 1 0 = twoBlockInterval n (n1 + 1) (t + i.val) ∧
      C (σ i) 1 1 = twoBlockInterval n (t + i.val + 1) n := by
    have hi := i.isLt
    exact twoBlockCellIntervals rfl rfl (by omega) (σ i) (himage i)
  have hsizes (i : Fin (m + 1)) :
      ((C (σ i) 0 0).card : Int) = a i ∧
      ((C (σ i) 0 1).card : Int) = (n1 : Int) - a i ∧
      ((C (σ i) 1 0).card : Int) = (n2 : Int) - a i ∧
      ((C (σ i) 1 1).card : Int) = (n : Int) - (n1 : Int) - (n2 : Int) + a i := by
    have hi := i.isLt
    obtain ⟨h00, h01, h10, h11⟩ := hcells i
    exact twoBlockCellSizes h1n.le (by omega) hs₁ ht₁ (by omega) hsum
      (C (σ i)) h00 h01 h10 h11
  have ha : Set.BijOn a Set.univ
      (Set.Icc (max 0 ((n1 : Int) + (n2 : Int) - (n : Int))) (s : Int)) :=
    twoBlockParameter hsum htn rfl
  obtain ⟨hneX, hdX, hcX⟩ := twoBlockPartitionFacts hn1 h1n
  obtain ⟨hneY, hdY, hcY⟩ := twoBlockPartitionFacts hn2 h2n
  -- Alphabeta Math's §7.2 steps 1–2 match ordered cell pieces to
  -- construct a representative. To verify the particular product of
  -- transpositions in §7.3, use the classification equivalence from
  -- Proposition 7.3 with the entries computed above.
  obtain ⟨classify, hclass, _⟩ :=
    ParabolicDoubleCosetRepresentatives X 2 2 XBlock YBlock hneX hneY hdX hdY hcX hcY
  have hmat (f : G) :=
    (TwoBlockDoubleCosetMatrices X XBlock YBlock hneX hneY hdX hdY hcX hcY
      (fun r c => ((C f r c).card : Int))).mp ⟨f, fun _ _ => rfl⟩
  have cardX : X.card = n := by
    change (Finset.Icc 1 n).card = n
    rw [Nat.card_Icc]
    omega
  have cardX₀ : (XBlock 0).card = n1 := by
    change (twoBlockInterval n 1 n1).card = n1
    rw [twoBlockCardInterval le_rfl h1n.le]
    omega
  have cardY₀ : (YBlock 0).card = n2 := by
    change (twoBlockInterval n 1 n2).card = n2
    rw [twoBlockCardInterval le_rfl h2n.le]
    omega
  refine ⟨left, right, σ, fun _ => ⟨rfl, rfl⟩, hzero, hsucc, ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    have hj := j.isLt
    have hk := k.isLt
    have hjk' : j.val ≠ k.val := fun e => hjk (Fin.ext e)
    have hl (l : Fin m) : (left l).val = s - l.val := rfl
    have hr (l : Fin m) : (right l).val = t + l.val + 1 := rfl
    have hne (l : Fin m) : left l ≠ right l := by
      intro e
      have h := congrArg Subtype.val e
      rw [hl, hr] at h
      omega
    simp only [Equiv.Perm.support_swap (hne _), Finset.disjoint_left,
      Finset.mem_insert, Finset.mem_singleton]
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      have he := congrArg Subtype.val (hx.symm.trans hy) <;>
      simp only [hl, hr] at he <;>
      omega
  · constructor
    · intro i j hij
      have he := congrArg (fun q => ((classify q).val 0 0 : Int)) hij
      change ((classify (DoubleCoset.mk K H (σ i))).val 0 0 : Int) =
        ((classify (DoubleCoset.mk K H (σ j))).val 0 0 : Int) at he
      rw [hclass, hclass, (hsizes i).1, (hsizes j).1] at he
      exact ha.2.1 (Set.mem_univ _) (Set.mem_univ _) he
    · intro q
      let f : G := q.out
      have hf : DoubleCoset.mk K H f = q := DoubleCoset.out_eq' q
      obtain ⟨z, ⟨hlo, hhi, hz00, hz01, hz10, hz11⟩, _⟩ := hmat f
      simp only [cardX, cardX₀, cardY₀] at hlo hhi hz01 hz10 hz11
      have hhi' : z ≤ (s : Int) := by
        rcases le_total n1 n2 with h | h
        · simpa only [s, min_eq_left h] using hhi.trans (min_le_left ..)
        · simpa only [s, min_eq_right h] using hhi.trans (min_le_right ..)
      obtain ⟨i, _, hi⟩ := ha.2.2 (Set.mem_Icc.mpr ⟨hlo, hhi'⟩)
      change a i = z at hi
      refine ⟨i, ?_⟩
      change DoubleCoset.mk K H (σ i) = q
      rw [← hf]
      apply classify.injective
      apply Subtype.ext
      funext r c
      rw [hclass, hclass]
      obtain ⟨hi00, hi01, hi10, hi11⟩ := hsizes i
      rw [hi] at hi00 hi01 hi10 hi11
      have he00 := hi00.trans hz00.symm
      have he01 := hi01.trans hz01.symm
      have he10 := hi10.trans hz10.symm
      have he11 := hi11.trans hz11.symm
      fin_cases r <;> fin_cases c
      · exact Int.ofNat_inj.mp he00
      · exact Int.ofNat_inj.mp he01
      · exact Int.ofNat_inj.mp he10
      · exact Int.ofNat_inj.mp he11
  · exact ha
  · intro i C' size
    obtain ⟨h00, h01, h10, h11⟩ := hsizes i
    refine ⟨h00, h01, h10, h11, ?_, ?_⟩
    · intro r c
      obtain ⟨e00, e01, e10, e11⟩ := hcells i
      fin_cases r <;> fin_cases c
      · exact ⟨_, _, e00⟩
      · exact ⟨_, _, e01⟩
      · exact ⟨_, _, e10⟩
      · exact ⟨_, _, e11⟩
    · -- The registered block formula includes empty cells. Each empty
      -- cell contributes only the identity subgroup, so omit those cells
      -- as in §7.3.
      exact (ParabolicMackeyIntersectionBlocks X 2 2 XBlock YBlock
        hneX hneY hdX hdY hcX hcY (σ i)).trans (twoBlockOmitEmpty (C (σ i))))

#print axioms StandardTwoBlockRepresentatives
