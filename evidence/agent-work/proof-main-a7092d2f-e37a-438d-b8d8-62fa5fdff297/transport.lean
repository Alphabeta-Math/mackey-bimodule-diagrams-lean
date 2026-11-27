
private abbrev threeCosetsInterval := Finset.Icc (9 : Nat) 12

private def threeCosetsShift : ↥(Finset.Icc (1 : Nat) 4) ≃ ↥threeCosetsInterval where
  toFun x := ⟨x.val + 8, Finset.mem_Icc.mpr (by
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp x.property
    exact ⟨by omega, by omega⟩)⟩
  invFun y := ⟨y.val - 8, Finset.mem_Icc.mpr (by
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp y.property
    exact ⟨by omega, by omega⟩)⟩
  left_inv _ := Subtype.ext (Nat.add_sub_cancel _ _)
  right_inv y := by
    apply Subtype.ext
    have h := (Finset.mem_Icc.mp y.property).1
    change y.val - 8 + 8 = y.val
    omega

private abbrev threeCosetsPoint (n : Nat) (h₁ : 9 ≤ n := by decide)
    (h₂ : n ≤ 12 := by decide) : ↥threeCosetsInterval :=
  ⟨n, Finset.mem_Icc.mpr ⟨h₁, h₂⟩⟩

private abbrev threeCosetsMiddle : Equiv.Perm ↥threeCosetsInterval :=
  Equiv.swap (threeCosetsPoint 10) (threeCosetsPoint 11)

private abbrev threeCosetsLast : Equiv.Perm ↥threeCosetsInterval :=
  Equiv.swap (threeCosetsPoint 9) (threeCosetsPoint 12) * threeCosetsMiddle

private abbrev threeCosetsRep (i : Fin 3) : Equiv.Perm ↥threeCosetsInterval :=
  if i = 0 then 1 else if i = 1 then threeCosetsMiddle else threeCosetsLast

private theorem threeCosets_congr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (x y : α) :
    e.permCongrHom (Equiv.swap x y) = Equiv.swap (e x) (e y) := by
  apply Equiv.ext
  intro z
  obtain ⟨w, rfl⟩ := e.surjective z
  change e (Equiv.swap x y (e.symm (e w))) = Equiv.swap (e x) (e y) (e w)
  rw [e.symm_apply_apply, e.injective.swap_apply]

private theorem threeCosets_congr_eq {U V : Type*} [Group U] [Group V]
    (e : U ≃* V) (A : Subgroup U) (B : Subgroup V) (he : ∀ x, e x ∈ B ↔ x ∈ A)
    (x y : U) :
    DoubleCoset.mk B B (e x) = DoubleCoset.mk B B (e y) ↔
      DoubleCoset.mk A A x = DoubleCoset.mk A A y := by
  simp only [DoubleCoset.eq]
  constructor
  · rintro ⟨l, hl, r, hr, h⟩
    obtain ⟨l, rfl⟩ := e.surjective l
    obtain ⟨r, rfl⟩ := e.surjective r
    exact ⟨l, (he l).mp hl, r, (he r).mp hr, e.injective (by simpa only [map_mul] using h)⟩
  · rintro ⟨l, hl, r, hr, rfl⟩
    exact ⟨e l, (he l).mpr hl, e r, (he r).mpr hr, by simp only [map_mul]⟩

private theorem threeCosets_local :
    Function.Bijective (fun i => DoubleCoset.mk (threeCosetsSplit threeCosetsInterval 10)
      (threeCosetsSplit threeCosetsInterval 10) (threeCosetsRep i)) := by
  let X := Finset.Icc (1 : Nat) 4
  let blocks (i : Fin 2) : Finset ↥X :=
    if i = 0 then Finset.filter (fun y : ↥X => 1 ≤ y.val ∧ y.val ≤ 2) Finset.univ
    else Finset.filter (fun y : ↥X => 3 ≤ y.val ∧ y.val ≤ 4) Finset.univ
  let factors (i : Fin 2) := threeCosetsRange (fun x : ↥X => x ∈ blocks i)
  let T : Subgroup (Equiv.Perm ↥X) := ⨆ i, factors i
  have hT : T = threeCosetsSplit X 2 := by
    have hlo : (threeCosetsRange
        (fun x : ↥X => x ∈ Finset.filter (fun y : ↥X => 1 ≤ y.val ∧ y.val ≤ 2)
          Finset.univ)) = threeCosetsHalf X 2 false := by
      ext f
      rw [threeCosetsRange_mem, (threeCosetsHalf_mem X 2 f).1]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h (x : ↥X) := (Finset.mem_Icc.mp x.property).1
      simp only [h, true_and, Nat.not_le]
    have hhi : (threeCosetsRange
        (fun x : ↥X => x ∈ Finset.filter (fun y : ↥X => 3 ≤ y.val ∧ y.val ≤ 4)
          Finset.univ)) = threeCosetsHalf X 2 true := by
      ext f
      rw [threeCosetsRange_mem, (threeCosetsHalf_mem X 2 f).2]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h (x : ↥X) := (Finset.mem_Icc.mp x.property).2
      simp only [h, and_true, Nat.not_le]
      simp only [Nat.lt_succ_iff]
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      fin_cases i
      · change _ ≤ threeCosetsSplit X 2
        exact hlo.trans_le le_sup_left
      · change _ ≤ threeCosetsSplit X 2
        exact hhi.trans_le le_sup_right
    · apply sup_le
      · exact hlo.symm.trans_le (le_iSup factors 0)
      · exact hhi.symm.trans_le (le_iSup factors 1)
  -- The Alphabeta Math plan records Proposition 7.3, steps 1–2, which
  -- match ordered pieces of the two partitions. The registered §7.3 theorem
  -- checks the specific transpositions against that double-coset
  -- classification. Specialize it with both split sizes 2 and shift by 8.
  obtain ⟨l, r, s, hpoints, hzero, hsucc, _, hbij, _, _⟩ :=
    StandardTwoBlockRepresentatives 4 2 2 (by decide) (by decide) (by decide) (by decide)
  change (∀ j : Fin 2, (l j).val = 2 - j.val ∧ (r j).val = 2 + j.val + 1) at hpoints
  change (∀ j : Fin 2, s j.succ = Equiv.swap (l j) (r j) * s j.castSucc) at hsucc
  change Function.Bijective (fun i : Fin 3 => DoubleCoset.mk T T (s i)) at hbij
  let e := threeCosetsShift.permCongrHom
  let A := threeCosetsSplit threeCosetsInterval 10
  have hmem (f : Equiv.Perm ↥X) : e f ∈ A ↔ f ∈ T := by
    rw [hT, threeCosetsSplit_mem, threeCosetsSplit_mem]
    have h (x : ↥X) : (threeCosetsShift x).val ≤ 10 ↔ x.val ≤ 2 := by
      change x.val + 8 ≤ 10 ↔ x.val ≤ 2
      omega
    have he (x : ↥X) : e f (threeCosetsShift x) = threeCosetsShift (f x) := by
      change threeCosetsShift (f (threeCosetsShift.symm (threeCosetsShift x))) = _
      rw [Equiv.symm_apply_apply]
    constructor
    · intro hf x
      simpa only [he, h] using hf (threeCosetsShift x)
    · intro hf y
      obtain ⟨x, rfl⟩ := threeCosetsShift.surjective y
      simpa only [he, h] using hf x
  have hleft₀ : threeCosetsShift (l (0 : Fin 2)) = threeCosetsPoint 10 := by
    apply Subtype.ext
    change (l (0 : Fin 2)).val + 8 = 10
    exact congrArg (fun n : Nat => n + 8) (hpoints 0).1
  have hright₀ : threeCosetsShift (r (0 : Fin 2)) = threeCosetsPoint 11 := by
    apply Subtype.ext
    change (r (0 : Fin 2)).val + 8 = 11
    exact congrArg (fun n : Nat => n + 8) (hpoints 0).2
  have hleft₁ : threeCosetsShift (l (1 : Fin 2)) = threeCosetsPoint 9 := by
    apply Subtype.ext
    change (l (1 : Fin 2)).val + 8 = 9
    exact congrArg (fun n : Nat => n + 8) (hpoints 1).1
  have hright₁ : threeCosetsShift (r (1 : Fin 2)) = threeCosetsPoint 12 := by
    apply Subtype.ext
    change (r (1 : Fin 2)).val + 8 = 12
    exact congrArg (fun n : Nat => n + 8) (hpoints 1).2
  have he₀ : e (s 0) = 1 := by rw [hzero, map_one]
  have he₁ : e (s 1) = threeCosetsMiddle := by
    have h := hsucc 0
    change s 1 = Equiv.swap (l (0 : Fin 2)) (r (0 : Fin 2)) * s 0 at h
    rw [h, map_mul, he₀, mul_one]
    change threeCosetsShift.permCongrHom (Equiv.swap (l (0 : Fin 2)) (r (0 : Fin 2))) = _
    rw [threeCosets_congr_swap, hleft₀, hright₀]
  have he₂ : e (s 2) = threeCosetsLast := by
    have h := hsucc 1
    change s 2 = Equiv.swap (l (1 : Fin 2)) (r (1 : Fin 2)) * s 1 at h
    rw [h, map_mul, he₁]
    change threeCosetsShift.permCongrHom (Equiv.swap (l (1 : Fin 2)) (r (1 : Fin 2))) * _ = _
    rw [threeCosets_congr_swap, hleft₁, hright₁]
  have hrep (i : Fin 3) : e (s i) = threeCosetsRep i := by
    fin_cases i
    · exact he₀
    · exact he₁
    · exact he₂
  constructor
  · intro i j h
    apply hbij.1
    apply (threeCosets_congr_eq e T A hmem (s i) (s j)).mp
    rwa [hrep, hrep]
  · intro q
    obtain ⟨x, hx⟩ := e.surjective q.out
    obtain ⟨i, hi⟩ := hbij.2 (DoubleCoset.mk T T x)
    refine ⟨i, ?_⟩
    change DoubleCoset.mk A A (threeCosetsRep i) = q
    rw [← DoubleCoset.out_eq' q, ← hx, ← hrep]
    exact (threeCosets_congr_eq e T A hmem (s i) x).mpr hi
