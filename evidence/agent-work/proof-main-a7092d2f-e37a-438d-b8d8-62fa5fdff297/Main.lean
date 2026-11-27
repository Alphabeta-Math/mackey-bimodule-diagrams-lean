import MackeyDiagrams
import Proofs.StandardTwoBlockRepresentatives
import Proofs.ProductParabolicDoubleCosets

set_option maxHeartbeats 2000000

private abbrev threeCosetsRange {α : Type*} (p : α → Prop) [DecidablePred p] :
    Subgroup (Equiv.Perm α) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := p))

private theorem threeCosetsRange_mem {α : Type*} (p : α → Prop) [DecidablePred p]
    (f : Equiv.Perm α) : f ∈ threeCosetsRange p ↔ ∀ x, ¬p x → f x = x := by
  constructor
  · rintro ⟨g, rfl⟩ x hx
    exact Equiv.Perm.ofSubtype_apply_of_not_mem g hx
  · intro hf
    let g := Equiv.Perm.subtypeEquivSubtypePerm p
    exact ⟨g.symm ⟨f, hf⟩, congrArg Subtype.val (g.apply_symm_apply ⟨f, hf⟩)⟩

private abbrev threeCosetsHalf (X : Finset Nat) (m : Nat) (upper : Bool) :
    Subgroup (Equiv.Perm ↥X) :=
  threeCosetsRange (fun x : ↥X =>
    x ∈ Finset.filter (fun y : ↥X => if upper then m < y.val else y.val ≤ m) Finset.univ)

private abbrev threeCosetsSplit (X : Finset Nat) (m : Nat) : Subgroup (Equiv.Perm ↥X) :=
  threeCosetsHalf X m false ⊔ threeCosetsHalf X m true

private theorem threeCosetsHalf_mem (X : Finset Nat) (m : Nat) (f : Equiv.Perm ↥X) :
    (f ∈ threeCosetsHalf X m false ↔ ∀ x : ↥X, m < x.val → f x = x) ∧
    (f ∈ threeCosetsHalf X m true ↔ ∀ x : ↥X, x.val ≤ m → f x = x) := by
  constructor <;> rw [threeCosetsRange_mem] <;> simp [Finset.mem_filter]

private theorem threeCosetsSplit_mem (X : Finset Nat) (m : Nat) (f : Equiv.Perm ↥X) :
    f ∈ threeCosetsSplit X m ↔ ∀ x : ↥X, (f x).val ≤ m ↔ x.val ≤ m := by
  let p := fun x : ↥X => x.val ≤ m
  let S : Subgroup (Equiv.Perm ↥X) :=
    { carrier := { g | ∀ x, p (g x) ↔ p x }
      one_mem' := fun _ => Iff.rfl
      mul_mem' := fun hg hh x => (hg _).trans (hh x)
      inv_mem' := fun {g} hg x => by
        change p (g.symm x) ↔ p x
        rw [← hg (g.symm x), g.apply_symm_apply] }
  have low (x : ↥X) : (x ∈ Finset.filter p Finset.univ) ↔ p x := by simp
  have high (x : ↥X) : (x ∈ Finset.filter (fun y => m < y.val) Finset.univ) ↔ ¬p x := by
    simp [p]
  constructor
  · intro hf
    have hle : threeCosetsSplit X m ≤ S := by
      apply sup_le
      · rintro _ ⟨g, rfl⟩ x
        exact (low _).symm.trans ((Equiv.Perm.ofSubtype_apply_mem_iff_mem g x).trans (low _))
      · rintro _ ⟨g, rfl⟩ x
        apply not_iff_not.mp
        exact (high _).symm.trans ((Equiv.Perm.ofSubtype_apply_mem_iff_mem g x).trans (high _))
    exact hle hf
  · intro hf
    have hlo (x : ↥X) : (f x ∈ Finset.filter p Finset.univ) ↔ x ∈ Finset.filter p Finset.univ :=
      (low _).trans ((hf _).trans (low _).symm)
    have hhi (x : ↥X) : (f x ∈ Finset.filter (fun y => m < y.val) Finset.univ) ↔
        x ∈ Finset.filter (fun y => m < y.val) Finset.univ :=
      (high _).trans ((not_congr (hf _)).trans (high _).symm)
    let a := Equiv.Perm.ofSubtype (f.subtypePerm hlo)
    let b := Equiv.Perm.ofSubtype (f.subtypePerm hhi)
    have ha : a ∈ threeCosetsHalf X m false := ⟨_, rfl⟩
    have hb : b ∈ threeCosetsHalf X m true := ⟨_, rfl⟩
    have hab : a * b = f := by
      apply Equiv.ext
      intro x
      change a (b x) = f x
      by_cases hx : p x
      · rw [(threeCosetsHalf_mem X m b).2.mp hb x hx]
        exact Equiv.Perm.ofSubtype_subtypePerm_of_mem hlo ((low x).mpr hx)
      · have he : b x = f x :=
          Equiv.Perm.ofSubtype_subtypePerm_of_mem hhi ((high x).mpr hx)
        rw [he]
        exact (threeCosetsHalf_mem X m a).1.mp ha _ (Nat.lt_of_not_ge (hx ∘ (hf x).mp))
    rw [← hab]
    have ha' : threeCosetsHalf X m false ≤ threeCosetsSplit X m := le_sup_left
    have hb' : threeCosetsHalf X m true ≤ threeCosetsSplit X m := le_sup_right
    exact (threeCosetsSplit X m).mul_mem (ha' ha) (hb' hb)

private theorem threeCosets_conj_prod {U V : Type*} [Group U] [Group V]
    (A : Subgroup U) (B : Subgroup V) (u : V) :
    (A.prod B).map (MulAut.conj ((1 : U), u)).toMonoidHom =
      A.prod (B.map (MulAut.conj u).toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_prod, Subgroup.mem_prod, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

private theorem threeCosets_top_right {U : Type*} [Group U] (A : Subgroup U) :
    Subsingleton (DoubleCoset.Quotient (A : Set U) (↑(⊤ : Subgroup U))) := by
  constructor
  intro q r
  rw [← DoubleCoset.out_eq' q, ← DoubleCoset.out_eq' r]
  exact DoubleCoset.eq.mpr
    ⟨1, A.one_mem, q.out⁻¹ * r.out, Subgroup.mem_top _, by simp⟩

private theorem threeCosets_top_left {U : Type*} [Group U] (A : Subgroup U) :
    Subsingleton (DoubleCoset.Quotient (↑(⊤ : Subgroup U)) (A : Set U)) := by
  constructor
  intro q r
  rw [← DoubleCoset.out_eq' q, ← DoubleCoset.out_eq' r]
  exact DoubleCoset.eq.mpr
    ⟨r.out * q.out⁻¹, Subgroup.mem_top _, 1, A.one_mem, by simp⟩

-- The product formula's registered version uses subgroups of Perm Nat
-- and obtains a block splitting. Here G is already the split product, so
-- project a double-coset factorization, or assemble it with the full factors.
private theorem threeCosets_product {U V W I : Type*} [Group U] [Group V] [Group W]
    (A : Subgroup U) (B : Subgroup V) (C : Subgroup W) (s : I → W)
    (hs : Function.Bijective (fun i => DoubleCoset.mk C C (s i))) :
    Function.Bijective (fun i => DoubleCoset.mk
      (A.prod ((⊤ : Subgroup V).prod C)) ((⊤ : Subgroup U).prod (B.prod C))
      (1, 1, s i)) := by
  constructor
  · intro i j h
    obtain ⟨k, hk, l, hl, he⟩ := DoubleCoset.eq.mp h
    exact hs.1 (DoubleCoset.eq.mpr ⟨k.2.2, hk.2.2, l.2.2, hl.2.2,
      congrArg (fun x : U × V × W => x.2.2) he⟩)
  · intro q
    let x := q.out
    obtain ⟨i, hi⟩ := hs.2 (DoubleCoset.mk C C x.2.2)
    obtain ⟨k, hk, l, hl, he⟩ := DoubleCoset.eq.mp hi
    refine ⟨i, ?_⟩
    rw [← DoubleCoset.out_eq' q]
    exact DoubleCoset.eq.mpr
      ⟨(1, x.2.1, k), ⟨A.one_mem, Subgroup.mem_top _, hk⟩,
        (x.1, 1, l), ⟨Subgroup.mem_top _, B.one_mem, hl⟩, Prod.ext (by change x.1 = 1 * 1 * x.1; simp)
          (Prod.ext (by change x.2.1 = x.2.1 * 1 * 1; simp) he)⟩
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
private theorem threeCosets_points (x : ↥threeCosetsInterval) :
    x = threeCosetsPoint 9 ∨ x = threeCosetsPoint 10 ∨
      x = threeCosetsPoint 11 ∨ x = threeCosetsPoint 12 := by
  obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp x.property
  have h : x.val = 9 ∨ x.val = 10 ∨ x.val = 11 ∨ x.val = 12 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

private theorem threeCosets_middle_test (x : ↥threeCosetsInterval) :
    (threeCosetsMiddle x).val ≤ 10 ↔ x.val = 9 ∨ x.val = 11 := by
  rcases threeCosets_points x with rfl | rfl | rfl | rfl <;> decide

private theorem threeCosets_last_test (x : ↥threeCosetsInterval) :
    (threeCosetsLast x).val ≤ 10 ↔ ¬(x.val ≤ 10) := by
  rcases threeCosets_points x with rfl | rfl | rfl | rfl <;> decide

private theorem threeCosets_conj_split_mem (X : Finset Nat) (m : Nat)
    (s f : Equiv.Perm ↥X) :
    f ∈ (threeCosetsSplit X m).map (MulAut.conj s).toMonoidHom ↔
      ∀ x : ↥X, (s.symm (f x)).val ≤ m ↔ (s.symm x).val ≤ m := by
  rw [Subgroup.mem_map_equiv, threeCosetsSplit_mem]
  change (∀ x : ↥X, (s.symm (f (s x))).val ≤ m ↔ x.val ≤ m) ↔ _
  constructor
  · intro h x
    simpa only [s.apply_symm_apply] using h (s.symm x)
  · intro h x
    simpa only [s.symm_apply_apply] using h (s x)

-- The two membership tests specify the ordered intersection cells of
-- Proposition 7.3, steps 1–2. Here only their pointwise separation is needed:
-- each point of the third ambient block has a distinct pair of memberships.
private theorem threeCosets_middle_inf :
    threeCosetsSplit threeCosetsInterval 10 ⊓
      (threeCosetsSplit threeCosetsInterval 10).map (MulAut.conj threeCosetsMiddle).toMonoidHom =
        ⊥ := by
  ext f
  rw [Subgroup.mem_inf, threeCosetsSplit_mem, threeCosets_conj_split_mem, Subgroup.mem_bot]
  constructor
  · rintro ⟨hlo, hmid⟩
    apply Equiv.ext
    intro x
    change f x = x
    specialize hlo x
    have he := hmid x
    change (threeCosetsMiddle (f x)).val ≤ 10 ↔ (threeCosetsMiddle x).val ≤ 10 at he
    rw [threeCosets_middle_test, threeCosets_middle_test] at he
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp x.property
    obtain ⟨h₃, h₄⟩ := Finset.mem_Icc.mp (f x).property
    apply Subtype.ext
    omega
  · rintro rfl
    exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

private theorem threeCosets_conj_half_swap :
    (threeCosetsHalf threeCosetsInterval 10 false).map (MulAut.conj threeCosetsLast).toMonoidHom =
      threeCosetsHalf threeCosetsInterval 10 true ∧
    (threeCosetsHalf threeCosetsInterval 10 true).map (MulAut.conj threeCosetsLast).toMonoidHom =
      threeCosetsHalf threeCosetsInterval 10 false := by
  let s := threeCosetsLast
  have hp (x : ↥threeCosetsInterval) : 10 < (s x).val ↔ x.val ≤ 10 := by
    rw [← Nat.not_le, threeCosets_last_test, not_not]
  have hq (x : ↥threeCosetsInterval) : (s x).val ≤ 10 ↔ 10 < x.val :=
    (threeCosets_last_test x).trans Nat.not_le
  have hTransport (p q : ↥threeCosetsInterval → Prop) (h : ∀ x, q (s x) ↔ p x)
      (f : Equiv.Perm ↥threeCosetsInterval) :
      (∀ x, p x → (MulAut.conj s).symm f x = x) ↔ (∀ x, q x → f x = x) := by
    constructor
    · intro hf y hy
      obtain ⟨x, rfl⟩ := s.surjective y
      have he := hf x ((h x).mp hy)
      change s.symm (f (s x)) = x at he
      rwa [Equiv.symm_apply_eq] at he
    · intro hf x hx
      change s.symm (f (s x)) = x
      rw [hf (s x) ((h x).mpr hx), s.symm_apply_apply]
  constructor <;> ext f <;> rw [Subgroup.mem_map_equiv]
  · rw [(threeCosetsHalf_mem _ _ _).1, (threeCosetsHalf_mem _ _ f).2]
    exact hTransport _ _ hq f
  · rw [(threeCosetsHalf_mem _ _ _).2, (threeCosetsHalf_mem _ _ f).1]
    exact hTransport _ _ hp f

theorem ProductParabolicsWithThreeDoubleCosets : (let X₀ := Finset.Icc (1 : Nat) 4
let X₁ := Finset.Icc (5 : Nat) 8
let X₂ := Finset.Icc (9 : Nat) 12
let P₀ := Equiv.Perm ↥X₀
let P₁ := Equiv.Perm ↥X₁
let P₂ := Equiv.Perm ↥X₂
let G := P₀ × (P₁ × P₂)
let half := fun (X : Finset Nat) (m : Nat) (upper : Bool) =>
  let block := Finset.filter
    (fun x : ↥X => if upper then m < Subtype.val x else Subtype.val x ≤ m) Finset.univ
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ block))
let split := fun (X : Finset Nat) (m : Nat) => half X m false ⊔ half X m true
let A₀ := split X₀ 2
let A₁ := split X₁ 6
let A₂ := split X₂ 10
let K : Subgroup G := Subgroup.prod A₀ (Subgroup.prod ⊤ A₂)
let H : Subgroup G := Subgroup.prod ⊤ (Subgroup.prod A₁ A₂)
let σ₁ : P₂ := Equiv.swap
  ⟨10, Finset.mem_Icc.mpr ⟨by decide, by decide⟩⟩
  ⟨11, Finset.mem_Icc.mpr ⟨by decide, by decide⟩⟩
let σ₂ : P₂ := (Equiv.swap
  ⟨9, Finset.mem_Icc.mpr ⟨by decide, by decide⟩⟩
  ⟨12, Finset.mem_Icc.mpr ⟨by decide, by decide⟩⟩) * σ₁
let σ : Fin 3 → G := fun i => (1, 1, if i = 0 then 1 else if i = 1 then σ₁ else σ₂)
let conj := fun g : G => MulEquiv.toMonoidHom (MulAut.conj g)
let L := fun i : Fin 3 => K ⊓ Subgroup.map (conj (σ i)) H
let lastFactor := fun T : Subgroup P₂ =>
  (Subgroup.prod ⊥ (Subgroup.prod ⊥ T) : Subgroup G)
let F₀ := lastFactor (half X₂ 10 false)
let F₁ := lastFactor (half X₂ 10 true)
Subsingleton (DoubleCoset.Quotient (A₀ : Set P₀) (↑(⊤ : Subgroup P₀))) ∧
  Subsingleton (DoubleCoset.Quotient (↑(⊤ : Subgroup P₁)) (A₁ : Set P₁)) ∧
  Function.Bijective (fun i => DoubleCoset.mk K H (σ i)) ∧
  L 0 = Subgroup.prod A₀ (Subgroup.prod A₁ A₂) ∧
  L 1 = Subgroup.prod A₀ (Subgroup.prod A₁ ⊥) ∧
  L 2 = L 0 ∧
  Subgroup.map (conj (σ 2)) F₀ = F₁ ∧
  Subgroup.map (conj (σ 2)) F₁ = F₀) :=
(by
  intro X₀ X₁ X₂ P₀ P₁ P₂ G half split A₀ A₁ A₂ K H σ₁ σ₂ σ conj L lastFactor F₀ F₁
  -- Xiao, Example 7.7 (archived PDF p. 31, published 28 November revision
  -- p. 33). The first two factors are unrestricted on one side.
  -- The product calculation uses the split groups directly, as in §7.3.
  have hσ (i : Fin 3) : σ i = (1, 1, threeCosetsRep i) := rfl
  have hbij : Function.Bijective (fun i => DoubleCoset.mk K H (σ i)) := by
    change Function.Bijective (fun i => DoubleCoset.mk
      (A₀.prod ((⊤ : Subgroup P₁).prod A₂)) ((⊤ : Subgroup P₀).prod (A₁.prod A₂))
      (1, 1, threeCosetsRep i))
    exact threeCosets_product A₀ A₁ A₂ threeCosetsRep threeCosets_local
  have hL (i : Fin 3) :
      L i = A₀.prod (A₁.prod (A₂ ⊓ A₂.map (MulAut.conj (threeCosetsRep i)).toMonoidHom)) := by
    change K ⊓ H.map (MulAut.conj (σ i)).toMonoidHom = _
    rw [hσ]
    change (A₀.prod ((⊤ : Subgroup P₁).prod A₂)) ⊓
      ((⊤ : Subgroup P₀).prod (A₁.prod A₂)).map
        (MulAut.conj (1, (1, threeCosetsRep i))).toMonoidHom = _
    rw [threeCosets_conj_prod, threeCosets_conj_prod]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_top, true_and]
    tauto
  have hzero : L 0 = A₀.prod (A₁.prod A₂) := by
    rw [hL]
    change A₀.prod (A₁.prod (A₂ ⊓ A₂.map (MulAut.conj (1 : P₂)).toMonoidHom)) = _
    have h : (MulAut.conj (1 : P₂)).toMonoidHom = MonoidHom.id P₂ := by
      ext x
      simp
    simp only [h, Subgroup.map_id, inf_idem]
  have hmiddle : L 1 = A₀.prod (A₁.prod ⊥) := by
    rw [hL]
    change A₀.prod (A₁.prod (threeCosetsSplit threeCosetsInterval 10 ⊓
      (threeCosetsSplit threeCosetsInterval 10).map (MulAut.conj threeCosetsMiddle).toMonoidHom)) = _
    rw [threeCosets_middle_inf]
  have hlast : L 2 = L 0 := by
    rw [hL, hzero]
    have h : (threeCosetsSplit threeCosetsInterval 10).map (MulAut.conj threeCosetsLast).toMonoidHom =
        threeCosetsSplit threeCosetsInterval 10 := by
      change (threeCosetsHalf threeCosetsInterval 10 false ⊔ threeCosetsHalf threeCosetsInterval 10 true).map
        (MulAut.conj threeCosetsLast).toMonoidHom = _
      rw [Subgroup.map_sup, threeCosets_conj_half_swap.1, threeCosets_conj_half_swap.2]
      exact sup_comm _ _
    change A₀.prod (A₁.prod (A₂ ⊓ (threeCosetsSplit threeCosetsInterval 10).map
      (MulAut.conj threeCosetsLast).toMonoidHom)) = A₀.prod (A₁.prod A₂)
    rw [h]
    exact congrArg (fun T : Subgroup P₂ => A₀.prod (A₁.prod T)) (inf_idem (a := A₂))
  have hF (b : Bool) :
      (lastFactor (half X₂ 10 b)).map (conj (σ 2)) =
        lastFactor ((half X₂ 10 b).map (MulAut.conj threeCosetsLast).toMonoidHom) := by
    change ((⊥ : Subgroup P₀).prod ((⊥ : Subgroup P₁).prod (half X₂ 10 b))).map
      (MulAut.conj (1, (1, threeCosetsLast))).toMonoidHom = _
    rw [threeCosets_conj_prod, threeCosets_conj_prod]
  exact ⟨threeCosets_top_right A₀, threeCosets_top_left A₁, hbij, hzero, hmiddle, hlast,
    (hF false).trans (congrArg lastFactor threeCosets_conj_half_swap.1),
    (hF true).trans (congrArg lastFactor threeCosets_conj_half_swap.2)⟩)

#print axioms ProductParabolicsWithThreeDoubleCosets
