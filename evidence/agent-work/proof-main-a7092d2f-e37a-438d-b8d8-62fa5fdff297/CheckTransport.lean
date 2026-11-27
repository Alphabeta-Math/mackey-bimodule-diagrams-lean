import MackeyDiagrams
import Proofs.StandardTwoBlockRepresentatives
import Proofs.ProductParabolicDoubleCosets
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
  let T : Subgroup (Equiv.Perm ↥X) := ⨆ i : Fin 2, threeCosetsRange
    (fun x : ↥X => x ∈ (if i = 0 then
        Finset.filter (fun y : ↥X => 1 ≤ y.val ∧ y.val ≤ 2) Finset.univ
      else Finset.filter (fun y : ↥X => 3 ≤ y.val ∧ y.val ≤ 4) Finset.univ))
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
      rfl
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      fin_cases i
      · change _ ≤ threeCosetsSplit X 2
        exact hlo.trans_le le_sup_left
      · change _ ≤ threeCosetsSplit X 2
        exact hhi.trans_le le_sup_right
    · apply sup_le
      · exact hlo.symm.trans_le (le_iSup _ (0 : Fin 2))
      · exact hhi.symm.trans_le (le_iSup _ (1 : Fin 2))
  -- In the Alphabeta Math proof plan for §7.2, steps 1–2 match ordered
  -- pieces of the two partitions. The registered §7.3 theorem already
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
  have hleft₀ : threeCosetsShift (l 0) = threeCosetsPoint 10 := by
    apply Subtype.ext
    change (l 0).val + 8 = 10
    rw [(hpoints 0).1]
    rfl
  have hright₀ : threeCosetsShift (r 0) = threeCosetsPoint 11 := by
    apply Subtype.ext
    change (r 0).val + 8 = 11
    rw [(hpoints 0).2]
    rfl
  have hleft₁ : threeCosetsShift (l 1) = threeCosetsPoint 9 := by
    apply Subtype.ext
    change (l 1).val + 8 = 9
    rw [(hpoints 1).1]
    rfl
  have hright₁ : threeCosetsShift (r 1) = threeCosetsPoint 12 := by
    apply Subtype.ext
    change (r 1).val + 8 = 12
    rw [(hpoints 1).2]
    rfl
  have he₀ : e (s 0) = 1 := by rw [hzero, map_one]
  have he₁ : e (s 1) = threeCosetsMiddle := by
    have h := hsucc 0
    change s 1 = Equiv.swap (l 0) (r 0) * s 0 at h
    rw [h, map_mul, he₀, mul_one]
    change threeCosetsShift.permCongrHom (Equiv.swap (l 0) (r 0)) = _
    rw [threeCosets_congr_swap, hleft₀, hright₀]
  have he₂ : e (s 2) = threeCosetsLast := by
    have h := hsucc 1
    change s 2 = Equiv.swap (l 1) (r 1) * s 1 at h
    rw [h, map_mul, he₁]
    change threeCosetsShift.permCongrHom (Equiv.swap (l 1) (r 1)) * _ = _
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
    rw [← DoubleCoset.out_eq' q, ← hx, ← hrep]
    exact (threeCosets_congr_eq e T A hmem (s i) x).mpr hi
