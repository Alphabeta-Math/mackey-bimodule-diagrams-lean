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

-- ProductParabolicDoubleCosets starts with subgroups of Perm Nat and
-- obtains a block splitting. Here G is already the split product, so
-- DoubleCoset.eq gives the coordinate factorization directly. The full
-- factors supply the first two coordinates when assembling the witnesses.
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
