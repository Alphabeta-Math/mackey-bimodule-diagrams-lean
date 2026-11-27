import MackeyDiagrams
import Proofs.ReplacementForTwoProjections
import Proofs.ReplacementForTwoMultiplications
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks
import Proofs.CaseOneRightProjectionConstruction
import Proofs.CaseTwoLeftProjectionConstruction
namespace OutsideRegionsAux
open MackeyDiagrams

private abbrev conj {V : Type*} [Group V] (p : V) (H : Subgroup V) :=
  H.map (MulAut.conj p).toMonoidHom

private theorem mem_conj {V : Type*} [Group V] {p v : V} {H : Subgroup V} :
    v ∈ conj p H ↔ p⁻¹ * v * p ∈ H := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change p⁻¹ * (p * w * p⁻¹) * p ∈ H
    rw [show p⁻¹ * (p * w * p⁻¹) * p = w by group]
    exact hw
  · intro hv
    refine ⟨p⁻¹ * v * p, hv, ?_⟩
    change p * (p⁻¹ * v * p) * p⁻¹ = v
    group

private theorem conj_one {V : Type*} [Group V] (H : Subgroup V) : conj 1 H = H := by
  ext y
  simp only [mem_conj, inv_one, one_mul, mul_one]

private theorem conj_mul {V : Type*} [Group V] (p q : V) (H : Subgroup V) :
    conj p (conj q H) = conj (p * q) H := by
  ext v
  simp only [mem_conj, mul_inv_rev]
  rw [show q⁻¹ * (p⁻¹ * v * p) * q = q⁻¹ * p⁻¹ * v * (p * q) by group]

private theorem conj_eq_self {V : Type*} [Group V] {p : V} {H : Subgroup V} (hp : p ∈ H) :
    conj p H = H := by
  ext v
  rw [mem_conj]
  constructor
  · intro hv
    have h := H.mul_mem (H.mul_mem hp hv) (H.inv_mem hp)
    convert h using 1
    group
  · intro hv
    exact H.mul_mem (H.mul_mem (H.inv_mem hp) hv) hp

private theorem dot_ranges {U : Type*} [Group U] {J K : Subgroup U}
    {a b : ConjEmbedding J K} (x : Dot a b) :
    a.toHom.range = conj x.element b.toHom.range := by
  have eq (v : J) : a.toHom v = x.element * b.toHom v * x.element⁻¹ := by
    rw [← x.intertwines v, mul_inv_cancel_right]
  ext g
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨b.toHom v, ⟨v, rfl⟩, (eq v).symm⟩
  · rintro ⟨_, ⟨v, rfl⟩, hv⟩
    exact ⟨v, (eq v).trans hv⟩

private theorem range_comp_le {U : Type*} [Group U] {J K L : Subgroup U}
    (a : ConjEmbedding K L) (b : ConjEmbedding J K) :
    (a.comp b).toHom.range ≤ a.toHom.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨b.toHom x, rfl⟩

section
variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev leftBound (p : A) := a.toHom.range ⊓ conj p b.toHom.range
private abbrev rightBound (p : A) := (a.comp d).toHom.range ⊔ conj p (b.comp c).toHom.range

private abbrev leftParameter {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :=
  a.toHom z.element⁻¹ * x.element * b.toHom y.element

private abbrev rightParameter {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :=
  m.element * j.toHom n.element * ell.element⁻¹

private theorem left_bound_transport (q : A) (z : G) (y : D) :
    conj (a.toHom z) (leftBound a b q) = leftBound a b (a.toHom z * q * b.toHom y) := by
  have ha := conj_eq_self (show a.toHom z ∈ a.toHom.range from ⟨z, rfl⟩)
  have hb := conj_eq_self (show b.toHom y ∈ b.toHom.range from ⟨y, rfl⟩)
  unfold leftBound
  rw [show conj (a.toHom z) (a.toHom.range ⊓ conj q b.toHom.range) =
    conj (a.toHom z) a.toHom.range ⊓ conj (a.toHom z) (conj q b.toHom.range) from
    Subgroup.map_inf _ _ _ (MulAut.conj (a.toHom z)).injective, ha, conj_mul, ← conj_mul (a.toHom z * q) (b.toHom y), hb]

private theorem bound_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :
    conj (a.toHom z.element⁻¹) (a.comp r).toHom.range ≤
      leftBound a b (leftParameter a b c d e f x y z) := by
  rw [← left_bound_transport a b x.element z.element⁻¹ y.element]
  apply Subgroup.map_mono
  refine le_inf (range_comp_le a r) ?_
  rw [dot_ranges x]
  exact Subgroup.map_mono (range_comp_le b s)

private theorem bound_right {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :
    rightBound a b c d (rightParameter a b c d e f ell m n) ≤ conj m.element j.toHom.range := by
  apply sup_le
  · rw [dot_ranges m]
    exact Subgroup.map_mono (range_comp_le j v)
  · change conj (m.element * j.toHom n.element * ell.element⁻¹) (b.comp c).toHom.range ≤ _
    rw [dot_ranges ell, ← conj_mul, ← conj_mul,
      conj_mul ell.element⁻¹ ell.element, inv_mul_cancel, conj_one]
    refine (Subgroup.map_mono (range_comp_le j w)).trans ?_
    rw [conj_eq_self (show j.toHom n.element ∈ j.toHom.range from ⟨n.element, rfl⟩)]

private theorem first_injective {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e))
    (h : conj (a.toHom z.element⁻¹) (a.comp r).toHom.range =
      leftBound a b (leftParameter a b c d e f x y z)) :
    Function.Injective (Generator.mixedMultiplicationBasis a b r s x) := by
  rw [← left_bound_transport a b x.element z.element⁻¹ y.element] at h
  have image : (a.comp r).toHom.range = leftBound a b x.element :=
    Subgroup.map_injective (MulAut.conj (a.toHom z.element⁻¹)).injective h
  apply Generator.injective_mixedMultiplicationBasis
  intro k v hkv
  have hk : a.toHom k ∈ (a.comp r).toHom.range := by
    rw [image]
    exact ⟨⟨k, rfl⟩, ⟨b.toHom v, ⟨v, rfl⟩, hkv.symm⟩⟩
  obtain ⟨u, hu⟩ := hk
  exact ⟨u, a.injective hu⟩

private def inclusion {K : Subgroup U} (S : Subgroup K) : ConjEmbedding (S.map K.subtype) K :=
  ⟨Subgroup.inclusion (Subgroup.map_subtype_le S), ⟨1, fun _ => by simp⟩⟩

private theorem inclusion_mem {K : Subgroup U} (S : Subgroup K) (v : S.map K.subtype) :
    (inclusion S).toHom v ∈ S := by
  obtain ⟨x, hx, he⟩ := v.property
  exact (Subtype.ext he : x = (inclusion S).toHom v) ▸ hx

private theorem inclusion_range {K : Subgroup U} (S : Subgroup K) :
    (inclusion S).toHom.range = S := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact inclusion_mem S v
  · intro v hv
    exact ⟨⟨(v : U), ⟨v, hv, rfl⟩⟩, rfl⟩

private def restrictTo {K L : Subgroup U} (a : ConjEmbedding K L) (S : Subgroup L)
    (h : a.toHom.range ≤ S) : ConjEmbedding K (S.map L.subtype) :=
  ⟨(L.subtype.comp a.toHom).codRestrict _ (fun x => ⟨a.toHom x, h ⟨x, rfl⟩, rfl⟩),
    a.hasRepresentative⟩

private def conjugated {K L : Subgroup U} (a : ConjEmbedding K L) (p : L) :
    ConjEmbedding K L :=
  ⟨(MulAut.conj p).toMonoidHom.comp a.toHom, by
    obtain ⟨s, hs⟩ := a.hasRepresentative
    refine ⟨(p : U) * s, fun x => ?_⟩
    change (p : U) * (a.toHom x : U) * (p : U)⁻¹ = _
    rw [hs]
    group⟩

private theorem conjugated_range {K L : Subgroup U} (a : ConjEmbedding K L) (p : L) :
    (conjugated a p).toHom.range = conj p a.toHom.range :=
  (MonoidHom.map_range _ _).symm

-- The inverse is conjugation by the inverse representative on the range.
private theorem lift_through {K L J : Subgroup U}
    (a : ConjEmbedding K L) (j : ConjEmbedding J L) (h : j.toHom.range ≤ a.toHom.range) :
    ∃ r : ConjEmbedding J K, a.comp r = j := by
  obtain ⟨q, hq⟩ := a.hasRepresentative
  have candidate (x : J) : ∃ y : K, a.toHom y = j.toHom x ∧
      (y : U) = q⁻¹ * (j.toHom x : U) * q := by
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    refine ⟨y, hy, ?_⟩
    have he : q * (y : U) * q⁻¹ = (j.toHom x : U) := by rw [← hq, hy]
    rw [← he]
    group
  let r : ConjEmbedding J K := ⟨
    ((MulAut.conj q⁻¹).toMonoidHom.comp (L.subtype.comp j.toHom)).codRestrict K (by
      intro x
      obtain ⟨y, _, hy⟩ := candidate x
      change q⁻¹ * (j.toHom x : U) * (q⁻¹)⁻¹ ∈ K
      rw [inv_inv, ← hy]
      exact y.property), by
    obtain ⟨w, hw⟩ := j.hasRepresentative
    refine ⟨q⁻¹ * w, fun x => ?_⟩
    change q⁻¹ * (j.toHom x : U) * (q⁻¹)⁻¹ = _
    rw [hw]
    group⟩
  refine ⟨r, ConjEmbedding.ext (MonoidHom.ext fun x => ?_)⟩
  obtain ⟨y, hy, hxy⟩ := candidate x
  have hr : r.toHom x = y := Subtype.ext (by
    change q⁻¹ * (j.toHom x : U) * (q⁻¹)⁻¹ = (y : U)
    rw [inv_inv, hxy])
  change a.toHom (r.toHom x) = j.toHom x
  rw [hr, hy]

end
end OutsideRegionsAux
namespace OutsideRegionsAux

private abbrev Perm := Equiv.Perm Nat
private abbrev Finitary := Subgroup.closure {σ : Perm | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) : Subgroup Perm :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X))

private abbrev ParabolicPerm (H : Subgroup Perm) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H = ⨆ i, blockSym (blocks i)

private abbrev Parabolic (H : Subgroup Finitary) := ParabolicPerm (H.map Finitary.subtype)

private theorem of_family {ι : Type} [Finite ι] (blocks : ι → Finset Nat)
    (hne : ∀ i, (blocks i).Nonempty)
    (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) :
    ParabolicPerm (⨆ i, blockSym (blocks i)) := by
  letI : Fintype ι := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  exact ⟨_, blocks ∘ e, fun i => hne (e i),
    fun i j hij => hd (fun h => hij (e.injective h)),
    (e.iSup_comp (g := fun i => blockSym (blocks i))).symm⟩

private theorem same_block {ι : Type} {X : ι → Finset Nat}
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) {i j : ι} {x : Nat}
    (hi : x ∈ X i) (hj : x ∈ X j) : i = j := by
  by_contra h
  exact Finset.disjoint_left.mp (hd h) hi hj

private theorem block_trivial (S : Finset Nat) (h : ∀ x y, x ∈ S → y ∈ S → x = y) :
    blockSym S = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨σ, rfl⟩
  apply Subgroup.mem_bot.mpr
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ S
  · rw [Equiv.Perm.ofSubtype_apply_of_mem σ hx]
    exact h _ _ (σ ⟨x, hx⟩).property hx
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem σ hx

private def padded {ι : Type} (X : Finset Nat) (S : ι → Finset Nat) (Y : Finset Nat) :
    ι ⊕ ↥(X \ Y) → Finset Nat := Sum.elim S (fun x => {x.val})

private theorem pad_blocks {ι : Type} [Fintype ι] (X : Finset Nat) (S : ι → Finset Nat)
    (hS : ∀ i, S i ⊆ X) (hne : ∀ i, (S i).Nonempty)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    let Y := Finset.univ.biUnion S
    let T := padded X S Y
    (∀ i, (T i).Nonempty) ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
    (∀ x, x ∈ X ↔ ∃ i, x ∈ T i) ∧ (⨆ i, blockSym (S i)) = ⨆ i, blockSym (T i) := by
  classical
  intro Y T
  have hY (x : Nat) : x ∈ Y ↔ ∃ i, x ∈ S i := by simp [Y]
  constructor
  · rintro (i | x)
    · exact hne i
    · exact Finset.singleton_nonempty _
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases i with (i | i) <;> rcases j with (j | j)
    · exact hij (congrArg Sum.inl (same_block hd hx hy))
    · have h : x = j.val := Finset.mem_singleton.mp hy
      exact (Finset.mem_sdiff.mp j.property).2 (h ▸ (hY x).mpr ⟨i, hx⟩)
    · have h : x = i.val := Finset.mem_singleton.mp hx
      exact (Finset.mem_sdiff.mp i.property).2 (h ▸ (hY x).mpr ⟨j, hy⟩)
    · exact hij (congrArg Sum.inr (Subtype.ext
        ((Finset.mem_singleton.mp hx).symm.trans (Finset.mem_singleton.mp hy))))
  constructor
  · intro x
    constructor
    · intro hx
      by_cases hy : x ∈ Y
      · obtain ⟨i, hi⟩ := (hY x).mp hy
        exact ⟨Sum.inl i, hi⟩
      · exact ⟨Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hy⟩⟩, Finset.mem_singleton_self x⟩
    · rintro ⟨i | j, hx⟩
      · exact hS i hx
      · rw [Finset.mem_singleton.mp hx]
        exact (Finset.mem_sdiff.mp j.property).1
  apply le_antisymm
  · exact iSup_le fun i => le_iSup (fun k => blockSym (T k)) (Sum.inl i)
  · apply iSup_le
    rintro (i | j)
    · exact le_iSup (fun k => blockSym (S k)) i
    · change blockSym {j.val} ≤ _
      rw [block_trivial _ (fun x y hx hy =>
        (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm)]
      exact bot_le

private theorem parabolic_conj_perm {H : Subgroup Perm} (hH : ParabolicPerm H) (σ : Perm) :
    ParabolicPerm (conj σ H) := by
  classical
  obtain ⟨n, X, hne, hd, rfl⟩ := hH
  have image_block (S : Finset Nat) : conj σ (blockSym S) = blockSym (S.image σ) := by
    let Y := S.image σ
    have mem_image (x : Nat) : x ∈ S ↔ σ x ∈ Y := by simp [Y]
    let e : S ≃ Y := σ.subtypeEquiv mem_image
    have commute (f : Equiv.Perm S) :
        MulAut.conj σ (Equiv.Perm.ofSubtype f) = Equiv.Perm.ofSubtype (e.permCongr f) := by
      apply Equiv.ext
      intro x
      obtain ⟨y, rfl⟩ := σ.surjective x
      change σ (Equiv.Perm.ofSubtype f (σ.symm (σ y))) = Equiv.Perm.ofSubtype (e.permCongr f) (σ y)
      rw [σ.symm_apply_apply]
      by_cases hy : y ∈ S
      · rw [Equiv.Perm.ofSubtype_apply_of_mem f hy,
          Equiv.Perm.ofSubtype_apply_of_mem _ ((mem_image y).mp hy)]
        change (e (f ⟨y, hy⟩) : Nat) = (e.permCongr f (e ⟨y, hy⟩) : Nat)
        simp
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem f hy, Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun h =>
          hy ((mem_image y).mpr h))]
    ext τ
    constructor
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨e.permCongr f, (commute f).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨f, rfl⟩ := e.permCongr.surjective g
      exact ⟨Equiv.Perm.ofSubtype f, ⟨f, rfl⟩, commute f⟩
  change ParabolicPerm (Subgroup.map _ (⨆ i, blockSym (X i)))
  rw [Subgroup.map_iSup]
  simp only [show ∀ S, (blockSym S).map (MulAut.conj σ).toMonoidHom = blockSym (S.image σ) from image_block]
  refine ⟨n, fun i => (X i).image σ, fun i => (hne i).image _, ?_, rfl⟩
  intro i j hij
  exact Finset.disjoint_image_of_injective σ.injective (hd hij)

private theorem parabolic_inf_on {ι κ : Type} [Finite ι] [Finite κ] (X : Finset Nat)
    (A : ι → Finset Nat) (B : κ → Finset Nat)
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ j, (B j).Nonempty)
    (dA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (dB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (coverA : ∀ x, x ∈ X ↔ ∃ i, x ∈ A i)
    (coverB : ∀ x, x ∈ X ↔ ∃ j, x ∈ B j) :
    ParabolicPerm ((⨆ i, blockSym (A i)) ⊓ (⨆ j, blockSym (B j))) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  let Cell := {ij : ι × κ // (A ij.1 ∩ B ij.2).Nonempty}
  let cell (ij : Cell) := A ij.val.1 ∩ B ij.val.2
  rw [FiniteParabolicIntersectionBlocks X A B hA hB dA dB coverA coverB]
  have omitEmpty : (⨆ i, ⨆ j, blockSym (A i ∩ B j)) = ⨆ ij, blockSym (cell ij) := by
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun j => ?_
      by_cases h : (A i ∩ B j).Nonempty
      · exact le_iSup (fun ij => blockSym (cell ij)) (⟨(i, j), h⟩ : Cell)
      · rw [block_trivial _ (fun x _ hx _ => (h ⟨x, hx⟩).elim)]
        exact bot_le
    · refine iSup_le fun ij => ?_
      exact (le_iSup (fun j => blockSym (A ij.val.1 ∩ B j)) ij.val.2).trans
        (le_iSup (fun i => ⨆ j, blockSym (A i ∩ B j)) ij.val.1)
  change ParabolicPerm (⨆ i, ⨆ j, blockSym (A i ∩ B j))
  rw [omitEmpty]
  refine of_family cell (fun ij => ij.property) ?_
  intro ij kl h
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
  obtain ⟨hk, hl⟩ := Finset.mem_inter.mp hy
  exact h (Subtype.ext (Prod.ext (same_block dA hi hk) (same_block dB hj hl)))

private theorem parabolic_sup_on {ι κ : Type} [Finite ι] [Finite κ] (X : Finset Nat) (A : ι → Finset Nat)
    (B : κ → Finset Nat) (hA : ∀ i, (A i).Nonempty) (hB : ∀ j, (B j).Nonempty)
    (dA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (dB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (coverA : ∀ x, x ∈ X ↔ ∃ i, x ∈ A i)
    (coverB : ∀ x, x ∈ X ↔ ∃ j, x ∈ B j) :
    ParabolicPerm ((⨆ i, blockSym (A i)) ⊔ (⨆ j, blockSym (B j))) := by
  classical
  let block : ι ⊕ κ → Finset Nat := Sum.elim A B
  let overlap : (ι ⊕ κ) → (ι ⊕ κ) → Prop := fun u v =>
    match u, v with
    | Sum.inl i, Sum.inr j => (A i ∩ B j).Nonempty
    | _, _ => False
  let graph := SimpleGraph.fromRel overlap
  let componentBlock : graph.ConnectedComponent → Finset Nat := fun c =>
    let inComponent : Nat → Prop := fun x =>
      ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v
    @Finset.filter Nat inComponent (Classical.decPred inComponent) X
  have memComponent (c : graph.ConnectedComponent) (x : Nat) :
      x ∈ componentBlock c ↔ x ∈ X ∧
        ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v :=
    @Finset.mem_filter Nat _ (Classical.decPred _) _ _
  have blockNonempty (v : ι ⊕ κ) : (block v).Nonempty := by
    cases v with
    | inl i => exact hA i
    | inr j => exact hB j
  have blockSubset (v : ι ⊕ κ) : block v ⊆ X := by
    intro x hx
    cases v with
    | inl i => exact (coverA x).mpr ⟨i, hx⟩
    | inr j => exact (coverB x).mpr ⟨j, hx⟩
  have overlap_component {u v : ι ⊕ κ} {x : Nat}
      (hu : x ∈ block u) (hv : x ∈ block v) :
      graph.connectedComponentMk u = graph.connectedComponentMk v := by
    cases u with
    | inl i =>
      cases v with
      | inl j => rw [same_block dA hu hv]
      | inr j =>
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        apply (SimpleGraph.fromRel_adj overlap _ _).mpr
        exact ⟨Sum.inl_ne_inr, Or.inl ⟨x, Finset.mem_inter.mpr ⟨hu, hv⟩⟩⟩
    | inr j =>
      cases v with
      | inl i =>
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        apply (SimpleGraph.fromRel_adj overlap _ _).mpr
        exact ⟨Sum.inr_ne_inl, Or.inr ⟨x, Finset.mem_inter.mpr ⟨hv, hu⟩⟩⟩
      | inr k => rw [same_block dB hu hv]
  have joinFormula :
      ((⨆ i, blockSym (A i)) ⊔ (⨆ j, blockSym (B j))) =
        ⨆ c, blockSym (componentBlock c) :=
    FiniteParabolicJoinBlocks X A B hA hB dA dB coverA coverB
  rw [joinFormula]
  let _ : Finite (ι ⊕ κ) := by
    let _ : Fintype ι := Fintype.ofFinite ι
    let _ : Fintype κ := Fintype.ofFinite κ
    exact Finite.of_fintype _
  refine of_family componentBlock ?_ ?_
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      obtain ⟨x, hx⟩ := blockNonempty v
      exact ⟨x, (memComponent _ x).mpr ⟨blockSubset v hx, v, rfl, hx⟩⟩
  · intro c d h
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨_, u, huc, hu⟩ := (memComponent c x).mp hx
    obtain ⟨_, v, hvd, hv⟩ := (memComponent d x).mp hy
    exact h (huc.symm.trans ((overlap_component hu hv).trans hvd))

private theorem parabolic_lattice {H K : Subgroup Perm}
    (hH : ParabolicPerm H) (hK : ParabolicPerm K) :
    ParabolicPerm (H ⊓ K) ∧ ParabolicPerm (H ⊔ K) := by
  classical
  obtain ⟨n, A, hA, dA, rfl⟩ := hH
  obtain ⟨m, B, hB, dB, rfl⟩ := hK
  let X := Finset.univ.biUnion A ∪ Finset.univ.biUnion B
  obtain ⟨hA', dA', cA, eqA⟩ := pad_blocks X A
    (fun i x hx => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hA dA
  obtain ⟨hB', dB', cB, eqB⟩ := pad_blocks X B
    (fun i x hx => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hB dB
  rw [eqA, eqB]
  exact ⟨parabolic_inf_on X _ _ hA' hB' dA' dB' cA cB,
    parabolic_sup_on X _ _ hA' hB' dA' dB' cA cB⟩

private theorem parabolic_finite {H : Subgroup Finitary} (hH : Parabolic H) : Finite H := by
  classical
  obtain ⟨n, blocks, _, _, hblocks⟩ := hH
  let X := Finset.univ.biUnion blocks
  have hsub : H.map Finitary.subtype ≤ blockSym X := by
    rw [hblocks]
    refine iSup_le fun i σ hs => ?_
    obtain ⟨τ, rfl⟩ := hs
    let σ : Perm := Equiv.Perm.ofSubtype τ
    have moved_mem (x : Nat) (hx : σ x ≠ x) : x ∈ X := by
      by_contra hn
      have hi : x ∉ blocks i := fun hx' => hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx'⟩)
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem τ hi)
    have preserves (x : Nat) : σ x ∈ X ↔ x ∈ X := by
      by_cases h : σ x = x
      · rw [h]
      · have hy : σ (σ x) ≠ σ x := fun hh => h (σ.injective hh)
        exact iff_of_true (moved_mem (σ x) hy) (moved_mem x h)
    exact ⟨σ.subtypePerm preserves, Equiv.Perm.ofSubtype_subtypePerm preserves moved_mem⟩
  letI : Finite (blockSym X) :=
    (Set.finite_range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))).to_subtype
  exact Finite.of_injective
    (fun h : H => (⟨(h.val : Perm), hsub ⟨h.val, h.property, rfl⟩⟩ : blockSym X))
    (fun _ _ hh => Subtype.ext (Subtype.ext (congrArg (fun y : blockSym X => y.val) hh)))

open MackeyDiagrams

private theorem parabolic_embedding {H K : Subgroup Finitary}
    (i : ConjEmbedding H K) (hH : Parabolic H) : Parabolic (i.toHom.range.map K.subtype) := by
  obtain ⟨q, hq⟩ := i.hasRepresentative
  have hr : (i.toHom.range.map K.subtype).map Finitary.subtype =
      conj (q : Perm) (H.map Finitary.subtype) := by
    ext x
    constructor
    · rintro ⟨_, ⟨_, ⟨y, rfl⟩, rfl⟩, rfl⟩
      exact ⟨y.val, ⟨y.val, y.property, rfl⟩, congrArg Finitary.subtype (hq y).symm⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      let x : H := ⟨y, hy⟩
      exact ⟨(i.toHom x : Finitary), ⟨i.toHom x, ⟨x, rfl⟩, rfl⟩, congrArg Finitary.subtype (hq x)⟩
  show ParabolicPerm _
  rw [hr]
  exact parabolic_conj_perm hH q

private theorem parabolic_conj_image {A : Subgroup Finitary} {H : Subgroup A}
    (hH : Parabolic (H.map A.subtype)) (p : A) : Parabolic ((conj p H).map A.subtype) := by
  let i := conjugated (inclusion H) p
  have hi : i.toHom.range = conj p H := by
    rw [conjugated_range, inclusion_range]
  rw [← hi]
  exact parabolic_embedding i hH

private theorem parabolic_region_bounds {G A D F C E : Subgroup Finitary}
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (p : A) (hG : Parabolic G) (hD : Parabolic D)
    (hF : Parabolic F) (hC : Parabolic C) :
    Parabolic ((rightBound a b c d p).map A.subtype) ∧
      Parabolic ((leftBound a b p).map A.subtype) := by
  let incl := Finitary.subtype.comp A.subtype
  have hjoin := (parabolic_lattice (parabolic_embedding (a.comp d) hC)
      (parabolic_conj_image (parabolic_embedding (b.comp c) hF) p)).2
  have hmeet := (parabolic_lattice (parabolic_embedding a hG)
      (parabolic_conj_image (parabolic_embedding b hD) p)).1
  constructor
  · show ParabolicPerm (((rightBound a b c d p).map A.subtype).map Finitary.subtype)
    rw [Subgroup.map_map, rightBound, Subgroup.map_sup, ← Subgroup.map_map, ← Subgroup.map_map]
    exact hjoin
  · show ParabolicPerm (((leftBound a b p).map A.subtype).map Finitary.subtype)
    rw [Subgroup.map_map, leftBound, Subgroup.map_inf _ _ _ incl.injective, ← Subgroup.map_map, ← Subgroup.map_map]
    exact hmeet

end OutsideRegionsAux
