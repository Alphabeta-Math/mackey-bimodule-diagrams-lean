import MackeyDiagrams
import Proofs.ReplacementForTwoProjections
import Proofs.ReplacementForTwoMultiplications
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks
import Proofs.CaseOneRightProjectionConstruction
import Proofs.CaseTwoLeftProjectionConstruction

set_option maxHeartbeats 2000000

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
    refine (Subgroup.map_mono (f := (MulAut.conj m.element).toMonoidHom)
      (Subgroup.map_mono (f := (MulAut.conj (j.toHom n.element)).toMonoidHom)
        (range_comp_le j w))).trans ?_
    change conj m.element (conj (j.toHom n.element) j.toHom.range) ≤ _
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
  let _ : Fintype ι := Fintype.ofFinite ι
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
  apply Finset.disjoint_left.mpr
  intro x hi hj
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hi
  obtain ⟨z, hz, hxz⟩ := Finset.mem_image.mp hj
  exact Finset.disjoint_left.mp (hd hij) hy (σ.injective (hxz.trans hxy.symm) ▸ hz)

private theorem parabolic_inf_on {ι κ : Type} [Finite ι] [Finite κ] (X : Finset Nat)
    (A : ι → Finset Nat) (B : κ → Finset Nat)
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ j, (B j).Nonempty)
    (dA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (dB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (coverA : ∀ x, x ∈ X ↔ ∃ i, x ∈ A i)
    (coverB : ∀ x, x ∈ X ↔ ∃ j, x ∈ B j) :
    ParabolicPerm ((⨆ i, blockSym (A i)) ⊓ (⨆ j, blockSym (B j))) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
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
  let _ : Finite (blockSym X) :=
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

private theorem parabolic_region_bounds {G A D F C : Subgroup Finitary}
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (p : A) (hG : Parabolic G) (hD : Parabolic D)
    (hF : Parabolic F) (hC : Parabolic C) :
    Parabolic ((rightBound a b c d p).map A.subtype) ∧
      Parabolic ((leftBound a b p).map A.subtype) := by
  have hincl : Function.Injective (Finitary.subtype.comp A.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hjoin := (parabolic_lattice (parabolic_embedding (a.comp d) hC)
      (parabolic_conj_image (parabolic_embedding (b.comp c) hF) p)).2
  have hmeet := (parabolic_lattice (parabolic_embedding a hG)
      (parabolic_conj_image (parabolic_embedding b hD) p)).1
  constructor
  · show ParabolicPerm (((rightBound a b c d p).map A.subtype).map Finitary.subtype)
    rw [Subgroup.map_map, rightBound, Subgroup.map_sup, ← Subgroup.map_map, ← Subgroup.map_map]
    exact hjoin
  · show ParabolicPerm (((leftBound a b p).map A.subtype).map Finitary.subtype)
    rw [Subgroup.map_map, leftBound, Subgroup.map_inf _ _ _ hincl, ← Subgroup.map_map, ← Subgroup.map_map]
    exact hmeet

end OutsideRegionsAux
namespace OutsideRegionsAux
open MackeyDiagrams

-- The registered Lemma 6.3 proves existence and uniqueness of the merged
-- projection parameter. Its internal coefficient computation also identifies
-- that parameter. Keep the coefficient calculation local so the bounds can
-- use the actual product of the three marked labels.
universe u
noncomputable section
set_option maxHeartbeats 1500000

private abbrev Vec (X : Type*) := X →₀ Complex

-- A contravariant basis map acts by precomposition on coefficients.
private def Pulls {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X) : Prop :=
  ∀ v, L v y = v x

private theorem pulls_single {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X)
    (h : ∀ i : X, L (Finsupp.single i 1) y = Finsupp.single i (1 : Complex) x) :
    Pulls L y x := by
  let l := (Finsupp.lapply y : Vec Y →ₗ[Complex] Complex).comp L
  have he : l = (Finsupp.lapply x : Vec X →ₗ[Complex] Complex) := by
    apply Finsupp.lhom_ext
    intro i w
    have hs : Finsupp.single i w = w • Finsupp.single i (1 : Complex) := by
      simp [Finsupp.smul_single]
    rw [hs, map_smul, map_smul]
    exact congrArg (w • ·) (h i)
  exact fun v => LinearMap.congr_fun he v

private theorem pulls_of_single {X Y : Type*} {L : Vec X →ₗ[Complex] Vec Y}
    {forward : X → Y} {x : X} {y : Y} (inv : ∀ i, forward i = y ↔ i = x)
    (h : ∀ i : X, L (Finsupp.single i 1) = Finsupp.single (forward i) 1) :
    Pulls L y x := by
  classical
  apply pulls_single
  intro i
  rw [h i]
  simp only [Finsupp.single_apply, inv]

private theorem pulls_mixed {U : Type u} [Group U] {K H P L : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (d : ConjEmbedding L K) (e : ConjEmbedding L H)
    (p : ProjectionDot.Mixed a b d e)
    (y : ((Word.up d).tensor (.down e)).basis.carrier) :
    Pulls (Diagram.mixedProjection (R := Complex) a b d e p.dot p.finite).eval.toLinearMap
      y (Generator.mixedMultiplicationBasis a b d e p.dot y) := by
  classical
  apply pulls_single
  intro i
  change (Biset.Hom.transfer Complex (Generator.mixedMultiplicationBasis a b d e p.dot)
    (Generator.mixedMultiplication_equivariant a b d e p.dot) p.finite).toLinearMap
      (Finsupp.single i 1) y = _
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_apply, Finsupp.single_apply]
  by_cases h : i = Generator.mixedMultiplicationBasis a b d e p.dot y
  · simp [h]
  · simp [h, Ne.symm h]

section Balanced
variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {X X' : Biset K H} {Y Y' : Biset H J}

-- The unchanged strand makes the balancing parameter unique at a fixed output
-- representative. Thus no orbit multiplicity is introduced by tensoring a pullback.
private theorem pulls_horizontal_right (L : Biset.Hom Complex X X')
    (free : ∀ (s : Y.carrier) (h : H), Y.act (h, 1) s = s → h = 1)
    {x' : X'.carrier} {x : X.carrier} (hx : Pulls L.toLinearMap x' x) (s : Y.carrier) :
    Pulls (L.horizontal (Biset.Hom.id Y)).toLinearMap (X'.pair Y x' s) (X.pair Y x s) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨i,t⟩ => ?_)
  change (L.horizontal (Biset.Hom.id Y)).toLinearMap (Finsupp.single (X.pair Y i t) 1)
    (X'.pair Y x' s) = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
    (Finsupp.single t 1) (X'.pair Y x' s) = Finsupp.single (X.pair Y i t) 1 (X.pair Y x s)
  by_cases ht : ∃ h : H, Y.act (h, 1) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y i t = X.pair Y (X.act (1,h) i) s := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single s 1) (X'.pair Y x' s) = v x' := by
      apply pulls_single ((Biset.pairLinear Complex X' Y).flip (Finsupp.single s 1))
      intro j
      change Biset.pairLinear Complex X' Y (Finsupp.single j 1) (Finsupp.single s 1)
        (X'.pair Y x' s) = _
      rw [Biset.pairLinear_single, mul_one]
      have hi : X'.pair Y j s = X'.pair Y x' s ↔ j = x' := by
        constructor
        · intro hp
          obtain ⟨k, hk, hs⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (X'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    -- Rechoose the input representative before using the horizontal basis formula.
    have hre := congrArg (fun w => (L.horizontal (Biset.Hom.id Y)).toLinearMap
      (Finsupp.single w 1) (X'.pair Y x' s)) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
      (Finsupp.single t 1) (X'.pair Y x' s) =
      Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single (X.act (1,h) i) 1))
      (Finsupp.single s 1) (X'.pair Y x' s) at hre
    rw [hre, heval, hx _ , he]
    have hi : X.pair Y (X.act (1,h) i) s = X.pair Y x s ↔ X.act (1,h) i = x := by
      constructor
      · intro hp
        obtain ⟨k, hk, hs⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (X.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single t 1) (X'.pair Y x' s) = 0 := by
      have he : (Finsupp.lapply (X'.pair Y x' s) : Vec (X'.tensor Y).carrier →ₗ[Complex] Complex).comp
          ((Biset.pairLinear Complex X' Y).flip (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X' Y (Finsupp.single j r) (Finsupp.single t 1)
          (X'.pair Y x' s) = 0
        rw [Biset.pairLinear_single, mul_one, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, _, hk⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, _, hk⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

private theorem pulls_horizontal_left (L : Biset.Hom Complex Y Y')
    (free : ∀ (s : X.carrier) (h : H), X.act (1, h) s = s → h = 1)
    {y' : Y'.carrier} {y : Y.carrier} (hy : Pulls L.toLinearMap y' y) (s : X.carrier) :
    Pulls ((Biset.Hom.id X).horizontal L).toLinearMap (X.pair Y' s y') (X.pair Y s y) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨t,i⟩ => ?_)
  change ((Biset.Hom.id X).horizontal L).toLinearMap (Finsupp.single (X.pair Y t i) 1)
    (X.pair Y' s y') = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
    (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') = Finsupp.single (X.pair Y t i) 1 (X.pair Y s y)
  by_cases ht : ∃ h : H, X.act (1, h) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y t i = X.pair Y s (Y.act (h,1) i) := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single s 1) v (X.pair Y' s y') = v y' := by
      apply pulls_single (Biset.pairLinear Complex X Y' (Finsupp.single s 1))
      intro j
      rw [Biset.pairLinear_single, one_mul]
      have hi : X.pair Y' s j = X.pair Y' s y' ↔ j = y' := by
        constructor
        · intro hp
          obtain ⟨k, hs, hk⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (Y'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    have hre := congrArg (fun w => ((Biset.Hom.id X).horizontal L).toLinearMap
      (Finsupp.single w 1) (X.pair Y' s y')) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
      (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') =
      Biset.pairLinear Complex X Y' (Finsupp.single s 1)
      (L.toLinearMap (Finsupp.single (Y.act (h,1) i) 1)) (X.pair Y' s y') at hre
    rw [hre, heval, hy _ , he]
    have hi : X.pair Y s (Y.act (h,1) i) = X.pair Y s y ↔ Y.act (h,1) i = y := by
      constructor
      · intro hp
        obtain ⟨k, hs, hk⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (Y.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single t 1) v (X.pair Y' s y') = 0 := by
      have he : (Finsupp.lapply (X.pair Y' s y') : Vec (X.tensor Y').carrier →ₗ[Complex] Complex).comp
          (Biset.pairLinear Complex X Y' (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X Y' (Finsupp.single t 1) (Finsupp.single j r)
          (X.pair Y' s y') = 0
        rw [Biset.pairLinear_single, one_mul, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, hk, _⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, hk, _⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

end Balanced

end

noncomputable section
set_option maxHeartbeats 2000000

variable {U : Type u} [Group U]
variable {K H J L M : Subgroup U}

private abbrev ev {p q : Word K H} (d : LabelledDrawing Complex p q) := d.interpret.eval.toLinearMap

private abbrev drawId (p : Word K H) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private abbrev before {p q r : Word K H} (d : LabelledDrawing Complex p q)
    (e : LabelledDrawing Complex q r) := LabelledDrawing.vertical d e

private abbrev atLeft {p q : Word K H} (d : LabelledDrawing Complex p q)
    (r : Word H J) := LabelledDrawing.horizontal d (drawId r)

private abbrev atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :=
  before (.ordinary (.associate p q r))
    (before (.horizontal (drawId p) d) (.ordinary (.unassociate p q' r')))

private abbrev pair (p : Word K H) (q : Word H J) := p.basis.pair q.basis

private abbrev triple (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :=
  pair (p.tensor q) r (pair p q x y) z

private theorem pulls_before {p q r : Word K H}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex q r}
    {z : r.basis.carrier} {y : q.basis.carrier} {x : p.basis.carrier}
    (he : Pulls (ev e) z y) (hd : Pulls (ev d) y x) : Pulls (ev (before d e)) z x := by
  intro v
  change ev e (ev d v) z = _
  rw [he _, hd _]

private theorem pulls_assoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.associate p q r))) (pair p (q.tensor r) x (pair q r y z))
      (triple p q r x y z) := by
  let i := Biset.associateBasisEquiv p.basis q.basis r.basis
  have hi : ∀ v : _, i v = i (triple p q r x y z) ↔ v = triple p q r x y z :=
    fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨xy,t⟩ => ?_)
  exact Quotient.inductionOn xy (fun ⟨s,w⟩ => Diagram.eval_associate_single p q r s w t 1)

private theorem pulls_unassoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.unassociate p q r))) (triple p q r x y z)
      (pair p (q.tensor r) x (pair q r y z)) := by
  let i := (Biset.associateBasisEquiv p.basis q.basis r.basis).symm
  have hi : ∀ v : _, i v = i (pair p (q.tensor r) x (pair q r y z)) ↔
      v = pair p (q.tensor r) x (pair q r y z) := fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨s,yz⟩ => ?_)
  exact Quotient.inductionOn yz (fun ⟨w,t⟩ => Diagram.eval_unassociate_single p q r s w t 1)

private theorem pulls_atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    {d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')}
    (free : ∀ (s : p.basis.carrier) (h : H), p.basis.act (1, h) s = s → h = 1)
    (s : p.basis.carrier) {x : q'.basis.carrier} {y : r'.basis.carrier}
    {x' : q.basis.carrier} {y' : r.basis.carrier}
    (hd : Pulls (ev d) (pair q' r' x y) (pair q r x' y')) :
    Pulls (ev (atRight p d)) (triple p q' r' s x y) (triple p q r s x' y') := by
  apply pulls_before (pulls_before (pulls_unassoc p q' r' s x y) ?_)
    (pulls_assoc p q r s x' y')
  exact pulls_horizontal_left d.interpret.eval free hd s

private theorem free_up_left (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.induction a).act (h, 1) s = s) : h = 1 := by
  change h * s * (a.toHom 1)⁻¹ = s at eq
  simpa using mul_right_cancel (show h * s = 1 * s by simpa using eq)

private theorem free_up_right (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.induction a).act (1, h) s = s) : h = 1 := by
  change 1 * s * (a.toHom h)⁻¹ = s at eq
  apply a.injective
  have he : (a.toHom h)⁻¹ = 1 :=
    mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_right (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.restriction a).act (1, h) s = s) : h = 1 := by
  change a.toHom 1 * s * h⁻¹ = s at eq
  have he : h⁻¹ = 1 := mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_left (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.restriction a).act (h, 1) s = s) : h = 1 := by
  change a.toHom h * s * (1 : K)⁻¹ = s at eq
  apply a.injective
  exact mul_right_cancel (show a.toHom h * s = a.toHom 1 * s by simpa using eq)

private theorem up_balance (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    pair (Word.up a) (Word.up b) (x * a.toHom y) 1 = pair (Word.up a) (Word.up b) x y := by
  simpa [pair, Word.basis, Biset.induction] using
    (Biset.induction a).pair_balance (Biset.induction b) y x 1

private theorem pulls_merge (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) :
    Pulls (ev (.trivalent (.mergeUp a b))) x (pair (Word.up a) (Word.up b) x 1) := by
  have hi (w : ((Word.up a).tensor (.up b)).basis.carrier) (z : K) :
      Generator.mergeUpBasis a b w = z ↔ w = pair (Word.up a) (Word.up b) z 1 := by
    refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
    change s * a.toHom t = z ↔ pair (Word.up a) (Word.up b) s t = _
    constructor
    · rintro rfl
      exact (up_balance a b s t).symm
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom t = z * a.toHom 1 at eq
      simpa using eq
  apply pulls_of_single (fun w => hi w x)
  intro w
  refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
  exact Diagram.eval_mergeUp_single a b s t 1

private theorem pulls_split (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    Pulls (ev (.trivalent (.splitUp a b))) (pair (Word.up a) (Word.up b) x y) (x * a.toHom y) := by
  apply pulls_single
  intro s
  change (Diagram.splitUp (R := Complex) a b).eval.toLinearMap (Finsupp.single s 1)
    (pair (Word.up a) (Word.up b) x y) = _
  rw [Diagram.eval_splitUp_single]
  classical
  have hi : pair (Word.up a) (Word.up b) s 1 = pair (Word.up a) (Word.up b) x y ↔
      s = x * a.toHom y := by
    constructor
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom 1 = x * a.toHom y at eq
      simpa using eq
    · rintro rfl
      exact up_balance a b x y
  simp only [Finsupp.single_apply, hi]

private theorem sum_eval (p q : Word K H) (xs : List (Complex × Diagram Complex p q)) :
    (ScopedDiagram.linearCombination (xs.map fun (c,d) => (c, ScopedDiagram.ordinary d))).eval.toLinearMap =
      (xs.map fun (c,d) => c • d.eval.toLinearMap).sum := by
  apply LinearMap.ext
  intro v
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c,d⟩
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply]
    rw [ih]
    rfl

private theorem singleton_mixed (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d) :
    ev (.compactProjection a b c d [(1,p)]) =
      (Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem singleton_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) :
    ev (.parallelUp a b c d [(1,p)]) =
      (Diagram.parallelUp (R := Complex) a b c d p).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.parallelUp (R := Complex) a b c d p)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem pulls_compact (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d)
    (x : K) (y : J) :
    Pulls (ev (.compactProjection a b c d [(1,p)])) (pair (Word.up c) (Word.down d) x y)
      (Generator.mixedPair a b (a.toHom x * p.dot.element * b.toHom y)) := by
  rw [singleton_mixed]
  exact pulls_mixed a b c d p _

private theorem pulls_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) (x : K) (y : J) :
    Pulls (ev (.parallelUp a b c d [(1,p)])) (pair (Word.up c) (Word.up d) x y)
      (pair (Word.up a) (Word.up b) (x * c.toHom y * p.element⁻¹) 1) := by
  rw [singleton_parallel]
  intro v
  change ev (.trivalent (.splitUp c d))
    ((Diagram.upDot (R := Complex) p).eval.toLinearMap (ev (.trivalent (.mergeUp a b)) v))
    (pair (Word.up c) (Word.up d) x y) = _
  rw [pulls_split c d x y _]
  have he : Pulls (Diagram.upDot (R := Complex) p).eval.toLinearMap
      (x * c.toHom y) (x * c.toHom y * p.element⁻¹) := by
    refine pulls_of_single (forward := fun z : K => z * p.element)
      ?_ (fun z => Diagram.eval_upDot_single p z 1)
    intro s
    exact eq_mul_inv_iff_mul_eq.symm
  rw [he _, pulls_merge a b _ _]

end

noncomputable section
set_option maxHeartbeats 2400000

variable {U : Type u} [Group U] {G A D F C E B B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A)
  (c : ConjEmbedding F D) (d : ConjEmbedding C G)
  (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev bottom := ((Word.down a).tensor (.up b)).tensor (.up c)
private abbrev top := ((Word.up d).tensor (.up e)).tensor (.down f)
private abbrev mergedBottom := (Word.down a).tensor (.up (b.comp c))
private abbrev mergedTop := (Word.up (d.comp e)).tensor (.down f)

private abbrev splitBottom : LabelledDrawing Complex (mergedBottom a b c) (bottom a b c) :=
  before (.horizontal (drawId (.down a)) (.trivalent (.splitUp b c)))
    (.ordinary (.unassociate (.down a) (.up b) (.up c)))

private abbrev mergeTop : LabelledDrawing Complex (top d e f) (mergedTop d e f) :=
  .horizontal (.trivalent (.mergeUp d e)) (drawId (.down f))

private abbrev mergedEval (drawing : LabelledDrawing Complex (bottom a b c) (top d e f)) :=
  ev (before (splitBottom a b c) (before drawing (mergeTop d e f)))

private abbrev leftDrawing (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B)
    (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × Dot (r.comp t) (d.comp e))) :=
  before (atLeft (.compactProjection a b r s xs) (.up c))
    (before (atRight (.up r) (.compactProjection s c t f ys))
      (atLeft (.parallelUp r t d e zs) (.down f)))

private abbrev rightDrawing (u' : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B')
    (ells : List (Complex × Dot (b.comp c) (u'.comp w)))
    (ms : List (Complex × ProjectionDot.Mixed a u' d v))
    (ns : List (Complex × ProjectionDot.Mixed v w e f)) :=
  before (atRight (.down a) (.parallelUp b c u' w ells))
    (before (atLeft (.compactProjection a u' d v ms) (.up w))
      (atRight (.up d) (.compactProjection v w e f ns)))

private theorem pulls_splitBottom (x y : A) (z : D) :
    Pulls (ev (splitBottom a b c)) (triple (.down a) (.up b) (.up c) x y z)
      (pair (.down a) (.up (b.comp c)) x (y * b.toHom z)) := by
  apply pulls_before (pulls_unassoc (.down a) (.up b) (.up c) x y z)
  exact pulls_horizontal_left (X := Biset.restriction a) (Diagram.splitUp (R := Complex) b c).eval (free_down_right a)
    (pulls_split b c y z) x

private theorem pulls_mergeTop (g : G) (h : F) :
    Pulls (ev (mergeTop d e f)) (pair (.up (d.comp e)) (.down f) g h)
      (triple (.up d) (.up e) (.down f) g 1 h) := by
  exact pulls_horizontal_right (Y := Biset.restriction f) (Diagram.mergeUp (R := Complex) d e).eval
    (free_down_left f) (pulls_merge d e g) h

private theorem mixedPair_coord {K H P : Subgroup U}
    (α : ConjEmbedding K P) (β : ConjEmbedding H P) (x y : P) :
    pair (.down α) (.up β) x y = Generator.mixedPair α β (x * y) := by
  apply (Generator.mixedEquiv α β).injective
  change x * y = Generator.mixedProduct α β (Generator.mixedPair α β (x * y))
  rw [Generator.mixedProduct_mixedPair]

-- Lemma 6.3, left backward calculation. At each stage the linear coefficient
-- is evaluated at its unique backwards coordinate. The fixed strands act
-- freely at the balancing interfaces, so rebracketing retains the fiber sum.
private theorem pulls_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedPair a (b.comp c)
        (a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h)) := by
  let g' := g * z.element⁻¹
  let y' := y.dot.element * c.toHom h
  let x' := a.toHom g' * x.dot.element * b.toHom y'
  have step₃ : Pulls (ev (atLeft (.parallelUp r t d e [(1,z)]) (.down f)))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up r) (.up t) (.down f) g' 1 h) := by
    have hp := pulls_parallel r t d e z g 1
    simp only [map_one, mul_one] at hp
    exact pulls_horizontal_right (Y := Biset.restriction f) _ (free_down_left f) hp h
  have step₂ : Pulls (ev (atRight (.up r) (.compactProjection s c t f [(1,y)])))
      (triple (.up r) (.up t) (.down f) g' 1 h) (triple (.up r) (.down s) (.up c) g' y' 1) := by
    apply pulls_atRight (.up r) (free_up_right r) g'
    have hp := pulls_compact s c t f y 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₁ : Pulls (ev (atLeft (.compactProjection a b r s [(1,x)]) (.up c)))
      (triple (.up r) (.down s) (.up c) g' y' 1) (triple (.down a) (.up b) (.up c) x' 1 1) :=
    pulls_horizontal_right _ (free_up_left c) (pulls_compact a b r s x g' y') _
  have step₀ := pulls_splitBottom a b c x' 1 1
  simp only [map_one, mul_one] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h))
  have hc : x' = a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h := by
    simp only [x', g', y', leftParameter, ConjEmbedding.comp_apply, map_mul, mul_assoc]
  rw [← hc]
  exact out

-- Lemma 6.3, right backward calculation. The parallel vertex contributes
-- right multiplication by ell⁻¹. Its reversed intertwining equation
-- moves that factor through the right boundary action.
private theorem pulls_right {u' : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (u'.comp w))
    (m : ProjectionDot.Mixed a u' d v) (n : ProjectionDot.Mixed v w e f)
    (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (rightDrawing a b c d e f u' v w [(1,ell)] [(1,m)] [(1,n)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedPair a (b.comp c)
        (a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h)) := by
  let n' := n.dot.element * w.toHom h
  let m' := a.toHom g * m.dot.element * u'.toHom n'
  have step₃ : Pulls (ev (atRight (.up d) (.compactProjection v w e f [(1,n)])))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up d) (.down v) (.up w) g n' 1) := by
    apply pulls_atRight (.up d) (free_up_right d) g
    have hp := pulls_compact v w e f n 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₂ : Pulls (ev (atLeft (.compactProjection a u' d v [(1,m)]) (.up w)))
      (triple (.up d) (.down v) (.up w) g n' 1) (triple (.down a) (.up u') (.up w) m' 1 1) :=
    pulls_horizontal_right _ (free_up_left w) (pulls_compact a u' d v m g n') _
  have step₁ : Pulls (ev (atRight (.down a) (.parallelUp b c u' w [(1,ell)])))
      (triple (.down a) (.up u') (.up w) m' 1 1)
      (triple (.down a) (.up b) (.up c) m' ell.element⁻¹ 1) := by
    apply pulls_atRight (.down a) (free_down_right a) m'
    simpa only [map_one, mul_one, one_mul] using pulls_parallel b c u' w ell 1 1
  have step₀ := pulls_splitBottom a b c m' ell.element⁻¹ 1
  simp only [map_one, mul_one] at step₀
  rw [mixedPair_coord a (b.comp c) m' ell.element⁻¹] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h))
  have hel := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at hel
  have hc : m' * ell.element⁻¹ =
      a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h := by
    simp only [m', n', rightParameter, ConjEmbedding.comp_apply, map_mul, mul_assoc, hel]
  rw [← hc]
  exact out

end
end OutsideRegionsAux
namespace OutsideRegionsAux
open MackeyDiagrams

noncomputable section
variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)
variable (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)

private abbrev mergeBottom : LabelledDrawing Complex (bottom a b c) (mergedBottom a b c) :=
  before (.ordinary (.associate (.down a) (.up b) (.up c)))
    (.horizontal (drawId (.down a)) (.trivalent (.mergeUp b c)))

private abbrev splitTop : LabelledDrawing Complex (mergedTop d e f) (top d e f) :=
  .horizontal (.trivalent (.splitUp d e)) (drawId (.down f))

private abbrev targetProjection :=
  before (mergeBottom a b c)
    (before (.compactProjection a (b.comp c) (d.comp e) f [(1,p)]) (splitTop d e f))

private abbrev targetMultiplication :=
  before (mergeTop d e f)
    (before (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) (splitBottom a b c))

-- The boundary frames come in inverse pairs, by the typed trivalent
-- and reassociation identities. This bridges merged coordinates and the
-- full three-strand equality used in the endpoint.
private theorem cancel_splitBottom_mergeBottom :
    (splitBottom a b c).interpret.eval.vertical (mergeBottom a b c).interpret.eval =
      Biset.Hom.id (mergedBottom a b c).basis := by
  let X := (Word.down a).basis
  let Y := (Word.up b).basis
  let Z := (Word.up c).basis
  let S := (Diagram.id (R := Complex) (.down a)).eval.horizontal (Diagram.splitUp b c).eval
  let M := (Diagram.id (R := Complex) (.down a)).eval.horizontal (Diagram.mergeUp b c).eval
  change (S.vertical (Biset.unassociate X Y Z Complex)).vertical
    ((Biset.associate X Y Z Complex).vertical M) = _
  refine Biset.Hom.cancel_middle _ _ _ _ Biset.unassociate_associate ?_
  change ((Biset.Hom.id (R := Complex) X).horizontal (Diagram.splitUp b c).eval).vertical
    ((Biset.Hom.id X).horizontal (Diagram.mergeUp b c).eval) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id X).horizontal
    (((Diagram.splitUp (R := Complex) b c).vertical (Diagram.mergeUp b c)).eval) = _
  rw [Diagram.splitUp_mergeUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_mergeBottom_splitBottom :
    (mergeBottom a b c).interpret.eval.vertical (splitBottom a b c).interpret.eval =
      Biset.Hom.id (bottom a b c).basis := by
  change ((Biset.associate (Word.down a).basis (Word.up b).basis (Word.up c).basis
      Complex).vertical
      ((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.mergeUp b c).eval)).vertical
    (((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.splitUp b c).eval).vertical
      (Biset.unassociate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex)) = _
  refine Biset.Hom.cancel_middle _ _ _ _ ?_ Biset.associate_unassociate
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id (Word.down a).basis).horizontal
    ((Diagram.mergeUp (R := Complex) b c).vertical (Diagram.splitUp b c)).eval = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_splitTop_mergeTop :
    (splitTop d e f).interpret.eval.vertical (mergeTop d e f).interpret.eval =
      Biset.Hom.id (mergedTop d e f).basis := by
  change ((Diagram.splitUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)).vertical
      ((Diagram.mergeUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.splitUp (R := Complex) d e).vertical (Diagram.mergeUp d e)).eval.horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.splitUp_mergeUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_mergeTop_splitTop :
    (mergeTop d e f).interpret.eval.vertical (splitTop d e f).interpret.eval =
      Biset.Hom.id (top d e f).basis := by
  change ((Diagram.mergeUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)).vertical
      ((Diagram.splitUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.mergeUp (R := Complex) d e).vertical (Diagram.splitUp d e)).eval.horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem frame_eq {U : Type*} [Group U] {K H : Subgroup U}
    {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (preInv : LabelledDrawing Complex p p₀) (postInv : LabelledDrawing Complex q₀ q)
    (hp : preInv.interpret.eval.vertical pre.interpret.eval = Biset.Hom.id p.basis)
    (hq : post.interpret.eval.vertical postInv.interpret.eval = Biset.Hom.id q.basis)
    (x y : LabelledDrawing Complex p q) :
    ev (before pre (before x post)) = ev (before pre (before y post)) ↔
      x.interpret.eval = y.interpret.eval := by
  constructor
  · intro h
    have he : pre.interpret.eval.vertical (x.interpret.eval.vertical post.interpret.eval) =
        pre.interpret.eval.vertical (y.interpret.eval.vertical post.interpret.eval) :=
      Biset.Hom.ext h
    have undo (z : LabelledDrawing Complex p q) :
        (preInv.interpret.eval.vertical (pre.interpret.eval.vertical
          (z.interpret.eval.vertical post.interpret.eval))).vertical postInv.interpret.eval =
        z.interpret.eval := by
      rw [← Biset.Hom.vertical_assoc preInv.interpret.eval, hp, Biset.Hom.id_vertical,
        Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]
    have h' := congrArg (fun z => (preInv.interpret.eval.vertical z).vertical postInv.interpret.eval) he
    exact (undo x).symm.trans (h'.trans (undo y))
  · intro h
    exact congrArg (fun z : Biset.Hom Complex p.basis q.basis =>
      (pre.interpret.eval.vertical (z.vertical post.interpret.eval)).toLinearMap) h

private theorem framed_target {U : Type*} [Group U] {K H : Subgroup U}
    {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (preInv : LabelledDrawing Complex p p₀) (postInv : LabelledDrawing Complex q₀ q)
    (hp : pre.interpret.eval.vertical preInv.interpret.eval = Biset.Hom.id p₀.basis)
    (hq : postInv.interpret.eval.vertical post.interpret.eval = Biset.Hom.id q₀.basis)
    (target : LabelledDrawing Complex p₀ q₀) :
    ev (before pre (before (before preInv (before target postInv)) post)) = ev target := by
  change (pre.interpret.eval.vertical
    ((preInv.interpret.eval.vertical (target.interpret.eval.vertical postInv.interpret.eval)).vertical
      post.interpret.eval)).toLinearMap = _
  rw [Biset.Hom.vertical_assoc preInv.interpret.eval,
    ← Biset.Hom.vertical_assoc pre.interpret.eval, hp, Biset.Hom.id_vertical,
    Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]

private theorem projection_comparison
    (drawing : LabelledDrawing Complex (bottom a b c) (top d e f)) (q : A)
    (h : ∀ (g : G) (k : F), Pulls (mergedEval a b c d e f drawing)
      (pair (.up (d.comp e)) (.down f) g k)
      (Generator.mixedPair a (b.comp c) (a.toHom g * q * (b.comp c).toHom k))) :
    drawing.interpret.eval = (targetProjection a b c d e f p).interpret.eval ↔ q = p.dot.element := by
  classical
  have htarget : mergedEval a b c d e f (targetProjection a b c d e f p) =
      ev (.compactProjection a (b.comp c) (d.comp e) f [(1, p)]) :=
    framed_target (splitBottom a b c) (mergeTop d e f) (mergeBottom a b c) (splitTop d e f)
      (cancel_splitBottom_mergeBottom a b c) (cancel_splitTop_mergeTop d e f) _
  rw [← frame_eq (splitBottom a b c) (mergeTop d e f) (mergeBottom a b c) (splitTop d e f)
    (cancel_mergeBottom_splitBottom a b c) (cancel_mergeTop_splitTop d e f)]
  change (mergedEval a b c d e f drawing =
    mergedEval a b c d e f (targetProjection a b c d e f p)) ↔ _
  rw [htarget]
  constructor
  · intro he
    have hq := h 1 1 (Finsupp.single (Generator.mixedPair a (b.comp c) q) 1)
    rw [he] at hq
    rw [pulls_compact a (b.comp c) (d.comp e) f p 1 1 _] at hq
    simp only [map_one, one_mul, mul_one, Finsupp.single_eq_same] at hq
    by_contra hne
    have hne' : Generator.mixedPair a (b.comp c) (p.dot.element) ≠
        Generator.mixedPair a (b.comp c) q :=
      fun h => hne ((Generator.mixedEquiv a (b.comp c)).symm.injective h.symm)
    rw [Finsupp.single_eq_of_ne hne'] at hq
    exact zero_ne_one hq
  · rintro rfl
    apply LinearMap.ext
    intro input
    apply Finsupp.ext
    intro output
    refine Quotient.inductionOn output (fun ⟨g,k⟩ => ?_)
    exact (h g k input).trans (pulls_compact a (b.comp c) (d.comp e) f p g k input).symm

private theorem left_project_eval {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) :
    (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]).interpret.eval =
      (targetProjection a b c d e f p).interpret.eval ↔ leftParameter a b c d e f x.dot y.dot z = p.dot.element :=
  projection_comparison a b c d e f p _ _ (pulls_left a b c d e f x y z)

private theorem right_project_eval {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f) :
    (rightDrawing a b c d e f j v w [(1,ell)] [(1,m)] [(1,n)]).interpret.eval =
      (targetProjection a b c d e f p).interpret.eval ↔ rightParameter a b c d e f ell m.dot n.dot = p.dot.element :=
  projection_comparison a b c d e f p _ _ (pulls_right a b c d e f ell m n)

end
end OutsideRegionsAux
namespace OutsideRegionsAux
open MackeyDiagrams
noncomputable section

variable {U : Type*} [Group U] {K H J L M G A D F C E B : Subgroup U}

private abbrev col {X : Type*} (x : X) : Vec X :=
  Finsupp.single x 1

private theorem push_before {p q r : Word K H}
    (D : LabelledDrawing Complex p q) (E : LabelledDrawing Complex q r)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier)
    (hd : ev D (col x) = col y) (he : ev E (col y) = col z) :
    ev (before D E) (col x) = col z := by
  change ev E (ev D (col x)) = _
  rw [hd, he]

private theorem push_atLeft {p p' : Word K H} {q : Word H J}
    (D : LabelledDrawing Complex p p') (x : p.basis.carrier) (y : q.basis.carrier)
    (x' : p'.basis.carrier) (hd : ev D (col x) = col x') :
    ev (atLeft D q) (col (pair p q x y)) = col (pair p' q x' y) := by
  change (D.interpret.eval.horizontal (Diagram.id q).eval).toLinearMap _ = _
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply, hd,
    Biset.pairLinear_single, one_mul]

private theorem push_atRight {p : Word K H} {q : Word H J} {s : Word J L}
    {q' : Word H M} {s' : Word M L}
    (D : LabelledDrawing Complex (q.tensor s) (q'.tensor s'))
    (x : p.basis.carrier) (y : q.basis.carrier) (z : s.basis.carrier)
    (y' : q'.basis.carrier) (z' : s'.basis.carrier)
    (hd : ev D (col (pair q s y z)) = col (pair q' s' y' z')) :
    ev (atRight p D) (col (triple p q s x y z)) = col (triple p q' s' x y' z') := by
  change (Diagram.unassociate (R := Complex) p q' s').eval.toLinearMap
    (((Diagram.id p).eval.horizontal D.interpret.eval).toLinearMap
      ((Diagram.associate (R := Complex) p q s).eval.toLinearMap (col (triple p q s x y z)))) = _
  rw [Diagram.eval_associate_single, Biset.Hom.horizontal_single, one_smul,
    Diagram.eval_id_apply, hd, Biset.pairLinear_single, one_mul, Diagram.eval_unassociate_single]

private theorem push_mixed (a : ConjEmbedding K A) (b : ConjEmbedding H A)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (x : Dot (a.comp l) (b.comp r)) (g : K) (h : H) :
    ev (.mixedMultiplication a b l r [(1,x)]) (col (pair (.up l) (.down r) g h)) =
      col (pair (.down a) (.up b) (a.toHom g * x.element * b.toHom h) 1) := by
  let label : DotLabel Complex (a.comp l) (b.comp r) := Finsupp.single x 1
  have hterms : label.terms = [(1,x)] := by
    classical
    simp [label, DotLabel.terms]
  rw [← hterms]
  have hcol := ((MixedCrossingFiniteFiberConvention (U := U)).2.2.1 a b l r label).1
    (pair (.up l) (.down r) g h)
  rw [hterms] at hcol
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] at hcol
  exact hcol

private theorem push_parallel (a : ConjEmbedding H A) (b : ConjEmbedding L H)
    (j : ConjEmbedding J A) (w : ConjEmbedding L J)
    (x : Dot (a.comp b) (j.comp w)) (g : A) (h : H) :
    ev (.parallelUp a b j w [(1,x)]) (col (pair (.up a) (.up b) g h)) =
      col (pair (.up j) (.up w) (g * a.toHom h * x.element) 1) := by
  rw [singleton_parallel]
  change (Diagram.splitUp (R := Complex) j w).eval.toLinearMap
    ((Diagram.upDot x).eval.toLinearMap ((Diagram.mergeUp a b).eval.toLinearMap
      (col (pair (.up a) (.up b) g h)))) = _
  rw [Diagram.eval_mergeUp_single, Diagram.eval_upDot_single, Diagram.eval_splitUp_single]

variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev framedMul (drawing : LabelledDrawing Complex (top d e f) (bottom a b c)) :=
  before (splitTop d e f) (before drawing (mergeBottom a b c))

private theorem push_splitTop (g : G) (h : F) :
    ev (splitTop d e f) (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (triple (.up d) (.up e) (.down f) g 1 h) := by
  change (Diagram.horizontal (R := Complex) (Diagram.splitUp d e) (Diagram.id (.down f))).eval.toLinearMap _ = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_splitUp_single,
    Diagram.eval_id_apply, Biset.pairLinear_single, one_mul]

private theorem push_mergeBottom (x y : A) (z : D) :
    ev (mergeBottom a b c) (col (triple (.down a) (.up b) (.up c) x y z)) =
      col (Generator.mixedPair a (b.comp c) (x * (y * b.toHom z))) := by
  change (Diagram.horizontal (R := Complex) (Diagram.id (.down a)) (Diagram.mergeUp b c)).eval.toLinearMap
    ((Diagram.associate (.down a) (.up b) (.up c)).eval.toLinearMap
      (col (triple (.down a) (.up b) (.up c) x y z))) = _
  rw [Diagram.eval_associate_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, Diagram.eval_mergeUp_single, Biset.pairLinear_single, one_mul]
  exact congrArg col (mixedPair_coord a (b.comp c) x (y * b.toHom z))

private abbrev leftMulDrawing (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B) (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :=
  before (atLeft (.parallelUp d e r t [(1,z.inverse)]) (.down f))
    (before (atRight (.up r) (.mixedMultiplication s c t f [(1,y)]))
      (atLeft (.mixedMultiplication a b r s [(1,x)]) (.up c)))

private abbrev rightMulDrawing (j : ConjEmbedding B A) (v : ConjEmbedding C B)
    (w : ConjEmbedding F B) (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :=
  before (atRight (.up d) (.mixedMultiplication v w e f [(1,n)]))
    (before (atLeft (.mixedMultiplication a j d v [(1,m)]) (.up w))
      (atRight (.down a) (.parallelUp j w b c [(1,ell.inverse)])))

-- The forward columns of Xiao's Theorem 6.5 specialize to the same
-- parameter products as the backward coefficient calculation of Lemma 6.3.
private theorem push_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    ev (framedMul a b c d e f (leftMulDrawing a b c d e f r s t x y z))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * leftParameter a b c d e f x y z * (b.comp c).toHom h)) := by
  let g' := g * z.element⁻¹
  let t' := y.element * c.toHom h
  let q := a.toHom g' * x.element * b.toHom t'
  have h₁ := push_atLeft (.parallelUp d e r t [(1,z.inverse)])
    (q := .down f) (pair (.up d) (.up e) g 1) h (pair (.up r) (.up t) g' 1) (by
      simpa only [g', map_one, mul_one, Dot.inverse] using push_parallel d e r t z.inverse g 1)
  have h₂ := push_atRight (p := Word.up r) (.mixedMultiplication s c t f [(1,y)])
    g' 1 h t' 1 (by simpa only [t', map_one, one_mul] using push_mixed s c t f y 1 h)
  have h₃ := push_atLeft (.mixedMultiplication a b r s [(1,x)])
    (q := .up c) (pair (.up r) (.down s) g' t') 1
    (pair (.down a) (.up b) q 1) (push_mixed a b r s x g' t')
  have h₄ := push_mergeBottom a b c q 1 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  simpa only [q, g', t', leftParameter, map_one, one_mul, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc] using hEval

private theorem push_right {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) (g : G) (h : F) :
    ev (framedMul a b c d e f (rightMulDrawing a b c d e f j v w ell m n))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * rightParameter a b c d e f ell m n * (b.comp c).toHom h)) := by
  let n' := n.element * w.toHom h
  let q := a.toHom g * m.element * j.toHom n'
  have h₁ := push_atRight (p := Word.up d) (.mixedMultiplication v w e f [(1,n)])
    g 1 h n' 1 (by simpa only [n', map_one, one_mul] using push_mixed v w e f n 1 h)
  have h₂ := push_atLeft (.mixedMultiplication a j d v [(1,m)])
    (q := .up w) (pair (.up d) (.down v) g n') 1
    (pair (.down a) (.up j) q 1) (push_mixed a j d v m g n')
  have h₃ := push_atRight (p := Word.down a) (.parallelUp j w b c [(1,ell.inverse)])
    q 1 1 ell.element⁻¹ 1 (by
      simpa only [map_one, mul_one, one_mul, Dot.inverse] using push_parallel j w b c ell.inverse 1 1)
  have h₄ := push_mergeBottom a b c q ell.element⁻¹ 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  have he := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at he
  simpa only [q, n', rightParameter, map_one, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc, he] using hEval

private theorem multiplication_comparison
    (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (drawing : LabelledDrawing Complex (top d e f) (bottom a b c)) (q : A)
    (h : ∀ (g : G) (k : F), ev (framedMul a b c d e f drawing)
      (col (pair (.up (d.comp e)) (.down f) g k)) =
      col (Generator.mixedPair a (b.comp c) (a.toHom g * q * (b.comp c).toHom k))) :
    drawing.interpret.eval = (targetMultiplication a b c d e f p).interpret.eval ↔ q = p.dot.element := by
  classical
  have htarget : ev (framedMul a b c d e f (targetMultiplication a b c d e f p)) =
      ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) :=
    framed_target (splitTop d e f) (mergeBottom a b c) (mergeTop d e f) (splitBottom a b c)
      (cancel_splitTop_mergeTop d e f) (cancel_splitBottom_mergeBottom a b c) _
  have col_target (g : G) (k : F) :
      ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)])
        (col (pair (.up (d.comp e)) (.down f) g k)) =
        col (Generator.mixedPair a (b.comp c) (a.toHom g * p.dot.element * (b.comp c).toHom k)) := by
    refine (push_mixed a (b.comp c) (d.comp e) f p.dot g k).trans ?_
    apply congrArg col
    exact (mixedPair_coord a (b.comp c) _ 1).trans (congrArg _ (mul_one _))
  rw [← frame_eq (splitTop d e f) (mergeBottom a b c) (mergeTop d e f) (splitBottom a b c)
    (cancel_mergeTop_splitTop d e f) (cancel_mergeBottom_splitBottom a b c)]
  change (ev (framedMul a b c d e f drawing) =
    ev (framedMul a b c d e f (targetMultiplication a b c d e f p))) ↔ _
  rw [htarget]
  constructor
  · intro he
    have eq := h 1 1
    rw [he, col_target] at eq
    simp only [map_one, one_mul, mul_one] at eq
    apply (Generator.mixedEquiv a (b.comp c)).symm.injective
    exact Finsupp.single_left_injective one_ne_zero eq.symm
  · rintro rfl
    apply Finsupp.lhom_ext
    intro z k
    have hc (z : (mergedTop d e f).basis.carrier) :
        ev (framedMul a b c d e f drawing) (col z) =
        ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) (col z) :=
      Quotient.inductionOn z fun ⟨g,h'⟩ => (h g h').trans (col_target g h').symm
    rw [show Finsupp.single z k = k • col z by simp [col, Finsupp.smul_single],
      map_smul, map_smul, hc]

private theorem left_mul_eval {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (x : Dot (a.comp r) (b.comp s)) (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :
    (leftMulDrawing a b c d e f r s t x y z).interpret.eval =
      (targetMultiplication a b c d e f p).interpret.eval ↔ leftParameter a b c d e f x y z = p.dot.element :=
  multiplication_comparison a b c d e f p _ _ (push_left a b c d e f x y z)

private theorem right_mul_eval {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (ell : Dot (b.comp c) (j.comp w)) (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :
    (rightMulDrawing a b c d e f j v w ell m n).interpret.eval =
      (targetMultiplication a b c d e f p).interpret.eval ↔ rightParameter a b c d e f ell m n = p.dot.element :=
  multiplication_comparison a b c d e f p _ _ (push_right a b c d e f ell m n)

end
end OutsideRegionsAux
namespace OutsideRegionsAux
open MackeyDiagrams

section
variable {U : Type*} [Group U] {G A D F C E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private theorem finite_mixed {K H P L : Subgroup U} [Finite K] [Finite H]
    (α : ConjEmbedding K P) (β : ConjEmbedding H P)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (x : Dot (α.comp l) (β.comp r)) :
    ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis α β l r x w = z} := by
  let _ : Finite ((Word.up l).tensor (.down r)).basis.carrier :=
    Finite.of_surjective (fun p : K × H => (Biset.induction l).pair (Biset.restriction r) p.1 p.2)
      (fun w => Quotient.exists_rep w)
  exact fun _ => Set.toFinite _

private theorem lower_le_max (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) :
    (a.comp (d.comp e)).toHom.range ≤ leftBound a b p.element := by
  apply le_inf (range_comp_le a (d.comp e))
  rw [dot_ranges p]
  exact Subgroup.map_mono (range_comp_le b (c.comp f))

-- The Case 2 supplier constructs the full intersection. For the interval
-- here, use inverses of the given embeddings restricted to any H in the
-- interval, and construct both singleton crossings on this same group.
private theorem left_witness [Finite G] [Finite D] [Finite F]
    (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) (H : Subgroup A)
    (hlo : (a.comp (d.comp e)).toHom.range ≤ H) (hhi : H ≤ leftBound a b p.element) :
    let B := H.map A.subtype
    ∃ (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
      (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
      (z : Dot (r.comp t) (d.comp e)),
      conj (a.toHom z.element⁻¹) (a.comp r).toHom.range = H ∧
        leftParameter a b c d e f x.dot y.dot z = p.element := by
  intro B
  let j := inclusion H
  have hj : j.toHom.range = H := inclusion_range H
  obtain ⟨r, hr⟩ := lift_through a j (by
    rw [hj]
    exact hhi.trans inf_le_left)
  let _ : Finite B := Finite.of_injective r.toHom r.injective
  have hs' : (conjugated j p.element⁻¹).toHom.range ≤ b.toHom.range := by
    rw [conjugated_range, hj]
    calc
      _ ≤ conj p.element⁻¹ (conj p.element b.toHom.range) :=
        Subgroup.map_mono (hhi.trans inf_le_right)
      _ = _ := by rw [conj_mul, inv_mul_cancel, conj_one]
  obtain ⟨s, hs⟩ := lift_through b (conjugated j p.element⁻¹) hs'
  let t := restrictTo (a.comp (d.comp e)) H hlo
  have hjt : j.comp t = a.comp (d.comp e) := ConjEmbedding.ext (MonoidHom.ext fun _ => rfl)
  have ht₁ : r.comp t = d.comp e := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro v
    apply a.injective
    have h₁ := congrArg (fun m : ConjEmbedding B A => m.toHom (t.toHom v)) hr
    have h₂ := congrArg (fun m : ConjEmbedding E A => m.toHom v) hjt
    exact h₁.trans h₂
  have hbs (v : B) : b.toHom (s.toHom v) =
      p.element⁻¹ * j.toHom v * p.element := by
    have hv := congrArg (fun m : ConjEmbedding B A => m.toHom v) hs
    change b.toHom (s.toHom v) = p.element⁻¹ * j.toHom v * (p.element⁻¹)⁻¹ at hv
    rwa [inv_inv] at hv
  have ht₂ : s.comp t = c.comp f := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro v
    apply b.injective
    change b.toHom (s.toHom (t.toHom v)) = ((b.comp c).comp f).toHom v
    rw [hbs]
    change p.element⁻¹ * (j.comp t).toHom v * p.element = _
    rw [hjt, mul_assoc, p.intertwines, inv_mul_cancel_left]
  let x : Dot (a.comp r) (b.comp s) := ⟨p.element, by
    intro v
    rw [hr]
    change j.toHom v * p.element = p.element * b.toHom (s.toHom v)
    rw [hbs]
    group⟩
  let y : Dot (s.comp t) (c.comp f) := ⟨1, by intro v; rw [ht₂, mul_one, one_mul]⟩
  let z : Dot (r.comp t) (d.comp e) := ⟨1, by intro v; rw [ht₁, mul_one, one_mul]⟩
  refine ⟨r, s, t, ⟨x, finite_mixed a b r s x⟩, ⟨y, finite_mixed s c t f y⟩, z, ?_, ?_⟩
  · change conj (a.toHom (1 : G)⁻¹) (a.comp r).toHom.range = H
    rw [inv_one, map_one, conj_one, hr, hj]
  · change a.toHom (1 : G)⁻¹ * p.element * b.toHom (1 : D) = p.element
    rw [inv_one, map_one, map_one, one_mul, mul_one]

private theorem right_witness [Finite A]
    (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f) :
    let S := rightBound a b c d p.dot.element
    let B := S.map A.subtype
    ∃ (j : ConjEmbedding B A) (v : ConjEmbedding C B) (w : ConjEmbedding F B)
      (ell : Dot (b.comp c) (j.comp w)) (m : ProjectionDot.Mixed a j d v)
      (n : ProjectionDot.Mixed v w e f),
      conj m.dot.element j.toHom.range = S ∧
      rightParameter a b c d e f ell m.dot n.dot = p.dot.element := by
  intro S B
  -- Theorem 6.4(1) supplies the join construction once the middle
  -- intersection has finite index. Its ambient group is a subgroup of A.
  have hindex : Subgroup.FiniteIndex
      ((a.comp d).toHom.range.subgroupOf (a.toHom.range ⊓ S)) := inferInstance
  obtain ⟨j, v, w, ell, m, n, hj, _, _, he, hm, hn, _, _⟩ :=
    (CaseOneRightProjectionConstruction a b c d e f).1 p hindex
  refine ⟨j, v, w, ell, m, n, ?_, ?_⟩
  · have h : j = inclusion S :=
      ConjEmbedding.ext (MonoidHom.ext fun u => Subtype.ext (hj u))
    rw [hm, conj_one, h, inclusion_range]
  · unfold rightParameter
    simp only [he, hm, hn, map_one, one_mul, inv_inv]

end
end OutsideRegionsAux

theorem ParabolicExtremalOutsideRestrictionRegions : (
let P := Equiv.Perm Nat
let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H =
      iSup (fun i => MonoidHom.range
        (Equiv.Perm.ofSubtype (p := fun k : Nat => k ∈ blocks i)))
∀ {G A D F C E : Subgroup U},
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  ∀ (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let image := fun {H K : Subgroup U} (α : MackeyDiagrams.ConjEmbedding H K) =>
    MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom α)
  let conjugate := fun (h : A) (H : Subgroup A) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj h)) H
  ∀ p : MackeyDiagrams.Dot (comp a de) (comp bc f),
  let element := MackeyDiagrams.Dot.element p
  let lower := image (comp a de)
  let maximum := image a ⊓ conjugate element (image b)
  let minimum := image ad ⊔ conjugate element (image bc)
  Subgroup.FiniteIndex (Subgroup.subgroupOf lower (image a ⊓ conjugate element (image bc))) →
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let basisMap := @MackeyDiagrams.Generator.mixedMultiplicationBasis U _
  let finiteFibers := fun {X Y : Type} (q : X → Y) => ∀ z, Set.Finite {w | q w = z}
  ∃ hp : finiteFibers (basisMap a bc de f p),
  let outside := tensor (tensor (down a) (up b)) (up c)
  let inside := tensor (tensor (up d) (up e)) (down f)
  let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let identity := fun {K H : Subgroup U} (w : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) w)
  let parallel := fun {H K J L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding H K) (β : MackeyDiagrams.ConjEmbedding L H)
      (α' : MackeyDiagrams.ConjEmbedding J K) (β' : MackeyDiagrams.ConjEmbedding L J)
      (x : MackeyDiagrams.Dot (comp α β) (comp α' β')) =>
    MackeyDiagrams.LabelledDrawing.parallelUp α β α' β' [((1 : Complex), x)]
  let project := fun {K H J L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K J) (β : MackeyDiagrams.ConjEmbedding H J)
      (l : MackeyDiagrams.ConjEmbedding L K) (r : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.Dot (comp α l) (comp β r))
      (h : finiteFibers (basisMap α β l r x)) =>
    MackeyDiagrams.LabelledDrawing.compactProjection α β l r
      [((1 : Complex), (⟨x, h⟩ : MackeyDiagrams.ProjectionDot.Mixed α β l r))]
  let multiply := fun {K H J L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K J) (β : MackeyDiagrams.ConjEmbedding H J)
      (l : MackeyDiagrams.ConjEmbedding L K) (r : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.Dot (comp α l) (comp β r)) =>
    MackeyDiagrams.LabelledDrawing.mixedMultiplication α β l r [((1 : Complex), x)]
  let atRight := fun {K H J L J' : Subgroup U} (w : MackeyDiagrams.Word K H)
      {v : MackeyDiagrams.Word H J} {s : MackeyDiagrams.Word J L}
      {v' : MackeyDiagrams.Word H J'} {s' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor v s) (tensor v' s')) =>
    vertical (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate w v s))
      (vertical (horizontal (identity w) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate w v' s')))
  let Left := Σ B : {B : Subgroup U // parabolic B},
    Σ r : MackeyDiagrams.ConjEmbedding B.val G,
    Σ s : MackeyDiagrams.ConjEmbedding B.val D,
    Σ t : MackeyDiagrams.ConjEmbedding E B.val,
      MackeyDiagrams.Dot (comp a r) (comp b s) ×
      MackeyDiagrams.Dot (comp s t) (comp c f) × MackeyDiagrams.Dot (comp r t) de
  let Right := Σ B : {B : Subgroup U // parabolic B},
    Σ j : MackeyDiagrams.ConjEmbedding B.val A,
    Σ v : MackeyDiagrams.ConjEmbedding C B.val,
    Σ w : MackeyDiagrams.ConjEmbedding F B.val,
      MackeyDiagrams.Dot bc (comp j w) ×
      MackeyDiagrams.Dot ad (comp j v) × MackeyDiagrams.Dot (comp v e) (comp w f)
  let transportLeft : Left → Subgroup A := fun ⟨_, r, _, _, _, _, z⟩ =>
    conjugate (MackeyDiagrams.ConjEmbedding.toHom a (MackeyDiagrams.Dot.element z)⁻¹)
      (image (comp a r))
  let transportRight : Right → Subgroup A := fun ⟨_, j, _, _, _, m, _⟩ =>
    conjugate (MackeyDiagrams.Dot.element m) (image j)
  let leftFinite : Left → Prop := fun ⟨_, r, s, t, x, y, _⟩ =>
    finiteFibers (basisMap a b r s x) ∧ finiteFibers (basisMap s c t f y)
  let rightFinite : Right → Prop := fun ⟨_, j, v, w, _, m, n⟩ =>
    finiteFibers (basisMap a j d v m) ∧ finiteFibers (basisMap v w e f n)
  let leftProject : (l : Left) → leftFinite l → MackeyDiagrams.LabelledDrawing Complex outside inside :=
    fun ⟨_, r, s, t, x, y, z⟩ h =>
      vertical
        (horizontal
          (project a b r s x h.1)
          (identity (up c)))
        (vertical (atRight (up r) (project s c t f y h.2))
          (horizontal (parallel r t d e z)
            (identity (down f))))
  let rightProject : (r : Right) → rightFinite r → MackeyDiagrams.LabelledDrawing Complex outside inside :=
    fun ⟨_, j, v, w, ell, m, n⟩ h =>
      vertical (atRight (down a) (parallel b c j w ell))
        (vertical
          (horizontal
            (project a j d v m h.1)
            (identity (up w)))
          (atRight (up d) (project v w e f n h.2)))
  let leftMultiply : Left → MackeyDiagrams.LabelledDrawing Complex inside outside :=
    fun ⟨_, r, s, t, x, y, z⟩ =>
      vertical
        (horizontal (parallel d e r t (MackeyDiagrams.Dot.inverse z))
          (identity (down f)))
        (vertical (atRight (up r) (multiply s c t f y))
          (horizontal
            (multiply a b r s x)
            (identity (up c))))
  let rightMultiply : Right → MackeyDiagrams.LabelledDrawing Complex inside outside :=
    fun ⟨_, j, v, w, ell, m, n⟩ =>
      vertical (atRight (up d) (multiply v w e f n))
        (vertical
          (horizontal (multiply a j d v m)
            (identity (up w)))
          (atRight (down a) (parallel j w b c (MackeyDiagrams.Dot.inverse ell))))
  let targetProject : MackeyDiagrams.LabelledDrawing Complex outside inside :=
    vertical
      (vertical (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.associate (down a) (up b) (up c)))
        (horizontal (identity (down a))
          (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp b c))))
      (vertical (project a bc de f p hp)
        (horizontal (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp d e))
          (identity (down f))))
  let targetMultiply : MackeyDiagrams.LabelledDrawing Complex inside outside :=
    vertical
      (horizontal (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
        (identity (down f)))
      (vertical (multiply a bc de f p)
        (vertical
          (horizontal (identity (down a))
            (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
          (MackeyDiagrams.LabelledDrawing.ordinary
            (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))))
  let evalProject := fun (q : MackeyDiagrams.LabelledDrawing Complex outside inside) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret q) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret targetProject)
  let evalMultiply := fun (q : MackeyDiagrams.LabelledDrawing Complex inside outside) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret q) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret targetMultiply)
  let leftProjectRegions : Set (Subgroup A) :=
    {H | ∃ (l : Left) (h : leftFinite l), transportLeft l = H ∧ evalProject (leftProject l h)}
  let rightProjectRegions : Set (Subgroup A) :=
    {H | ∃ (r : Right) (h : rightFinite r), transportRight r = H ∧ evalProject (rightProject r h)}
  let leftMultiplyRegions : Set (Subgroup A) :=
    {H | ∃ l : Left, transportLeft l = H ∧ evalMultiply (leftMultiply l)}
  let rightMultiplyRegions : Set (Subgroup A) :=
    {H | ∃ r : Right, transportRight r = H ∧ evalMultiply (rightMultiply r)}
  let firstProjectionUnitFibers : Left → Prop := fun ⟨_, r, s, _, x, _, _⟩ =>
    let q := basisMap a b r s x
    ∀ z ∈ Set.range q, ∃! w, q w = z
  IsLeast rightProjectRegions minimum ∧ IsLeast rightMultiplyRegions minimum ∧
  IsGreatest leftProjectRegions maximum ∧ IsGreatest leftMultiplyRegions maximum ∧
  (∀ H : Subgroup A, parabolic (Subgroup.map (Subgroup.subtype A) H) →
    lower ≤ H → H ≤ maximum → H ∈ leftProjectRegions ∧ H ∈ leftMultiplyRegions) ∧
  (∀ (l : Left) (h : leftFinite l), evalProject (leftProject l h) →
    transportLeft l = maximum → firstProjectionUnitFibers l)
) :=
(by
  classical
  open MackeyDiagrams OutsideRegionsAux in
  intro P finitary U parabolic G A D F C E hG hA hD hF hC _hE a b c d e f
    comp bc ad de image conjugate p element lower maximum minimum index
    up down tensor basisMap finiteFibers
  let _ : Finite G := parabolic_finite hG
  let _ : Finite A := parabolic_finite hA
  let _ : Finite D := parabolic_finite hD
  let _ : Finite F := parabolic_finite hF
  let hp : finiteFibers (basisMap a bc de f p) :=
    ((EvaluationForTwoProjections a b c d e f).1 p).2.1.mpr index
  refine ⟨hp, ?_⟩
  intro outside inside vertical horizontal identity parallel project multiply atRight Left Right
    transportLeft transportRight leftFinite rightFinite leftProject rightProject leftMultiply
    rightMultiply targetProject targetMultiply evalProject evalMultiply leftProjectRegions
    rightProjectRegions leftMultiplyRegions rightMultiplyRegions firstProjectionUnitFibers
  let parameter : ProjectionDot.Mixed a bc de f := ⟨p, hp⟩
  -- Xiao, Proposition 8.6, archived original p. 38 (bc57d13777e7df14…),
  -- revised published p. 40 (6d7e885955f23ae6…). The Alphabeta Math
  -- rendering gives the proof in prose and refers to the numbered Cases
  -- 1–4 of Theorems 6.4 and 6.5. These cases fix the two directions and
  -- the two crossing orientations. Compare regions after transport into A.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-three-outside
  -- The relative-index hypothesis supplies the target fiber witness by
  -- the registered Lemma 6.3. All witness diagrams retain their vertices.
  -- Prop. 7.1's meet and join suppliers use partitions of a common support,
  -- so the local adapter pads the two block families with singleton blocks.
  obtain ⟨minParabolic, maxParabolic⟩ :=
    parabolic_region_bounds a b c d element hG hD hF hC
  -- Case 1 and its Case 3 reversal. The registered Theorem 6.4(1)
  -- constructs the right shape at the join, with dots (p⁻¹, 1, 1).
  -- Its middle index is finite in a subgroup of the finite group A.
  obtain ⟨j, v, w, ell, m, n, hj, hright⟩ :=
    right_witness a b c d e f parameter
  let rmin : Right := ⟨⟨minimum.map A.subtype, minParabolic⟩, j, v, w, ell, m.dot, n.dot⟩
  have rminFinite : rightFinite rmin := ⟨m.finite, n.finite⟩
  have minP : minimum ∈ rightProjectRegions :=
    ⟨rmin, rminFinite, hj, (right_project_eval a b c d e f parameter ell m n).2 hright⟩
  have minM : minimum ∈ rightMultiplyRegions :=
    ⟨rmin, hj, (right_mul_eval a b c d e f parameter ell m.dot n.dot).2 hright⟩
  -- Case 2 and its Case 4 reversal. The full-intersection supplier
  -- gives the maximal Case 2 witness. Its restricted-embedding construction
  -- is carried out here for every intermediate parabolic H. Finite domains
  -- justify both transfer maps, and the same dots give the opposite map.
  have leftInterval : ∀ H : Subgroup A, parabolic (H.map A.subtype) →
      lower ≤ H → H ≤ maximum → H ∈ leftProjectRegions ∧ H ∈ leftMultiplyRegions := by
    intro H hH hlo hhi
    obtain ⟨r, s, t, x, y, z, htrans, hparam⟩ := left_witness a b c d e f p H hlo hhi
    let l : Left := ⟨⟨H.map A.subtype, hH⟩, r, s, t, x.dot, y.dot, z⟩
    have hfinite : leftFinite l := ⟨x.finite, y.finite⟩
    exact ⟨⟨l, hfinite, htrans, (left_project_eval a b c d e f parameter x y z).2 hparam⟩,
      ⟨l, htrans, (left_mul_eval a b c d e f parameter x.dot y.dot z).2 hparam⟩⟩
  obtain ⟨maxP, maxM⟩ := leftInterval maximum maxParabolic (lower_le_max a b c d e f p) le_rfl
  -- Lemma 6.3 and Theorem 6.5 identify the effective group element by the
  -- unit balanced pair. The coefficient and column checks are local since
  -- the replacement suppliers package existence and equality classes.
  -- In particular no inference about internal groups is made from a mere
  -- existence of a replacement at an unrelated region.
  refine ⟨⟨minP, ?_⟩, ⟨minM, ?_⟩, ⟨maxP, ?_⟩, ⟨maxM, ?_⟩, leftInterval, ?_⟩
  · rintro H ⟨⟨⟨B, hB⟩, j, v, w, ell, m, n⟩, hm, rfl, he⟩
    have h := (right_project_eval a b c d e f parameter ell ⟨m, hm.1⟩ ⟨n, hm.2⟩).1 he
    change rightBound a b c d p.element ≤ conj m.element j.toHom.range
    rw [← h]
    exact bound_right a b c d e f ell m n
  · rintro H ⟨⟨⟨B, hB⟩, j, v, w, ell, m, n⟩, rfl, he⟩
    have h := (right_mul_eval a b c d e f parameter ell m n).1 he
    change rightBound a b c d p.element ≤ conj m.element j.toHom.range
    rw [← h]
    exact bound_right a b c d e f ell m n
  · rintro H ⟨⟨⟨B, hB⟩, r, s, t, x, y, z⟩, hx, rfl, he⟩
    have h := (left_project_eval a b c d e f parameter ⟨x, hx.1⟩ ⟨y, hx.2⟩ z).1 he
    change conj (a.toHom z.element⁻¹) (a.comp r).toHom.range ≤ leftBound a b p.element
    rw [← h]
    exact bound_left a b c d e f x y z
  · rintro H ⟨⟨⟨B, hB⟩, r, s, t, x, y, z⟩, rfl, he⟩
    have h := (left_mul_eval a b c d e f parameter x y z).1 he
    change conj (a.toHom z.element⁻¹) (a.comp r).toHom.range ≤ leftBound a b p.element
    rw [← h]
    exact bound_left a b c d e f x y z
  · rintro ⟨⟨B, hB⟩, r, s, t, x, y, z⟩ hx he hmax
    have h := (left_project_eval a b c d e f parameter ⟨x, hx.1⟩ ⟨y, hx.2⟩ z).1 he
    change conj (a.toHom z.element⁻¹) (a.comp r).toHom.range = leftBound a b p.element at hmax
    rw [← h] at hmax
    -- The first crossing's common images now come from the full
    -- intersection. The project's mixed-basis injectivity lemma applies.
    have hinj := first_injective a b c d e f x y z hmax
    change ∀ u ∈ Set.range (basisMap a b r s x), ∃! w, basisMap a b r s x w = u
    rintro _ ⟨w, rfl⟩
    exact ⟨w, rfl, fun w' hw' => hinj hw'⟩)
