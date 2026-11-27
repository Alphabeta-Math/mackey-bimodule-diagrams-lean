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
