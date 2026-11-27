import MackeyDiagrams
import Proofs.ParabolicExtremalOutsideRestrictionRegions
import Proofs.ReplacementForTwoMultiplications

set_option maxHeartbeats 2000000

namespace OutsideMultiplicationProof
open MackeyDiagrams

-- The subgroup restriction and conjugation adapters are local versions of
-- those in Proofs/ParabolicExtremalOutsideRestrictionRegions.lean.
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
private theorem lower_le_max (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) :
    (a.comp (d.comp e)).toHom.range ≤ leftBound a b p.element := by
  apply le_inf (range_comp_le a (d.comp e))
  rw [dot_ranges p]
  exact Subgroup.map_mono (range_comp_le b (c.comp f))


private theorem normalizedLeft (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) :
    let H := leftBound a b p.element
    let B := H.map A.subtype
    ∃ (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
      (x : Dot (a.comp r) (b.comp s)) (y : Dot (s.comp t) (c.comp f))
      (z : Dot (d.comp e) (r.comp t)),
      (∀ k : B, (a.toHom (r.toHom k) : U) = (k : U)) ∧
      (∀ k : B, ((p.element * b.toHom (s.toHom k) * p.element⁻¹ : A) : U) = (k : U)) ∧
      (∀ k : E, (t.toHom k : U) = ((a.comp (d.comp e)).toHom k : U)) ∧
      z.element = 1 ∧ y.element = 1 ∧ x.element = p.element := by
  intro H B
  have hlo : (a.comp (d.comp e)).toHom.range ≤ H := lower_le_max a b c d e f p
  have hhi : H ≤ leftBound a b p.element := le_rfl
  let j := inclusion H
  have hj : j.toHom.range = H := inclusion_range H
  obtain ⟨r, hr⟩ := lift_through a j (by
    rw [hj]
    exact hhi.trans inf_le_left)
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

  let z : Dot (d.comp e) (r.comp t) := ⟨1, by intro v; rw [ht₁, mul_one, one_mul]⟩
  refine ⟨r, s, t, x, y, z, ?_, ?_, fun _ => rfl, rfl, rfl, rfl⟩
  · intro k
    exact congrArg (fun i : ConjEmbedding B A => (i.toHom k : U)) hr
  · intro k
    rw [hbs]
    have h : p.element * (p.element⁻¹ * j.toHom k * p.element) * p.element⁻¹ = j.toHom k := by
      group
    rw [h]
    rfl

end

private abbrev Perm := Equiv.Perm Nat
private abbrev Finitary := Subgroup.closure {σ : Perm | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) : Subgroup Perm :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X))

private abbrev ParabolicPerm (H : Subgroup Perm) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H = ⨆ i, blockSym (blocks i)

private abbrev Parabolic (H : Subgroup Finitary) := ParabolicPerm (H.map Finitary.subtype)
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


-- Proposition 8.6 gives the attained extremal transported groups. The
-- attaining witnesses have parabolic regions. Transport is itself a
-- conjugation-induced embedding, so these two images are parabolic.
private theorem attainedBounds {G A D F C E : Subgroup Finitary}
    (hG : Parabolic G) (hA : Parabolic A) (hD : Parabolic D) (hF : Parabolic F)
    (hC : Parabolic C) (hE : Parabolic E)
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)
    (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) :
    Parabolic ((leftBound a b p.element).map A.subtype) ∧
      Parabolic ((rightBound a b c d p.element).map A.subtype) ∧
      (∀ z, Set.Finite {s | Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p s = z}) := by
  let _ : Finite A := parabolic_finite hA
  rcases ParabolicExtremalOutsideRestrictionRegions hG hA hD hF hC hE a b c d e f p
    (by infer_instance) with ⟨hfinite, -, hRight, -, hLeft, -, -⟩
  rcases hLeft.1 with ⟨⟨B, r, s, t, x, y, z⟩, hB, _⟩
  rcases hRight.1 with ⟨⟨B', j, v, w, ell, m, n⟩, hP, _⟩
  change conj (a.toHom z.element⁻¹) (a.comp r).toHom.range = leftBound a b p.element at hB
  change conj m.element j.toHom.range = rightBound a b c d p.element at hP
  refine ⟨?_, ?_, hfinite⟩
  · rw [← hB, ← conjugated_range]
    exact parabolic_embedding _ B.property
  · rw [← hP, ← conjugated_range]
    exact parabolic_embedding _ B'.property

end OutsideMultiplicationProof
