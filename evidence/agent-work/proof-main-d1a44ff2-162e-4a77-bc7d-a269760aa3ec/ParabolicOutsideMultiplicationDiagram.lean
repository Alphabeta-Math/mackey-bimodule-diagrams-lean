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


-- The singleton basis calculations use the multiplication conjunct of the
-- registered MixedCrossingFiniteFiberConvention and the shared merge–dot–split
-- expansion. These local specializations follow the basis calculation in
-- Proofs/ParabolicExtremalOutsideRestrictionRegions.lean.
noncomputable section

variable {U : Type*} [Group U] {K H J L M G A D F C E B B' : Subgroup U}

private abbrev Vec (X : Type*) := X →₀ Complex
private abbrev ev {p q : Word K H} (d : LabelledDrawing Complex p q) :=
  d.interpret.eval.toLinearMap

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
private theorem singleton_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) :
    ev (.parallelUp a b c d [(1,p)]) =
      (Diagram.parallelUp (R := Complex) a b c d p).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.parallelUp (R := Complex) a b c d p)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev bottom := ((Word.down a).tensor (.up b)).tensor (.up c)
private abbrev top := ((Word.up d).tensor (.up e)).tensor (.down f)
private abbrev mergedBottom := (Word.down a).tensor (.up (b.comp c))
private abbrev mergedTop := (Word.up (d.comp e)).tensor (.down f)

private abbrev splitBottom : LabelledDrawing Complex (mergedBottom a b c) (bottom a b c) :=
  before (.horizontal (drawId (.down a)) (.trivalent (.splitUp b c)))
    (.ordinary (.unassociate (.down a) (.up b) (.up c)))

private abbrev mergeTop : LabelledDrawing Complex (top d e f) (mergedTop d e f) :=
  .horizontal (.trivalent (.mergeUp d e)) (drawId (.down f))
private theorem mixedPair_coord {K H P : Subgroup U}
    (α : ConjEmbedding K P) (β : ConjEmbedding H P) (x y : P) :
    pair (.down α) (.up β) x y = Generator.mixedPair α β (x * y) := by
  apply (Generator.mixedEquiv α β).injective
  change x * y = Generator.mixedProduct α β (Generator.mixedPair α β (x * y))
  rw [Generator.mixedProduct_mixedPair]
private abbrev mergeBottom : LabelledDrawing Complex (bottom a b c) (mergedBottom a b c) :=
  before (.ordinary (.associate (.down a) (.up b) (.up c)))
    (.horizontal (drawId (.down a)) (.trivalent (.mergeUp b c)))

private abbrev splitTop : LabelledDrawing Complex (mergedTop d e f) (top d e f) :=
  .horizontal (.trivalent (.splitUp d e)) (drawId (.down f))
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
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (d.comp e) (r.comp t)) :=
  before (atLeft (.parallelUp d e r t [(1,z)]) (.down f))
    (before (atRight (.up r) (.mixedMultiplication s c t f [(1,y)]))
      (atLeft (.mixedMultiplication a b r s [(1,x)]) (.up c)))

private abbrev rightMulDrawing (j : ConjEmbedding B A) (v : ConjEmbedding C B)
    (w : ConjEmbedding F B) (ell : Dot (j.comp w) (b.comp c))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :=
  before (atRight (.up d) (.mixedMultiplication v w e f [(1,n)]))
    (before (atLeft (.mixedMultiplication a j d v [(1,m)]) (.up w))
      (atRight (.down a) (.parallelUp j w b c [(1,ell)])))

-- The forward columns of Xiao's Theorem 6.5 specialize to the same
-- parameter products as the backward coefficient calculation of Lemma 6.3.
private theorem push_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (d.comp e) (r.comp t)) (g : G) (h : F) :
    ev (framedMul a b c d e f (leftMulDrawing a b c d e f r s t x y z))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * (a.toHom z.element * x.element * b.toHom y.element) * (b.comp c).toHom h)) := by
  let g' := g * z.element
  let t' := y.element * c.toHom h
  let q := a.toHom g' * x.element * b.toHom t'
  have h₁ := push_atLeft (.parallelUp d e r t [(1,z)])
    (q := .down f) (pair (.up d) (.up e) g 1) h (pair (.up r) (.up t) g' 1) (by
      simpa only [g', map_one, mul_one] using push_parallel d e r t z g 1)
  have h₂ := push_atRight (p := Word.up r) (.mixedMultiplication s c t f [(1,y)])
    g' 1 h t' 1 (by simpa only [t', map_one, one_mul] using push_mixed s c t f y 1 h)
  have h₃ := push_atLeft (.mixedMultiplication a b r s [(1,x)])
    (q := .up c) (pair (.up r) (.down s) g' t') 1
    (pair (.down a) (.up b) q 1) (push_mixed a b r s x g' t')
  have h₄ := push_mergeBottom a b c q 1 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  simpa only [q, g', t', map_one, one_mul, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc] using hEval

private theorem push_right {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (j.comp w) (b.comp c))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) (g : G) (h : F) :
    ev (framedMul a b c d e f (rightMulDrawing a b c d e f j v w ell m n))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * (m.element * j.toHom n.element * ell.element) * (b.comp c).toHom h)) := by
  let n' := n.element * w.toHom h
  let q := a.toHom g * m.element * j.toHom n'
  have h₁ := push_atRight (p := Word.up d) (.mixedMultiplication v w e f [(1,n)])
    g 1 h n' 1 (by simpa only [n', map_one, one_mul] using push_mixed v w e f n 1 h)
  have h₂ := push_atLeft (.mixedMultiplication a j d v [(1,m)])
    (q := .up w) (pair (.up d) (.down v) g n') 1
    (pair (.down a) (.up j) q 1) (push_mixed a j d v m g n')
  have h₃ := push_atRight (p := Word.down a) (.parallelUp j w b c [(1,ell)])
    q 1 1 ell.element 1 (by
      simpa only [map_one, mul_one, one_mul] using push_parallel j w b c ell 1 1)
  have h₄ := push_mergeBottom a b c q ell.element 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  have he := ell.intertwines h
  simp only [ConjEmbedding.comp_apply] at he
  simpa only [q, n', map_one, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc, he] using hEval


-- These are the boundary inverse checks used in the registered proof of
-- Theorem 6.5, specialized to the shared trivalent drawings at this boundary.
private theorem splitRightInverse :
    let S := (splitTop d e f).interpret.eval
    let M := (Diagram.horizontal (R := Complex) (Diagram.mergeUp d e)
      (Diagram.id (.down f))).eval
    M.vertical S = Biset.Hom.id (top d e f).basis := by
  dsimp only
  change ((Diagram.mergeUp (R := Complex) d e).eval.horizontal (Diagram.id (.down f)).eval).vertical
    ((Diagram.splitUp d e).eval.horizontal (Diagram.id (.down f)).eval) = _
  rw [Biset.Hom.horizontal_vertical]
  change (((Diagram.mergeUp (R := Complex) d e).vertical (Diagram.splitUp d e)).eval).horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem mergeLeftInverse :
    let M := (mergeBottom a b c).interpret.eval
    let S := ((Diagram.horizontal (R := Complex) (Diagram.id (.down a))
      (Diagram.splitUp b c)).vertical (Diagram.unassociate (.down a) (.up b) (.up c))).eval
    M.vertical S = Biset.Hom.id (bottom a b c).basis := by
  dsimp only
  change ((Biset.associate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex).vertical
    ((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.mergeUp b c).eval)).vertical
    (((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.splitUp b c).eval).vertical
      (Biset.unassociate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex)) = _
  refine Biset.Hom.cancel_middle _ _ _ _ ?_ Biset.associate_unassociate
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id (Word.down a).basis).horizontal
    (((Diagram.mergeUp (R := Complex) b c).vertical (Diagram.splitUp b c)).eval) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem framedExt
    {D₁ D₂ : LabelledDrawing Complex (top d e f) (bottom a b c)}
    (h : ∀ (g : G) (k : F), ev (framedMul a b c d e f D₁) (col (pair (.up (d.comp e)) (.down f) g k)) =
      ev (framedMul a b c d e f D₂) (col (pair (.up (d.comp e)) (.down f) g k))) :
    D₁.interpret.eval = D₂.interpret.eval := by
  have eq : (framedMul a b c d e f D₁).interpret.eval =
      (framedMul a b c d e f D₂).interpret.eval := by
    apply Biset.Hom.ext
    apply Finsupp.lhom_ext
    intro z coef
    refine Quotient.inductionOn z fun ⟨g,k⟩ => ?_
    change ev (framedMul a b c d e f D₁)
        (Finsupp.single (pair (.up (d.comp e)) (.down f) g k) coef) =
      ev (framedMul a b c d e f D₂) (Finsupp.single (pair (.up (d.comp e)) (.down f) g k) coef)
    have hs : Finsupp.single (pair (.up (d.comp e)) (.down f) g k) coef =
        coef • col (pair (.up (d.comp e)) (.down f) g k) := by
      rw [col, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, h]
  let P := (Diagram.horizontal (R := Complex) (Diagram.mergeUp d e)
    (Diagram.id (.down f))).eval
  let Q := ((Diagram.horizontal (R := Complex) (Diagram.id (.down a))
      (Diagram.splitUp b c)).vertical (Diagram.unassociate (.down a) (.up b) (.up c))).eval
  let S := (splitTop d e f).interpret.eval
  let T := (mergeBottom a b c).interpret.eval
  change S.vertical (D₁.interpret.eval.vertical T) = S.vertical (D₂.interpret.eval.vertical T) at eq
  have hc := congrArg (fun x => (P.vertical x).vertical Q) eq
  change (P.vertical (S.vertical (D₁.interpret.eval.vertical T))).vertical Q =
    (P.vertical (S.vertical (D₂.interpret.eval.vertical T))).vertical Q at hc
  have hP : P.vertical S = Biset.Hom.id (top d e f).basis := splitRightInverse d e f
  have hQ : T.vertical Q = Biset.Hom.id (bottom a b c).basis := mergeLeftInverse a b c
  simpa only [← Biset.Hom.vertical_assoc P S, hP, Biset.Hom.id_vertical,
    Biset.Hom.vertical_assoc _ T Q, hQ, Biset.Hom.vertical_id] using hc

private abbrev multiplierFormula (drawing : LabelledDrawing Complex (top d e f) (bottom a b c))
    (M : MonoidAlgebra Complex A) :=
  ∀ (g : G) (k : F),
    ev (framedMul a b c d e f drawing) (col (pair (.up (d.comp e)) (.down f) g k)) =
      Finsupp.mapDomain (Generator.mixedPair a (b.comp c))
        (MonoidAlgebra.single (a.toHom g) 1 * M *
          MonoidAlgebra.single ((b.comp c).toHom k) 1).coeff

-- Theorem 6.5 gives the multiplier for each diagram. Identify that
-- multiplier by the unit balanced pair, then apply its formula to all pairs.
private theorem specializeMultiplier
    (drawing : LabelledDrawing Complex (top d e f) (bottom a b c))
    (M : MonoidAlgebra Complex A) (hm : multiplierFormula a b c d e f drawing M)
    (p : A)
    (hunit : ev (framedMul a b c d e f drawing) (col (pair (.up (d.comp e)) (.down f) 1 1)) =
      col (Generator.mixedPair a (b.comp c) p)) :
    ∀ (g : G) (k : F),
      ev (framedMul a b c d e f drawing) (col (pair (.up (d.comp e)) (.down f) g k)) =
        col (Generator.mixedPair a (b.comp c) (a.toHom g * p * (b.comp c).toHom k)) := by
  have hm₁ := hm 1 1
  rw [hunit] at hm₁
  have he : M = MonoidAlgebra.single p 1 := by
    apply MonoidAlgebra.coeff_injective
    have hinj : Function.Injective (Generator.mixedPair a (b.comp c)) :=
      (Generator.mixedEquiv a (b.comp c)).symm.injective
    apply Finsupp.mapDomain_injective hinj
    change Finsupp.mapDomain (Generator.mixedPair a (b.comp c)) M.coeff = _
    simpa only [map_one, show MonoidAlgebra.single (1 : A) (1 : Complex) = 1 from rfl,
      one_mul, mul_one, MonoidAlgebra.coeff_single, Finsupp.mapDomain_single, col] using hm₁.symm
  rw [he] at hm
  intro g k
  simpa only [MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.coeff_single,
    Finsupp.mapDomain_single, col] using hm g k

end
end OutsideMultiplicationProof

theorem ParabolicOutsideMultiplicationDiagram : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
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
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  ∀ p : MackeyDiagrams.Dot (comp a de) (comp bc f),
  let element := MackeyDiagrams.Dot.element p
  let conjugate := fun (k : A) (H : Subgroup A) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj k)) H
  let Bmax := Subgroup.map (Subgroup.subtype A)
    (MonoidHom.range (hom a) ⊓ conjugate element (MonoidHom.range (hom b)))
  let Pp := Subgroup.map (Subgroup.subtype A)
    (MonoidHom.range (hom ad) ⊔ conjugate element (MonoidHom.range (hom bc)))
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let identity := fun {K H : Subgroup U} (w : MackeyDiagrams.Word K H) =>
    ordinary (MackeyDiagrams.Diagram.id w)
  let eval := fun {K H : Subgroup U} {v w : MackeyDiagrams.Word K H}
      (drawing : MackeyDiagrams.LabelledDrawing Complex v w) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let bottom := tensor (tensor (up d) (up e)) (down f)
  let top := tensor (tensor (down a) (up b)) (up c)
  let parallel := fun {H K J L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding H K) (β : MackeyDiagrams.ConjEmbedding L H)
      (α' : MackeyDiagrams.ConjEmbedding J K) (β' : MackeyDiagrams.ConjEmbedding L J)
      (x : MackeyDiagrams.Dot (comp α β) (comp α' β')) =>
    MackeyDiagrams.LabelledDrawing.parallelUp α β α' β' [((1 : Complex), x)]
  let multiply := fun {K H J L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K J) (β : MackeyDiagrams.ConjEmbedding H J)
      (l : MackeyDiagrams.ConjEmbedding L K) (r : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.Dot (comp α l) (comp β r)) =>
    MackeyDiagrams.LabelledDrawing.mixedMultiplication α β l r [((1 : Complex), x)]
  let atRight := fun {K H J L J' : Subgroup U} (w : MackeyDiagrams.Word K H)
      {v : MackeyDiagrams.Word H J} {s : MackeyDiagrams.Word J L}
      {v' : MackeyDiagrams.Word H J'} {s' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor v s) (tensor v' s')) =>
    vertical (ordinary (MackeyDiagrams.Diagram.associate w v s))
      (vertical (horizontal (identity w) crossing)
        (ordinary (MackeyDiagrams.Diagram.unassociate w v' s')))
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex (tensor (up de) (down f)) bottom :=
    horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp d e))
      (identity (down f))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top (tensor (down a) (up bc)) :=
    vertical (ordinary (MackeyDiagrams.Diagram.associate (down a) (up b) (up c)))
      (horizontal (identity (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp b c)))
  let evaluatesAsQp := fun (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    ∀ (g : G) (h : F),
      MackeyDiagrams.Biset.Hom.toLinearMap
        (eval (vertical splitBottom (vertical diagram mergeTop)))
        (Finsupp.single (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction de)
          (MackeyDiagrams.Biset.restriction f) g h) 1) =
      Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc
        (hom a g * element * hom bc h)) 1
  parabolic Bmax ∧ parabolic Pp ∧
  ∃ (r : MackeyDiagrams.ConjEmbedding Bmax G)
    (s : MackeyDiagrams.ConjEmbedding Bmax D)
    (t : MackeyDiagrams.ConjEmbedding E Bmax)
    (u : MackeyDiagrams.ConjEmbedding Pp A)
    (v : MackeyDiagrams.ConjEmbedding C Pp)
    (w : MackeyDiagrams.ConjEmbedding F Pp)
    (z : MackeyDiagrams.Dot de (comp r t))
    (y : MackeyDiagrams.Dot (comp s t) (comp c f))
    (x : MackeyDiagrams.Dot (comp a r) (comp b s))
    (n : MackeyDiagrams.Dot (comp v e) (comp w f))
    (m : MackeyDiagrams.Dot ad (comp u v))
    (ℓ : MackeyDiagrams.Dot (comp u w) bc),
    (∀ k : Bmax, ((hom a (hom r k) : A) : U) = (k : U)) ∧
    (∀ k : Bmax, ((element * hom b (hom s k) * element⁻¹ : A) : U) = (k : U)) ∧
    (∀ k : E, (hom t k : U) = ((hom (comp a de) k : A) : U)) ∧
    (∀ k : Pp, ((hom u k : A) : U) = (k : U)) ∧
    (∀ k : C, (hom v k : U) = ((hom ad k : A) : U)) ∧
    (∀ k : F, (hom w k : U) = ((element * hom bc k * element⁻¹ : A) : U)) ∧
    MackeyDiagrams.Dot.element z = 1 ∧ MackeyDiagrams.Dot.element y = 1 ∧
    MackeyDiagrams.Dot.element x = element ∧
    MackeyDiagrams.Dot.element n = 1 ∧ MackeyDiagrams.Dot.element m = 1 ∧
    MackeyDiagrams.Dot.element ℓ = element ∧
    let left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical (horizontal (parallel d e r t z) (identity (down f)))
        (vertical (atRight (up r) (multiply s c t f y))
          (horizontal (multiply a b r s x)
            (identity (up c))))
    let right : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical (atRight (up d) (multiply v w e f n))
        (vertical (horizontal (multiply a u d v m)
          (identity (up w)))
          (atRight (down a) (parallel u w b c ℓ)))
    eval left = eval right ∧ evaluatesAsQp left
) :=
(by
  classical
  open MackeyDiagrams OutsideMultiplicationProof in
  intro finitary U parabolic G A D F C E hG hA hD hF hC hE a b c d e f
    comp hom bc ad de p element conjugate Bmax Pp up down tensor vertical horizontal
    ordinary identity eval bottom top parallel multiply atRight splitBottom mergeTop evaluatesAsQp
  -- Xiao, §8.3, Proposition 8.6 and the following multiplication figure,
  -- archived original pp. 38–39 and published 28 November revision pp. 40–41
  -- (SHA-256 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-three-outside
  -- This endpoint has no linked numbered Alphabeta Math proof. The author’s
  -- mirror gives a prose proof here. Use its numbered Cases 1
  -- and 2 of Theorem 6.4 for the regions, and Cases 3 and 4 of Theorem 6.5
  -- for the reversed arrows. The extremal result supplies transported
  -- attainment. The displayed label equations require specific witnesses.
  obtain ⟨parB, parP, hfinite⟩ := attainedBounds hG hA hD hF hC hE a b c d e f p
  -- Case 2 transported by a: restrict a⁻¹ and b⁻¹ after undoing conjugation
  -- by p. The intertwining of p puts (ade)(E) inside the full intersection.
  obtain ⟨r, s, t, x, y, z, hr, hs, ht, hz, hy, hx⟩ :=
    normalizedLeft a b c d e f p
  -- Case 1: finite A supplies the middle relative index. Its projection
  -- witness packages the finite fibers; the reversed vertices only use
  -- their eligible labels. Reversal inverts the parallel dot p⁻¹.
  let _ : Finite A := parabolic_finite hA
  let q : ProjectionDot.Mixed a bc de f := ⟨p, hfinite⟩
  have hindex : Subgroup.FiniteIndex (ad.toHom.range.subgroupOf
        (a.toHom.range ⊓ rightBound a b c d element)) := inferInstance
  obtain ⟨j, v, w, l, m, n, hj, hv, hw, hl, hm, hn, _, _⟩ :=
    (CaseOneRightProjectionConstruction a b c d e f).1 q hindex
  have hv' (k : C) : (v.toHom k : U) = ((ad.toHom k : A) : U) :=
    (hj (v.toHom k)).symm.trans (congrArg Subtype.val (hv k))
  have hw' (k : F) : (w.toHom k : U) = ((element * bc.toHom k * element⁻¹ : A) : U) :=
    (hj (w.toHom k)).symm.trans (congrArg Subtype.val (hw k))
  have hl' : l.inverse.element = element := by
    change l.element⁻¹ = element
    rw [hl, inv_inv]
  refine ⟨parB, parP, r, s, t, j, v, w, z, y, x, n.dot, m.dot, l.inverse,
    hr, hs, ht, hj, hv', hw', hz, hy, hx, hn, hm, hl', ?_⟩
  intro left right
  -- Cases 3 and 4 give the group-algebra multiplier form on the merged
  -- boundary. Instantiate it at these exact typed crossings. Compute the
  -- multiplier by applying each diagram to the unit balanced pair. The
  -- checked MixedCrossingFiniteFiberConvention supplies the weighted
  -- multiplication columns using the same mixedMultiplicationBasis map.
  let singleton := fun {K H : Subgroup U} {i₁ i₂ : ConjEmbedding H K}
      (k : Dot i₁ i₂) => (Finsupp.single k 1 : DotLabel Complex i₁ i₂)
  have hterms {K H : Subgroup U} {i₁ i₂ : ConjEmbedding H K} (k : Dot i₁ i₂) :
      DotLabel.terms (singleton k) = [(1, k)] := by simp [singleton, DotLabel.terms]
  have leftSupplier := (ReplacementForTwoMultiplications a b c d e f).1
    ⟨Bmax, r, s, t, singleton z, singleton y, singleton x⟩
  have rightSupplier := (ReplacementForTwoMultiplications a b c d e f).2.1
    ⟨Pp, j, v, w, singleton n.dot, singleton m.dot, singleton l.inverse⟩
  change ∃ M : MonoidAlgebra Complex A, _ ∧ _ at leftSupplier rightSupplier
  obtain ⟨ML, _, hL⟩ := leftSupplier
  obtain ⟨MR, _, hR⟩ := rightSupplier
  dsimp only at hL hR
  simp only [hterms] at hL hR
  have leftUnit : ev (framedMul a b c d e f left) (col (pair (.up de) (.down f) 1 1)) =
      col (Generator.mixedPair a bc element) := by
    simpa only [hz, hy, hx, map_one, mul_one, one_mul] using
      push_left a b c d e f x y z 1 1
  have rightUnit : ev (framedMul a b c d e f right) (col (pair (.up de) (.down f) 1 1)) =
      col (Generator.mixedPair a bc element) := by
    simpa only [hn, hm, hl', map_one, mul_one, one_mul] using
      push_right a b c d e f l.inverse m.dot n.dot 1 1
  have hLeft := specializeMultiplier a b c d e f left ML hL element leftUnit
  have hRight := specializeMultiplier a b c d e f right MR hR element rightUnit
  -- Boundary merges and splits are inverse after evaluation. The
  -- singleton columns therefore determine equality at the original
  -- three-strand boundary, with all marked vertices still present.
  exact ⟨framedExt a b c d e f (fun g k => (hLeft g k).trans (hRight g k).symm), hLeft⟩)

#print axioms ParabolicOutsideMultiplicationDiagram
