import Mathlib
import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
import Proofs.ParabolicExtremalOutsideRestrictionRegions

set_option maxHeartbeats 2000000

-- The compiled prerequisites keep their calculation lemmas private.
-- Mathlib reexports Batteries' open-private command, which lets these
-- adapters refer to the checked declarations in their original modules.
open private parabolic_region_bounds parabolic_finite left_project_eval right_project_eval
  left_bound_transport dot_ranges range_comp_le conj OutsideRegionsAux.conj_mul first_injective lower_le_max
  leftParameter rightParameter leftBound from Proofs.ParabolicExtremalOutsideRestrictionRegions

open private inclusion inclusion_range lift_through conjugated conjugated_range restrictTo
  finite_mixed conj_one from Proofs.ParabolicExtremalOutsideRestrictionRegions

namespace ParabolicCaseTwoProjectionFiberIndicesAux

open MackeyDiagrams

variable {U : Type*} [Group U]

private theorem crossingFiberSize {K H P L : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (p : ProjectionDot.Mixed a b l r) :
    ∀ z ∈ Set.range (Generator.mixedMultiplicationBasis a b l r p.dot),
      Nat.card {w // Generator.mixedMultiplicationBasis a b l r p.dot w = z} =
        (a.comp l).toHom.range.relIndex (leftBound a b p.dot.element) := by
  intro z hz
  -- Lemma 6.3 and (6.1). Insert identities to use the registered calculation
  -- for one crossing. The mixed basis coordinate equivalence preserves fibers.
  have h := (EvaluationForTwoProjections a b (ConjEmbedding.id H) l (ConjEmbedding.id L) r).2.1
    p (Generator.mixedProduct a b z) |>.2 (by
      obtain ⟨w, rfl⟩ := hz
      exact ⟨w, rfl⟩)
  refine (Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))).trans h
  exact ⟨congrArg (Generator.mixedProduct a b), fun he => (Generator.mixedEquiv a b).injective he⟩

private theorem mapConjugate {X Y : Type*} [Group X] [Group Y]
    (m : X →* Y) (g : X) (H : Subgroup X) :
    (conj g H).map m = conj (m g) (H.map m) := by
  change (H.map (MulAut.conj g).toMonoidHom).map m =
    (H.map m).map (MulAut.conj (m g)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext u
  change m (g * u * g⁻¹) = m g * m u * (m g)⁻¹
  simp

section
variable {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)
variable {r : ConjEmbedding B G} {s : ConjEmbedding B D} {t : ConjEmbedding E B}

private theorem transportIndices
    (x : Dot (a.comp r) (b.comp s)) (y : Dot (s.comp t) (c.comp f))
    (z : Dot (r.comp t) (d.comp e))
    (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f))
    (hParameter : leftParameter a b c d e f x y z = p.element) :
    let H := conj (a.toHom z.element⁻¹) (a.comp r).toHom.range
    let other := conj p.element (b.comp c).toHom.range
    let lower := (a.comp (d.comp e)).toHom.range
    let maximum := leftBound a b p.element
    lower ≤ H ∧ H ≤ maximum ∧ lower ≤ H ⊓ other ∧
      (a.comp r).toHom.range.relIndex (leftBound a b x.element) = H.relIndex maximum ∧
      (s.comp t).toHom.range.relIndex (leftBound s c y.element) = lower.relIndex (H ⊓ other) := by
  intro H other lower maximum
  let q := a.toHom z.element⁻¹
  let k := q * x.element
  have hk : k * b.toHom y.element = p.element := hParameter
  have hMaximum : conj q (leftBound a b x.element) = maximum :=
    (left_bound_transport a b x.element z.element⁻¹ y.element).trans
      (congrArg (leftBound a b) hk)
  have hSub : (a.comp r).toHom.range ≤ leftBound a b x.element := by
    refine le_inf (range_comp_le a r) ?_
    rw [dot_ranges x]
    exact Subgroup.map_mono (range_comp_le b s)
  have hFirst : (a.comp r).toHom.range.relIndex (leftBound a b x.element) =
      H.relIndex maximum := by
    rw [← hMaximum]
    exact (Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj q).injective).symm
  -- For the second crossing the injection is b followed by conjugation
  -- by a(z⁻¹)x. The y-conjugate of c(F) then maps to p(bc)(F)p⁻¹.
  let φ : D →* A := (MulAut.conj k).toMonoidHom.comp b.toHom
  have hφ : Function.Injective φ := (MulAut.conj k).injective.comp b.injective
  have φ_map (S : Subgroup D) : S.map φ = conj k (S.map b.toHom) :=
    (Subgroup.map_map _ _ _).symm
  have hImage {J : Subgroup U} (m : ConjEmbedding J B) :
      (s.comp m).toHom.range.map φ = conj q (a.comp (r.comp m)).toHom.range := by
    rw [φ_map, MonoidHom.map_range]
    change conj (q * x.element) (b.comp (s.comp m)).toHom.range = _
    let dot : Dot (a.comp (r.comp m)) (b.comp (s.comp m)) :=
      ⟨x.element, fun v => x.intertwines (m.toHom v)⟩
    rw [← OutsideRegionsAux.conj_mul]
    exact congrArg (conj q) (dot_ranges dot).symm
  have hs : s.toHom.range.map φ = H := hImage (ConjEmbedding.id B)
  have hc : (conj y.element c.toHom.range).map φ = other := by
    rw [φ_map, mapConjugate, MonoidHom.map_range, OutsideRegionsAux.conj_mul, hk]
    rfl
  have hLower : (s.comp t).toHom.range.map φ = lower := by
    rw [hImage]
    have h := congrArg (fun S => conj q (S.map a.toHom)) (dot_ranges z)
    change conj q ((r.comp t).toHom.range.map a.toHom) =
      conj q ((conj z.element (d.comp e).toHom.range).map a.toHom) at h
    rw [mapConjugate, OutsideRegionsAux.conj_mul] at h
    change _ = conj (a.toHom z.element⁻¹ * a.toHom z.element) _ at h
    rw [← map_mul, inv_mul_cancel, map_one] at h
    change conj q ((r.comp t).toHom.range.map a.toHom) =
      conj 1 ((d.comp e).toHom.range.map a.toHom) at h
    rw [MonoidHom.map_range, MonoidHom.map_range] at h
    rw [conj_one] at h
    exact h
  have hSecondUpper : (leftBound s c y.element).map φ = H ⊓ other := by
    change (s.toHom.range ⊓ conj y.element c.toHom.range).map φ = _
    rw [Subgroup.map_inf _ _ _ hφ, hs, hc]
  have hSecondLower : (s.comp t).toHom.range ≤ leftBound s c y.element := by
    refine le_inf (range_comp_le s t) ?_
    rw [dot_ranges y]
    exact Subgroup.map_mono (range_comp_le c f)
  have hBoth : lower ≤ H ⊓ other := by
    rw [← hLower, ← hSecondUpper]
    exact Subgroup.map_mono hSecondLower
  refine ⟨hBoth.trans inf_le_left, ?_, hBoth, hFirst, ?_⟩
  · rw [← hMaximum]
    exact Subgroup.map_mono hSub
  · rw [← hLower, ← hSecondUpper]
    exact (Subgroup.relIndex_map_map_of_injective _ _ hφ).symm

-- Keep the three actual labels of the restricted-embedding construction
-- from Proposition 8.6 for the maximal witness requested by this endpoint.
private theorem labelledLeftWitness [Finite G] [Finite D] [Finite F]
    (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) (H : Subgroup A)
    (hlo : (a.comp (d.comp e)).toHom.range ≤ H) (hhi : H ≤ leftBound a b p.element) :
    let B := H.map A.subtype
    ∃ (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
      (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
      (z : Dot (r.comp t) (d.comp e)),
      conj (a.toHom z.element⁻¹) (a.comp r).toHom.range = H ∧
        leftParameter a b c d e f x.dot y.dot z = p.element ∧
        x.dot.element = p.element ∧ y.dot.element = 1 ∧ z.element = 1 := by
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
      _ = _ := by rw [OutsideRegionsAux.conj_mul, inv_mul_cancel, conj_one]
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
  refine ⟨r, s, t, ⟨x, finite_mixed a b r s x⟩, ⟨y, finite_mixed s c t f y⟩, z, ?_, ?_, rfl, rfl, rfl⟩
  · change conj (a.toHom (1 : G)⁻¹) (a.comp r).toHom.range = H
    rw [inv_one, map_one, conj_one, hr, hj]
  · change a.toHom (1 : G)⁻¹ * p.element * b.toHom (1 : D) = p.element
    rw [inv_one, map_one, map_one, one_mul, mul_one]

end
end ParabolicCaseTwoProjectionFiberIndicesAux

theorem ParabolicCaseTwoProjectionFiberIndices : (
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
  let ade := comp a de
  let image := fun {H K : Subgroup U} (α : MackeyDiagrams.ConjEmbedding H K) =>
    MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom α)
  let conjugate := fun (g : A) (H : Subgroup A) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) H
  ∀ p : MackeyDiagrams.Dot ade (comp bc f),
  let element := MackeyDiagrams.Dot.element p
  let lower := image ade
  let other := conjugate element (image bc)
  let maximum := image a ⊓ conjugate element (image b)
  let minimum := image ad ⊔ other
  let rightRegion := Subgroup.map (Subgroup.subtype A) minimum
  let basisMap := @MackeyDiagrams.Generator.mixedMultiplicationBasis U _
  let finiteFibers := fun {X Y : Type} (q : X → Y) => ∀ z, Set.Finite {w | q w = z}
  let fiberSize := fun {X Y : Type} (q : X → Y) (n : Nat) =>
    ∀ z ∈ Set.range q, Nat.card {w : X // q w = z} = n
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
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
  let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex outside inside) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let atRight := fun {K H J L J' : Subgroup U} (w : MackeyDiagrams.Word K H)
      {v : MackeyDiagrams.Word H J} {s : MackeyDiagrams.Word J L}
      {v' : MackeyDiagrams.Word H J'} {s' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor v s) (tensor v' s')) =>
    vertical (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate w v s))
      (vertical (horizontal (identity w) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate w v' s')))
  let target : finiteFibers (basisMap a bc de f p) →
      MackeyDiagrams.LabelledDrawing Complex outside inside := fun hp =>
    vertical
      (vertical (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.associate (down a) (up b) (up c)))
        (horizontal (identity (down a))
          (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp b c))))
      (vertical (project a bc de f p hp)
        (horizontal
          (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp d e))
          (identity (down f))))
  let Left := Σ B : {B : Subgroup U // parabolic B},
    Σ r : MackeyDiagrams.ConjEmbedding B.val G,
    Σ s : MackeyDiagrams.ConjEmbedding B.val D,
    Σ t : MackeyDiagrams.ConjEmbedding E B.val,
      MackeyDiagrams.Dot (comp a r) (comp b s) ×
      MackeyDiagrams.Dot (comp s t) (comp c f) ×
      MackeyDiagrams.Dot (comp r t) de
  let Right := Σ j : MackeyDiagrams.ConjEmbedding rightRegion A,
    Σ v : MackeyDiagrams.ConjEmbedding C rightRegion,
    Σ w : MackeyDiagrams.ConjEmbedding F rightRegion,
      MackeyDiagrams.Dot bc (comp j w) ×
      MackeyDiagrams.Dot ad (comp j v) ×
      MackeyDiagrams.Dot (comp v e) (comp w f)
  let transport : Left → Subgroup A := fun ⟨_, r, _, _, _, _, z⟩ =>
    conjugate (MackeyDiagrams.ConjEmbedding.toHom a (MackeyDiagrams.Dot.element z)⁻¹)
      (image (comp a r))
  let leftFinite : Left → Prop := fun ⟨_, r, s, t, x, y, _⟩ =>
    finiteFibers (basisMap a b r s x) ∧ finiteFibers (basisMap s c t f y)
  let rightFinite : Right → Prop := fun ⟨j, v, w, _, m, n⟩ =>
    finiteFibers (basisMap a j d v m) ∧ finiteFibers (basisMap v w e f n)
  let rightLabels : Right → Prop := fun ⟨j, v, w, ell, m, n⟩ =>
    (∀ k : rightRegion, (MackeyDiagrams.ConjEmbedding.toHom j k : U) = (k : U)) ∧
    comp j v = ad ∧
    (∀ h : F, MackeyDiagrams.ConjEmbedding.toHom (comp j w) h =
      MulAut.conj element (MackeyDiagrams.ConjEmbedding.toHom bc h)) ∧
    MackeyDiagrams.Dot.element ell = element⁻¹ ∧
    MackeyDiagrams.Dot.element m = 1 ∧ MackeyDiagrams.Dot.element n = 1
  let left : (l : Left) → leftFinite l → MackeyDiagrams.LabelledDrawing Complex outside inside :=
    fun ⟨_, r, s, t, x, y, z⟩ h =>
      vertical
        (horizontal (project a b r s x h.1) (identity (up c)))
        (vertical (atRight (up r) (project s c t f y h.2))
          (horizontal (parallel r t d e z) (identity (down f))))
  let right : (r : Right) → rightFinite r → MackeyDiagrams.LabelledDrawing Complex outside inside :=
    fun ⟨j, v, w, ell, m, n⟩ h =>
      vertical (atRight (down a) (parallel b c j w ell))
        (vertical
          (horizontal (project a j d v m h.1) (identity (up w)))
          (atRight (up d) (project v w e f n h.2)))
  let firstFiberIsSingleton : Left → Prop := fun ⟨_, r, s, _, x, _, _⟩ =>
    let q := basisMap a b r s x
    ∀ z ∈ Set.range q, ∃! w, q w = z
  let indices : Left → Prop := fun l =>
    let H := transport l
    let firstIndex := Subgroup.relIndex H maximum
    let secondIndex := Subgroup.relIndex lower (H ⊓ other)
    lower ≤ H ∧ H ≤ maximum ∧ lower ≤ H ⊓ other ∧
    Subgroup.FiniteIndex (Subgroup.subgroupOf H maximum) ∧
    Subgroup.FiniteIndex (Subgroup.subgroupOf lower (H ⊓ other)) ∧
    (match l with
    | ⟨_, r, s, t, x, y, _⟩ =>
      fiberSize (basisMap a b r s x) firstIndex ∧
      fiberSize (basisMap s c t f y) secondIndex) ∧
    (H = maximum → firstIndex = 1 ∧ firstFiberIsSingleton l)
  let maximalLeftLabels : Left → Prop := fun ⟨_, _, _, _, x, y, z⟩ =>
    MackeyDiagrams.Dot.element x = element ∧
    MackeyDiagrams.Dot.element y = 1 ∧ MackeyDiagrams.Dot.element z = 1
  parabolic rightRegion ∧
  ∃ (hp : finiteFibers (basisMap a bc de f p)) (r : Right) (hr : rightFinite r),
    rightLabels r ∧
    evaluate (right r hr) = evaluate (target hp) ∧
    let realizes := fun (l : Left) (hl : leftFinite l) =>
      evaluate (left l hl) = evaluate (right r hr)
    (∀ (l : Left) (hl : leftFinite l), realizes l hl → indices l) ∧
    (∀ H : Subgroup A, parabolic (Subgroup.map (Subgroup.subtype A) H) →
      lower ≤ H → H ≤ maximum →
      ∃ (l : Left) (hl : leftFinite l), transport l = H ∧ realizes l hl) ∧
    (∃ (l : Left) (hl : leftFinite l),
      transport l = maximum ∧ maximalLeftLabels l ∧ realizes l hl ∧
      Subgroup.relIndex (transport l) maximum = 1 ∧ firstFiberIsSingleton l)
) :=
(
by
  classical
  open MackeyDiagrams ParabolicCaseTwoProjectionFiberIndicesAux in
  intro P finitary U parabolic G A D F C E hG hA hD hF hC hE a b c d e f
    comp bc ad de ade image conjugate p element lower other maximum minimum rightRegion
    basisMap finiteFibers fiberSize up down tensor outside inside vertical horizontal identity
    parallel project evaluate atRight target Left Right transport leftFinite rightFinite
    rightLabels left right firstFiberIsSingleton indices maximalLeftLabels
  -- Alphabeta Math, Proposition 8.6 (archived original p. 38, revised
  -- published PDF p. 40). The portal gives the proof in prose and refers
  -- to Lemma 6.3 and to Cases 1 and 2 of Theorem 6.4. The projection diagram
  -- is on archived p. 39 and revised p. 41.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-three-outside
  let _ : Finite A := parabolic_finite hA
  let _ : Finite G := parabolic_finite hG
  let _ : Finite D := parabolic_finite hD
  let _ : Finite F := parabolic_finite hF
  have targetIndex : (lower.subgroupOf (image a ⊓ other)).FiniteIndex := inferInstance
  obtain ⟨hp, hExtremal⟩ :=
    ParabolicExtremalOutsideRestrictionRegions hG hA hD hF hC hE a b c d e f p targetIndex
  let parameter : ProjectionDot.Mixed a bc de f := ⟨p, hp⟩
  obtain ⟨minParabolic, maxParabolic⟩ := parabolic_region_bounds a b c d element hG hD hF hC
  -- Case 1 of Theorem 6.4 gives the right composite at the join.
  -- Its middle index is finite in the finite ambient group A.
  have middleIndex : ((image ad).subgroupOf (image a ⊓ minimum)).FiniteIndex := inferInstance
  obtain ⟨j, v, w, ell, m, n, hj, hv, hw, hell, hm, hn, _, _⟩ :=
    (CaseOneRightProjectionConstruction a b c d e f).1 parameter middleIndex
  let rr : Right := ⟨j, v, w, ell, m.dot, n.dot⟩
  have hr : rightFinite rr := ⟨m.finite, n.finite⟩
  have hrightLabels : rightLabels rr :=
    ⟨hj, ConjEmbedding.ext (MonoidHom.ext hv), hw, hell, hm, hn⟩
  have hrightParam : rightParameter a b c d e f ell m.dot n.dot = p.element := by
    change m.dot.element * j.toHom n.dot.element * ell.element⁻¹ = p.element
    rw [hell, hm, hn, map_one, mul_one, one_mul, inv_inv]
  have heRight : evaluate (right rr hr) = evaluate (target hp) :=
    (right_project_eval a b c d e f parameter ell m n).2 hrightParam
  refine ⟨minParabolic, hp, rr, hr, hrightLabels, heRight, ?_⟩
  have hIndices : ∀ (l : Left) (hl : leftFinite l),
      evaluate (left l hl) = evaluate (right rr hr) → indices l := by
    rintro ⟨⟨B, hB⟩, r, s, t, x, y, z⟩ hl he
    have hparam :=
      (left_project_eval a b c d e f parameter ⟨x, hl.1⟩ ⟨y, hl.2⟩ z).1 (he.trans heRight)
    -- Lemma 6.3 identifies the effective crossing element of these three
    -- vertices. Transport each local stabilizer index via the corresponding
    -- injective map, keeping the two bases and their image conditions separate.
    let H := conjugate (a.toHom z.element⁻¹) (image (comp a r))
    obtain ⟨hlo, hhi, hboth, hfirst, hsecond⟩ :=
      transportIndices a b c d e f x y z p hparam
    have hFiniteFirst : (H.subgroupOf maximum).FiniteIndex := inferInstance
    have hFiniteSecond : (lower.subgroupOf (H ⊓ other)).FiniteIndex := inferInstance
    refine ⟨hlo, hhi, hboth, hFiniteFirst, hFiniteSecond, ⟨?_, ?_⟩, ?_⟩
    · exact fun u hu =>
        (crossingFiberSize a b r s ⟨x, hl.1⟩ u hu).trans hfirst
    · exact fun u hu =>
        (crossingFiberSize s c t f ⟨y, hl.2⟩ u hu).trans hsecond
    · intro heq
      change H = maximum at heq
      have hOne : H.relIndex maximum = 1 := by
        rw [heq, Subgroup.relIndex_self]
      have hmax : conj (a.toHom z.element⁻¹) (a.comp r).toHom.range =
          leftBound a b (leftParameter a b c d e f x y z) := by
        rw [hparam]
        exact heq
      have hinj := first_injective a b c d e f x y z hmax
      refine ⟨hOne, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact ⟨w, rfl, fun w' hw' => hinj hw'⟩
  refine ⟨hIndices, ?_, ?_⟩
  · -- Proposition 8.6 supplies every point of the interval at this boundary.
    intro H hH hlo hhi
    obtain ⟨l, hl, htrans, he⟩ := (hExtremal.2.2.2.2.1 H hH hlo hhi).1
    exact ⟨l, hl, htrans, he.trans heRight.symm⟩
  · -- Case 2 uses the full intersection. Expose the labels (p, 1, 1)
    -- from the restricted-embedding construction for this particular witness.
    obtain ⟨r, s, t, x, y, z, htrans, hparam, hx, hy, hz⟩ :=
      labelledLeftWitness a b c d e f p maximum (lower_le_max a b c d e f p) le_rfl
    let ll : Left := ⟨⟨maximum.map A.subtype, maxParabolic⟩, r, s, t, x.dot, y.dot, z⟩
    have hl : leftFinite ll := ⟨x.finite, y.finite⟩
    have heLeft : evaluate (left ll hl) = evaluate (target hp) :=
      (left_project_eval a b c d e f parameter x y z).2 hparam
    have he := heLeft.trans heRight.symm
    have hmax := (hIndices ll hl he).2.2.2.2.2.2 htrans
    exact ⟨ll, hl, htrans, ⟨hx, hy, hz⟩, he, hmax⟩

)

#print axioms ParabolicCaseTwoProjectionFiberIndices
