import MackeyDiagrams
import Proofs.ParabolicExtremalOutsideRestrictionRegions
import Proofs.ParabolicCaseTwoProjectionFiberIndices
import Proofs.EvaluationForTwoProjections

set_option maxHeartbeats 2000000

-- These checked construction and evaluation lemmas belong to the registered
-- extremal-regions supplier. Keep the adapter with the consuming endpoint.
open private parabolic_region_bounds parabolic_finite left_project_eval leftParameter
  lower_le_max inclusion inclusion_range lift_through conjugated conjugated_range
  restrictTo finite_mixed conj conj_one OutsideRegionsAux.conj_mul
  from Proofs.ParabolicExtremalOutsideRestrictionRegions

theorem ParabolicOutsideProjectionDiagram : (
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
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let image := fun {H K : Subgroup U} (g : MackeyDiagrams.ConjEmbedding H K) =>
    MonoidHom.range (hom g)
  let conjugate := fun (g : A) (H : Subgroup A) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) H
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let ade := comp a de
  ∀ p : MackeyDiagrams.Dot ade (comp bc f),
  let element := MackeyDiagrams.Dot.element p
  let other := conjugate element (image bc)
  let maximum := image a ⊓ conjugate element (image b)
  let minimum := image ad ⊔ other
  let Bmax := Subgroup.map (Subgroup.subtype A) maximum
  let Pp := Subgroup.map (Subgroup.subtype A) minimum
  let basisMap := @MackeyDiagrams.Generator.mixedMultiplicationBasis U _
  let finiteFibers := fun {X Y : Type} (q : X → Y) => ∀ z, Set.Finite {w | q w = z}
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let id := fun {K H : Subgroup U} (word : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) word)
  let projection := fun {K H J L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K J) (β : MackeyDiagrams.ConjEmbedding H J)
      (l : MackeyDiagrams.ConjEmbedding L K) (r : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.Dot (comp α l) (comp β r))
      (finite : finiteFibers (basisMap α β l r x)) =>
    MackeyDiagrams.LabelledDrawing.compactProjection α β l r
      [((1 : Complex), (⟨x, finite⟩ : MackeyDiagrams.ProjectionDot.Mixed α β l r))]
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let atRight := fun {K H J L J' : Subgroup U} (w : MackeyDiagrams.Word K H)
      {v : MackeyDiagrams.Word H J} {s : MackeyDiagrams.Word J L}
      {v' : MackeyDiagrams.Word H J'} {s' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor v s) (tensor v' s')) =>
    vertical (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate w v s))
      (vertical (horizontal (id w) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate w v' s')))
  parabolic Bmax ∧ parabolic Pp ∧
  ∃ (r : MackeyDiagrams.ConjEmbedding Bmax G)
    (s : MackeyDiagrams.ConjEmbedding Bmax D)
    (t : MackeyDiagrams.ConjEmbedding E Bmax)
    (u : MackeyDiagrams.ConjEmbedding Pp A)
    (v : MackeyDiagrams.ConjEmbedding C Pp)
    (w : MackeyDiagrams.ConjEmbedding F Pp)
    (x : MackeyDiagrams.Dot (comp a r) (comp b s))
    (y : MackeyDiagrams.Dot (comp s t) (comp c f))
    (z : MackeyDiagrams.Dot (comp r t) de)
    (ell : MackeyDiagrams.Dot bc (comp u w))
    (m : MackeyDiagrams.Dot ad (comp u v))
    (n : MackeyDiagrams.Dot (comp v e) (comp w f))
    (hx : finiteFibers (basisMap a b r s x))
    (hy : finiteFibers (basisMap s c t f y))
    (hm : finiteFibers (basisMap a u d v m))
    (hn : finiteFibers (basisMap v w e f n))
    (hp : finiteFibers (basisMap a bc de f p)),
    let left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical (horizontal (projection a b r s x hx) (id (up c)))
        (vertical (atRight (up r) (projection s c t f y hy))
          (horizontal
            (MackeyDiagrams.LabelledDrawing.parallelUp r t d e [((1 : Complex), z)])
            (id (down f))))
    let right : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical
        (atRight (down a)
          (MackeyDiagrams.LabelledDrawing.parallelUp b c u w [((1 : Complex), ell)]))
        (vertical (horizontal (projection a u d v m hm) (id (up w)))
          (atRight (up d) (projection v w e f n hn)))
    let fiberTransfer : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical
        (vertical
          (MackeyDiagrams.LabelledDrawing.ordinary
            (MackeyDiagrams.Diagram.associate (down a) (up b) (up c)))
          (horizontal (id (down a))
            (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp b c))))
        (vertical (projection a bc de f p hp)
          (horizontal
            (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp d e))
            (id (down f))))
    let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
    (∀ k : Bmax, (hom (comp a r) k : U) = (k : U)) ∧
    (∀ k : Bmax, (MulAut.conj element (hom (comp b s) k) : U) = (k : U)) ∧
    (∀ k : E, (hom t k : U) = (hom ade k : U)) ∧
    (∀ k : Pp, (hom u k : U) = (k : U)) ∧
    comp u v = ad ∧
    (∀ k : F, hom (comp u w) k = MulAut.conj element (hom bc k)) ∧
    MackeyDiagrams.Dot.element x = element ∧
    MackeyDiagrams.Dot.element y = 1 ∧ MackeyDiagrams.Dot.element z = 1 ∧
    MackeyDiagrams.Dot.element ell = element⁻¹ ∧
    MackeyDiagrams.Dot.element m = 1 ∧ MackeyDiagrams.Dot.element n = 1 ∧
    (let q := basisMap a b r s x
     ∀ k ∈ Set.range q, ∃! j, q j = k) ∧
    eval left = eval right ∧
    eval left = eval fiberTransfer
) :=
(by
  classical
  open MackeyDiagrams in
  intro P finitary U parabolic G A D F C E hG hA hD hF hC hE a b c d e f
    comp hom image conjugate bc ad de ade p element other maximum minimum Bmax Pp
    basisMap finiteFibers up down tensor vertical horizontal id projection bottom top atRight
  -- Xiao, Proposition 8.6 and the projection identity immediately after it.
  -- Archived original (bc57d137…), pp. 38–39; published 28 November revision
  -- (813c82da…), pp. 40–41. The displayed equality compares evaluations.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-three-outside
  have hMax : parabolic Bmax :=
    (parabolic_region_bounds a b c d element hG hD hF hC).2

  -- Theorem 6.4, numbered Case 1. The registered fiber-index theorem
  -- supplies the join witness with its inclusion and (p⁻¹, 1, 1) labels.
  -- Its finite-index checks use finiteness of the ambient parabolics.
  obtain ⟨hMin, hp, ⟨u, v, w, ell, m, n⟩, ⟨hm, hn⟩,
    ⟨hu, huv, huw, hell, hmel, hnel⟩, hRight, hIndices, _, _⟩ :=
    ParabolicCaseTwoProjectionFiberIndices hG hA hD hF hC hE a b c d e f p

  -- Theorem 6.4, numbered Case 2, transported as in Proposition 8.6.
  -- The supplier's existential maximal left witness leaves its exact
  -- embeddings implicit. Use the restricted inverses on Bmax to expose
  -- all three required maps on that specific subgroup of the ambient group.
  let j := inclusion maximum
  have hj : j.toHom.range = maximum := inclusion_range maximum
  obtain ⟨r, hr⟩ := lift_through a j (by
    rw [hj]
    exact inf_le_left)
  have hsRange : (conjugated j element⁻¹).toHom.range ≤ b.toHom.range := by
    rw [conjugated_range, hj]
    calc
      _ ≤ conj element⁻¹ (conj element b.toHom.range) := Subgroup.map_mono inf_le_right
      _ = _ := by rw [OutsideRegionsAux.conj_mul, inv_mul_cancel, conj_one]
  obtain ⟨s, hs⟩ := lift_through b (conjugated j element⁻¹) hsRange
  let t := restrictTo ade maximum (lower_le_max a b c d e f p)
  have hjt : j.comp t = ade := ConjEmbedding.ext (MonoidHom.ext fun _ => rfl)
  have hrt : r.comp t = de := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro k
    apply a.injective
    change ((a.comp r).comp t).toHom k = ade.toHom k
    rw [hr, hjt]
  have hbs (k : Bmax) : b.toHom (s.toHom k) = element⁻¹ * j.toHom k * element := by
    have hk := congrArg (fun l : ConjEmbedding Bmax A => l.toHom k) hs
    change b.toHom (s.toHom k) = element⁻¹ * j.toHom k * (element⁻¹)⁻¹ at hk
    simpa only [inv_inv] using hk
  have hst : s.comp t = c.comp f := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro k
    apply b.injective
    change b.toHom (s.toHom (t.toHom k)) = (bc.comp f).toHom k
    rw [hbs]
    change element⁻¹ * (j.comp t).toHom k * element = _
    rw [hjt, mul_assoc, p.intertwines, inv_mul_cancel_left]
  let x : Dot (a.comp r) (b.comp s) := ⟨element, by
    intro k
    rw [hr]
    change j.toHom k * element = element * b.toHom (s.toHom k)
    rw [hbs]
    group⟩
  let y : Dot (s.comp t) (c.comp f) := ⟨1, by intro k; rw [hst, mul_one, one_mul]⟩
  let z : Dot (r.comp t) de := ⟨1, by intro k; rw [hrt, mul_one, one_mul]⟩
  let _ : Finite G := parabolic_finite hG
  let _ : Finite D := parabolic_finite hD
  let _ : Finite F := parabolic_finite hF
  let _ : Finite Bmax := Finite.of_injective r.toHom r.injective
  let X : ProjectionDot.Mixed a b r s := ⟨x, finite_mixed a b r s x⟩
  let Y : ProjectionDot.Mixed s c t f := ⟨y, finite_mixed s c t f y⟩

  -- Lemma 6.3 and (6.1). The checked effective-element calculation
  -- identifies the transfer for these exact singleton labels, including
  -- the inverse trace dot. Specialize the supplier's effective-element
  -- lemma to identify the particular parameter in Lemma 6.3.
  have hParameter : leftParameter a b c d e f x y z = p.element := by
    change a.toHom (1 : G)⁻¹ * p.element * b.toHom (1 : D) = p.element
    rw [inv_one, map_one, map_one, one_mul, mul_one]
  have hLeft := (left_project_eval a b c d e f
    (⟨p, hp⟩ : ProjectionDot.Mixed a bc de f) X Y z).2 hParameter
  have hEqual := hLeft.trans hRight.symm

  -- At the maximum, the registered Case 2 calculation gives relative
  -- index one and a unique preimage in each nonempty first fiber.
  have hTransport : conj (a.toHom z.element⁻¹) (a.comp r).toHom.range = maximum := by
    change conj (a.toHom (1 : G)⁻¹) (a.comp r).toHom.range = maximum
    rw [inv_one, map_one, conj_one, hr, hj]
  obtain ⟨_, _, _, _, _, _, hAtMax⟩ := hIndices
    ⟨⟨Bmax, hMax⟩, r, s, t, x, y, z⟩ ⟨X.finite, Y.finite⟩ hEqual
  have hSingleton := (hAtMax hTransport).2
  have hLeftInclusion (k : Bmax) : ((a.comp r).toHom k : U) = (k : U) := by
    rw [hr]
    rfl
  have hLeftConjugate (k : Bmax) :
      (MulAut.conj element ((b.comp s).toHom k) : U) = (k : U) := by
    have hk : MulAut.conj element ((b.comp s).toHom k) = j.toHom k := by
      change element * b.toHom (s.toHom k) * element⁻¹ = j.toHom k
      rw [hbs]
      group
    exact congrArg Subtype.val hk
  refine ⟨hMax, hMin, r, s, t, u, v, w, x, y, z, ell, m, n,
    X.finite, Y.finite, hm, hn, hp,
    hLeftInclusion, hLeftConjugate, (fun _ => rfl), hu, huv, huw,
    rfl, rfl, rfl, hell, hmel, hnel, hSingleton, hEqual, hLeft⟩)
