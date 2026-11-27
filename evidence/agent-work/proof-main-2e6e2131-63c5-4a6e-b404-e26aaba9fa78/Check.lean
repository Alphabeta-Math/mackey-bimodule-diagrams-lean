import Mathlib.GroupTheory.DoubleCoset
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionAdjunction

namespace MixedCrossingFiberMapsAux

open MackeyDiagrams

section
variable {U : Type*} [Group U] {K H G L : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

private abbrev Q := ((Biset.induction l).tensor (Biset.restriction r)).carrier
private abbrev pair (k : K) (h : H) : Q l r :=
  (Biset.induction l).pair (Biset.restriction r) k h
private abbrev qB := Generator.mixedMultiplicationBasis a b l r d
private abbrev q (w : Q l r) : G := Generator.mixedProduct a b (qB a b l r d w)
private abbrev tr (s g : G) (t : H) : G := g * (b.toHom t)⁻¹ * s⁻¹
private abbrev fiber (g : G) := {w : Q l r | q a b l r d w = g}
private abbrev survives (s : G) (T : Set H) (g : G) := {t | t ∈ T ∧ tr b s g t ∈ a.toHom.range}
private abbrev transversal (T : Set H) :=
  ∀ h : H, ∃! t : H, t ∈ T ∧ h * t⁻¹ ∈ r.toHom.range

private theorem q_pair (k : K) (h : H) :
    q a b l r d (pair l r k h) = a.toHom k * d.element * b.toHom h :=
  Generator.mixedProduct_mixedPair a b _

private theorem qB_eq_iff (w : Q l r) (g : G) :
    qB a b l r d w = Generator.mixedPair a b g ↔ q a b l r d w = g :=
  (Generator.mixedEquiv a b).injective.eq_iff.symm.trans (by
    change (q a b l r d w = Generator.mixedProduct a b (Generator.mixedPair a b g)) ↔ _
    rw [Generator.mixedProduct_mixedPair])

private def leftHom : K →* U := G.subtype.comp a.toHom
private def rightHom (s : G) : H →* U :=
  (MulAut.conj (s : U)).toMonoidHom.comp (G.subtype.comp b.toHom)
private abbrev intersection (s : G) := (leftHom a).range ⊓ (rightHom b s).range
private abbrev diagonal := ((leftHom a).comp l.toHom).range

private theorem leftHom_injective : Function.Injective (leftHom a) :=
  Subtype.coe_injective.comp a.injective

private theorem rightHom_injective (s : G) : Function.Injective (rightHom b s) :=
  (MulAut.conj (s : U)).injective.comp (Subtype.coe_injective.comp b.injective)

private theorem diagonal_agrees (z : L) : rightHom b d.element (r.toHom z) = leftHom a (l.toHom z) := by
  have hd := congrArg (fun x : G => (x : U)) (d.intertwines z)
  change leftHom a (l.toHom z) * (d.element : U) =
    (d.element : U) * (b.toHom (r.toHom z) : U) at hd
  change (d.element : U) * (b.toHom (r.toHom z) : U) * (d.element : U)⁻¹ = _
  rw [← hd, mul_inv_cancel_right]

private theorem diagonal_le : diagonal a l ≤ intersection a b d.element := by
  rintro x ⟨z, rfl⟩
  exact ⟨⟨l.toHom z, rfl⟩, ⟨r.toHom z, diagonal_agrees a b l r d z⟩⟩

private theorem base_eq_iff (k : K) (h : H) :
    q a b l r d (pair l r k h) = d.element ↔ leftHom a k * rightHom b d.element h = 1 := by
  rw [q_pair]
  change (_ : G) = _ ↔ (a.toHom k : U) *
    ((d.element : U) * (b.toHom h : U) * (d.element : U)⁻¹) = 1
  rw [← Subtype.coe_inj]
  change (a.toHom k : U) * (d.element : U) * (b.toHom h : U) = (d.element : U) ↔ _
  rw [← mul_assoc, ← mul_assoc, mul_inv_eq_one]

/- Article §5.1, Proposition 5.1 proof, stabilizer and index calculation.
   No numbered Alphabeta Math proof is supplied. In the base fiber, the first
   coordinate in the intersection identifies a balanced class with a left coset.
   This computes the relative index directly, without a quotient tower. -/
private theorem base_pair_eq_iff (k k' : K) (h h' : H)
    (hk : leftHom a k * rightHom b d.element h = 1)
    (hk' : leftHom a k' * rightHom b d.element h' = 1) :
    pair l r k h = pair l r k' h' ↔ (leftHom a k)⁻¹ * leftHom a k' ∈ diagonal a l := by
  constructor
  · intro eq
    obtain ⟨z, hz, _⟩ := Quotient.exact eq
    change 1 * k * (l.toHom z)⁻¹ = k' at hz
    refine ⟨z⁻¹, ?_⟩
    rw [← hz]
    simp [map_mul, map_inv]
  · rintro ⟨z, hz⟩
    change leftHom a (l.toHom z) = _ at hz
    have hleft : leftHom a k * leftHom a (l.toHom z) = leftHom a k' := by
      rw [hz, mul_inv_cancel_left]
    have hright : (rightHom b d.element (r.toHom z))⁻¹ * rightHom b d.element h = rightHom b d.element h' := by
      rw [diagonal_agrees a b l r d, hz, mul_inv_rev, inv_inv, mul_assoc, hk, mul_one]
      exact (eq_inv_of_mul_eq_one_right hk').symm
    apply Quotient.sound
    refine ⟨z⁻¹, ?_, ?_⟩
    · change 1 * k * (l.toHom z⁻¹)⁻¹ = k'
      simp only [one_mul, map_inv, inv_inv]
      exact leftHom_injective a (by rw [map_mul, hleft])
    · change r.toHom z⁻¹ * h * (1 : H)⁻¹ = h'
      simp only [inv_one, mul_one, map_inv]
      exact rightHom_injective b d.element (by rw [map_mul, map_inv, hright])

private noncomputable def baseFiberEquiv :
    ((intersection a b d.element) ⧸ (diagonal a l).subgroupOf (intersection a b d.element)) ≃
      fiber a b l r d d.element := by
  classical
  let I := intersection a b d.element
  let D := (diagonal a l).subgroupOf I
  have existsLeft (x : I) : ∃ k : K, leftHom a k = (x : U) := x.property.1
  have existsRight (x : I) : ∃ h : H, rightHom b d.element h = (x : U)⁻¹ :=
    (I.inv_mem x.property).2
  choose k hk using existsLeft
  choose h hh using existsRight
  have he (x : I) : leftHom a (k x) * rightHom b d.element (h x) = 1 := by
    rw [hk, hh, mul_inv_cancel]
  let f : I → fiber a b l r d d.element :=
    fun x => ⟨pair l r (k x) (h x), (base_eq_iff a b l r d _ _).2 (he x)⟩
  have rel (x y : I) :
      f x = f y ↔ QuotientGroup.leftRel D x y := by
    rw [← Subtype.coe_inj]
    change pair l r (k x) (h x) = pair l r (k y) (h y) ↔ _
    rw [base_pair_eq_iff a b l r d _ _ _ _ (he x) (he y), hk, hk,
      QuotientGroup.leftRel_apply]
    rfl
  let lift : I ⧸ D → fiber a b l r d d.element :=
    Quotient.lift f (fun x y hxy => (rel x y).2 hxy)
  refine Equiv.ofBijective lift ⟨?_, ?_⟩
  · intro x y
    refine Quotient.inductionOn₂ x y fun x y heq => ?_
    exact Quotient.sound ((rel x y).1 heq)
  · rintro ⟨w, hw⟩
    obtain ⟨⟨k₀, h₀⟩, hrep⟩ := Quotient.exists_rep w
    change pair l r k₀ h₀ = w at hrep
    subst w
    have hp := (base_eq_iff a b l r d k₀ h₀).1 hw
    let x : I := ⟨leftHom a k₀, ⟨⟨k₀, rfl⟩,
      ⟨h₀⁻¹, by rw [map_inv, eq_inv_of_mul_eq_one_right hp, inv_inv]⟩⟩⟩
    refine ⟨Quotient.mk _ x, Subtype.ext ?_⟩
    change pair l r (k x) (h x) = pair l r k₀ h₀
    rw [base_pair_eq_iff a b l r d _ _ _ _ (he x) hp, hk]
    change (leftHom a k₀)⁻¹ * leftHom a k₀ ∈ diagonal a l
    rw [inv_mul_cancel]
    exact (diagonal a l).one_mem

private theorem range_q :
    Set.range (q a b l r d) =
      DoubleCoset.doubleCoset d.element (a.toHom.range : Set G) b.toHom.range := by
  ext g
  rw [Set.mem_range, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨w, rfl⟩
    refine Quotient.inductionOn w (fun ⟨k,h⟩ => ?_)
    exact ⟨_, ⟨k, rfl⟩, _, ⟨h, rfl⟩, q_pair a b l r d k h⟩
  · rintro ⟨_, ⟨k, rfl⟩, _, ⟨h, rfl⟩, hg⟩
    exact ⟨pair l r k h, (q_pair a b l r d k h).trans hg.symm⟩

private theorem q_act (p : K × H) (w : Q l r) :
    q a b l r d (((Biset.induction l).tensor (Biset.restriction r)).act p w) =
      a.toHom p.1 * q a b l r d w * (b.toHom p.2)⁻¹ := by
  change Generator.mixedProduct a b (Generator.mixedMultiplicationBasis a b l r d _) = _
  rw [Generator.mixedMultiplication_equivariant]
  conv_lhs =>
    rw [← Generator.mixedPair_mixedProduct a b (qB a b l r d w)]
  change (a.toHom p.1 * q a b l r d w * (1 : G)⁻¹) *
    (1 * 1 * (b.toHom p.2)⁻¹) = _
  simp

private noncomputable def fiberEquivBase (g : G)
    (hg : g ∈ Set.range (q a b l r d)) : fiber a b l r d d.element ≃ fiber a b l r d g := by
  rw [range_q, DoubleCoset.mem_doubleCoset] at hg
  obtain ⟨_, ⟨k, rfl⟩, _, ⟨h, rfl⟩, hg⟩ := hg
  refine Equiv.subtypeEquiv (((Biset.induction l).tensor (Biset.restriction r)).actEquiv
    (k, h⁻¹)) ?_
  intro w
  change q a b l r d w = d.element ↔
    q a b l r d (((Biset.induction l).tensor (Biset.restriction r)).act (k, h⁻¹) w) = g
  rw [q_act, hg, map_inv, inv_inv, mul_right_cancel_iff, mul_left_cancel_iff]

private theorem fiber_card (g : G) (hg : g ∈ Set.range (q a b l r d)) :
    Nat.card (fiber a b l r d g) = (diagonal a l).relIndex (intersection a b d.element) := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_congr ((baseFiberEquiv a b l r d).trans (fiberEquivBase a b l r d g hg)).symm

private theorem fiber_finite (g : G) (hg : g ∈ Set.range (q a b l r d)) :
    (fiber a b l r d g).Finite ↔ (diagonal a l).IsFiniteRelIndex (intersection a b d.element) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, Subgroup.finiteIndex_iff_finite_quotient]
  let e := (baseFiberEquiv a b l r d).trans (fiberEquivBase a b l r d g hg)
  constructor
  · intro h
    letI := h.to_subtype
    exact Finite.of_injective e e.injective
  · intro h
    letI := Finite.of_surjective e e.surjective
    exact Set.toFinite _

private theorem qB_fiber_eq (g : G) :
    {w | qB a b l r d w = Generator.mixedPair a b g} = fiber a b l r d g :=
  Set.ext (fun w => qB_eq_iff a b l r d w g)

private theorem all_finite_iff :
    (∀ z, Set.Finite {w | qB a b l r d w = z}) ↔
      (diagonal a l).IsFiniteRelIndex (intersection a b d.element) := by
  constructor
  · intro hf
    have hs : d.element ∈ Set.range (q a b l r d) :=
      ⟨pair l r 1 1, by rw [q_pair]; simp⟩
    apply (fiber_finite a b l r d _ hs).1
    rw [← qB_fiber_eq]
    exact hf _
  · intro hf z
    obtain ⟨g, rfl⟩ := (Generator.mixedEquiv a b).symm.surjective z
    change Set.Finite {w | qB a b l r d w = Generator.mixedPair a b g}
    rw [qB_fiber_eq]
    by_cases hg : g ∈ Set.range (q a b l r d)
    · exact (fiber_finite a b l r d g hg).2 hf
    · apply Set.Finite.subset Set.finite_empty
      intro w hw
      exact (hg ⟨w, hw⟩).elim

private theorem cap_finite_iff :
    (∀ h : H, Set.Finite {w | Generator.multiplicationCapBasis r w = h}) ↔
      r.toHom.range.FiniteIndex := by
  constructor
  · intro hf
    letI := (hf 1).to_subtype
    let e := (QuotientGroup.quotientRightRelEquivQuotientLeftRel r.toHom.range).symm.trans
      (Generator.rightCosetEquivCapFiber r 1)
    exact Subgroup.finiteIndex_iff_finite_quotient.2 (Finite.of_injective e e.injective)
  · exact Generator.multiplicationCap_finiteFiber r

private theorem trace_eq_iff (k : K) (t : H) (g : G) :
    a.toHom k = tr b d.element g t ↔ q a b l r d (pair l r k t) = g := by
  rw [q_pair]
  change a.toHom k = g * (b.toHom t)⁻¹ * d.element⁻¹ ↔ _
  rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, mul_assoc]

/- Article §5.1, Proposition 5.1 proof, right-coset representatives.
   The trace value determines the first coordinate by injectivity. -/
private noncomputable def survivorPair (T : Set H) (g : G)
    (t : survives a b d.element T g) : fiber a b l r d g :=
  ⟨pair l r (Classical.choose t.property.2) t, (trace_eq_iff a b l r d _ _ _).1
    (Classical.choose_spec t.property.2)⟩

private theorem survivorPair_bijective (T : Set H) (hT : transversal r T) (g : G) :
    Function.Bijective (survivorPair a b l r d T g) := by
  constructor
  · intro t t' heq
    have hh := Quotient.exact (congrArg Subtype.val heq)
    obtain ⟨z, _, hz⟩ := hh
    change r.toHom z * (t : H) * (1 : H)⁻¹ = (t' : H) at hz
    simp only [inv_one, mul_one] at hz
    obtain ⟨v, _, hv⟩ := hT t'
    apply Subtype.ext
    exact (hv t ⟨t.property.1, ⟨z, by rw [← hz, mul_inv_cancel_right]⟩⟩).trans
      (hv t' ⟨t'.property.1, ⟨1, by simp⟩⟩).symm
  · rintro ⟨w, hw⟩
    obtain ⟨⟨k,h⟩, hrep⟩ := Quotient.exists_rep w
    change pair l r k h = w at hrep
    obtain ⟨t, ⟨htT, z, hz⟩, _⟩ := hT h
    have hbal : pair l r k h = pair l r (k * l.toHom z) t := by
      apply Quotient.sound
      refine ⟨z⁻¹, ?_, ?_⟩
      · change 1 * k * (l.toHom z⁻¹)⁻¹ = _
        simp
      · change r.toHom z⁻¹ * h * (1 : H)⁻¹ = t
        simp only [inv_one, mul_one, map_inv, hz]
        group
    have hk : a.toHom (k * l.toHom z) = tr b d.element g t :=
      (trace_eq_iff a b l r d _ _ _).2 (by rw [← hbal, hrep]; exact hw)
    let t₀ : survives a b d.element T g := ⟨t, htT, ⟨_, hk⟩⟩
    refine ⟨t₀, Subtype.ext ?_⟩
    change pair l r (Classical.choose t₀.property.2) t = w
    rw [show Classical.choose t₀.property.2 = k * l.toHom z from
      a.injective ((Classical.choose_spec t₀.property.2).trans hk.symm), ← hbal, hrep]

private theorem projection_transversal
    (hf : ∀ z, Set.Finite {w | qB a b l r d w = z})
    (T : Set H) (hT : transversal r T) (g : G) :
    ∃ ht : (survives a b d.element T g).Finite,
      (Diagram.mixedProjection (R := Complex) a b l r d hf).eval.toLinearMap
        (Finsupp.single (Generator.mixedPair a b g) 1) =
      Finset.sum ht.toFinset (fun t =>
        Biset.pairLinear Complex (Biset.induction l) (Biset.restriction r)
          (Generator.traceBasis Complex a (tr b d.element g t)) (Finsupp.single t 1)) := by
  classical
  let x := Generator.mixedPair a b g
  let tail := Diagram.mixedProjectionTail (R := Complex) a b l r d
  let after := RightCupTrace.mixedProjectionTail_finiteAfter (R := Complex) a b l r d hf
  let e := Equiv.ofBijective (survivorPair a b l r d T g)
    (survivorPair_bijective a b l r d T hT g)
  have hfg : (fiber a b l r d g).Finite := by
    rw [← qB_fiber_eq]
    exact hf x
  letI := hfg.to_subtype
  letI := Finite.of_injective e e.injective
  let ht : (survives a b d.element T g).Finite := Set.toFinite _
  refine ⟨ht, ?_⟩
  -- The expanded trace tail is pointwise finite under hf, with its actual cup
  -- index set and the original mixed boundary.
  rw [← ScopedDiagram.eval_expandedMixedProjection a b l r d hf]
  change (RightCupTrace.ofFiniteAfter tail after).eval.toLinearMap (Finsupp.single x 1) = _
  rw [RightCupTrace.eval_single]
  unfold RightCupTrace.basisSum
  let idx : survives a b d.element T g → reverseCupUnitFiber r :=
    fun t => RightCupTrace.outputCupIndex l r (e t)
  have hw (t : survives a b d.element T g) : qB a b l r d (e t).val = x :=
    (qB_eq_iff a b l r d _ _).2 (e t).property
  symm
  refine Finset.sum_bij (fun t mt => idx ⟨t, ht.mem_toFinset.mp mt⟩) ?_ ?_ ?_ ?_
  · intro t mt
    exact (after x).mem_toFinset.mpr
      (RightCupTrace.projectionTerm_ne_zero a b l r d x _ (hw ⟨t, ht.mem_toFinset.mp mt⟩))
  · intro t mt t' mt' he
    exact congrArg Subtype.val (e.injective (RightCupTrace.outputCupIndex_injOnFiber
      (R := Complex) a b l r d x (hw ⟨t, ht.mem_toFinset.mp mt⟩)
      (hw ⟨t', ht.mem_toFinset.mp mt'⟩) he))
  · intro i mi
    obtain ⟨w, hqx, hi⟩ := RightCupTrace.preimage_of_projectionTerm_ne_zero
      a b l r d x i ((after x).mem_toFinset.mp mi)
    obtain ⟨t, htw⟩ := e.surjective ⟨w, (qB_eq_iff a b l r d _ _).1 hqx⟩
    refine ⟨t, ht.mem_toFinset.mpr t.property, ?_⟩
    change RightCupTrace.outputCupIndex l r (e t).val = i
    rw [htw]
    exact hi
  · intro t mt
    let t₀ : survives a b d.element T g := ⟨t, ht.mem_toFinset.mp mt⟩
    let k := Classical.choose t₀.property.2
    have hk : a.toHom k = tr b d.element g t := Classical.choose_spec t₀.property.2
    change Biset.pairLinear Complex (Biset.induction l) (Biset.restriction r)
        (Generator.traceBasis Complex a (tr b d.element g t)) (Finsupp.single t 1) =
      RightCupTrace.term tail x (idx t₀)
    rw [RightCupTrace.projectionTerm_eq_single a b l r d x (e t₀).val (hw t₀)]
    change _ = Finsupp.single (pair l r k t) 1
    rw [← hk, Generator.traceBasis_image, Biset.pairLinear_single, one_mul]

private theorem leftHom_range (α : U) (ha : ∀ k : K, α * (k : U) * α⁻¹ ∈ G) :
    (leftHom (ConjEmbedding.ofConjugator α ha)).range =
      Subgroup.map (MulAut.conj α).toMonoidHom K := by
  ext x
  change (∃ k : K, α * (k : U) * α⁻¹ = x) ↔
    ∃ k : U, k ∈ K ∧ α * k * α⁻¹ = x
  exact ⟨fun ⟨k, hk⟩ => ⟨k, k.property, hk⟩, fun ⟨k, hK, hk⟩ => ⟨⟨k, hK⟩, hk⟩⟩

private theorem rightHom_range (β : U) (hb : ∀ h : H, β * (h : U) * β⁻¹ ∈ G) (s : G) :
    (rightHom (ConjEmbedding.ofConjugator β hb) s).range =
      Subgroup.map (MulAut.conj ((s : U) * β)).toMonoidHom H := by
  ext x
  have he (h : U) :
      (s : U) * (β * h * β⁻¹) * (s : U)⁻¹ = ((s : U) * β) * h * ((s : U) * β)⁻¹ := by
    group
  change (∃ h : H, (s : U) * (β * (h : U) * β⁻¹) * (s : U)⁻¹ = x) ↔
    ∃ h : U, h ∈ H ∧ ((s : U) * β) * h * ((s : U) * β)⁻¹ = x
  simp only [he]
  exact ⟨fun ⟨h, hx⟩ => ⟨h, h.property, hx⟩, fun ⟨h, hH, hx⟩ => ⟨⟨h, hH⟩, hx⟩⟩

private theorem diagonal_range (α c : U)
    (ha : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
    (hc : ∀ z : L, c * (z : U) * c⁻¹ ∈ K) :
    diagonal (ConjEmbedding.ofConjugator α ha) (ConjEmbedding.ofConjugator c hc) =
      Subgroup.map (MulAut.conj (α * c)).toMonoidHom L := by
  ext x
  have he (z : U) : α * (c * z * c⁻¹) * α⁻¹ = (α * c) * z * (α * c)⁻¹ := by group
  change (∃ z : L, α * (c * (z : U) * c⁻¹) * α⁻¹ = x) ↔
    ∃ z : U, z ∈ L ∧ (α * c) * z * (α * c)⁻¹ = x
  simp only [he]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, z.property, hz⟩, fun ⟨z, hL, hz⟩ => ⟨⟨z, hL⟩, hz⟩⟩

private theorem survivors_infinite (T : Set H) (hT : transversal r T) (g : G)
    (hinf : (fiber a b l r d g).Infinite) : (survives a b d.element T g).Infinite := by
  intro ht
  letI := ht.to_subtype
  letI := Finite.of_surjective _ (survivorPair_bijective a b l r d T hT g).2
  exact hinf (Set.toFinite _)

private theorem multiplication_eval (w : Q l r) :
    (Diagram.mixedMultiplication (R := Complex) a b l r d).eval.toLinearMap
      (Finsupp.single w 1) = Finsupp.single (Generator.mixedPair a b (q a b l r d w)) 1 := by
  let equivariant := Generator.mixedMultiplication_equivariant a b l r d
  change (Biset.Hom.ofFunction (R := Complex) (qB a b l r d) equivariant).toLinearMap
    (Finsupp.single w 1) = _
  rw [Biset.Hom.ofFunction_single]
  exact congrArg (fun z => Finsupp.single z (1 : Complex))
    (Generator.mixedPair_mixedProduct a b _).symm

private theorem projection_eval (hf : ∀ z, Set.Finite {w | qB a b l r d w = z}) (g : G) :
    (Diagram.mixedProjection (R := Complex) a b l r d hf).eval.toLinearMap
      (Finsupp.single (Generator.mixedPair a b g) 1) =
    Finset.sum (hf (Generator.mixedPair a b g)).toFinset (fun w => Finsupp.single w 1) := by
  let equivariant := Generator.mixedMultiplication_equivariant a b l r d
  change (Biset.Hom.transfer Complex (qB a b l r d) equivariant hf).toLinearMap
    (Finsupp.single (Generator.mixedPair a b g) 1) = _
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]

end
end MixedCrossingFiberMapsAux

universe u
theorem MixedCrossingFiberMaps : ∀ {U : Type u} [Group U] (K H G L : Subgroup U) (α β a b : U)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G)
    (ha : ∀ ℓ : L, a * (ℓ : U) * a⁻¹ ∈ K)
    (hb : ∀ ℓ : L, b * (ℓ : U) * b⁻¹ ∈ H)
    (hs : (α * a) * (β * b)⁻¹ ∈ G),
  let eα := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let eβ := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let ea := MackeyDiagrams.ConjEmbedding.ofConjugator a ha
  let eb := MackeyDiagrams.ConjEmbedding.ofConjugator b hb
  let d : MackeyDiagrams.Dot (eα.comp ea) (eβ.comp eb) :=
    MackeyDiagrams.Dot.ofRepresentatives (α * a) (β * b)
      (by
        intro ℓ
        change α * (a * (ℓ : U) * a⁻¹) * α⁻¹ = _
        simp only [mul_inv_rev, mul_assoc])
      (by
        intro ℓ
        change β * (b * (ℓ : U) * b⁻¹) * β⁻¹ = _
        simp only [mul_inv_rev, mul_assoc]) hs
  let s := d.element
  let A := eα.toHom.range
  let B := eβ.toHom.range
  let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
  ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
    let j := DoubleCoset.mk A B s
    let orbit := DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
    let Ls := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((s : U) * β))) H
    let Limage := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (α * a))) L
    let finiteIndex := Subgroup.IsFiniteRelIndex Limage Ls
    let n := Subgroup.relIndex Limage Ls
    let X := MackeyDiagrams.Biset.induction ea
    let Y := MackeyDiagrams.Biset.restriction eb
    let qBasis := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ ea eb d
    let q := fun w : (X.tensor Y).carrier =>
      MackeyDiagrams.Generator.mixedProduct eα eβ (qBasis w)
    let fiber := fun g : G => {w | q w = g}
    let ι := MackeyDiagrams.Diagram.mixedMultiplication (R := Complex) eα eβ ea eb d
    let finiteFibers := ∀ z, Set.Finite {w | qBasis w = z}
    let traceArg := fun (g : G) (t : H) => g * (eβ.toHom t)⁻¹ * s⁻¹
    let survives := fun (T : Set H) (g : G) => {t | t ∈ T ∧ traceArg g t ∈ A}
    let rightTransversal := fun T : Set H =>
      ∀ h : H, ∃! t : H, t ∈ T ∧ h * t⁻¹ ∈ eb.toHom.range
    Limage ≤ Ls ∧
    (∀ (k : K) (h : H), q (X.pair Y k h) = eα.toHom k * s * eβ.toHom h) ∧
    (∀ w : (X.tensor Y).carrier,
      (MackeyDiagrams.Diagram.eval ι).toLinearMap (Finsupp.single w 1) =
        Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ (q w)) 1) ∧
    Set.range q = orbit ∧
    (∀ g : G, g ∈ orbit → finiteIndex → Nat.card (fiber g) = n) ∧
    (finiteFibers ↔ finiteIndex) ∧
    (∀ g : G, g ∈ orbit → ¬ finiteIndex → Set.Infinite (fiber g)) ∧
    ((∀ h : H, Set.Finite {w | MackeyDiagrams.Generator.multiplicationCapBasis eb w = h}) ↔
      Subgroup.FiniteIndex eb.toHom.range) ∧
    (∀ (T : Set H), rightTransversal T → ∀ g : G, g ∈ orbit → ¬ finiteIndex →
      Set.Infinite (survives T g)) ∧
    (∀ hf : finiteFibers,
      let p := MackeyDiagrams.Diagram.mixedProjection (R := Complex) eα eβ ea eb d hf
      let evalOnBasis := fun g : G =>
        (MackeyDiagrams.Diagram.eval p).toLinearMap
          (Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ g) 1)
      (∀ g : G, evalOnBasis g = Finset.sum
        (hf (MackeyDiagrams.Generator.mixedPair eα eβ g)).toFinset
        (fun w => Finsupp.single w 1)) ∧
      (∀ (T : Set H), rightTransversal T → ∀ g : G,
        ∃ ht : Set.Finite (survives T g), evalOnBasis g = Finset.sum ht.toFinset
          (fun t => MackeyDiagrams.Biset.pairLinear Complex X Y
            (MackeyDiagrams.Generator.traceBasis Complex eα (traceArg g t))
            (Finsupp.single t 1)))) :=
by
  classical
  open MackeyDiagrams MixedCrossingFiberMapsAux in
  intro U inst K H G L α β a b hα hβ ha hb hs eα eβ ea eb d s A B J σ hσ
    j orbit Ls Limage finiteIndex n X Y qBasis q fiber ι finiteFibers traceArg survives
    rightTransversal
  -- Article §5.1, Proposition 5.1 proof. The shared balanced basis and typed
  -- generators supply the balancing, intertwining, multiplication and trace
  -- rules. The functor-level strand and adjunction comparisons are unnecessary
  -- for these basis columns.
  have hLimage : MixedCrossingFiberMapsAux.diagonal eα ea = Limage :=
    MixedCrossingFiberMapsAux.diagonal_range α a hα ha
  have hLs : MixedCrossingFiberMapsAux.intersection eα eβ s = Ls := by
    change (MixedCrossingFiberMapsAux.leftHom eα).range ⊓
      (MixedCrossingFiberMapsAux.rightHom eβ s).range = _
    rw [MixedCrossingFiberMapsAux.leftHom_range α hα,
      MixedCrossingFiberMapsAux.rightHom_range β hβ s]
  have hLe := MixedCrossingFiberMapsAux.diagonal_le eα eβ ea eb d
  change MixedCrossingFiberMapsAux.diagonal eα ea ≤
    MixedCrossingFiberMapsAux.intersection eα eβ s at hLe
  rw [hLimage, hLs] at hLe
  have hsOrbit : s ∈ orbit := by
    change s ∈ DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
    exact DoubleCoset.mem_doubleCoset.2 (DoubleCoset.eq.1 (hσ j))
  have hRange : Set.range q = orbit :=
    (MixedCrossingFiberMapsAux.range_q eα eβ ea eb d).trans
      (DoubleCoset.doubleCoset_eq_of_mem hsOrbit)
  have hcard (g : G) (hg : g ∈ orbit) : Nat.card (fiber g) = n := by
    have hc := MixedCrossingFiberMapsAux.fiber_card eα eβ ea eb d g (hRange ▸ hg)
    change Nat.card (fiber g) =
      (MixedCrossingFiberMapsAux.diagonal eα ea).relIndex
        (MixedCrossingFiberMapsAux.intersection eα eβ s) at hc
    rw [hLimage, hLs] at hc
    exact hc
  have hfinite : finiteFibers ↔ finiteIndex := by
    have hf := MixedCrossingFiberMapsAux.all_finite_iff eα eβ ea eb d
    change finiteFibers ↔ (MixedCrossingFiberMapsAux.diagonal eα ea).IsFiniteRelIndex
      (MixedCrossingFiberMapsAux.intersection eα eβ s) at hf
    rw [hLimage, hLs] at hf
    exact hf
  have hinfinite (g : G) (hg : g ∈ orbit) (hi : ¬ finiteIndex) : Set.Infinite (fiber g) := by
    have hf := MixedCrossingFiberMapsAux.fiber_finite eα eβ ea eb d g (hRange ▸ hg)
    change (fiber g).Finite ↔ (MixedCrossingFiberMapsAux.diagonal eα ea).IsFiniteRelIndex
      (MixedCrossingFiberMapsAux.intersection eα eβ s) at hf
    rw [hLimage, hLs] at hf
    exact fun h => hi (hf.1 h)
  refine ⟨hLe, MixedCrossingFiberMapsAux.q_pair eα eβ ea eb d,
    MixedCrossingFiberMapsAux.multiplication_eval eα eβ ea eb d, hRange,
    fun g hg _ => hcard g hg, hfinite, hinfinite, MixedCrossingFiberMapsAux.cap_finite_iff eb,
    fun T hT g hg hi => MixedCrossingFiberMapsAux.survivors_infinite eα eβ ea eb d T hT g
      (hinfinite g hg hi), ?_⟩
  intro hf
  exact ⟨MixedCrossingFiberMapsAux.projection_eval eα eβ ea eb d hf,
    MixedCrossingFiberMapsAux.projection_transversal eα eβ ea eb d hf⟩

#print axioms MixedCrossingFiberMaps
