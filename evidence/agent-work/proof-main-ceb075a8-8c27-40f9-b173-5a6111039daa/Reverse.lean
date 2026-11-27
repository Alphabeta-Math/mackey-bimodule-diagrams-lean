
section Reverse

variable {U : Type u} [Group U] {H G : Subgroup U}
variable {R : Type v} [CommSemiring R] {a b : ConjEmbedding H G}

private abbrev capCarrier (a : ConjEmbedding H G) :=
  ((Biset.induction a).tensor (Biset.restriction a)).carrier

private abbrev capPair (a : ConjEmbedding H G) (x y : G) : capCarrier a :=
  (Biset.induction a).pair (Biset.restriction a) x y

private def capShift (d : Dot a b) : capCarrier a → capCarrier b :=
  Quotient.map' (fun xy : G × G => (xy.1 * d.element, d.element⁻¹ * xy.2)) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    change 1 * x.1 * (a.toHom h)⁻¹ = y.1 at hx
    change a.toHom h * x.2 * (1 : G)⁻¹ = y.2 at hy
    have hd : b.toHom h * d.element⁻¹ = d.element⁻¹ * a.toHom h :=
      d.inverse.intertwines h
    have hi := d.intertwines h⁻¹
    rw [map_inv, map_inv] at hi
    refine ⟨h, ?_, ?_⟩
    · change 1 * (x.1 * d.element) * (b.toHom h)⁻¹ = y.1 * d.element
      rw [← hx, mul_assoc x.1, ← hi, ← mul_assoc]
    · change b.toHom h * (d.element⁻¹ * x.2) * (1 : G)⁻¹ = d.element⁻¹ * y.2
      rw [← hy, ← mul_assoc (b.toHom h), hd, mul_assoc, mul_assoc])

private theorem capShift_inverse (d : Dot a b) (z : capCarrier a) :
    capShift d.inverse (capShift d z) = z := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change capPair a (xy.1 * d.element * d.element⁻¹) ((d.element⁻¹)⁻¹ * (d.element⁻¹ * xy.2)) =
    capPair a xy.1 xy.2
  simp [mul_assoc]

private theorem capShift_forward_inverse (d : Dot a b) (z : capCarrier b) :
    capShift d (capShift d.inverse z) = z := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change capPair b (xy.1 * d.element⁻¹ * d.element) (d.element⁻¹ * ((d.element⁻¹)⁻¹ * xy.2)) =
    capPair b xy.1 xy.2
  simp [mul_assoc]

private theorem capShift_product (d : Dot a b) (z : capCarrier a) :
    Generator.multiplicationCapBasis b (capShift d z) =
      Generator.multiplicationCapBasis a z := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change xy.1 * d.element * (d.element⁻¹ * xy.2) = xy.1 * xy.2
  group

private theorem reverseBasis (a : ConjEmbedding H G) (ha : a.toHom.range.FiniteIndex) (g : G) :
    (Diagram.reverseCup (R := R) a ha).eval.toLinearMap (Finsupp.single g 1) =
      ∑ z ∈ (Generator.multiplicationCap_finiteFiber a ha g).toFinset, Finsupp.single z 1 := by
  change (Generator.reverseCup R a ha).toLinearMap (Finsupp.single g 1) = _
  rw [Generator.reverseCup, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]

private theorem reverseTerm (d : Dot a b) (z : capCarrier a) :
    ((Diagram.upDot (R := R) d).horizontal (.id (.down a))).eval.toLinearMap
      (Finsupp.single z 1) =
    ((Diagram.id (R := R) (.up b)).horizontal (.downDot d.inverse)).eval.toLinearMap
      (Finsupp.single (capShift d z) 1) := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change ((Diagram.upDot (R := R) d).horizontal (.id (.down a))).eval.toLinearMap
      (Finsupp.single (capPair a xy.1 xy.2) 1) =
    ((Diagram.id (R := R) (.up b)).horizontal (.downDot d.inverse)).eval.toLinearMap
      (Finsupp.single (capPair b (xy.1 * d.element) (d.element⁻¹ * xy.2)) 1)
  simp only [capPair, Diagram.eval_horizontal_single, Diagram.eval_id_apply, Diagram.eval_upDot_single,
    Diagram.eval_downDot_single, Dot.inverse, inv_inv, Biset.pairLinear_single, one_smul,
    mul_one, ← mul_assoc, mul_inv_cancel, one_mul]

/- Proposition 3.1, equation (3.4). The draft reindexes chosen right coset
   representatives by t ↦ d⁻¹*t. The Lean reverse cup is a transfer, so we
   reindex the actual product fibers by [x,y] ↦ [x*d,d⁻¹*y]. This is the
   same change in the second representative and uses both supplied finiteness
   witnesses. Both terms at corresponding fiber elements give [x*d,y]. -/
private theorem reverse (d : Dot a b)
    (ha : a.toHom.range.FiniteIndex) (hb : b.toHom.range.FiniteIndex) :
    ((Diagram.reverseCup (R := R) a ha).vertical ((Diagram.upDot d).horizontal (.id (.down a)))).eval =
    ((Diagram.reverseCup (R := R) b hb).vertical ((Diagram.id (.up b)).horizontal (.downDot d.inverse))).eval := by
  classical
  apply Biset.Hom.ext
  apply extOnBasis
  intro g
  change G at g
  rw [Diagram.eval_vertical_apply, Diagram.eval_vertical_apply,
    reverseBasis a ha g, reverseBasis b hb g, map_sum, map_sum]
  let fa := Generator.multiplicationCap_finiteFiber a ha g
  let fb := Generator.multiplicationCap_finiteFiber b hb g
  change ∑ z ∈ fa.toFinset, ((Diagram.upDot (R := R) d).horizontal (.id (.down a))).eval.toLinearMap
      (Finsupp.single z 1) =
    ∑ z ∈ fb.toFinset, ((Diagram.id (R := R) (.up b)).horizontal (.downDot d.inverse)).eval.toLinearMap
      (Finsupp.single z 1)
  refine Finset.sum_bij' (fun z _ => capShift d z) (fun z _ => capShift d.inverse z) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    exact fb.mem_toFinset.mpr ((capShift_product d z).trans (fa.mem_toFinset.mp hz))
  · intro z hz
    exact fa.mem_toFinset.mpr ((capShift_product d.inverse z).trans (fb.mem_toFinset.mp hz))
  · intro z _
    exact capShift_inverse d z
  · intro z _
    exact capShift_forward_inverse d z
  · intro z _
    exact reverseTerm d z

end Reverse
