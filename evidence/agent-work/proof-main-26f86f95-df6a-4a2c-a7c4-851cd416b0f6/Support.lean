namespace TraceCapBendSupport

open MackeyDiagrams MackeyDiagrams.Diagram

universe u
variable {U : Type u} [Group U] {K H G : Subgroup U}
variable (a : ConjEmbedding K H) (b : ConjEmbedding H G)

private theorem cup_transversal (finite : a.toHom.range.FiniteIndex) :
    ∃ T : Finset H, (∀ h : H, ∃! t : {t // t ∈ T}, h * t.val⁻¹ ∈ a.toHom.range) ∧
      (reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single 1 1) =
        ∑ t ∈ T, Finsupp.single ((Word.up a).basis.pair (Word.down a).basis t⁻¹ t) 1 := by
  obtain ⟨s, hs⟩ := a.hasRepresentative
  have hs' (h : K) : s * (h : U) * s⁻¹ ∈ H := hs h ▸ (a.toHom h).property
  have ha : a = ConjEmbedding.ofConjugator s hs' :=
    ConjEmbedding.ext (MonoidHom.ext fun h => Subtype.ext (hs h))
  subst a
  have h := (FiniteIndexReverseAdjunction.{u, 0} K H s hs').2.2.2.2 finite
  obtain ⟨⟨T, hT⟩, _, _, hcup⟩ := h
  refine ⟨T, hT, ?_⟩
  have hsum := ((hcup T hT).1 1).1
  simp only [MonoidAlgebra.coeff_single, one_mul] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Biset.pairLinear_single, mul_one]

private theorem rightUnit_pair_one (v : H →₀ Complex) :
    (rightUnit (R := Complex) (.down a)).eval.toLinearMap
      (Biset.pairLinear Complex (Word.down a).basis (Word.empty H).basis
        (Finsupp.single 1 1) v) = v := by
  let f := (rightUnit (R := Complex) (.down a)).eval.toLinearMap ∘ₗ
    (Biset.pairLinear Complex (Word.down a).basis (Word.empty H).basis (Finsupp.single 1 1))
  have hf : f = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro t c
    change (rightUnit (R := Complex) (.down a)).eval.toLinearMap
      (Biset.pairLinear Complex (Word.down a).basis (Word.empty H).basis
        (Finsupp.single 1 1) (Finsupp.single t c)) = Finsupp.single t c
    rw [Biset.pairLinear_single, one_mul, eval_rightUnit_single]
    change Finsupp.single (a.toHom 1 * 1 * (t⁻¹)⁻¹) c = _
    simp
  exact LinearMap.congr_fun hf v

private theorem left_single (x y : G) :
    ((BentVertex.traceCap b a).expand (R := Complex)).eval.toLinearMap
      (Finsupp.single ((Word.down (b.comp a)).basis.pair (Word.up b).basis x y) 1) =
        Generator.traceBasis Complex b (x * y) := by
  change (vertical (horizontal (splitDown b a) (id (.up b)))
    (vertical (associate (.down a) (.down b) (.up b))
      (vertical (horizontal (id (.down a)) (traceCap b)) (rightUnit (.down a))))).eval.toLinearMap
    (Finsupp.single ((Word.down (b.comp a)).basis.pair (Word.up b).basis x y) 1) = _
  rw [eval_vertical_apply, eval_vertical_apply, eval_vertical_apply,
    eval_horizontal_single (splitDown b a) (id (.up b)) x y 1, one_smul,
    eval_splitDown_single, eval_id_apply, Biset.pairLinear_single, one_mul,
    eval_associate_single (.down a) (.down b) (.up b) 1 x y 1]
  rw [eval_horizontal_single (id (.down a)) (traceCap b) 1
    ((Word.down b).basis.pair (Word.up b).basis x y) 1,
    one_smul, eval_id_apply, eval_traceCap_single, one_smul]
  exact rightUnit_pair_one a _

private theorem insertRightUnit_single (y : G) :
    (insertRightUnit (R := Complex) (.up b)).eval.toLinearMap (Finsupp.single y 1) =
      Finsupp.single ((Word.up b).basis.pair (Word.empty H).basis y 1) 1 := by
  change (Biset.insertRightUnit (Word.up b).basis Complex).toLinearMap _ = _
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]

private theorem branch_single (finite : a.toHom.range.FiniteIndex) (y : G) (T : Finset H)
    (hc : (reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single 1 1) =
      ∑ t ∈ T, Finsupp.single ((Word.up a).basis.pair (Word.down a).basis t⁻¹ t) 1) :
    ((BentVertex.reverseCup b a finite).expand (R := Complex)).eval.toLinearMap (Finsupp.single y 1) =
      ∑ t ∈ T, Finsupp.single
        ((Word.up (b.comp a)).basis.pair (Word.down a).basis (y * b.toHom t⁻¹) t) 1 := by
  change (vertical (insertRightUnit (.up b))
    (vertical (horizontal (id (.up b)) (reverseCup a finite))
      (vertical (unassociate (.up b) (.up a) (.down a))
        (horizontal (mergeUp b a) (id (.down a)))))).eval.toLinearMap (Finsupp.single y 1) = _
  rw [eval_vertical_apply, eval_vertical_apply, eval_vertical_apply,
    insertRightUnit_single b, eval_horizontal_single (id (.up b)) (reverseCup a finite) y 1 1,
    one_smul, eval_id_apply, hc, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Biset.pairLinear_single, one_mul, eval_unassociate_single (.up b) (.up a) (.down a) y t⁻¹ t 1,
    eval_horizontal_single (mergeUp b a) (id (.down a)) _ t 1, one_smul,
    eval_mergeUp_single, eval_id_apply, Biset.pairLinear_single, one_mul]

private abbrev tail (a : ConjEmbedding K H) (b : ConjEmbedding H G) :
    Diagram Complex ((Word.down (b.comp a)).tensor ((Word.up (b.comp a)).tensor (.down a))) (.down a) :=
  .vertical (.unassociate (.down (b.comp a)) (.up (b.comp a)) (.down a))
    (.vertical (.horizontal (.traceCap (b.comp a)) (.id (.down a))) (.leftUnit (.down a)))

private theorem tail_single (x z : G) (t : H) :
    (tail a b).eval.toLinearMap
      (Finsupp.single ((Word.down (b.comp a)).basis.pair
        ((Word.up (b.comp a)).tensor (.down a)).basis x
        ((Word.up (b.comp a)).basis.pair (Word.down a).basis z t)) 1) =
    (leftUnit (R := Complex) (.down a)).eval.toLinearMap
      (Biset.pairLinear Complex (Word.empty K).basis (Word.down a).basis
        (Generator.traceBasis Complex (b.comp a) (x * z)) (Finsupp.single t 1)) := by
  unfold tail
  rw [eval_vertical_apply, eval_vertical_apply,
    eval_unassociate_single (.down (b.comp a)) (.up (b.comp a)) (.down a) x z t 1,
    eval_horizontal_single (traceCap (b.comp a)) (id (.down a)) _ t 1, one_smul,
    eval_traceCap_single, one_smul, eval_id_apply]

private theorem right_sum (finite : a.toHom.range.FiniteIndex) (x y : G) (T : Finset H)
    (hc : (reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single 1 1) =
      ∑ t ∈ T, Finsupp.single ((Word.up a).basis.pair (Word.down a).basis t⁻¹ t) 1) :
    (vertical (horizontal (id (.down (b.comp a))) ((BentVertex.reverseCup b a finite).expand))
      (tail a b)).eval.toLinearMap
        (Finsupp.single ((Word.down (b.comp a)).basis.pair (Word.up b).basis x y) 1) =
      ∑ t ∈ T, (leftUnit (R := Complex) (.down a)).eval.toLinearMap
        (Biset.pairLinear Complex (Word.empty K).basis (Word.down a).basis
          (Generator.traceBasis Complex (b.comp a) (x * (y * b.toHom t⁻¹))) (Finsupp.single t 1)) := by
  rw [eval_vertical_apply,
    eval_horizontal_single (id (.down (b.comp a))) ((BentVertex.reverseCup b a finite).expand) x y 1,
    one_smul, eval_id_apply, branch_single a b finite y T hc, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Biset.pairLinear_single, one_mul, tail_single]

end TraceCapBendSupport
