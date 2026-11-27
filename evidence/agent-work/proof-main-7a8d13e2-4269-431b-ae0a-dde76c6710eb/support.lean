namespace ReverseCupBendSupport

open MackeyDiagrams MackeyDiagrams.Diagram

universe u
noncomputable section
variable {U : Type u} [Group U] {K H G : Subgroup U}

private abbrev RightTransversal {A B : Subgroup U} (a : ConjEmbedding A B) (T : Finset B) :=
  ∀ g : B, ∃! t : {t // t ∈ T}, g * t.val⁻¹ ∈ a.toHom.range

-- Use the registered cup formula, transporting it along the equality between
-- the given embedding and the embedding defined by its conjugating representative.
private theorem cupTransversal {A B : Subgroup U} (a : ConjEmbedding A B)
    (finite : a.toHom.range.FiniteIndex) :
    (∃ T, RightTransversal a T) ∧
    ∀ (T : Finset B), RightTransversal a T → ∀ g : B,
      (reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single g 1) =
        ∑ t ∈ T, Finsupp.single ((Word.up a).basis.pair (Word.down a).basis (g * t⁻¹) t) 1 := by
  obtain ⟨s, hs⟩ := a.hasRepresentative
  have hs' (h : A) : s * (h : U) * s⁻¹ ∈ B := hs h ▸ (a.toHom h).property
  have ha : a = ConjEmbedding.ofConjugator s hs' :=
    ConjEmbedding.ext (MonoidHom.ext fun h => Subtype.ext (hs h))
  subst a
  obtain ⟨hExists, _, _, hcup⟩ :=
    (FiniteIndexReverseAdjunction.{u, 0} A B s hs').2.2.2.2 finite
  refine ⟨hExists, fun T hT g => ?_⟩
  have h := ((hcup T hT).1 g).1
  simp only [MonoidAlgebra.coeff_single] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro t _
  rw [Biset.pairLinear_single, one_mul]

variable (a : ConjEmbedding K H) (b : ConjEmbedding H G)

private abbrev rightBend (finite : (b.comp a).toHom.range.FiniteIndex) :
    Diagram Complex (.up b) ((Word.up (b.comp a)).tensor (.down a)) :=
  .vertical (.insertLeftUnit (.up b))
    (.vertical (.horizontal (.reverseCup (b.comp a) finite) (.id (.up b)))
      (.vertical (.associate (.up (b.comp a)) (.down (b.comp a)) (.up b))
        (.horizontal (.id (.up (b.comp a))) ((BentVertex.traceCap b a).expand))))

private abbrev outputSingle (x : G) (t : H) :
    ((Word.up (b.comp a)).tensor (.down a)).basis.carrier →₀ Complex :=
  Finsupp.single ((Word.up (b.comp a)).basis.pair (Word.down a).basis x t) 1

private theorem leftSum (finite : a.toHom.range.FiniteIndex) (g : G) (T : Finset H)
    (hcup : (reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single 1 1) =
      ∑ t ∈ T, Finsupp.single ((Word.up a).basis.pair (Word.down a).basis t⁻¹ t) 1) :
    ((BentVertex.reverseCup b a finite).expand (R := Complex)).eval.toLinearMap (Finsupp.single g 1) =
      ∑ t ∈ T, outputSingle a b (g * (b.toHom t)⁻¹) t := by
  have hunit :
      (insertRightUnit (R := Complex) (.up b)).eval.toLinearMap (Finsupp.single g 1) =
        Finsupp.single ((Word.up b).basis.pair (Word.empty H).basis g 1) 1 := by
    change (Biset.insertRightUnit (Word.up b).basis Complex).toLinearMap _ = _
    exact Biset.Hom.ofFunction_single _ _ _ _
  change (vertical (insertRightUnit (.up b))
    (vertical (horizontal (id (.up b)) (reverseCup a finite))
      (vertical (unassociate (.up b) (.up a) (.down a))
        (horizontal (mergeUp b a) (id (.down a)))))).eval.toLinearMap (Finsupp.single g 1) = _
  rw [eval_vertical_apply, eval_vertical_apply, eval_vertical_apply,
    hunit, eval_horizontal_single (id (.up b)) (reverseCup a finite) g 1 1,
    one_smul, eval_id_apply, hcup, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Biset.pairLinear_single, one_mul, eval_unassociate_single (.up b) (.up a) (.down a) g t⁻¹ t 1,
    eval_horizontal_single (mergeUp b a) (id (.down a)) _ t 1, one_smul,
    eval_mergeUp_single, eval_id_apply, Biset.pairLinear_single, one_mul, map_inv]

private theorem traceBranch (t : G) :
    ((BentVertex.traceCap b a).expand (R := Complex)).eval.toLinearMap
      (Finsupp.single ((Word.down (b.comp a)).basis.pair (Word.up b).basis t 1) 1) =
        Generator.traceBasis Complex b t := by
  let f := (rightUnit (R := Complex) (.down a)).eval.toLinearMap ∘ₗ
    (Biset.pairLinear Complex (Word.down a).basis (Word.empty H).basis (Finsupp.single 1 1))
  have hf : f = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro h c
    change (rightUnit (R := Complex) (.down a)).eval.toLinearMap
      (Biset.pairLinear Complex (Word.down a).basis (Word.empty H).basis
        (Finsupp.single 1 1) (Finsupp.single h c)) = Finsupp.single h c
    rw [Biset.pairLinear_single, one_mul, eval_rightUnit_single]
    change Finsupp.single (a.toHom 1 * 1 * (h⁻¹)⁻¹) c = _
    simp
  change (vertical (horizontal (splitDown b a) (id (.up b)))
    (vertical (associate (.down a) (.down b) (.up b))
      (vertical (horizontal (id (.down a)) (traceCap b)) (rightUnit (.down a))))).eval.toLinearMap
    (Finsupp.single ((Word.down (b.comp a)).basis.pair (Word.up b).basis t 1) 1) = _
  rw [eval_vertical_apply, eval_vertical_apply, eval_vertical_apply,
    eval_horizontal_single (splitDown b a) (id (.up b)) t 1 1, one_smul,
    eval_splitDown_single, eval_id_apply, Biset.pairLinear_single, one_mul,
    eval_associate_single (.down a) (.down b) (.up b) 1 t 1 1,
    eval_horizontal_single (id (.down a)) (traceCap b) 1
      ((Word.down b).basis.pair (Word.up b).basis t 1) 1,
    one_smul, eval_id_apply, eval_traceCap_single, one_smul, mul_one]
  exact LinearMap.congr_fun hf _

private abbrev rightTerm (g t : G) :
    ((Word.up (b.comp a)).tensor (.down a)).basis.carrier →₀ Complex :=
  Biset.pairLinear Complex (Word.up (b.comp a)).basis (Word.down a).basis
    (Finsupp.single (g * t⁻¹) 1) (Generator.traceBasis Complex b t)

private theorem rightSum (finite : (b.comp a).toHom.range.FiniteIndex) (g : G) (S : Finset G)
    (hcup : (reverseCup (R := Complex) (b.comp a) finite).eval.toLinearMap (Finsupp.single g 1) =
      ∑ t ∈ S, Finsupp.single
        ((Word.up (b.comp a)).basis.pair (Word.down (b.comp a)).basis (g * t⁻¹) t) 1) :
    (rightBend a b finite).eval.toLinearMap (Finsupp.single g 1) = ∑ t ∈ S, rightTerm a b g t := by
  -- In the balanced tensor product, 1 ⊗ g is represented by g ⊗ 1.
  have hbalance : (Biset.regular G).pair (Word.up b).basis g 1 =
      (Biset.regular G).pair (Word.up b).basis 1 g := by
    have h := (Biset.regular G).pair_balance (Word.up b).basis g 1 1
    change (Biset.regular G).pair (Word.up b).basis (1 * 1 * (g⁻¹)⁻¹) 1 =
      (Biset.regular G).pair (Word.up b).basis 1 (g * 1 * (b.toHom 1)⁻¹) at h
    simpa only [inv_inv, one_mul, map_one, inv_one, mul_one] using h
  unfold rightBend
  rw [eval_vertical_apply, eval_vertical_apply, eval_vertical_apply, eval_insertLeftUnit_single,
    ← hbalance,
    eval_horizontal_single (reverseCup (b.comp a) finite) (id (.up b)) g 1 1,
    one_smul, eval_id_apply, hcup]
  let pairWithOne := (Biset.pairLinear Complex
    ((Word.up (b.comp a)).tensor (.down (b.comp a))).basis (Word.up b).basis).flip
      (Finsupp.single 1 1)
  let tail := (horizontal (R := Complex) (id (.up (b.comp a)))
      ((BentVertex.traceCap b a).expand)).eval.toLinearMap ∘ₗ
    (associate (R := Complex) (.up (b.comp a)) (.down (b.comp a)) (.up b)).eval.toLinearMap ∘ₗ
    pairWithOne
  change tail (∑ t ∈ S, Finsupp.single
    ((Word.up (b.comp a)).basis.pair (Word.down (b.comp a)).basis (g * t⁻¹) t) 1) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [tail, pairWithOne, LinearMap.comp_apply, LinearMap.flip_apply]
  rw [Biset.pairLinear_single, mul_one,
    eval_associate_single (.up (b.comp a)) (.down (b.comp a)) (.up b) (g * t⁻¹) t 1 1,
    eval_horizontal_single (id (.up (b.comp a))) ((BentVertex.traceCap b a).expand) _ _ 1,
    one_smul, eval_id_apply, traceBranch]

end
end ReverseCupBendSupport
