import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

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

theorem TraceCapBend : (
∀ {U : Type*} [Group U] (K H G : Subgroup U)
    (α : MackeyDiagrams.ConjEmbedding K H) (γ : MackeyDiagrams.ConjEmbedding H G)
    (finite : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom α))),
  let composite := MackeyDiagrams.ConjEmbedding.comp γ α
  let downComposite := MackeyDiagrams.Word.down composite
  let upComposite := MackeyDiagrams.Word.up composite
  let downGamma := MackeyDiagrams.Word.down γ
  let upGamma := MackeyDiagrams.Word.up γ
  let upAlpha := MackeyDiagrams.Word.up α
  let output := MackeyDiagrams.Word.down α
  let input := MackeyDiagrams.Word.tensor downComposite upGamma
  let idOutput := MackeyDiagrams.Diagram.id (R := Complex) output
  let left : MackeyDiagrams.Diagram Complex input output :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.splitDown γ α)
        (MackeyDiagrams.Diagram.id upGamma))
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.associate output downGamma upGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idOutput (MackeyDiagrams.Diagram.traceCap γ))
          (MackeyDiagrams.Diagram.rightUnit output)))
  let rightBranch : MackeyDiagrams.Diagram Complex upGamma
      (MackeyDiagrams.Word.tensor upComposite output) :=
    MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit upGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id upGamma)
          (MackeyDiagrams.Diagram.reverseCup α finite))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upGamma upAlpha output)
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeUp γ α) idOutput)))
  let right : MackeyDiagrams.Diagram Complex input output :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id downComposite) rightBranch)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.unassociate downComposite upComposite output)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.traceCap composite) idOutput)
          (MackeyDiagrams.Diagram.leftUnit output)))
  MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right
) :=
(by
  open MackeyDiagrams MackeyDiagrams.Diagram TraceCapBendSupport in
  intro U _ K H G a b finite
  -- Xiao, §3.5, Proposition 3.4, trace-cap row. Archived PDF pp. 12–13
  -- (bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and revised published PDF pp. 14–15
  -- (6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e)
  -- give the same ordered boundary K–G–H to K–H and the same trace calculation.
  -- Step 3.1 of Alphabeta Math's module tensor universal property factors
  -- through the balance relations. The shared evaluator handles that descent.
  -- Step 4.1 compares maps on elementary tensors. Here Quotient.inductionOn
  -- gives representatives of balanced pairs and eval_ext_on_generators
  -- extends the comparison linearly. Step 5.1 needs no choice for descent.
  -- The finite transversal below comes from the reverse-cup formula.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  change ((BentVertex.traceCap b a).expand (R := Complex)).eval =
    (vertical (horizontal (id (.down (b.comp a))) ((BentVertex.reverseCup b a finite).expand))
      (tail a b)).eval
  classical
  -- Use the registered reverse-adjunction theorem only for its cup formula
  -- and unique right transversal, instantiated at the inner finite-index image.
  -- The companion merges/splits theorem builds from the same shared basis rules.
  -- Those rules apply here directly to a and b, without choosing conjugators
  -- for the merge or split. The trace tests use the coordinator's basis rules.
  obtain ⟨T, hT, hcup⟩ := cup_transversal a finite
  apply eval_ext_on_generators
  intro z
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change G at x y
  let input := Finsupp.single ((Word.down (b.comp a)).basis.pair (Word.up b).basis x y) (1 : Complex)
  change ((BentVertex.traceCap b a).expand (R := Complex)).eval.toLinearMap input =
    (vertical (horizontal (id (.down (b.comp a))) ((BentVertex.reverseCup b a finite).expand))
      (tail a b)).eval.toLinearMap input
  dsimp only [input]
  rw [left_single a b x y, right_sum a b finite x y T hcup]
  let term (t : H) : H →₀ Complex :=
    (leftUnit (R := Complex) (.down a)).eval.toLinearMap
      (Biset.pairLinear Complex (Word.empty K).basis (Word.down a).basis
        (Generator.traceBasis Complex (b.comp a) (x * (y * b.toHom t⁻¹))) (Finsupp.single t 1))
  change Generator.traceBasis Complex b (x * y) = ∑ t ∈ T, term t
  -- Multiplying by the image of t⁻¹ reduces the large trace to a
  -- test on the corresponding right coset in H when x * y is in the image.
  have product (t : H) :
      x * (y * b.toHom t⁻¹) = (x * y) * (b.toHom t)⁻¹ := by
    rw [map_inv, mul_assoc]
  have zeroTerm (t : H) (hout : ¬ ∃ k : K, (b.comp a).toHom k = x * (y * b.toHom t⁻¹)) :
      term t = 0 := by
    dsimp only [term]
    rw [Generator.traceBasis_outside Complex (b.comp a) _ hout, map_zero, LinearMap.zero_apply, map_zero]
  by_cases hin : ∃ h : H, b.toHom h = x * y
  · obtain ⟨h, hh⟩ := hin
    rw [← hh, Generator.traceBasis_image]
    -- Exactly one representative survives the large trace.
    obtain ⟨t, ht, unique⟩ := hT h
    obtain ⟨k, hk⟩ := ht
    have htProduct : x * (y * b.toHom (t.val)⁻¹) = (b.comp a).toHom k := by
      rw [product, ← hh, ← map_inv, ← map_mul, ← hk, ConjEmbedding.comp_apply]
    have hterm : term t.val = Finsupp.single h 1 := by
      dsimp only [term]
      rw [htProduct, Generator.traceBasis_image, Biset.pairLinear_single, one_mul,
        eval_leftUnit_single]
      change Finsupp.single (a.toHom k * t.val * (1 : H)⁻¹) 1 = _
      rw [hk, inv_one, mul_one, mul_assoc, inv_mul_cancel, mul_one]
    rw [Finset.sum_eq_single t.val, hterm]
    · intro s hs hst
      apply zeroTerm
      rintro ⟨l, hl⟩
      rw [product, ← hh, ← map_inv, ← map_mul, ConjEmbedding.comp_apply] at hl
      have hm : h * s⁻¹ ∈ a.toHom.range := ⟨l, b.injective hl⟩
      exact hst (congrArg Subtype.val (unique ⟨s, hs⟩ hm))
    · exact fun hmissing => (hmissing t.property).elim
  · -- The composite image is contained in the outer image, which is
    -- invariant under multiplication by b.toHom t.
    rw [Generator.traceBasis_outside Complex b _ hin]
    symm
    apply Finset.sum_eq_zero
    intro t _
    apply zeroTerm
    rintro ⟨k, hk⟩
    rw [product, ConjEmbedding.comp_apply] at hk
    apply hin
    refine ⟨a.toHom k * t, ?_⟩
    rw [map_mul, hk, mul_assoc, inv_mul_cancel, mul_one])
