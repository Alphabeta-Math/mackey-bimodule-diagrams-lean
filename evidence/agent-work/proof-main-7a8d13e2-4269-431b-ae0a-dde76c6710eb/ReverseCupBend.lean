import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

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

theorem ReverseCupBend : (∀ {U : Type*} [Group U] (K H G : Subgroup U)
    (α : MackeyDiagrams.ConjEmbedding K H) (γ : MackeyDiagrams.ConjEmbedding H G),
  let composite := MackeyDiagrams.ConjEmbedding.comp γ α
  ∀ finite : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom composite)),
  let alphaHom := MackeyDiagrams.ConjEmbedding.toHom α
  let gammaHom := MackeyDiagrams.ConjEmbedding.toHom γ
  let finiteAlpha : Subgroup.FiniteIndex (MonoidHom.range alphaHom) := by
    let _ := finite
    have finitePreimage : Subgroup.FiniteIndex
        (Subgroup.comap gammaHom (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom composite))) :=
      inferInstance
    change Subgroup.FiniteIndex (Subgroup.comap gammaHom
      (MonoidHom.range (MonoidHom.comp gammaHom alphaHom))) at finitePreimage
    rw [MonoidHom.range_comp, Subgroup.comap_map_eq_self_of_injective
      (MackeyDiagrams.ConjEmbedding.injective γ)] at finitePreimage
    exact finitePreimage
  let upAlpha := MackeyDiagrams.Word.up α
  let downAlpha := MackeyDiagrams.Word.down α
  let upGamma := MackeyDiagrams.Word.up γ
  let downGamma := MackeyDiagrams.Word.down γ
  let upComposite := MackeyDiagrams.Word.up composite
  let downComposite := MackeyDiagrams.Word.down composite
  let output := MackeyDiagrams.Word.tensor upComposite downAlpha
  let idUpGamma := MackeyDiagrams.Diagram.id (R := Complex) upGamma
  let left : MackeyDiagrams.Diagram Complex upGamma output :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.insertRightUnit upGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal idUpGamma
          (MackeyDiagrams.Diagram.reverseCup α finiteAlpha))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upGamma upAlpha downAlpha)
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeUp γ α)
            (MackeyDiagrams.Diagram.id downAlpha))))
  let rightBranch : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.tensor downComposite upGamma) downAlpha :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.splitDown γ α) idUpGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.associate downAlpha downGamma upGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id downAlpha)
            (MackeyDiagrams.Diagram.traceCap γ))
          (MackeyDiagrams.Diagram.rightUnit downAlpha)))
  let right : MackeyDiagrams.Diagram Complex upGamma output :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.insertLeftUnit upGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.reverseCup composite finite)
          idUpGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.associate upComposite downComposite upGamma)
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id upComposite)
            rightBranch)))
  MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right) :=
(by
  open MackeyDiagrams MackeyDiagrams.Diagram ReverseCupBendSupport in
  intro U _ K H G a b
  dsimp only
  intro finite
  -- Xiao, §3.5, Proposition 3.4, reverse-cup row. The archived original
  -- PDF has the diagrams on p. 12 and the computation on p. 13
  -- (SHA256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2).
  -- The revised published PDF has them on pp. 14 and 15 respectively
  -- (SHA256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  --
  -- Alphabeta Math's module tensor universal property, Steps 3.1 and 4.1,
  -- descends along the balance relations. The shared biset tensor already
  -- performs that descent, and pair_balance applies it to the two basis
  -- representatives of the right unital insertion. As in Step 5.1, equality
  -- follows on generators, here the group elements with coefficient one.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  --
  -- FiniteIndexReverseAdjunction supplies the right transversal and the
  -- cup formula on group elements after transport to a conjugating
  -- representative. The shared merge/split basis rules underlying
  -- InductionRestrictionMergesAndSplits apply directly to a and b.
  -- The associate and trace basis rules apply to the resulting pairs.
  -- Its cup formula uses rightCosetEquivCapFiber and computes transfer
  -- coefficients with transferBasis_apply. The public projection of
  -- that formula already gives the required sum over representatives.
  have finiteAlpha : a.toHom.range.FiniteIndex := by
    let := finite
    have h : ((b.comp a).toHom.range.comap b.toHom).FiniteIndex := inferInstance
    change ((b.toHom.comp a.toHom).range.comap b.toHom).FiniteIndex at h
    rw [MonoidHom.range_comp, Subgroup.comap_map_eq_self_of_injective b.injective] at h
    exact h
  change ((BentVertex.reverseCup b a finiteAlpha).expand (R := Complex)).eval =
    (rightBend a b finite).eval
  classical
  obtain ⟨⟨S, hS⟩, cupLarge⟩ := cupTransversal (b.comp a) finite
  have cupSmall := (cupTransversal a finiteAlpha).2
  -- The article chooses a product transversal and isolates the slice
  -- indexed by the identity coset. For an arbitrary large transversal,
  -- pull back that slice along b.toHom. This gives the same surviving
  -- terms without requiring a separate choice of outer representatives.
  let T := S.preimage b.toHom b.injective.injOn
  have memT (t : H) : t ∈ T ↔ b.toHom t ∈ S := Finset.mem_preimage
  have cosetTest (x y : H) :
      b.toHom x * (b.toHom y)⁻¹ ∈ (b.comp a).toHom.range ↔
        x * y⁻¹ ∈ a.toHom.range := by
    rw [← map_inv, ← map_mul]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, b.injective hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg b.toHom hk⟩
  have hT : RightTransversal a T := by
    intro h
    obtain ⟨s, hs, unique⟩ := hS (b.toHom h)
    have hsImage : s.val ∈ b.toHom.range := by
      obtain ⟨k, hk⟩ := hs
      refine ⟨(a.toHom k)⁻¹ * h, ?_⟩
      rw [map_mul, map_inv, ← ConjEmbedding.comp_apply, hk]
      group
    obtain ⟨t, ht⟩ := hsImage
    have htT : t ∈ T := (memT t).2 (ht.symm ▸ s.property)
    refine ⟨⟨t, htT⟩, (cosetTest h t).1 ?_, ?_⟩
    · rwa [ht]
    · intro u hu
      apply Subtype.ext
      apply b.injective
      have he := unique ⟨b.toHom u.val, (memT u.val).1 u.property⟩ ((cosetTest h u.val).2 hu)
      exact (congrArg Subtype.val he).trans ht.symm
  have smallAtOne := cupSmall T hT (1 : H)
  simp only [one_mul] at smallAtOne
  apply eval_ext_on_generators
  intro g
  change G at g
  rw [leftSum a b finiteAlpha g T smallAtOne, rightSum a b finite g S (cupLarge S hS g)]
  calc
    _ = ∑ s ∈ S.filter (fun s => s ∈ b.toHom.range), rightTerm a b g s := by
      refine Finset.sum_bij (fun t _ => b.toHom t) ?_ ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_filter.mpr ⟨(memT t).1 ht, ⟨t, rfl⟩⟩
      · intro t _ u _ he
        exact b.injective he
      · intro s hs
        obtain ⟨hsS, t, ht⟩ := Finset.mem_filter.mp hs
        exact ⟨t, (memT t).2 (ht.symm ▸ hsS), ht⟩
      · intro t _
        simp only [rightTerm, Generator.traceBasis_image, outputSingle]
        rw [Biset.pairLinear_single, one_mul]
    _ = _ := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro s hs hsFiltered
      have hsOutside : ¬ ∃ t : H, b.toHom t = s := by
        intro himage
        exact hsFiltered (Finset.mem_filter.mpr ⟨hs, himage⟩)
      simp only [rightTerm, Generator.traceBasis_outside Complex b s hsOutside, map_zero])

#print axioms ReverseCupBend
