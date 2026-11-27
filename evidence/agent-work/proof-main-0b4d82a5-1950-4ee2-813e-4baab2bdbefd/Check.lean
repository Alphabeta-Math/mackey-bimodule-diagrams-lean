import MackeyDiagrams
import Proofs.InductionRestrictionAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

theorem MultiplicationCapBend : (
∀ {U : Type*} [Group U] (K H G : Subgroup U) (α γ : U)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ H)
    (hγ : ∀ h : H, γ * (h : U) * γ⁻¹ ∈ G),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let g := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let ga := MackeyDiagrams.ConjEmbedding.comp g a
  let upG := MackeyDiagrams.Word.up g
  let upA := MackeyDiagrams.Word.up a
  let upGA := MackeyDiagrams.Word.up ga
  let downA := MackeyDiagrams.Word.down a
  let downG := MackeyDiagrams.Word.down g
  let downGA := MackeyDiagrams.Word.down ga
  let straight := MackeyDiagrams.Diagram.id (R := Complex) upG
  let leftCap := MackeyDiagrams.Diagram.horizontal straight
    (MackeyDiagrams.Diagram.multiplicationCap a)
  let leftSplit := MackeyDiagrams.Diagram.horizontal
    (MackeyDiagrams.Diagram.splitUp g a) (MackeyDiagrams.Diagram.id downA)
  let left := MackeyDiagrams.Diagram.vertical leftSplit
    (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.associate upG upA downA)
      (MackeyDiagrams.Diagram.vertical leftCap (MackeyDiagrams.Diagram.rightUnit upG)))
  let rightCup := MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id downA)
    (MackeyDiagrams.Diagram.ordinaryCup (R := Complex) g)
  let rightBranch := MackeyDiagrams.Diagram.vertical
    (MackeyDiagrams.Diagram.insertRightUnit downA)
    (MackeyDiagrams.Diagram.vertical rightCup
      (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.unassociate downA downG upG)
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeDown g a) straight)))
  let rightCap := MackeyDiagrams.Diagram.horizontal
    (MackeyDiagrams.Diagram.multiplicationCap ga) straight
  let right := MackeyDiagrams.Diagram.vertical
    (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id upGA) rightBranch)
    (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.unassociate upGA downGA upG)
      (MackeyDiagrams.Diagram.vertical rightCap (MackeyDiagrams.Diagram.leftUnit upG)))
  MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right
) :=
(by
  intro U _ K H G α γ hα hγ a g ga upG upA upGA downA downG downGA
    straight leftCap leftSplit left rightCup rightBranch rightCap right
  exact (open MackeyDiagrams MackeyDiagrams.Diagram in by
    -- Xiao, § 3.5, Proposition 3.4, multiplication-cap row. It is on p. 12 of
    -- the archived original in source/ and p. 14 of the current published PDF.
    -- The published bytes match article-revision/mackey-bimodules.pdf. The two
    -- versions give the same shapes and the same tensor calculation for this row.
    --
    -- Alphabeta Math, thm-universal-property-of-module-tensor-products, steps
    -- 4.1 and 5.1. The typed evaluations already descend to the balanced
    -- quotient. Apply generator uniqueness on its complex linearization using
    -- eval_ext_on_generators, then use quotient induction to present a generator.
    apply eval_ext_on_generators
    intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨x, y⟩
    change G at x
    change H at y
    change left.eval.toLinearMap (Finsupp.single (upGA.basis.pair downA.basis x y) 1) =
      right.eval.toLinearMap (Finsupp.single (upGA.basis.pair downA.basis x y) 1)
    -- The paper suppresses rebracketing and unitors. On the left, splitUp
    -- inserts 1 in H, the small cap multiplies in H, and rightUnit applies
    -- the right H action along g.toHom.
    have hLeft : left.eval.toLinearMap (Finsupp.single (upGA.basis.pair downA.basis x y) 1) =
        Finsupp.single (x * g.toHom y) 1 := by
      change (rightUnit (R := Complex) upG).eval.toLinearMap
        ((horizontal (id upG) (multiplicationCap a)).eval.toLinearMap
          ((associate upG upA downA).eval.toLinearMap
            ((horizontal (splitUp g a) (id downA)).eval.toLinearMap
              (Finsupp.single (upGA.basis.pair downA.basis x y) (1 : Complex))))) = _
      rw [eval_horizontal_single (splitUp g a) (id downA) x y 1,
        one_smul, eval_splitUp_single, eval_id_apply, Biset.pairLinear_single, one_mul]
      rw [eval_associate_single upG upA downA x 1 y 1]
      rw [eval_horizontal_single (id upG) (multiplicationCap a), one_smul, eval_id_apply,
        eval_multiplicationCap_single a 1 y 1, one_mul, Biset.pairLinear_single, one_mul,
        eval_rightUnit_single upG]
      change Finsupp.single (1 * x * (g.toHom y⁻¹)⁻¹) 1 = _
      simp only [one_mul, map_inv, inv_inv]
    -- These are the basis formulas underlying InductionRestrictionMergesAndSplits
    -- and InductionRestrictionAdjunction. The bend uses splitUp on the left
    -- and mergeDown on the right, so the route's mergeUp and splitDown formulas
    -- are replaced by eval_splitUp_single and eval_mergeDown_single.
    -- On the right the ordinary cup at 1 inserts (1, 1) by map_one.
    have hBranch : rightBranch.eval.toLinearMap (Finsupp.single y 1) =
        Finsupp.single (downGA.basis.pair upG.basis (g.toHom y) 1) 1 := by
      have hInsert : (insertRightUnit (R := Complex) downA).eval.toLinearMap (Finsupp.single y 1) =
          Finsupp.single (downA.basis.pair (Biset.regular H) y 1) 1 := by
        change (Biset.insertRightUnit downA.basis Complex).toLinearMap (Finsupp.single y 1) = _
        rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]
      change (horizontal (mergeDown g a) (id upG)).eval.toLinearMap
        ((unassociate downA downG upG).eval.toLinearMap
          ((horizontal (id downA) (ordinaryCup g)).eval.toLinearMap
            ((insertRightUnit downA).eval.toLinearMap (Finsupp.single y (1 : Complex))))) = _
      rw [hInsert, eval_horizontal_single (id downA) (ordinaryCup g) y 1 1,
        one_smul, eval_id_apply, eval_ordinaryCup_single g 1 1, map_one,
        Biset.pairLinear_single, one_mul, eval_unassociate_single downA downG upG y 1 1 1]
      rw [eval_horizontal_single (mergeDown g a) (id upG), one_smul,
        eval_mergeDown_single g a y 1 1, mul_one, eval_id_apply, Biset.pairLinear_single, one_mul]
    -- The large cap multiplies in G and the left unitor acts on the retained 1.
    have hRight : right.eval.toLinearMap (Finsupp.single (upGA.basis.pair downA.basis x y) 1) =
        Finsupp.single (x * g.toHom y) 1 := by
      change (leftUnit (R := Complex) upG).eval.toLinearMap
        ((horizontal (multiplicationCap ga) (id upG)).eval.toLinearMap
          ((unassociate upGA downGA upG).eval.toLinearMap
            ((horizontal (id upGA) rightBranch).eval.toLinearMap
              (Finsupp.single (upGA.basis.pair downA.basis x y) (1 : Complex))))) = _
      rw [eval_horizontal_single (id upGA) rightBranch x y 1, one_smul,
        eval_id_apply, hBranch, Biset.pairLinear_single, one_mul]
      rw [eval_unassociate_single upGA downGA upG x (g.toHom y) 1 1]
      rw [eval_horizontal_single (multiplicationCap ga) (id upG), one_smul,
        eval_multiplicationCap_single ga x (g.toHom y) 1, eval_id_apply,
        Biset.pairLinear_single, one_mul, eval_leftUnit_single upG]
      change Finsupp.single ((x * g.toHom y) * 1 * (g.toHom 1)⁻¹) 1 = _
      simp only [mul_one, map_one, inv_one]
    exact hLeft.trans hRight.symm
  ))

#print axioms MultiplicationCapBend
