import MackeyDiagrams
import Proofs.InductionRestrictionAdjunction
import Proofs.ReverseTriangleIdentities
import Proofs.BalancedTensorAssociativity
import Proofs.InductionRestrictionBimoduleStrands

set_option maxHeartbeats 2000000

theorem CupCapStraightening : (
∀ {U : Type u} [Group U] (H G : Subgroup U) (α β : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let upA := MackeyDiagrams.Word.up a
  let downA := MackeyDiagrams.Word.down a
  let upB := MackeyDiagrams.Word.up b
  let downB := MackeyDiagrams.Word.down b
  let idUp := MackeyDiagrams.Diagram.id (R := Complex) upA
  let idDown := MackeyDiagrams.Diagram.id (R := Complex) downB
  let ordinaryUp :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.insertRightUnit upA)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal idUp (MackeyDiagrams.Diagram.ordinaryCup a))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upA downA upA)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.multiplicationCap a) idUp)
            (MackeyDiagrams.Diagram.leftUnit upA))))
  let ordinaryDown :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.insertLeftUnit downB)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.ordinaryCup b) idDown)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.associate downB upB downB)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal idDown (MackeyDiagrams.Diagram.multiplicationCap b))
            (MackeyDiagrams.Diagram.rightUnit downB))))
  MackeyDiagrams.Diagram.eval ordinaryUp = MackeyDiagrams.Diagram.eval idUp ∧
  MackeyDiagrams.Diagram.eval ordinaryDown = MackeyDiagrams.Diagram.eval idDown ∧
  (∀ finiteA : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)),
    let reverseUp :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.insertLeftUnit upA)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.reverseCup a finiteA) idUp)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.associate upA downA upA)
            (MackeyDiagrams.Diagram.vertical
              (MackeyDiagrams.Diagram.horizontal idUp (MackeyDiagrams.Diagram.traceCap a))
              (MackeyDiagrams.Diagram.rightUnit upA))))
    MackeyDiagrams.Diagram.eval reverseUp = MackeyDiagrams.Diagram.eval idUp) ∧
  (∀ finiteB : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b)),
    let reverseDown :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.insertRightUnit downB)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idDown (MackeyDiagrams.Diagram.reverseCup b finiteB))
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.unassociate downB upB downB)
            (MackeyDiagrams.Diagram.vertical
              (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.traceCap b) idDown)
              (MackeyDiagrams.Diagram.leftUnit downB))))
    MackeyDiagrams.Diagram.eval reverseDown = MackeyDiagrams.Diagram.eval idDown)
) :=
(
by
  open MackeyDiagrams MackeyDiagrams.Diagram in
    classical
    intro U _ H G α β hα hβ
    dsimp only
    have ordinaryCupAtOne (a : ConjEmbedding H G) :
        (ordinaryCup (R := Complex) a).eval.toLinearMap (Finsupp.single (1 : H) 1) =
          Finsupp.single ((Biset.restriction a).pair (Biset.induction a) 1 1) 1 := by
      rw [eval_ordinaryCup_single (R := Complex) a, map_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Proposition 3.2, step (1), equation (3.5).
      -- Evaluate the paper's x ⊗ 1 ⊗ 1 on the balanced basis.
      -- The project cup and cap basis rules compute directly in the diagram evaluator.
      -- The unit insertion, rebracketing and unit removal are explicit in Lean.
      let a := ConjEmbedding.ofConjugator α hα
      let up := Word.up a
      let down := Word.down a
      apply eval_ext_on_generators
      intro x
      change G at x
      have insert (x : G) :
          (insertRightUnit (R := Complex) up).eval.toLinearMap (Finsupp.single x 1) =
            Finsupp.single (up.basis.pair (Biset.regular H) x 1) 1 := by
        change (Biset.insertRightUnit up.basis Complex).toLinearMap _ = _
        rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]
      change (leftUnit (R := Complex) up).eval.toLinearMap
        ((horizontal (multiplicationCap a) (id up)).eval.toLinearMap
          ((unassociate up down up).eval.toLinearMap
            ((horizontal (id up) (ordinaryCup a)).eval.toLinearMap
              ((insertRightUnit up).eval.toLinearMap (Finsupp.single x 1))))) =
        Finsupp.single x 1
      rw [insert x]
      rw [eval_horizontal_single (id up) (ordinaryCup a) x (1 : H) (1 : Complex),
        one_smul, eval_id_apply, ordinaryCupAtOne a, Biset.pairLinear_single, one_mul]
      rw [eval_unassociate_single up down up x (1 : G) (1 : G)]
      rw [eval_horizontal_single (multiplicationCap a) (id up)
          (up.basis.pair down.basis x 1) (1 : G) (1 : Complex),
        one_smul, eval_id_apply, eval_multiplicationCap_single, mul_one,
        Biset.pairLinear_single, one_mul, eval_leftUnit_single]
      change Finsupp.single (x * 1 * (a.toHom 1)⁻¹) (1 : Complex) = _
      simp
    · -- Proposition 3.2, step (2), equation (3.6).
      -- The other orientation gives 1 ⊗ 1 ⊗ y and caps the last two factors.
      let b := ConjEmbedding.ofConjugator β hβ
      let up := Word.up b
      let down := Word.down b
      apply eval_ext_on_generators
      intro y
      change G at y
      change (rightUnit (R := Complex) down).eval.toLinearMap
        ((horizontal (id down) (multiplicationCap b)).eval.toLinearMap
          ((associate down up down).eval.toLinearMap
            ((horizontal (ordinaryCup b) (id down)).eval.toLinearMap
              ((insertLeftUnit down).eval.toLinearMap (Finsupp.single y 1))))) =
        Finsupp.single y 1
      rw [eval_insertLeftUnit_single (R := Complex) down y 1]
      rw [eval_horizontal_single (ordinaryCup b) (id down) (1 : H) y (1 : Complex),
        one_smul, ordinaryCupAtOne b, eval_id_apply, Biset.pairLinear_single, one_mul]
      rw [eval_associate_single down up down (1 : G) (1 : G) y]
      rw [eval_horizontal_single (id down) (multiplicationCap b)
          (1 : G) (up.basis.pair down.basis 1 y) (1 : Complex),
        one_smul, eval_id_apply, eval_multiplicationCap_single, one_mul,
        Biset.pairLinear_single, one_mul, eval_rightUnit_single]
      change Finsupp.single (b.toHom 1 * 1 * (y⁻¹)⁻¹) (1 : Complex) = _
      simp
    · -- Proposition 3.2, step (3), equation (3.7).
      -- The checked diagram triangle already implements the paper's
      -- transversal sum on this exact composite, with the supplied index witness.
      -- The module universe of its unused categorical conjuncts can be zero.
      intro finiteA
      exact ((ReverseTriangleIdentities.{u, 0} H G α hα).2.2.2.2 finiteA).2.2.1.2
    · -- Proposition 3.2, step (4), equation (3.8).
      -- Use the downward diagram triangle with β's own finite-index witness.
      intro finiteB
      exact ((ReverseTriangleIdentities.{u, 0} H G β hβ).2.2.2.2 finiteB).2.2.1.1
)

#print axioms CupCapStraightening
