import MackeyDiagrams
import Proofs.InductionRestrictionAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

theorem OrdinaryCupBend : (
∀ {U : Type*} [Group U] (K H G : Subgroup U)
    (α : MackeyDiagrams.ConjEmbedding K H) (γ : MackeyDiagrams.ConjEmbedding H G),
  let composite := MackeyDiagrams.ConjEmbedding.comp γ α
  let upAlpha := MackeyDiagrams.Word.up α
  let downAlpha := MackeyDiagrams.Word.down α
  let upGamma := MackeyDiagrams.Word.up γ
  let downGamma := MackeyDiagrams.Word.down γ
  let upComposite := MackeyDiagrams.Word.up composite
  let downComposite := MackeyDiagrams.Word.down composite
  let output := MackeyDiagrams.Word.tensor downGamma upComposite
  let left : MackeyDiagrams.Diagram Complex upAlpha output :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.insertLeftUnit upAlpha)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.ordinaryCup γ)
          (MackeyDiagrams.Diagram.id upAlpha))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.associate downGamma upGamma upAlpha)
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id downGamma)
            (MackeyDiagrams.Diagram.mergeUp γ α))))
  let rightBranch : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.tensor upAlpha downComposite) downGamma :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id upAlpha)
        (MackeyDiagrams.Diagram.splitDown γ α))
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.unassociate upAlpha downAlpha downGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.multiplicationCap α)
            (MackeyDiagrams.Diagram.id downGamma))
          (MackeyDiagrams.Diagram.leftUnit downGamma)))
  let right : MackeyDiagrams.Diagram Complex upAlpha output :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.insertRightUnit upAlpha)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id upAlpha)
          (MackeyDiagrams.Diagram.ordinaryCup composite))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upAlpha downComposite upComposite)
          (MackeyDiagrams.Diagram.horizontal rightBranch
            (MackeyDiagrams.Diagram.id upComposite))))
  MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right
) :=
((by
  intro U _ K H G α γ composite upAlpha downAlpha upGamma downGamma
    upComposite downComposite output left rightBranch right
  exact (open MackeyDiagrams MackeyDiagrams.Diagram in by
    -- Xiao, § 3.5, Proposition 3.4, Ordinary cup. The diagram row is on p. 12
    -- of the archived original in source/ and p. 14 of the revised published
    -- PDF. The corresponding computations are on pp. 13 and 15 respectively.
    -- The download matches article-revision/mackey-bimodules.pdf. The archived
    -- original has a different SHA-256 digest.
    -- https://getcurious.cc/downloads/mackey-bimodules.pdf
    --
    -- Alphabeta Math, tensor-product universal property, Steps 3.1 and 4.1.
    -- The project already handles descent through the balance relation in
    -- the biset quotient and enforces additivity by Complex-linear extension.
    -- Use the generator uniqueness in Step 5.1 on the input word, whose
    -- basis consists of elements of H with coefficient one.
    -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
    apply eval_ext_on_generators
    intro x
    change H at x
    -- The paper suppresses the unitors and rebracketing. The project basis
    -- formulas for the ordinary cup, multiplication cap, mergeUp and splitDown
    -- apply directly to the supplied embeddings, at arbitrary index. They
    -- give the computations behind the two registered prerequisite results
    -- without specializing their statements to conjugator representatives.
    have hLeft : left.eval.toLinearMap (Finsupp.single x 1) =
        Finsupp.single (downGamma.basis.pair upComposite.basis 1 (γ.toHom x)) 1 := by
      change (horizontal (id downGamma) (mergeUp γ α)).eval.toLinearMap
        ((associate downGamma upGamma upAlpha).eval.toLinearMap
          ((horizontal (ordinaryCup γ) (id upAlpha)).eval.toLinearMap
            ((insertLeftUnit (R := Complex) upAlpha).eval.toLinearMap
              (Finsupp.single x 1)))) = _
      rw [eval_insertLeftUnit_single upAlpha,
        eval_horizontal_single (ordinaryCup γ) (id upAlpha) 1 x 1,
        one_smul, eval_ordinaryCup_single γ 1 1, map_one, eval_id_apply,
        Biset.pairLinear_single, one_mul,
        eval_associate_single downGamma upGamma upAlpha 1 1 x 1]
      rw [eval_horizontal_single (id downGamma) (mergeUp γ α), one_smul,
        eval_id_apply, eval_mergeUp_single γ α 1 x 1, one_mul,
        Biset.pairLinear_single, one_mul]
    have hBranch : rightBranch.eval.toLinearMap
        (Finsupp.single (upAlpha.basis.pair downComposite.basis x 1) 1) =
        Finsupp.single (γ.toHom x) 1 := by
      change (leftUnit (R := Complex) downGamma).eval.toLinearMap
        ((horizontal (multiplicationCap α) (id downGamma)).eval.toLinearMap
          ((unassociate upAlpha downAlpha downGamma).eval.toLinearMap
            ((horizontal (id upAlpha) (splitDown γ α)).eval.toLinearMap
              (Finsupp.single (upAlpha.basis.pair downComposite.basis x 1) 1)))) = _
      rw [eval_horizontal_single (id upAlpha) (splitDown γ α) x 1 1,
        one_smul, eval_id_apply, eval_splitDown_single γ α 1 1,
        Biset.pairLinear_single, one_mul,
        eval_unassociate_single upAlpha downAlpha downGamma x 1 1 1]
      rw [eval_horizontal_single (multiplicationCap α) (id downGamma), one_smul,
        eval_multiplicationCap_single α x 1 1, mul_one, eval_id_apply,
        Biset.pairLinear_single, one_mul, eval_leftUnit_single downGamma]
      change Finsupp.single (γ.toHom x * 1 * (1 : G)⁻¹) 1 = _
      simp only [inv_one, mul_one]
    have hRight : right.eval.toLinearMap (Finsupp.single x 1) =
        Finsupp.single (downGamma.basis.pair upComposite.basis (γ.toHom x) 1) 1 := by
      have hInsert : (insertRightUnit (R := Complex) upAlpha).eval.toLinearMap
          (Finsupp.single x 1) =
          Finsupp.single (upAlpha.basis.pair (Biset.regular K) x 1) 1 := by
        change (Biset.insertRightUnit upAlpha.basis Complex).toLinearMap
          (Finsupp.single x 1) = _
        rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]
      change (horizontal rightBranch (id upComposite)).eval.toLinearMap
        ((unassociate upAlpha downComposite upComposite).eval.toLinearMap
          ((horizontal (id upAlpha) (ordinaryCup composite)).eval.toLinearMap
            ((insertRightUnit (R := Complex) upAlpha).eval.toLinearMap
              (Finsupp.single x 1)))) = _
      rw [hInsert, eval_horizontal_single (id upAlpha) (ordinaryCup composite) x 1 1,
        one_smul, eval_id_apply, eval_ordinaryCup_single composite 1 1, map_one,
        Biset.pairLinear_single, one_mul,
        eval_unassociate_single upAlpha downComposite upComposite x 1 1 1]
      rw [eval_horizontal_single rightBranch (id upComposite), one_smul,
        hBranch, eval_id_apply, Biset.pairLinear_single, one_mul]
    rw [hLeft, hRight]
    -- The middle group is G on both strands. Its two regular middle actions
    -- identify the two output basis pairs by the balance relation.
    apply congrArg (fun z => Finsupp.single z (1 : Complex))
    change (Biset.restriction γ).pair (Biset.induction composite) 1 (γ.toHom x) =
      (Biset.restriction γ).pair (Biset.induction composite) (γ.toHom x) 1
    simpa [Biset.restriction, Biset.induction] using
      ((Biset.restriction γ).pair_balance (Biset.induction composite) (γ.toHom x) 1 1).symm
  )))
