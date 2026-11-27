import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 200000

universe u

open MackeyDiagrams in
private theorem rightUpCurl_biset {U : Type u} [Group U] {K H G : Subgroup U}
    (a : ConjEmbedding H G) (d : ConjEmbedding K H) (finite : d.toHom.range.FiniteIndex) :
    let up := Biset.induction a
    let loopUp := Biset.induction d
    let loopDown := Biset.restriction d
    let unit := Biset.Hom.id (R := Complex) up
    let cup := Generator.reverseCup Complex d finite
    let cap := Generator.multiplicationCap Complex d
    let insert := Biset.insertRightUnit up Complex
    let remove := Biset.rightUnit up Complex
    let reassoc := Biset.unassociate up loopUp loopDown Complex
    let assoc := Biset.associate up loopUp loopDown Complex
    let merge := (Generator.mergeUp Complex a d).horizontal (Biset.Hom.id loopDown)
    let split := (Generator.splitUp Complex a d).horizontal (Biset.Hom.id loopDown)
    let n : Complex := d.toHom.range.index
    (insert.vertical ((unit.horizontal cup).vertical (reassoc.vertical merge))).vertical
      (split.vertical (assoc.vertical ((unit.horizontal cap).vertical remove))) = unit.scale n := by
  run_tac do IO.eprintln "entered symbolic lemma"
  intro up loopUp loopDown unit cup cap insert remove reassoc assoc merge split n
  -- The upward merge and split are inverses on the two-factor word.
  -- Horizontal composition carries the identity on the downward leg.
  run_tac do IO.eprintln "checking merge–split supplier"
  have hMergeSplit :
      (Generator.mergeUp Complex a d).vertical (Generator.splitUp Complex a d) =
        Biset.Hom.id (up.tensor loopUp) :=
    Diagram.mergeUp_splitUp a d
  run_tac do IO.eprintln "checking middle cancellation"
  have hMiddle :
      (reassoc.vertical merge).vertical (split.vertical assoc) =
        Biset.Hom.id (up.tensor (loopUp.tensor loopDown)) := by
    refine Biset.Hom.cancel_middle reassoc merge split assoc ?_ Biset.unassociate_associate
    dsimp only [merge, split]
    rw [Biset.Hom.horizontal_vertical, hMergeSplit, Biset.Hom.id_vertical, Biset.Hom.horizontal_id]
  -- Xiao's transversal sum is evaluated by the finite multiplication-cap
  -- fiber theorem. Generator.capFiber_card uses Subgroup.index_eq_card to
  -- count these cosets. The finite-index hypothesis is for d.toHom.range.
  run_tac do IO.eprintln "checking cup–cap supplier"
  have hCupCap : cup.vertical cap = (Biset.Hom.id (Biset.regular H)).scale n :=
    Diagram.reverseCup_multiplicationCap d finite
  run_tac do IO.eprintln "checking horizontal scalar"
  have hLoop : (unit.horizontal cup).vertical (unit.horizontal cap) =
      (Biset.Hom.id (up.tensor (Biset.regular H))).scale n := by
    dsimp only [unit]
    rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical, hCupCap,
      Biset.Hom.horizontal_scale_right, Biset.Hom.horizontal_id]
  run_tac do IO.eprintln "checking final regrouping"
  calc
    _ = insert.vertical (((unit.horizontal cup).vertical
          ((reassoc.vertical merge).vertical (split.vertical assoc))).vertical
          ((unit.horizontal cap).vertical remove)) := by
        simp only [Biset.Hom.vertical_assoc]
    _ = insert.vertical (((unit.horizontal cup).vertical (unit.horizontal cap)).vertical remove) := by
        rw [hMiddle, Biset.Hom.vertical_id, Biset.Hom.vertical_assoc]
    _ = unit.scale n := by
        rw [hLoop, Biset.Hom.vertical_scale_left, Biset.Hom.id_vertical, Biset.Hom.vertical_scale_right]
        exact congrArg (fun f : Biset.Hom Complex up up => f.scale n) Biset.insertRightUnit_rightUnit

theorem RightUpReidemeisterCurl : (∀ {U : Type u} [Group U] (K H G : Subgroup U) (δ α : U)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)
  ∀ finite : Subgroup.FiniteIndex S,
    let curl := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.upToUpDown a d finite))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToUp a d))
    let straight := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
    let scaled := MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) straight
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaled)) :=
(by
  run_tac do IO.eprintln "entered article endpoint"
  intro U inst K H G δ α hδ hα d a S finite curl straight scaled
  -- Xiao's (4.1) and its unnumbered proof appear on pp. 14–15 of the
  -- project PDF and pp. 16–17 of the current published PDF. Both show
  -- the same junctions and identify the scalar using the same finite index.
  -- The typed trivalent expansion checks the connection to the explicit
  -- composite in the retained ReviewedRightUpCurl calculation. Its merge
  -- and split are separate maps before their evaluated cancellation.
  run_tac do IO.eprintln "expanding trivalent syntax"
  simp only [curl, straight, scaled, MackeyDiagrams.LabelledDrawing.interpret,
    MackeyDiagrams.ScopedDiagram.eval, MackeyDiagrams.TrivalentVertex.expand,
    MackeyDiagrams.BentVertex.expand, MackeyDiagrams.Diagram.eval, MackeyDiagrams.Word.basis]
  run_tac do IO.eprintln "applying symbolic lemma"
  exact rightUpCurl_biset a d finite)

#print axioms RightUpReidemeisterCurl
