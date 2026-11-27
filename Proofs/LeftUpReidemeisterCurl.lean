import Mathlib.Basic.Complex.Basic
import MackeyDiagrams
import Proofs.InductionRestrictionAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

universe u

theorem LeftUpReidemeisterCurl : (∀ {U : Type u} [Group U] (K H G : Subgroup U) (δ α : U)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let up := MackeyDiagrams.Word.up d
  let loopDown := MackeyDiagrams.Word.down a
  let loopUp := MackeyDiagrams.Word.up a
  let straight := MackeyDiagrams.Diagram.id (R := Complex) up
  let cup := MackeyDiagrams.Diagram.horizontal
    (MackeyDiagrams.Diagram.ordinaryCup a) straight
  let middle := MackeyDiagrams.Diagram.horizontal
    (MackeyDiagrams.Diagram.id loopDown)
    (MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.mergeUp a d)
      (MackeyDiagrams.Diagram.splitUp a d))
  let cap := MackeyDiagrams.Diagram.horizontal
    (MackeyDiagrams.Diagram.traceCap a) straight
  let curl :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.insertLeftUnit up)
      (MackeyDiagrams.Diagram.vertical cup
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.associate loopDown loopUp up)
          (MackeyDiagrams.Diagram.vertical middle
            (MackeyDiagrams.Diagram.vertical
              (MackeyDiagrams.Diagram.unassociate loopDown loopUp up)
              (MackeyDiagrams.Diagram.vertical cap
                (MackeyDiagrams.Diagram.leftUnit up))))))
  MackeyDiagrams.Diagram.eval curl = MackeyDiagrams.Diagram.eval straight) :=
(by
  intro U inst K H G δ α hδ hα d a up loopDown loopUp straight cup middle cap curl
  have hmid :
      (MackeyDiagrams.Generator.mergeUp Complex a d).vertical
        (MackeyDiagrams.Generator.splitUp Complex a d) =
      MackeyDiagrams.Biset.Hom.id ((MackeyDiagrams.Word.up a).basis.tensor
        (MackeyDiagrams.Word.up d).basis) :=
    MackeyDiagrams.Diagram.mergeUp_splitUp a d
  have hcup :
      (MackeyDiagrams.Generator.ordinaryCup Complex a).vertical
        (MackeyDiagrams.Generator.traceCap Complex a) =
      MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.regular H) :=
    MackeyDiagrams.Diagram.ordinaryCup_traceCap a
  simp only [curl, middle, cup, cap, straight, up, loopDown, loopUp,
    MackeyDiagrams.Diagram.eval, hmid, MackeyDiagrams.Word.basis,
    MackeyDiagrams.Biset.Hom.horizontal_id]
  rw [← MackeyDiagrams.Biset.Hom.vertical_assoc
      (MackeyDiagrams.Biset.associate (MackeyDiagrams.Biset.restriction a)
        (MackeyDiagrams.Biset.induction a) (MackeyDiagrams.Biset.induction d) Complex),
    MackeyDiagrams.Biset.Hom.vertical_id, ← MackeyDiagrams.Biset.Hom.vertical_assoc
      (MackeyDiagrams.Biset.associate (MackeyDiagrams.Biset.restriction a)
        (MackeyDiagrams.Biset.induction a) (MackeyDiagrams.Biset.induction d) Complex),
    MackeyDiagrams.Biset.associate_unassociate, MackeyDiagrams.Biset.Hom.id_vertical]
  rw [← MackeyDiagrams.Biset.Hom.vertical_assoc
      ((MackeyDiagrams.Generator.ordinaryCup Complex a).horizontal
        (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.induction d))),
    MackeyDiagrams.Biset.Hom.horizontal_vertical,
    MackeyDiagrams.Biset.Hom.id_vertical, hcup,
    MackeyDiagrams.Biset.Hom.horizontal_id, MackeyDiagrams.Biset.Hom.id_vertical]
  exact MackeyDiagrams.Biset.insertLeftUnit_leftUnit)
