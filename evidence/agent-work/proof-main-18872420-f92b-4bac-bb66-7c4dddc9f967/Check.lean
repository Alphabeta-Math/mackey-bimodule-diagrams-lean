import MackeyDiagrams
import Proofs.RightUpReidemeisterCurl
import Proofs.LeftDownReidemeisterCurl

set_option maxHeartbeats 2000000

theorem NormalizedIndexValuedReidemeisterCurls : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (δ α : U)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)
  ∀ finite : Subgroup.FiniteIndex S,
    let inverseIndex := (Subgroup.index S : Complex)⁻¹
    let rightUp := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.upToUpDown a d finite))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToUp a d))
    let leftDown := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.downToUpDown a d finite))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToDown a d))
    let straightUp := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
    let straightDown := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down a))
    MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret
        (MackeyDiagrams.LabelledDrawing.scale inverseIndex rightUp)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret straightUp) ∧
    MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret
        (MackeyDiagrams.LabelledDrawing.scale inverseIndex leftDown)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret straightDown)
) :=
(by
  intro U inst K H G δ α hδ hα d a S finite inverseIndex rightUp leftDown straightUp straightDown
  -- Xiao §4, Theorem 4.1, (4.1) and (4.4), supplies the two curl
  -- evaluations used in the unnumbered normalization on p. 15 of the
  -- archived original PDF and p. 17 of the revised PDF.
  -- Finite index is for the image of δ in H, common to both curls.
  have index_ne_zero : (S.index : Complex) ≠ 0 := by
    exact_mod_cast (@Subgroup.index_ne_zero H _ S finite)
  -- Interpret the outer scalar box as scalar multiplication of the
  -- evaluated map. This implements division while keeping the box and
  -- the two trivalent junctions as drawing syntax in the statement.
  have normalize {A B : Subgroup U} {p q : MackeyDiagrams.Word A B}
      (curl straight : MackeyDiagrams.LabelledDrawing Complex p q)
      (hcurl : curl.interpret.eval =
        (straight.scale (S.index : Complex)).interpret.eval) :
      (curl.scale inverseIndex).interpret.eval = straight.interpret.eval := by
    change curl.interpret.eval.scale inverseIndex = straight.interpret.eval
    rw [hcurl]
    apply MackeyDiagrams.Biset.Hom.ext
    change (S.index : Complex)⁻¹ •
      ((S.index : Complex) • straight.interpret.eval.toLinearMap) = _
    rw [← mul_smul, inv_mul_cancel₀ index_ne_zero, one_smul]
  exact ⟨normalize rightUp straightUp (RightUpReidemeisterCurl K H G δ α hδ hα finite),
    normalize leftDown straightDown (LeftDownReidemeisterCurl K H G δ α hδ hα finite)⟩)

#print axioms NormalizedIndexValuedReidemeisterCurls
