import MackeyDiagrams
import Proofs.TrivalentBendIdentities

set_option maxHeartbeats 2000000

theorem StraightMixedTrivalentVertices : (
∀ {U : Type*} [Group U] (K H G : Subgroup U)
    (α : MackeyDiagrams.ConjEmbedding K H) (γ : MackeyDiagrams.ConjEmbedding H G),
  let composite := MackeyDiagrams.ConjEmbedding.comp γ α
  let alphaHom := MackeyDiagrams.ConjEmbedding.toHom α
  let gammaHom := MackeyDiagrams.ConjEmbedding.toHom γ
  let alphaIndex := Subgroup.FiniteIndex (MonoidHom.range alphaHom)
  let compositeIndex :=
    Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom composite))
  let upAlpha := MackeyDiagrams.Word.up α
  let downAlpha := MackeyDiagrams.Word.down α
  let upGamma := MackeyDiagrams.Word.up γ
  let downGamma := MackeyDiagrams.Word.down γ
  let upComposite := MackeyDiagrams.Word.up composite
  let downComposite := MackeyDiagrams.Word.down composite
  let idUpAlpha := MackeyDiagrams.Diagram.id (R := Complex) upAlpha
  let idDownAlpha := MackeyDiagrams.Diagram.id (R := Complex) downAlpha
  let idUpGamma := MackeyDiagrams.Diagram.id (R := Complex) upGamma
  let idDownGamma := MackeyDiagrams.Diagram.id (R := Complex) downGamma
  let idUpComposite := MackeyDiagrams.Diagram.id (R := Complex) upComposite
  let idDownComposite := MackeyDiagrams.Diagram.id (R := Complex) downComposite
  let multiplicationCapVertex : Prop :=
    let boundary := MackeyDiagrams.Word.tensor upComposite downAlpha
    let firstBend : MackeyDiagrams.Diagram Complex boundary upGamma :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.splitUp γ α) idDownAlpha)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.associate upGamma upAlpha downAlpha)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal idUpGamma
              (MackeyDiagrams.Diagram.multiplicationCap α))
            (MackeyDiagrams.Diagram.rightUnit upGamma)))
    let rightBranch : MackeyDiagrams.Diagram Complex downAlpha
        (MackeyDiagrams.Word.tensor downComposite upGamma) :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit downAlpha)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idDownAlpha (MackeyDiagrams.Diagram.ordinaryCup γ))
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.unassociate downAlpha downGamma upGamma)
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeDown γ α) idUpGamma)))
    let secondBend : MackeyDiagrams.Diagram Complex boundary upGamma :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.horizontal idUpComposite rightBranch)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upComposite downComposite upGamma)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal
              (MackeyDiagrams.Diagram.multiplicationCap composite) idUpGamma)
            (MackeyDiagrams.Diagram.leftUnit upGamma)))
    let straight : MackeyDiagrams.LabelledDrawing Complex boundary upGamma :=
      MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToUp γ α)
    let straightMap := MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret straight)
    straightMap = MackeyDiagrams.Diagram.eval firstBend ∧
      straightMap = MackeyDiagrams.Diagram.eval secondBend
  let traceInput := MackeyDiagrams.Word.tensor downComposite upGamma
  let reverseOutput := MackeyDiagrams.Word.tensor upComposite downAlpha
  let traceCapFirstBend : MackeyDiagrams.Diagram Complex traceInput downAlpha :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.splitDown γ α) idUpGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.associate downAlpha downGamma upGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idDownAlpha (MackeyDiagrams.Diagram.traceCap γ))
          (MackeyDiagrams.Diagram.rightUnit downAlpha)))
  let reverseCupFirstBend (finiteAlpha : alphaIndex) :
      MackeyDiagrams.Diagram Complex upGamma reverseOutput :=
    MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit upGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal idUpGamma
          (MackeyDiagrams.Diagram.reverseCup α finiteAlpha))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upGamma upAlpha downAlpha)
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeUp γ α) idDownAlpha)))
  let traceCapVertex : Prop := ∀ finiteAlpha : alphaIndex,
    let secondBend : MackeyDiagrams.Diagram Complex traceInput downAlpha :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal idDownComposite (reverseCupFirstBend finiteAlpha))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate downComposite upComposite downAlpha)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.traceCap composite)
              idDownAlpha)
            (MackeyDiagrams.Diagram.leftUnit downAlpha)))
    let straight : MackeyDiagrams.LabelledDrawing Complex traceInput downAlpha :=
      MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.downUpToDown γ α)
    let straightMap := MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret straight)
    straightMap = MackeyDiagrams.Diagram.eval traceCapFirstBend ∧
      straightMap = MackeyDiagrams.Diagram.eval secondBend
  let ordinaryCupVertex : Prop :=
    let output := MackeyDiagrams.Word.tensor downGamma upComposite
    let firstBend : MackeyDiagrams.Diagram Complex upAlpha output :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertLeftUnit upAlpha)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.ordinaryCup γ) idUpAlpha)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.associate downGamma upGamma upAlpha)
            (MackeyDiagrams.Diagram.horizontal idDownGamma (MackeyDiagrams.Diagram.mergeUp γ α))))
    let rightBranch : MackeyDiagrams.Diagram Complex
        (MackeyDiagrams.Word.tensor upAlpha downComposite) downGamma :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal idUpAlpha (MackeyDiagrams.Diagram.splitDown γ α))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upAlpha downAlpha downGamma)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal
              (MackeyDiagrams.Diagram.multiplicationCap α) idDownGamma)
            (MackeyDiagrams.Diagram.leftUnit downGamma)))
    let secondBend : MackeyDiagrams.Diagram Complex upAlpha output :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit upAlpha)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idUpAlpha
            (MackeyDiagrams.Diagram.ordinaryCup composite))
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.unassociate upAlpha downComposite upComposite)
            (MackeyDiagrams.Diagram.horizontal rightBranch idUpComposite)))
    let straight : MackeyDiagrams.LabelledDrawing Complex upAlpha output :=
      MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upToDownUp γ α)
    let straightMap := MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret straight)
    straightMap = MackeyDiagrams.Diagram.eval firstBend ∧
      straightMap = MackeyDiagrams.Diagram.eval secondBend
  let reverseCupVertex : Prop := ∀ finiteComposite : compositeIndex,
    let finiteAlpha : alphaIndex := by
      let _ : Subgroup.FiniteIndex (MonoidHom.range (MonoidHom.comp gammaHom alphaHom)) :=
        finiteComposite
      have finitePreimage : Subgroup.FiniteIndex
          (Subgroup.comap gammaHom (MonoidHom.range (MonoidHom.comp gammaHom alphaHom))) :=
        inferInstance
      rw [MonoidHom.range_comp, Subgroup.comap_map_eq_self_of_injective
        (MackeyDiagrams.ConjEmbedding.injective γ)] at finitePreimage
      exact finitePreimage
    let secondBend : MackeyDiagrams.Diagram Complex upGamma reverseOutput :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertLeftUnit upGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal
            (MackeyDiagrams.Diagram.reverseCup composite finiteComposite) idUpGamma)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.associate upComposite downComposite upGamma)
            (MackeyDiagrams.Diagram.horizontal idUpComposite traceCapFirstBend)))
    let straight : MackeyDiagrams.LabelledDrawing Complex upGamma reverseOutput :=
      MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upToUpDown γ α finiteAlpha)
    let straightMap := MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret straight)
    straightMap = MackeyDiagrams.Diagram.eval (reverseCupFirstBend finiteAlpha) ∧
      straightMap = MackeyDiagrams.Diagram.eval secondBend
  multiplicationCapVertex ∧ traceCapVertex ∧ ordinaryCupVertex ∧ reverseCupVertex
) :=
(by
  -- Xiao, §3.5, straight-segment figure following Proposition 3.4.
  -- Archived original pp. 12–13 (pairs, then straight junctions).
  -- Published 28 November revision pp. 14–15, SHA-256
  -- 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- Alphabeta Math, tensor product universal property, Steps 3.1, 4.1,
  -- and 5.1: verify balance and additivity, descend through the relations,
  -- and identify the map on generators.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  -- Here the shared evaluator imposes middle-group balance by a biset
  -- quotient, then complex linearization imposes additivity. The compiled
  -- TrivalentBendIdentities supplies the resulting map equalities, so the
  -- generator computations from Proposition 3.4 are used through that theorem.
  intro U _ K H G α γ
  obtain ⟨multiplication, ordinary, trace, reverse⟩ :=
    TrivalentBendIdentities K H G α γ
  -- LabelledDrawing.interpret uses the ordinary scoped evaluator on
  -- TrivalentVertex.expand, which uses BentVertex.expand for these four
  -- orientations. This reduces directly; eval_bentVertex concerns the
  -- separate ScopedDiagram.bentVertex constructor.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Multiplication cap (upper left), at arbitrary index.
    exact ⟨rfl, multiplication⟩
  · -- Trace cap (upper right), with the index required by the smaller cup.
    intro finiteAlpha
    exact ⟨rfl, trace finiteAlpha⟩
  · -- Ordinary cup (lower left), at arbitrary index.
    exact ⟨rfl, ordinary⟩
  · -- Reverse cup (lower right), with the composite index. The endpoint
    -- and supplier pull back this index along γ. The resulting witnesses
    -- for the smaller cup are definitionally equal by proof irrelevance.
    intro finiteComposite
    exact ⟨rfl, reverse finiteComposite⟩)

#print axioms StraightMixedTrivalentVertices
