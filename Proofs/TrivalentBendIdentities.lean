import MackeyDiagrams
import Proofs.MultiplicationCapBend
import Proofs.TraceCapBend
import Proofs.OrdinaryCupBend
import Proofs.ReverseCupBend

set_option maxHeartbeats 2000000

theorem TrivalentBendIdentities : (
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
  let multiplicationCapBend : Prop :=
    let input := MackeyDiagrams.Word.tensor upComposite downAlpha
    let left : MackeyDiagrams.Diagram Complex input upGamma :=
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
    let right : MackeyDiagrams.Diagram Complex input upGamma :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.horizontal idUpComposite rightBranch)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upComposite downComposite upGamma)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal
              (MackeyDiagrams.Diagram.multiplicationCap composite) idUpGamma)
            (MackeyDiagrams.Diagram.leftUnit upGamma)))
    MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right
  let ordinaryCupBend : Prop :=
    let output := MackeyDiagrams.Word.tensor downGamma upComposite
    let left : MackeyDiagrams.Diagram Complex upAlpha output :=
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
    let right : MackeyDiagrams.Diagram Complex upAlpha output :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit upAlpha)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idUpAlpha
            (MackeyDiagrams.Diagram.ordinaryCup composite))
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.unassociate upAlpha downComposite upComposite)
            (MackeyDiagrams.Diagram.horizontal rightBranch idUpComposite)))
    MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right
  let traceInput := MackeyDiagrams.Word.tensor downComposite upGamma
  let reverseOutput := MackeyDiagrams.Word.tensor upComposite downAlpha
  let traceLeft : MackeyDiagrams.Diagram Complex traceInput downAlpha :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.splitDown γ α) idUpGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.associate downAlpha downGamma upGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idDownAlpha (MackeyDiagrams.Diagram.traceCap γ))
          (MackeyDiagrams.Diagram.rightUnit downAlpha)))
  let reverseLeft (finiteAlpha : alphaIndex) :
      MackeyDiagrams.Diagram Complex upGamma reverseOutput :=
    MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit upGamma)
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal idUpGamma
          (MackeyDiagrams.Diagram.reverseCup α finiteAlpha))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate upGamma upAlpha downAlpha)
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeUp γ α) idDownAlpha)))
  let traceCapBend : Prop := ∀ finiteAlpha : alphaIndex,
    let right : MackeyDiagrams.Diagram Complex traceInput downAlpha :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal idDownComposite (reverseLeft finiteAlpha))
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.unassociate downComposite upComposite downAlpha)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.traceCap composite)
              idDownAlpha)
            (MackeyDiagrams.Diagram.leftUnit downAlpha)))
    MackeyDiagrams.Diagram.eval traceLeft = MackeyDiagrams.Diagram.eval right
  let reverseCupBend : Prop := ∀ finiteComposite : compositeIndex,
    let finiteAlpha : alphaIndex := by
      let _ : Subgroup.FiniteIndex (MonoidHom.range (MonoidHom.comp gammaHom alphaHom)) :=
        finiteComposite
      have finitePreimage : Subgroup.FiniteIndex
          (Subgroup.comap gammaHom (MonoidHom.range (MonoidHom.comp gammaHom alphaHom))) :=
        inferInstance
      rw [MonoidHom.range_comp, Subgroup.comap_map_eq_self_of_injective
        (MackeyDiagrams.ConjEmbedding.injective γ)] at finitePreimage
      exact finitePreimage
    let right : MackeyDiagrams.Diagram Complex upGamma reverseOutput :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertLeftUnit upGamma)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal
            (MackeyDiagrams.Diagram.reverseCup composite finiteComposite) idUpGamma)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.associate upComposite downComposite upGamma)
            (MackeyDiagrams.Diagram.horizontal idUpComposite traceLeft)))
    MackeyDiagrams.Diagram.eval (reverseLeft finiteAlpha) = MackeyDiagrams.Diagram.eval right
  multiplicationCapBend ∧ ordinaryCupBend ∧ traceCapBend ∧ reverseCupBend
) :=
(by
  intro U _ K H G α γ
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Xiao, §3.5, Proposition 3.4, archived original p. 12 and revised
  -- published PDF p. 14. Both pages contain all four diagram pairs.
  -- The PDFs have different SHA-256 digests.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The four suppliers evaluate bottom to top on generators. This proof uses their
  -- evaluated equalities directly. The coordinator's BentVertex.expand
  -- and TrivalentVertex.expand describe the same left-hand composites,
  -- which the reviewed statement already spells out as typed diagrams.
  -- Alphabeta Math, module tensor universal property, Steps 3.1, 4.1 and 5.1.
  -- The shared biset quotient enforces balance over the middle group, and
  -- complex linearization enforces additivity. The suppliers then use
  -- equality on the resulting generators to identify the evaluated maps.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  · -- Multiplication cap has arbitrary index. Its supplier is expressed
    -- using actual conjugators, so recover representatives of both embeddings.
    obtain ⟨a, ha⟩ := α.hasRepresentative
    obtain ⟨g, hg⟩ := γ.hasRepresentative
    have haMem (k : K) : a * (k : U) * a⁻¹ ∈ H :=
      ha k ▸ (α.toHom k).property
    have hgMem (h : H) : g * (h : U) * g⁻¹ ∈ G :=
      hg h ▸ (γ.toHom h).property
    have hα : α = MackeyDiagrams.ConjEmbedding.ofConjugator a haMem :=
      MackeyDiagrams.ConjEmbedding.ext
        (MonoidHom.ext fun k => Subtype.ext (ha k))
    have hγ : γ = MackeyDiagrams.ConjEmbedding.ofConjugator g hgMem :=
      MackeyDiagrams.ConjEmbedding.ext
        (MonoidHom.ext fun h => Subtype.ext (hg h))
    rw [hα, hγ]
    exact MultiplicationCapBend K H G a g haMem hgMem
  · -- Ordinary cup has arbitrary index.
    exact OrdinaryCupBend K H G α γ
  · -- Trace cap uses finite index in H for the smaller reverse cup.
    intro finiteAlpha
    exact TraceCapBend K H G α γ finiteAlpha
  · -- Reverse cup uses finite composite index in G. Both types pull
    -- this back along the injective γ.toHom to form the smaller cup.
    intro finiteComposite
    exact ReverseCupBend K H G α γ finiteComposite)
