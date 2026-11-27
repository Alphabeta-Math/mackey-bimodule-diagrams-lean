import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.RightUpReidemeisterCurl

set_option maxHeartbeats 2000000

theorem CurlAcrossTrivalentVertex : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (γ α : U)
    (hγ : ∀ h : H, γ * (h : U) * γ⁻¹ ∈ G)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ H),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let ba := MackeyDiagrams.ConjEmbedding.comp b a
  let leftStrand := MackeyDiagrams.Word.up b
  let rightStrand := MackeyDiagrams.Word.up a
  let mergedStrand := MackeyDiagrams.Word.up ba
  let leftId := MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := Complex) leftStrand)
  let rightId := MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := Complex) rightStrand)
  let mergedId := MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := Complex) mergedStrand)
  let merge := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.mergeUp b a)
  let split := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.splitUp b a)
  let rightCurl := fun {A B M : Subgroup U}
      (strand : MackeyDiagrams.ConjEmbedding A B)
      (loop : MackeyDiagrams.ConjEmbedding M A)
      (finite : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom loop))) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.upToUpDown strand loop finite))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToUp strand loop))
  let evalDrawing := fun {A B : Subgroup U} {p q : MackeyDiagrams.Word A B}
      (drawing : MackeyDiagrams.LabelledDrawing Complex p q) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  (∀ (L : Subgroup U), L ≤ K →
    let inK := Subgroup.subgroupOf L K
    let imageK := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
    let imageL := Subgroup.map (MackeyDiagrams.ConjEmbedding.toHom a) inK
    Subgroup.FiniteIndex inK → Subgroup.FiniteIndex imageK → Subgroup.FiniteIndex imageL →
      Subgroup.index imageL = Subgroup.index imageK * Subgroup.relIndex L K) ∧
  (∀ (M : Subgroup U) (mergedLoop : MackeyDiagrams.ConjEmbedding M K),
    let mergedImage := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom mergedLoop)
    ∀ (finiteMerged : Subgroup.FiniteIndex mergedImage),
      let mergedIndex := Subgroup.index mergedImage
      let curlMerged := rightCurl ba mergedLoop finiteMerged
      evalDrawing curlMerged =
        evalDrawing
          (MackeyDiagrams.LabelledDrawing.scale (mergedIndex : Complex) mergedId) ∧
      (∀ (N : Subgroup U) (rightLoop : MackeyDiagrams.ConjEmbedding N K),
        let rightImage := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom rightLoop)
        ∀ (finiteRight : Subgroup.FiniteIndex rightImage),
          let rightIndex := Subgroup.index rightImage
          let curlRight := rightCurl a rightLoop finiteRight
          let curlOnRight := MackeyDiagrams.LabelledDrawing.horizontal leftId curlRight
          evalDrawing curlRight =
            evalDrawing
              (MackeyDiagrams.LabelledDrawing.scale (rightIndex : Complex) rightId) ∧
          (rightIndex = mergedIndex →
            evalDrawing (MackeyDiagrams.LabelledDrawing.vertical curlOnRight merge) =
              evalDrawing (MackeyDiagrams.LabelledDrawing.vertical merge curlMerged) ∧
            evalDrawing (MackeyDiagrams.LabelledDrawing.vertical split curlOnRight) =
              evalDrawing (MackeyDiagrams.LabelledDrawing.vertical curlMerged split))) ∧
      (∀ (N : Subgroup U) (leftLoop : MackeyDiagrams.ConjEmbedding N H),
        let leftImage := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom leftLoop)
        ∀ (finiteLeft : Subgroup.FiniteIndex leftImage),
          let leftIndex := Subgroup.index leftImage
          let curlLeft := rightCurl b leftLoop finiteLeft
          let curlOnLeft := MackeyDiagrams.LabelledDrawing.horizontal curlLeft rightId
          evalDrawing curlLeft =
            evalDrawing
              (MackeyDiagrams.LabelledDrawing.scale (leftIndex : Complex) leftId) ∧
          (leftIndex = mergedIndex →
            evalDrawing (MackeyDiagrams.LabelledDrawing.vertical curlOnLeft merge) =
              evalDrawing (MackeyDiagrams.LabelledDrawing.vertical merge curlMerged) ∧
            evalDrawing (MackeyDiagrams.LabelledDrawing.vertical split curlOnLeft) =
              evalDrawing (MackeyDiagrams.LabelledDrawing.vertical curlMerged split))))
) :=
(by
  intro U inst K H G γ α hγ hα a b ba leftStrand rightStrand mergedStrand
    leftId rightId mergedId merge split rightCurl evalDrawing
  refine ⟨?_, ?_⟩
  · intro L _ inK imageK imageL _ _ _
    -- Xiao § 3.2 (archived p. 9, revised published p. 11) uses the
    -- index of the image of L in H. Injectivity identifies the relative
    -- factor with the index of L.subgroupOf K. Mathlib orders the factors
    -- in the other order.
    change (inK.map a.toHom).index = a.toHom.range.index * inK.index
    exact (inK.index_map_of_injective a.injective).trans (Nat.mul_comm _ _)
  · open MackeyDiagrams in
    have evalCurl {A B M : Subgroup U} (strand : ConjEmbedding A B)
        (loop : ConjEmbedding M A) (finite : loop.toHom.range.FiniteIndex) :
        evalDrawing (rightCurl strand loop finite) =
          (Biset.Hom.id (R := Complex) (Word.up strand).basis).scale
            (loop.toHom.range.index : Complex) := by
      -- Theorem 4.1, (4.1) (archived p. 14, revised published p. 16),
      -- evaluates the finite undotted curl. The registered theorem is
      -- phrased using explicit conjugators. Recover representatives of
      -- both actual strand labels and keep the inner range's finite index.
      obtain ⟨s, hs⟩ := strand.hasRepresentative
      obtain ⟨d, hd⟩ := loop.hasRepresentative
      have hsMem (x : A) : s * (x : U) * s⁻¹ ∈ B :=
        hs x ▸ (strand.toHom x).property
      have hdMem (x : M) : d * (x : U) * d⁻¹ ∈ A :=
        hd x ▸ (loop.toHom x).property
      have hsEq : strand = ConjEmbedding.ofConjugator s hsMem :=
        ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (hs x))
      have hdEq : loop = ConjEmbedding.ofConjugator d hdMem :=
        ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (hd x))
      cases hsEq
      cases hdEq
      exact RightUpReidemeisterCurl M A B d s hdMem hsMem finite
    open MackeyDiagrams in
    have moveAcross {X Y : Biset G K}
        (f : Biset.Hom Complex X Y) (g : Biset.Hom Complex Y X)
        (branch : Biset.Hom Complex X X) (merged : Biset.Hom Complex Y Y)
        (n : Complex) (hBranch : branch = (Biset.Hom.id X).scale n)
        (hMerged : merged = (Biset.Hom.id Y).scale n) :
        branch.vertical f = f.vertical merged ∧
          g.vertical branch = merged.vertical g := by
      -- Section 1.2 identifies the typed merge and split maps. Linearity
      -- proves the slide for any pair of maps with these types, bypassing
      -- the inverse identities of InductionRestrictionMergesAndSplits.
      simp only [hBranch, hMerged, Biset.Hom.vertical_scale_left,
        Biset.Hom.vertical_scale_right, Biset.Hom.vertical_id, Biset.Hom.id_vertical,
        and_self]
    intro M mergedLoop mergedImage finiteMerged mergedIndex curlMerged
    have hMerged := evalCurl ba mergedLoop finiteMerged
    refine ⟨hMerged, ?_, ?_⟩
    · open MackeyDiagrams in
      intro N rightLoop rightImage finiteRight rightIndex curlRight curlOnRight
      have hRight := evalCurl a rightLoop finiteRight
      refine ⟨hRight, ?_⟩
      intro hIndex
      have hBranch : evalDrawing curlOnRight =
          (Biset.Hom.id (R := Complex) (leftStrand.tensor rightStrand).basis).scale
            (mergedIndex : Complex) := by
        change (Biset.Hom.id leftStrand.basis).horizontal (evalDrawing curlRight) = _
        rw [hRight, Biset.Hom.horizontal_scale_right, Biset.Hom.horizontal_id]
        change (Biset.Hom.id _).scale (rightIndex : Complex) = _
        rw [hIndex]
      exact moveAcross (evalDrawing merge) (evalDrawing split)
        (evalDrawing curlOnRight) (evalDrawing curlMerged) _ hBranch hMerged
    · open MackeyDiagrams in
      intro N leftLoop leftImage finiteLeft leftIndex curlLeft curlOnLeft
      have hLeft := evalCurl b leftLoop finiteLeft
      refine ⟨hLeft, ?_⟩
      intro hIndex
      -- Example 3.1 has unequal indices on the two branches. Use the
      -- given equality for this placement as for the right branch.
      have hBranch : evalDrawing curlOnLeft =
          (Biset.Hom.id (R := Complex) (leftStrand.tensor rightStrand).basis).scale
            (mergedIndex : Complex) := by
        change (evalDrawing curlLeft).horizontal (Biset.Hom.id rightStrand.basis) = _
        rw [hLeft, Biset.Hom.horizontal_scale_left, Biset.Hom.horizontal_id]
        change (Biset.Hom.id _).scale (leftIndex : Complex) = _
        rw [hIndex]
      exact moveAcross (evalDrawing merge) (evalDrawing split)
        (evalDrawing curlOnLeft) (evalDrawing curlMerged) _ hBranch hMerged)

#print axioms CurlAcrossTrivalentVertex
