import MackeyDiagrams
import Proofs.CurlAcrossTrivalentVertex
import Proofs.NormalizedIndexValuedReidemeisterCurls

theorem NormalizedTrivalentCurl : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (γ α : U)
    (hγ : ∀ h : H, γ * (h : U) * γ⁻¹ ∈ G)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ H),
  let left := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let right := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let merged := MackeyDiagrams.ConjEmbedding.comp left right
  let normalizes := fun {A B : Subgroup U} (strand : MackeyDiagrams.ConjEmbedding A B) =>
    ∀ (M : Subgroup U) (loop : MackeyDiagrams.ConjEmbedding M A),
      let image := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom loop)
      ∀ finite : Subgroup.FiniteIndex image,
        let curl := MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
            (MackeyDiagrams.TrivalentVertex.upToUpDown strand loop finite))
          (MackeyDiagrams.LabelledDrawing.trivalent
            (MackeyDiagrams.TrivalentVertex.upDownToUp strand loop))
        let straight := MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up strand))
        MackeyDiagrams.ScopedDiagram.eval
            (MackeyDiagrams.LabelledDrawing.interpret
              (MackeyDiagrams.LabelledDrawing.scale ((Subgroup.index image : Complex)⁻¹) curl)) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret straight)
  normalizes left ∧ normalizes right ∧ normalizes merged
) :=
(by
  intro U inst K H G γ α hγ hα left right merged normalizes
  open MackeyDiagrams in
  have normalize {A B : Subgroup U} (strand : ConjEmbedding A B) :
      normalizes strand := by
    intro M loop
    -- Theorem 4.1, (4.1), gives the scalar evaluation (archived p. 14,
    -- published revision p. 16). The § 4 normalization (archived p. 15,
    -- published revision p. 17) cancels that scalar over ℂ using the finite
    -- index of the loop image in A. The registered result uses
    -- Subgroup.index_ne_zero for this cancellation and takes explicit
    -- conjugators. Recover them and identify the embeddings by their homs.
    obtain ⟨s, hs⟩ := strand.hasRepresentative
    obtain ⟨d, hd⟩ := loop.hasRepresentative
    have hsMem (a : A) : s * (a : U) * s⁻¹ ∈ B :=
      hs a ▸ (strand.toHom a).property
    have hdMem (m : M) : d * (m : U) * d⁻¹ ∈ A :=
      hd m ▸ (loop.toHom m).property
    have hsEq : strand = ConjEmbedding.ofConjugator s hsMem :=
      ConjEmbedding.ext (MonoidHom.ext fun a => Subtype.ext (hs a))
    have hdEq : loop = ConjEmbedding.ofConjugator d hdMem :=
      ConjEmbedding.ext (MonoidHom.ext fun m => Subtype.ext (hd m))
    cases hsEq
    cases hdEq
    intro image finite curl straight
    -- The right-up projection is the same pair of typed trivalent
    -- junctions, with the reciprocal applied to the whole drawing.
    exact (NormalizedIndexValuedReidemeisterCurls M A B d s hdMem hsMem finite).1
  -- Xiao § 3.2, after Example 3.1 (archived p. 9, published revision p. 12).
  -- Apply the registered cancellation separately at the three placements.
  -- The slide in CurlAcrossTrivalentVertex assumes equal indices, and
  -- Example 3.1 shows that the branch indices can differ.
  exact ⟨normalize left, normalize right, normalize merged⟩)

#print axioms NormalizedTrivalentCurl
