import MackeyDiagrams
import Proofs.BlockwiseGroupElementDotCriterion

set_option maxHeartbeats 2000000

theorem DotBetweenImagesInOneBlock : (
let U := Equiv.Perm (Fin 4)
let B : Finset (Fin 4) := {0, 1}
let H : Subgroup U := iInf (fun x : {x : Fin 4 // x ∉ B} => MulAction.stabilizer U x.val)
let G : Subgroup U := ⊤
let α : U := 1
let β : U := Equiv.swap (1 : Fin 4) 2
let a : MackeyDiagrams.ConjEmbedding H G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator α (fun _ => Subgroup.mem_top _)
let b : MackeyDiagrams.ConjEmbedding H G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator β (fun _ => Subgroup.mem_top _)
Finset.image (fun x => α x) B ≠ Finset.image (fun x => β x) B ∧
  ∃ d : MackeyDiagrams.Dot a b, (MackeyDiagrams.Dot.element d : U) = β
) :=
(by
  -- Example 3.4 [ex:dot-in-one-block], archived PDF p. 11 and
  -- published 28 November revision p. 13. The HTML presents the example
  -- in one sentence. Its first claim is witnessed by paper label 3,
  -- encoded by 2 in Fin 4.
  intro U B H G α β a b
  constructor
  · intro heq
    have hβ₁ : β (1 : Fin 4) = 2 := Equiv.swap_apply_left _ _
    have h₂ : (2 : Fin 4) ∈ Finset.image (fun x => β x) B :=
      Finset.mem_image.mpr ⟨1, by simp [B], hβ₁⟩
    rw [← heq] at h₂
    obtain ⟨x, hx, hx₂⟩ := Finset.mem_image.mp h₂
    have hx' : x = 2 := hx₂
    subst x
    exact (by decide : (2 : Fin 4) ∉ ({0, 1} : Finset (Fin 4))) hx
  -- For the dot claim, implement the sufficiency construction in §3.4
  -- directly. The target has one block, so the ambient swap already
  -- extends the partial bijection from the beta image to the alpha image.
  -- BlockwiseGroupElementDotCriterion concerns finitary permutations of
  -- Nat and gives Nonempty for the dot type. This example requires a
  -- specified element in S₄. The shared ofRepresentatives constructor
  -- checks the intertwining equation from the two conjugation formulas.
  · have hinv : β⁻¹ = β := Equiv.symm_swap _ _
    let d : MackeyDiagrams.Dot a b :=
      MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl)
        (Subgroup.mem_top _)
    refine ⟨d, ?_⟩
    change (1 : U) * β⁻¹ = β
    rw [one_mul, hinv])

#print axioms DotBetweenImagesInOneBlock
