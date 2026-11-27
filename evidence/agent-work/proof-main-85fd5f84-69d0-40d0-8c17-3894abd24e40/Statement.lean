import MackeyDiagrams
import Proofs.MovingMergeDotBackToBranch

set_option autoImplicit false

#check ((let U := Equiv.Perm (Fin 4)
let G : Subgroup U := ⊤
let H := MulAction.stabilizer U (3 : Fin 4)
let K := H ⊓ MulAction.stabilizer U (2 : Fin 4)
let inG : ∀ x : U, x ∈ G := fun _ => Subgroup.mem_top _
let α : MackeyDiagrams.ConjEmbedding K H :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (by
    intro k
    simpa only [one_mul, inv_one, mul_one] using (inf_le_left : K ≤ H) k.property)
let γ : MackeyDiagrams.ConjEmbedding H G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (fun _ => inG _)
let target := MackeyDiagrams.ConjEmbedding.comp γ α
let g : G := ⟨Equiv.swap (2 : Fin 4) 3, inG _⟩
let gLabel : MackeyDiagrams.ConjEmbedding K G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator (g : U) (fun _ => inG _)
let input := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up γ)
  (MackeyDiagrams.Word.up α)
let output := MackeyDiagrams.Word.up target
let unitTensor := Finsupp.single
  (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction γ)
    (MackeyDiagrams.Biset.induction α) 1 1) (1 : Complex)
(g : U) ∈ Subgroup.centralizer (K : Set U) ∧ gLabel = target ∧ (g : U) ∉ H ∧
  ∃ d : MackeyDiagrams.Dot target target, MackeyDiagrams.Dot.element d = g ∧
    let B : MackeyDiagrams.LabelledDrawing Complex input output :=
      MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.trivalent
          (MackeyDiagrams.TrivalentVertex.mergeUp γ α))
        (MackeyDiagrams.DotLabel.upDrawing
          (Finsupp.single d (1 : Complex) : MackeyDiagrams.DotLabel Complex target target))
    let evalB := MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret B)
    MackeyDiagrams.Biset.Hom.toLinearMap evalB unitTensor = Finsupp.single g 1 ∧
      ∀ (β : MackeyDiagrams.ConjEmbedding K H) (label : MackeyDiagrams.DotLabel Complex α β)
        (h : MackeyDiagrams.ConjEmbedding.comp γ β = target),
        let A : MackeyDiagrams.LabelledDrawing Complex input
            (MackeyDiagrams.Word.up (MackeyDiagrams.ConjEmbedding.comp γ β)) :=
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal
              (MackeyDiagrams.LabelledDrawing.ordinary
                (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up γ)))
              (MackeyDiagrams.DotLabel.upDrawing label))
            (MackeyDiagrams.LabelledDrawing.trivalent
              (MackeyDiagrams.TrivalentVertex.mergeUp γ β))
        let evalA := MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.interpret
            (Eq.ndrec (motive := fun out =>
              MackeyDiagrams.LabelledDrawing Complex input (MackeyDiagrams.Word.up out)) A h))
        let imageA := MackeyDiagrams.Biset.Hom.toLinearMap evalA unitTensor
        imageA = Finsupp.mapDomain
          (fun term => MackeyDiagrams.ConjEmbedding.toHom γ (MackeyDiagrams.Dot.element term))
          label ∧
        (∀ x : G, x ∈ Finsupp.support imageA → (x : U) ∈ H) ∧
        evalA ≠ evalB) : Prop)
