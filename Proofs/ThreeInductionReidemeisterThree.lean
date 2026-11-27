import MackeyDiagrams
import Proofs.MultipliersUnderRelabelling
import Proofs.ThreeInductionCrossingMultipliers

set_option maxHeartbeats 2000000

theorem ThreeInductionReidemeisterThree : (
∀ {U : Type*} [Group U] (G A D F C E : Subgroup U)
    (repGA repAD repDF repGC repCE repEF : U)
    (hGA : ∀ a : A, repGA * (a : U) * repGA⁻¹ ∈ G)
    (hAD : ∀ d : D, repAD * (d : U) * repAD⁻¹ ∈ A)
    (hDF : ∀ f : F, repDF * (f : U) * repDF⁻¹ ∈ D)
    (hGC : ∀ c : C, repGC * (c : U) * repGC⁻¹ ∈ G)
    (hCE : ∀ e : E, repCE * (e : U) * repCE⁻¹ ∈ C)
    (hEF : ∀ f : F, repEF * (f : U) * repEF⁻¹ ∈ E),
  let ga := MackeyDiagrams.ConjEmbedding.ofConjugator repGA hGA
  let ad := MackeyDiagrams.ConjEmbedding.ofConjugator repAD hAD
  let df := MackeyDiagrams.ConjEmbedding.ofConjugator repDF hDF
  let gc := MackeyDiagrams.ConjEmbedding.ofConjugator repGC hGC
  let ce := MackeyDiagrams.ConjEmbedding.ofConjugator repCE hCE
  let ef := MackeyDiagrams.ConjEmbedding.ofConjugator repEF hEF
  let bottomPair := MackeyDiagrams.ConjEmbedding.comp ga ad
  let topPair := MackeyDiagrams.ConjEmbedding.comp gc ce
  let word := fun {P Q S T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (c : MackeyDiagrams.ConjEmbedding T S) =>
    MackeyDiagrams.Word.tensor
      (MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b))
      (MackeyDiagrams.Word.up c)
  let bottom := word ga ad df
  let top := word gc ce ef
  let straight := fun {P Q : Subgroup U} (a : MackeyDiagrams.ConjEmbedding Q P) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
  let merge := fun {P Q S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.mergeUp a b)
  let split := fun {P Q S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.splitUp a b)
  let splitBottom :=
    MackeyDiagrams.LabelledDrawing.vertical (split bottomPair df)
      (MackeyDiagrams.LabelledDrawing.horizontal (split ga ad) (straight df))
  let mergeTop :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (merge gc ce) (straight ef))
      (merge topPair ef)
  let mergedEvaluation := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top)
      (z : MonoidAlgebra Complex G) =>
    MonoidAlgebra.ofCoeff
      (MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.interpret
            (MackeyDiagrams.LabelledDrawing.vertical splitBottom
              (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
        (MonoidAlgebra.coeff z))
  let multiplier := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    mergedEvaluation drawing 1
  let crossing := fun {P Q Q' S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
        (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
    MackeyDiagrams.LabelledDrawing.vertical (merge a b)
      (MackeyDiagrams.LabelledDrawing.vertical (MackeyDiagrams.DotLabel.upDrawing weights)
        (split a' b'))
  let crossLeft := fun {P Q Q' S T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
      (c : MackeyDiagrams.ConjEmbedding T S)
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
        (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
    MackeyDiagrams.LabelledDrawing.horizontal (crossing a b a' b' weights)
      (straight c)
  let crossRight := fun {P Q S S' T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P)
      (b : MackeyDiagrams.ConjEmbedding S Q) (c : MackeyDiagrams.ConjEmbedding T S)
      (b' : MackeyDiagrams.ConjEmbedding S' Q) (c' : MackeyDiagrams.ConjEmbedding T S')
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp b c)
        (MackeyDiagrams.ConjEmbedding.comp b' c')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.associate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b)
          (MackeyDiagrams.Word.up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (straight a)
          (crossing b c b' c' weights))
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.unassociate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b')
            (MackeyDiagrams.Word.up c'))))
  let LeftLabels :=
    Σ (B : Subgroup U) (gb : MackeyDiagrams.ConjEmbedding B G)
      (bd : MackeyDiagrams.ConjEmbedding D B) (be : MackeyDiagrams.ConjEmbedding E B),
      MackeyDiagrams.DotLabel Complex bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd) ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp bd df) (MackeyDiagrams.ConjEmbedding.comp be ef) ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp gb be) topPair
  let RightLabels :=
    Σ (B' : Subgroup U) (ab' : MackeyDiagrams.ConjEmbedding B' A)
      (cb' : MackeyDiagrams.ConjEmbedding B' C) (b'f : MackeyDiagrams.ConjEmbedding F B'),
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ad df) (MackeyDiagrams.ConjEmbedding.comp ab' b'f) ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ga ab') (MackeyDiagrams.ConjEmbedding.comp gc cb') ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp cb' b'f) (MackeyDiagrams.ConjEmbedding.comp ce ef)
  let leftDiagram : LeftLabels → MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨_, gb, bd, be, x₁, x₂, x₃⟩ =>
      MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ad gb bd df x₁)
        (MackeyDiagrams.LabelledDrawing.vertical (crossRight gb bd df be ef x₂)
          (crossLeft gb be gc ce ef x₃))
  let rightDiagram : RightLabels → MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨_, ab', cb', b'f, y₁, y₂, y₃⟩ =>
      MackeyDiagrams.LabelledDrawing.vertical (crossRight ga ad df ab' b'f y₁)
        (MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ab' gc cb' b'f y₂)
          (crossRight gc cb' b'f ce ef y₃))
  let leftMultiplier := fun d : LeftLabels => multiplier (leftDiagram d)
  let rightMultiplier := fun d : RightLabels => multiplier (rightDiagram d)
  let leftEval := fun d : LeftLabels => MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (leftDiagram d))
  let rightEval := fun d : RightLabels => MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (rightDiagram d))
  let leftSetoid := Setoid.ker leftEval
  let rightSetoid := Setoid.ker rightEval
  ∃ (φ : LeftLabels → RightLabels) (ψ : RightLabels → LeftLabels)
    (classes : Equiv (Quotient leftSetoid) (Quotient rightSetoid)),
    (∀ d : LeftLabels, rightMultiplier (φ d) = leftMultiplier d) ∧
    (∀ e : RightLabels, leftMultiplier (ψ e) = rightMultiplier e) ∧
    (∀ d : LeftLabels, classes (Quotient.mk leftSetoid d) = Quotient.mk rightSetoid (φ d)) ∧
    (∀ e : RightLabels,
      Equiv.symm classes (Quotient.mk rightSetoid e) = Quotient.mk leftSetoid (ψ e)) ∧
    (∀ (d : LeftLabels) (e : RightLabels), rightEval e = leftEval d →
      classes (Quotient.mk leftSetoid d) = Quotient.mk rightSetoid e) ∧
    (∀ (e : RightLabels) (d : LeftLabels), leftEval d = rightEval e →
      Equiv.symm classes (Quotient.mk rightSetoid e) = Quotient.mk leftSetoid d)
) :=
(by
  intro U inst G A D F C E repGA repAD repDF repGC repCE repEF
    hGA hAD hDF hGC hCE hEF ga ad df gc ce ef bottomPair topPair
    word bottom top straight merge split splitBottom mergeTop mergedEvaluation multiplier
    crossing crossLeft crossRight LeftLabels RightLabels leftDiagram rightDiagram
    leftMultiplier rightMultiplier leftEval rightEval leftSetoid rightSetoid
  -- Theorem 6.2, § 6.1, archived PDF p. 20 and revised published PDF p. 22.
  -- The two diagrams appear on archived p. 19 and revised p. 21.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#thm:reidemeister-three
  -- The published proof is unnumbered. The numbers below index its three
  -- arguments in source order: descent, independence, and the round trips.
  -- The fourth conjunct of the registered multiplier theorem identifies
  -- equality of maps with equality at 1 for these six fixed boundary labels.
  -- It supplies the merged evaluation comparison directly, including
  -- cancellation of the boundary merge and split. The setoids here use
  -- Setoid.ker on individual admissible labellings. The diagram vector-space
  -- quotient from the route concerns finite expressions in drawings.
  have eval_iff (d e : MackeyDiagrams.LabelledDrawing Complex bottom top) :
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret e) ↔
        multiplier d = multiplier e :=
    (ThreeInductionCrossingMultipliers G A D F C E repGA repAD repDF repGC repCE repEF
      hGA hAD hDF hGC hCE hEF).2.2.2.1 d e
  obtain ⟨φ, ψ, hφ, hψ, hleft, hright⟩ :=
    MultipliersUnderRelabelling G A D F C E repGA repAD repDF repGC repCE repEF
      hGA hAD hDF hGC hCE hEF
  -- Step 1. The registered Lemma 6.1 uses the same termwise eligible dot
  -- language and crosses the same ordered pairs as leftDiagram and rightDiagram.
  have forwardEval (d : LeftLabels) : rightEval (φ d) = leftEval d :=
    (eval_iff (rightDiagram (φ d)) (leftDiagram d)).2 (hφ d)
  have backwardEval (e : RightLabels) : leftEval (ψ e) = rightEval e :=
    (eval_iff (leftDiagram (ψ e)) (rightDiagram e)).2 (hψ e)
  let forward : Quotient leftSetoid → Quotient rightSetoid :=
    Quotient.map φ (fun {d d'} (h : leftEval d = leftEval d') =>
      (forwardEval d).trans (h.trans (forwardEval d').symm))
  let backward : Quotient rightSetoid → Quotient leftSetoid :=
    Quotient.map ψ (fun {e e'} (h : rightEval e = rightEval e') =>
      (backwardEval e).trans (h.trans (backwardEval e').symm))
  -- Step 3. Quotient induction reduces the inverse laws to Lemma 6.1's
  -- round-trip equalities for the same two boundary evaluations.
  let classes : Equiv (Quotient leftSetoid) (Quotient rightSetoid) :=
    { toFun := forward
      invFun := backward
      left_inv := fun q => Quotient.inductionOn q fun d => by
        change Quotient.mk leftSetoid (ψ (φ d)) = Quotient.mk leftSetoid d
        exact Quotient.sound ((eval_iff (leftDiagram (ψ (φ d))) (leftDiagram d)).2 (hleft d))
      right_inv := fun q => Quotient.inductionOn q fun e => by
        change Quotient.mk rightSetoid (φ (ψ e)) = Quotient.mk rightSetoid e
        exact Quotient.sound ((eval_iff (rightDiagram (φ (ψ e))) (rightDiagram e)).2 (hright e)) }
  refine ⟨φ, ψ, classes, hφ, hψ, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  -- Step 2. Any admissible replacement evaluating to the input map agrees
  -- with the chosen output in the corresponding evaluation quotient.
  · intro d e he
    change Quotient.mk rightSetoid (φ d) = Quotient.mk rightSetoid e
    exact Quotient.sound ((forwardEval d).trans he.symm)
  · intro e d hd
    change Quotient.mk leftSetoid (ψ e) = Quotient.mk leftSetoid d
    exact Quotient.sound ((backwardEval e).trans hd.symm))
