import Proofs.EvaluationWithOneProjection
import Proofs.ExpansionIntoRightDiagrams

namespace CaseFiveInfiniteAux
open MackeyDiagrams

abbrev U := Multiplicative Int
abbrev P : Subgroup U := ⊤
abbrev T : Subgroup U := ⊥
abbrev p := MackeyDiagrams.ConjEmbedding.id P
abbrev a : MackeyDiagrams.ConjEmbedding T P :=
  { toHom := Subgroup.inclusion bot_le
    hasRepresentative := ⟨1, fun _ => by simp⟩ }
abbrev i := MackeyDiagrams.ConjEmbedding.id T
abbrev comp := @MackeyDiagrams.ConjEmbedding.comp U _
abbrev up := @MackeyDiagrams.Word.up U _
abbrev down := @MackeyDiagrams.Word.down U _
abbrev tensor := @MackeyDiagrams.Word.tensor U _
abbrev stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
abbrev beside := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
abbrev plain := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
abbrev ga := up a
abbrev ad := down a
abbrev df := up a
abbrev gc := up p
abbrev ce := down p
abbrev ef := up a
abbrev ai := up i
abbrev fj := down i
abbrev ck := up a
abbrev bottom := tensor ga (tensor ad df)
abbrev top := tensor gc (tensor ce ef)
theorem indexOne : (MackeyDiagrams.ConjEmbedding.toHom p).range.index = 1 := by
  change (MonoidHom.id P).range.index = 1
  rw [MonoidHom.range_eq_top_of_surjective (MonoidHom.id P) (fun x => ⟨x, rfl⟩),
    Subgroup.index_top]
abbrev leftDot := MackeyDiagrams.Dot.id (comp p p)
theorem leftFinite :
    ∀ z, Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis p p p p leftDot w = z} := by
  intro z
  have finite : (MackeyDiagrams.ConjEmbedding.toHom p).range.FiniteIndex :=
    ⟨by rw [indexOne]; decide⟩
  refine Set.Finite.subset (MackeyDiagrams.Generator.multiplicationCap_finiteFiber
    p finite (MackeyDiagrams.Generator.mixedProduct p p z)) ?_
  intro w hw
  have hcap : MackeyDiagrams.Generator.mixedProduct p p
      (MackeyDiagrams.Generator.mixedMultiplicationBasis p p p p leftDot w) =
      MackeyDiagrams.Generator.multiplicationCapBasis p w := by
    refine Quotient.inductionOn w (fun xy => ?_)
    change MackeyDiagrams.Generator.mixedProduct p p
      (MackeyDiagrams.Generator.mixedPair p p (xy.1 * 1 * xy.2)) = xy.1 * xy.2
    rw [MackeyDiagrams.Generator.mixedProduct_mixedPair, mul_one]
  exact hcap.symm.trans (congrArg (MackeyDiagrams.Generator.mixedProduct p p) hw)
abbrev drawId := fun {K H : Subgroup U} (w : MackeyDiagrams.Word K H) =>
  plain (MackeyDiagrams.Diagram.id w)
abbrev leftMixed := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex)
  p p a a [(1, MackeyDiagrams.Dot.id (comp p a))]
abbrev leftParallel := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex)
  p a p a [(1, MackeyDiagrams.Dot.id (comp p a))]
abbrev leftProject := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex)
  p p p p [(1, ⟨leftDot, leftFinite⟩)]
abbrev left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
  stack (plain (MackeyDiagrams.Diagram.unassociate ga ad df))
    (stack (beside leftMixed (drawId df))
      (stack (plain (MackeyDiagrams.Diagram.associate ce gc df))
        (stack (beside (drawId ce) leftParallel)
          (stack (plain (MackeyDiagrams.Diagram.unassociate ce gc ef))
            (stack (beside leftProject (drawId ef))
              (plain (MackeyDiagrams.Diagram.associate gc ce ef)))))))
abbrev dot := fun (b c : MackeyDiagrams.ConjEmbedding T P) (x : P) =>
  ({ element := x
     intertwines := fun h => by
       have hh : h = 1 := Subsingleton.elim _ _
       simp [hh] } : MackeyDiagrams.Dot b c)
abbrev Lower := MackeyDiagrams.DotLabel Complex (comp a i) (comp a i)
abbrev Middle := MackeyDiagrams.DotLabel Complex (comp a i) (comp p a)
abbrev Upper := MackeyDiagrams.DotLabel Complex (comp p a) (comp a i)
theorem rightFinite : ∀ (d : MackeyDiagrams.Dot (comp a i) (comp a i)) z,
    Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a a i i d w = z} := by
  let : Finite (MackeyDiagrams.Word.basis (tensor ai fj)).carrier := by
    change Finite (Quotient (MackeyDiagrams.Biset.balance
      (MackeyDiagrams.Biset.induction i) (MackeyDiagrams.Biset.restriction i)))
    infer_instance
  intro d z
  exact Set.toFinite _
noncomputable def right := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
  let projectionTerms : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a a i i) :=
    List.map (fun (term : Complex × MackeyDiagrams.Dot (comp a i) (comp a i)) =>
      (term.1, (⟨term.2, rightFinite term.2⟩ : MackeyDiagrams.ProjectionDot.Mixed a a i i)))
      (MackeyDiagrams.DotLabel.terms lower)
  let first := MackeyDiagrams.LabelledDrawing.compactProjection a a i i projectionTerms
  let second := MackeyDiagrams.LabelledDrawing.parallelUp a i p a
    (MackeyDiagrams.DotLabel.terms middle)
  let third := MackeyDiagrams.LabelledDrawing.mixedMultiplication p a a i
    (MackeyDiagrams.DotLabel.terms upper)
  (stack (beside (drawId ga) first)
    (stack (plain (MackeyDiagrams.Diagram.unassociate ga ai fj))
      (stack (beside second (drawId fj))
        (stack (plain (MackeyDiagrams.Diagram.associate gc ck fj))
          (beside (drawId gc) third)))) :
    MackeyDiagrams.LabelledDrawing Complex bottom top)
noncomputable def rightShape := MackeyDiagrams.LabelledDrawing.planarShape (right 0 0 0)
abbrev bottomBoundary := MackeyDiagrams.Word.boundary bottom
abbrev topBoundary := MackeyDiagrams.Word.boundary top
abbrev RightDrawing := MackeyDiagrams.LabelledDrawing.PlanarAtBoundary
  Complex bottomBoundary topBoundary rightShape
noncomputable def rightAt := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
  ({ bottom := bottom
     top := top
     diagram := right lower middle upper
     bottom_eq := rfl
     top_eq := rfl
     shape_eq := by rfl } : RightDrawing)
noncomputable def rightTerm := fun r : P =>
  right (Finsupp.single (dot (comp a i) (comp a i) r) 1)
    (Finsupp.single (dot (comp a i) (comp p a) r) 1)
    (Finsupp.single (dot (comp p a) (comp a i) 1) 1)
abbrev X := MackeyDiagrams.Word.basis bottom
abbrev Y := MackeyDiagrams.Word.basis top
abbrev inputPair := fun g x : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair a a x)
abbrev outputPair := fun h y : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction p)
    (MackeyDiagrams.Word.basis (tensor ce ef)) h (MackeyDiagrams.Generator.mixedPair p a y)
noncomputable def input := fun g x : P => Finsupp.single (inputPair g x) (1 : Complex)
noncomputable def output := fun z : P => Finsupp.single (outputPair z 1) (1 : Complex)
noncomputable def eval := fun (d : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d))
noncomputable def evalAt := fun (d : MackeyDiagrams.ScopedDiagram Complex
    (MackeyDiagrams.Boundary.word bottomBoundary) (MackeyDiagrams.Boundary.word topBoundary)) =>
  MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
    (MackeyDiagrams.ScopedDiagram.vertical
      (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderToBoundary bottom))
      (MackeyDiagrams.ScopedDiagram.vertical d
        (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderFromBoundary top)))))
noncomputable def interpretRight := fun (d : RightDrawing) =>
  MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret (s := rightShape) d
noncomputable def rightSum := fun (terms : List (Complex × RightDrawing)) =>
  MackeyDiagrams.ScopedDiagram.linearCombination
    (List.map (fun term => (term.1, interpretRight term.2)) terms)

end CaseFiveInfiniteAux
