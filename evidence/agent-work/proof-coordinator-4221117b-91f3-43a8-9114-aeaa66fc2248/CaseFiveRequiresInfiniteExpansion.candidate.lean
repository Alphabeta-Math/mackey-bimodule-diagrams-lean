import MackeyDiagrams.PointwiseIndexedDrawing
import Mathlib.Basic.Complex.Basic

def ReviewedStatementCandidate : Prop :=
let U := Multiplicative Int
let P : Subgroup U := ⊤
let T : Subgroup U := ⊥
let p := MackeyDiagrams.ConjEmbedding.id P
let a : MackeyDiagrams.ConjEmbedding T P :=
  { toHom := Subgroup.inclusion bot_le
    hasRepresentative := ⟨1, fun _ => by simp⟩ }
let i := MackeyDiagrams.ConjEmbedding.id T
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let beside := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let plain := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let ga := up a
let ad := down a
let df := up a
let gc := up p
let ce := down p
let ef := up a
let ai := up i
let fj := down i
let ck := up a
let bottom := tensor ga (tensor ad df)
let top := tensor gc (tensor ce ef)
let indexOne : (MackeyDiagrams.ConjEmbedding.toHom p).range.index = 1 := by
  change (MonoidHom.id P).range.index = 1
  rw [MonoidHom.range_eq_top_of_surjective (MonoidHom.id P) (fun x => ⟨x, rfl⟩),
    Subgroup.index_top]
let leftDot := MackeyDiagrams.Dot.id (comp p p)
let leftFinite :
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
let drawId := fun {K H : Subgroup U} (w : MackeyDiagrams.Word K H) =>
  plain (MackeyDiagrams.Diagram.id w)
let leftMixed := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex)
  p p a a [(1, MackeyDiagrams.Dot.id (comp p a))]
let leftParallel := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex)
  p a p a [(1, MackeyDiagrams.Dot.id (comp p a))]
let leftProject := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex)
  p p p p [(1, ⟨leftDot, leftFinite⟩)]
let left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
  stack (plain (MackeyDiagrams.Diagram.unassociate ga ad df))
    (stack (beside leftMixed (drawId df))
      (stack (plain (MackeyDiagrams.Diagram.associate ce gc df))
        (stack (beside (drawId ce) leftParallel)
          (stack (plain (MackeyDiagrams.Diagram.unassociate ce gc ef))
            (stack (beside leftProject (drawId ef))
              (plain (MackeyDiagrams.Diagram.associate gc ce ef)))))))
let dot := fun (b c : MackeyDiagrams.ConjEmbedding T P) (x : P) =>
  ({ element := x
     intertwines := fun h => by
       have hh : h = 1 := Subsingleton.elim _ _
       simp [hh] } : MackeyDiagrams.Dot b c)
let Lower := MackeyDiagrams.DotLabel Complex (comp a i) (comp a i)
let Middle := MackeyDiagrams.DotLabel Complex (comp a i) (comp p a)
let Upper := MackeyDiagrams.DotLabel Complex (comp p a) (comp a i)
let rightFinite : ∀ (d : MackeyDiagrams.Dot (comp a i) (comp a i)) z,
    Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a a i i d w = z} := by
  let : Finite (MackeyDiagrams.Word.basis (tensor ai fj)).carrier := by
    change Finite (Quotient (MackeyDiagrams.Biset.balance
      (MackeyDiagrams.Biset.induction i) (MackeyDiagrams.Biset.restriction i)))
    infer_instance
  intro d z
  exact Set.toFinite _
let right := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
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
let rightShape := MackeyDiagrams.LabelledDrawing.planarShape (right 0 0 0)
let bottomBoundary := MackeyDiagrams.Word.boundary bottom
let topBoundary := MackeyDiagrams.Word.boundary top
let RightDrawing := MackeyDiagrams.LabelledDrawing.PlanarAtBoundary
  Complex bottomBoundary topBoundary rightShape
let rightAt := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
  ({ bottom := bottom
     top := top
     diagram := right lower middle upper
     bottom_eq := rfl
     top_eq := rfl
     shape_eq := by rfl } : RightDrawing)
let rightTerm := fun r : P =>
  right (Finsupp.single (dot (comp a i) (comp a i) r) 1)
    (Finsupp.single (dot (comp a i) (comp p a) r) 1)
    (Finsupp.single (dot (comp p a) (comp a i) 1) 1)
let X := MackeyDiagrams.Word.basis bottom
let Y := MackeyDiagrams.Word.basis top
let inputPair := fun g x : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair a a x)
let outputPair := fun h y : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction p)
    (MackeyDiagrams.Word.basis (tensor ce ef)) h (MackeyDiagrams.Generator.mixedPair p a y)
let input := fun g x : P => Finsupp.single (inputPair g x) (1 : Complex)
let output := fun z : P => Finsupp.single (outputPair z 1) (1 : Complex)
let eval := fun (d : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d))
let evalAt := fun (d : MackeyDiagrams.ScopedDiagram Complex
    (MackeyDiagrams.Boundary.word bottomBoundary) (MackeyDiagrams.Boundary.word topBoundary)) =>
  MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
    (MackeyDiagrams.ScopedDiagram.vertical
      (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderToBoundary bottom))
      (MackeyDiagrams.ScopedDiagram.vertical d
        (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderFromBoundary top)))))
let interpretRight := fun (d : RightDrawing) =>
  MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret (s := rightShape) d
let rightSum := fun (terms : List (Complex × RightDrawing)) =>
  MackeyDiagrams.ScopedDiagram.linearCombination
    (List.map (fun term => (term.1, interpretRight term.2)) terms)
(MackeyDiagrams.ConjEmbedding.toHom p).range.index = 1 ∧
  (∀ (Q : Subgroup U), MackeyDiagrams.ConjEmbedding Q T → Q = T) ∧
  (∃ identify : Y.carrier ≃ P, ∀ h y : P, identify (outputPair h y) = h * y) ∧
  (∀ g x : P, eval left (input g x) = output (g * x)) ∧
  (∀ (lower : Lower) (middle : Middle) (upper : Upper) (g x : P),
    x ∉ Finset.image MackeyDiagrams.Dot.element (Finsupp.support lower) →
      eval (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.diagram
        (rightAt lower middle upper)) (input g x) = 0) ∧
  (∀ d : RightDrawing, ∃ support : Finset P, ∀ g x : P, x ∉ support →
    evalAt (interpretRight d) (input g x) = 0) ∧
  (∀ terms : List (Complex × RightDrawing),
    (∃ support : Finset P, ∀ g x : P, x ∉ support →
      evalAt (rightSum terms) (input g x) = 0) ∧
    evalAt (rightSum terms) ≠ eval left) ∧
  (∀ r g x : P, eval (rightTerm r) (input g x) =
    (if x = r then output (g * x) else 0)) ∧
  (∃ finite : ∀ v : Finsupp X.carrier Complex,
      Set.Finite {x : P | eval (rightTerm x) v ≠ 0},
    let drawing : MackeyDiagrams.PointwiseIndexedDrawing Complex bottom top P :=
      ⟨rightTerm, finite⟩
    ∀ v : Finsupp X.carrier Complex, eval left v = drawing.evalAt v)

#print axioms ReviewedStatementCandidate
