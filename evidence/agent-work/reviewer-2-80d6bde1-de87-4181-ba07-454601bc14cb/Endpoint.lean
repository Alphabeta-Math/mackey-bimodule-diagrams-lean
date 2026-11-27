import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.IndexedDrawing
import MackeyDiagrams.PointwiseIndexedBimodule

set_option autoImplicit false

def ExpansionIntoRightDiagrams : Prop :=
∀ {U : Type*} [Group U] (G A D F C E : Subgroup U)
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let ga := up a
  let ad := down b
  let df := up d
  let gc := up c
  let ce := down e
  let ef := up f
  let bottom := tensor ga (tensor ad df)
  let top := tensor gc (tensor ce ef)
  let X := MackeyDiagrams.Word.basis bottom
  let Y := MackeyDiagrams.Word.basis top
  let Pair := X.carrier × Y.carrier
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let orbit : Pair → Set Pair := MulAction.orbit (G × F)
  let coefficient := fun (M : MackeyDiagrams.Biset.Hom Complex X Y) (z : Pair) =>
    MackeyDiagrams.Biset.Hom.toLinearMap M (Finsupp.single z.1 (1 : Complex)) z.2
  let MiddleLabel := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (k : MackeyDiagrams.ConjEmbedding P C) =>
    MackeyDiagrams.Dot (comp a i) (comp c k)
  let UpperLabel := fun (P : Subgroup U)
      (j : MackeyDiagrams.ConjEmbedding P F) (k : MackeyDiagrams.ConjEmbedding P C) =>
    MackeyDiagrams.Dot (comp e k) (comp f j)
  let ProjectionTerm := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F) =>
    MackeyDiagrams.ProjectionDot.Mixed b d i j
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let rightDrawing := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
      (k : MackeyDiagrams.ConjEmbedding P C)
      (lower : List (Complex × ProjectionTerm P i j))
      (middle : List (Complex × MiddleLabel P i k))
      (upper : List (Complex × UpperLabel P j k)) =>
    let ai := up i
    let fj := down j
    let ck := up k
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId ga)
        (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.parallelUp a i c k middle) (drawId fj))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId gc)
              (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j upper))))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let IsRightTerm := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    ∃ (P : Subgroup U) (i : MackeyDiagrams.ConjEmbedding P A)
      (j : MackeyDiagrams.ConjEmbedding P F) (k : MackeyDiagrams.ConjEmbedding P C)
      (lower : List (Complex × ProjectionTerm P i j))
      (middle : List (Complex × MiddleLabel P i k))
      (upper : List (Complex × UpperLabel P j k)),
      drawing = rightDrawing P i j k lower middle upper
  ∀ (M : MackeyDiagrams.Biset.Hom Complex X Y),
    let supported : Set (Set Pair) := {O | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0}
    (∃ (weight : supported → Complex)
        (diagram : supported → MackeyDiagrams.LabelledDrawing Complex bottom top),
      (∀ O, IsRightTerm (diagram O)) ∧
      (∀ (O : supported) (z : Pair), O.val = orbit z → weight O = coefficient M z) ∧
      let summand := fun O => MackeyDiagrams.LabelledDrawing.scale (weight O) (diagram O)
      ∃ finite : ∀ v : Finsupp X.carrier Complex,
          Set.Finite (Function.support fun O =>
            MackeyDiagrams.Biset.Hom.toLinearMap (eval (summand O)) v),
        let expansion : MackeyDiagrams.PointwiseIndexedDrawing Complex bottom top supported :=
          ⟨summand, finite⟩
        M = MackeyDiagrams.PointwiseIndexedDrawing.evalHom expansion) ∧
    ((∃ terms : List (Complex × MackeyDiagrams.LabelledDrawing Complex bottom top),
        (∀ term ∈ terms, IsRightTerm term.2) ∧
        let expansion : MackeyDiagrams.IndexedDrawing Complex bottom top (Fin terms.length) :=
          ⟨Finset.univ, fun i =>
            MackeyDiagrams.LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩
        MackeyDiagrams.Biset.Hom.toLinearMap M = MackeyDiagrams.IndexedDrawing.eval expansion) ↔
      Set.Finite supported)
