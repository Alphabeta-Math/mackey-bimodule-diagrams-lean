import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.DotLabels
import MackeyDiagrams.IndexedDrawing
import MackeyDiagrams.PointwiseIndexedDrawing

noncomputable def reviewedEndpoint : Prop :=
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
  let input := fun (g : G) (x : D) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let orbit : Pair → Set Pair := MulAction.orbit (G × F)
  let stabilizer : Pair → Subgroup (G × F) := MulAction.stabilizer (G × F)
  let projected := fun z : Pair =>
    Subgroup.map (MonoidHom.comp (Subgroup.subtype F) (MonoidHom.snd G F)) (stabilizer z)
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
  ∀ (B : Subgroup U)
      (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B),
    let LeftUpper := MackeyDiagrams.ProjectionDot.Mixed u w c e
    let leftDrawing := fun
        (rs : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
        (ts : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w f)))
        (ss : List (Complex × LeftUpper)) =>
      let ug := down u
      let dv := up v
      let ew := up w
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b rs) (drawId df))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate ug dv df))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.horizontal (drawId ug)
                (MackeyDiagrams.LabelledDrawing.parallelUp v d w f ts))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ug ew ef))
                (MackeyDiagrams.LabelledDrawing.vertical
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.compactProjection u w c e ss) (drawId ef))
                  (MackeyDiagrams.LabelledDrawing.ordinary
                    (MackeyDiagrams.Diagram.associate gc ce ef))))))) :
        MackeyDiagrams.LabelledDrawing Complex bottom top)
    ∀ (rs : MackeyDiagrams.DotLabel Complex (comp u a) (comp v b))
      (ts : MackeyDiagrams.DotLabel Complex (comp v d) (comp w f))
      (ss : Finsupp LeftUpper Complex),
    let upperTerms := List.map (fun s => (ss s, s)) (Finset.toList (Finsupp.support ss))
    let M := eval (leftDrawing (MackeyDiagrams.DotLabel.terms rs)
      (MackeyDiagrams.DotLabel.terms ts) upperTerms)
    let supported := {O : Set Pair | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0}
    (∃ (diagram : supported → MackeyDiagrams.LabelledDrawing Complex bottom top)
        (weight : supported → Complex),
      (∀ O : supported,
        ∃ (r : D) (t : G) (s : E),
          let z := (input 1 r, output t s)
          let P := projected z
          O.val = orbit z ∧
          weight O = coefficient M z ∧
          ∃ (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
            (k : MackeyDiagrams.ConjEmbedding P C)
            (rDot : ProjectionTerm P i j) (tDot : MiddleLabel P i k) (sDot : UpperLabel P j k),
            (∀ h : P, (MackeyDiagrams.ConjEmbedding.toHom j h : U) = (h : U)) ∧
            MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot rDot) = r ∧
            MackeyDiagrams.Dot.element tDot = t ∧
            MackeyDiagrams.Dot.element sDot = s ∧
            diagram O = rightDrawing P i j k [(1, rDot)] [(1, tDot)] [(1, sDot)]) ∧
      let term := fun (O : supported) (x : Finsupp X.carrier Complex) =>
        weight O • MackeyDiagrams.Biset.Hom.toLinearMap (eval (diagram O)) x
      ∃ (finite : ∀ x : Finsupp X.carrier Complex, Set.Finite {O : supported | term O x ≠ 0}),
        let sum : MackeyDiagrams.PointwiseIndexedDrawing Complex bottom top supported :=
          ⟨fun O => MackeyDiagrams.LabelledDrawing.scale (weight O) (diagram O), finite⟩
        ∀ x : Finsupp X.carrier Complex,
          MackeyDiagrams.Biset.Hom.toLinearMap M x = sum.evalAt x) ∧
    ((∃ terms : List (Complex × MackeyDiagrams.LabelledDrawing Complex bottom top),
        (∀ term ∈ terms, IsRightTerm term.2) ∧
        let drawing : MackeyDiagrams.IndexedDrawing Complex bottom top (Fin terms.length) :=
          ⟨Finset.univ, fun i => MackeyDiagrams.LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩
        MackeyDiagrams.Biset.Hom.toLinearMap M = drawing.eval) ↔
      Set.Finite supported)
