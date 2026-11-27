import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.Index
import MackeyDiagrams.DotLabels
import MackeyDiagrams.Trivalent
import MackeyDiagrams.PlanarShape

universe u

set_option maxHeartbeats 1000000 in
theorem caseTwoLeftWiring :
  ∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let cf := comp c f
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let labelTerms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b r s))
      (ys : List (Complex × MackeyDiagrams.ProjectionDot.Mixed s c t f))
      (zs : List (Complex × MackeyDiagrams.Dot (comp r t) de)) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s xs) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (down f))))
  let right := fun {B' : Subgroup U} (u' : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp u' w))
      (ms : Finsupp (MackeyDiagrams.ProjectionDot.Mixed a u' d v) Complex)
      (ns : Finsupp (MackeyDiagrams.ProjectionDot.Mixed v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c u' w
        (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a u' d v (labelTerms ms))
          (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (labelTerms ns))))
  ∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b r s))
      (ys : List (Complex × MackeyDiagrams.ProjectionDot.Mixed s c t f))
      (zs : List (Complex × MackeyDiagrams.Dot (comp r t) de)),
    MackeyDiagrams.PlanarCode.encode (left r s t xs ys zs).erase.geometry =
      [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp] := by
  intros
  rfl

set_option maxHeartbeats 1000000 in
theorem caseTwoRightWiring :
  ∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let cf := comp c f
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let labelTerms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b r s))
      (ys : List (Complex × MackeyDiagrams.ProjectionDot.Mixed s c t f))
      (zs : List (Complex × MackeyDiagrams.Dot (comp r t) de)) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s xs) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (down f))))
  let right := fun {B' : Subgroup U} (u' : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp u' w))
      (ms : Finsupp (MackeyDiagrams.ProjectionDot.Mixed a u' d v) Complex)
      (ns : Finsupp (MackeyDiagrams.ProjectionDot.Mixed v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c u' w
        (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a u' d v (labelTerms ms))
          (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (labelTerms ns))))
  ∀ {B' : Subgroup U} (u' : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp u' w))
      (ms : Finsupp (MackeyDiagrams.ProjectionDot.Mixed a u' d v) Complex)
      (ns : Finsupp (MackeyDiagrams.ProjectionDot.Mixed v w e f) Complex),
    MackeyDiagrams.PlanarCode.encode (right u' v w ells ms ns).erase.geometry =
      [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection] := by
  intros
  rfl
