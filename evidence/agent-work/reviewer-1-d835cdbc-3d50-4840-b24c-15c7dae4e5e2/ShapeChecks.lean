import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.PlanarShape

open MackeyDiagrams
universe u
noncomputable section

theorem leftCrossingOrder {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F) :
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let cf := comp c f
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
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
  ∀ {B : Subgroup U} (r : ConjEmbedding B G)
      (s : ConjEmbedding B D) (t : ConjEmbedding E B)
      (xs : List (Complex × ProjectionDot.Mixed a b r s))
      (ys : List (Complex × ProjectionDot.Mixed s c t f))
      (zs : List (Complex × Dot (comp r t) de)),
    PlanarCode.encode (left r s t xs ys zs).erase =
      [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp] := by
  intros
  rfl

theorem rightCrossingOrder {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F) :
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let cf := comp c f
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
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
  ∀ {B' : Subgroup U} (u' : ConjEmbedding B' A)
      (v : ConjEmbedding C B') (w : ConjEmbedding F B')
      (ell : DotLabel Complex bc (comp u' w))
      (ms : Finsupp (ProjectionDot.Mixed a u' d v) Complex)
      (ns : Finsupp (ProjectionDot.Mixed v w e f) Complex),
    PlanarCode.encode (right u' v w ell ms ns).erase =
      [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection] := by
  intros
  rfl

section
variable {U : Type u} [Group U] {K H : Subgroup U} {bottom top : Word K H}
variable {Parameter : Type u}

def labelTerms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
def sumDrawings {bottom top : Word K H} := fun (coeff : Finsupp Parameter Complex)
      (terms : Parameter → MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    List.foldr (fun term total => MackeyDiagrams.LabelledDrawing.add
      (MackeyDiagrams.LabelledDrawing.scale term.1 (terms term.2)) total)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top))
      (labelTerms coeff)

local instance : DecidableEq Parameter := Classical.decEq _

theorem foldEmpty (terms : Parameter → LabelledDrawing Complex bottom top) :
    (sumDrawings (0 : Finsupp Parameter Complex) terms).erase =
      .zero bottom.directions top.directions := by
  simp [sumDrawings, labelTerms, LabelledDrawing.erase, Diagram.drawing]

theorem foldSingleton (p : Parameter) (c : Complex) (hc : c ≠ 0)
    (terms : Parameter → LabelledDrawing Complex bottom top) :
    (sumDrawings (Finsupp.single p c) terms).erase =
      .add (.scale (terms p).erase) (.zero bottom.directions top.directions) := by
  simp [sumDrawings, labelTerms, Finsupp.support_single_ne_zero p hc, LabelledDrawing.erase,
    Diagram.drawing]
end
