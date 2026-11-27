import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Index
import MackeyDiagrams.PlanarShape

universe u

noncomputable def ReviewedEndpoint : Prop :=
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
  let Parameter := MackeyDiagrams.ProjectionDot.Mixed a bc de f
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let combination := fun (coeff : Finsupp Parameter Complex) =>
    Finsupp.sum coeff (fun p weight => weight • Qstar p)
  let intersection := fun {K H P : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (p : P) =>
    MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom α) ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj p))
        (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom β))
  let adeRange := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (comp a de))
  let deRange := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom de)
  let n := fun (p : Parameter) =>
    Subgroup.relIndex adeRange (intersection a bc (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p)))
  let basisMap := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.ProjectionDot.Mixed α β η θ) =>
    MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ (MackeyDiagrams.ProjectionDot.dot x)
  let hasFiberSize := fun {X Y : Type u} (q : X → Y) (size : Nat) =>
    ∀ z ∈ Set.range q, Nat.card {w : X // q w = z} = size
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
  let fullIntersection := fun (p : Parameter)
      (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    let element := MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p)
    let B := Subgroup.map (Subgroup.subtype G)
      (Subgroup.comap (MackeyDiagrams.ConjEmbedding.toHom a) (intersection a b element))
    ∃ (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B),
      (∀ v : B, (MackeyDiagrams.ConjEmbedding.toHom r v : U) = (v : U)) ∧
      (∀ v : B,
        MackeyDiagrams.ConjEmbedding.toHom b (MackeyDiagrams.ConjEmbedding.toHom s v) =
          element⁻¹ *
            MackeyDiagrams.ConjEmbedding.toHom a (MackeyDiagrams.ConjEmbedding.toHom r v) *
            element) ∧
      comp r t = de ∧ comp s t = cf ∧
      ∃ (x : MackeyDiagrams.ProjectionDot.Mixed a b r s) (y : MackeyDiagrams.ProjectionDot.Mixed s c t f)
        (z : MackeyDiagrams.Dot (comp r t) de),
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot x) = element ∧
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot y) = 1 ∧ MackeyDiagrams.Dot.element z = 1 ∧
        hasFiberSize (basisMap a b r s x) 1 ∧
        hasFiberSize (basisMap s c t f y) (n p) ∧
        diagram = left r s t [(1, x)] [(1, y)] [(1, z)]
  let commonGroup := fun (coeff : Finsupp Parameter Complex)
      (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    let t := MackeyDiagrams.ConjEmbedding.id E
    ∃ (x : Parameter → MackeyDiagrams.ProjectionDot.Mixed a b de cf)
      (y : MackeyDiagrams.ProjectionDot.Mixed cf c t f)
      (z : MackeyDiagrams.Dot (comp de t) de),
      (∀ p : Parameter,
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot (x p)) =
          MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p) ∧
        ∀ v, Nat.card {w // basisMap a b de cf (x p) w = v} ≤ Subgroup.index deRange) ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot y) = 1 ∧
      MackeyDiagrams.Dot.element z = 1 ∧
      hasFiberSize (basisMap cf c t f y) 1 ∧
      drawing = left de cf t
        (List.map (fun term => (term.1, x term.2)) (labelTerms coeff)) [(1, y)] [(1, z)]
  let sumDrawings := fun (coeff : Finsupp Parameter Complex)
      (terms : Parameter → MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    List.foldr (fun term total => MackeyDiagrams.LabelledDrawing.add
      (MackeyDiagrams.LabelledDrawing.scale term.1 (terms term.2)) total)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top))
      (labelTerms coeff)
  (∀ p : Parameter, ∃ drawing, fullIntersection p drawing ∧ eval drawing = Qstar p) ∧
  (Subgroup.FiniteIndex deRange →
    ∀ coeff : Finsupp Parameter Complex,
      ∃ drawing, commonGroup coeff drawing ∧ eval drawing = combination coeff) ∧
  (∀ {B' : Subgroup U} (u' : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp u' w))
      (ms : Finsupp (MackeyDiagrams.ProjectionDot.Mixed a u' d v) Complex)
      (ns : Finsupp (MackeyDiagrams.ProjectionDot.Mixed v w e f) Complex),
    let drawing := right u' v w ells ms ns
    ∃ (coeff : Finsupp Parameter Complex)
      (terms : Parameter → MackeyDiagrams.LabelledDrawing Complex bottom top),
      (∀ p : Parameter, fullIntersection p (terms p) ∧ eval (terms p) = Qstar p) ∧
      eval drawing = combination coeff ∧
      (∀ other : Finsupp Parameter Complex, eval drawing = combination other → other = coeff) ∧
      eval (sumDrawings coeff terms) = eval drawing ∧
      (Subgroup.FiniteIndex deRange →
        ∃ replacement, commonGroup coeff replacement ∧ eval replacement = eval drawing))
