import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.PlanarShape

set_option linter.unusedVariables false
universe u

noncomputable def endpoint : Prop :=
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let ade := comp a de
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
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
  let eval := fun (drawing : Drawing) =>
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
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let fiberSize := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : ProjectionLabel α β η θ) (z : P) =>
    Nat.card {w // MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ
      (MackeyDiagrams.ProjectionDot.dot x) w = MackeyDiagrams.Generator.mixedPair α β z}
  let Parameter := ProjectionLabel a bc de f
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let terms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s (terms xs)) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f (terms ys)))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e (MackeyDiagrams.DotLabel.terms zs))
          (drawId (down f))))
  let right := fun {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c j w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))
  let IsRight := fun (drawing : Drawing) =>
    ∃ (B' : Subgroup U) (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex),
      drawing = right j v w ells ms ns
  let sumDrawings := fun (ds : List Drawing) =>
    match ds with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let conjugatedImage := fun (p : Parameter) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj
      (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p))))
      (MonoidHom.range (hom bc))
  let join := fun (p : Parameter) => MonoidHom.range (hom ad) ⊔ conjugatedImage p
  let middleFinite := fun (p : Parameter) =>
    Subgroup.FiniteIndex (Subgroup.subgroupOf (MonoidHom.range (hom ad))
      (MonoidHom.range (hom a) ⊓ join p))
  let nₚ := fun (p : Parameter) =>
    Subgroup.relIndex (MonoidHom.range (hom ade)) (MonoidHom.range (hom a) ⊓ conjugatedImage p)
  let expansion := fun (coeff : Finsupp Parameter Complex) =>
    Finsupp.sum coeff (fun p weight => weight • Qstar p)
  (∀ (p : Parameter), middleFinite p →
    let B' := Subgroup.map (Subgroup.subtype A) (join p)
    let p₀ := MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p)
    ∃ (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ell : MackeyDiagrams.Dot bc (comp j w))
      (m : ProjectionLabel a j d v) (n : ProjectionLabel v w e f),
      (∀ k : B', (hom j k : U) = (k : U)) ∧
      (∀ k : C, hom j (hom v k) = hom ad k) ∧
      (∀ k : F, hom j (hom w k) = (MulAut.conj p₀) (hom bc k)) ∧
      MackeyDiagrams.Dot.element ell = p₀⁻¹ ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m) = 1 ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot n) = 1 ∧
      (∀ z : B', fiberSize v w e f n z ≤ nₚ p) ∧
      eval (right j v w (Finsupp.single ell 1) (Finsupp.single m 1) (Finsupp.single n 1)) =
        Qstar p) ∧
  (Subgroup.FiniteIndex (MonoidHom.range (hom d)) →
    let j := MackeyDiagrams.ConjEmbedding.id A
    ∃ (ell : MackeyDiagrams.Dot bc (comp j bc)) (m : ProjectionLabel a j d ad)
      (n : Parameter → ProjectionLabel ad bc e f),
      MackeyDiagrams.Dot.element ell = 1 ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m) = 1 ∧
      (∀ z : A, fiberSize a j d ad m z = Subgroup.index (MonoidHom.range (hom d))) ∧
      (∀ (p : Parameter), MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot (n p)) =
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p) ∧
          (∀ z : A, fiberSize ad bc e f (n p) z ≤ nₚ p)) ∧
      (∀ (coeff : Finsupp Parameter Complex),
        eval (right j ad bc (Finsupp.single ell 1) (Finsupp.single m 1)
          (Finsupp.mapDomain n coeff)) = expansion coeff)) ∧
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de)
      (coeff : Finsupp Parameter Complex), eval (left r s t xs ys zs) = expansion coeff →
    ((∃ ds : List Drawing,
        (∀ drawing ∈ ds, IsRight drawing) ∧
        eval (sumDrawings ds) = eval (left r s t xs ys zs)) ↔
      ∀ p ∈ Finsupp.support coeff, middleFinite p))
