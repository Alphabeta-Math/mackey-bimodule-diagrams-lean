import MackeyDiagrams.DotLabels
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.GroupTheory.Index

noncomputable section
universe u
set_option maxHeartbeats 400000 in
def endpoint : Prop :=
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
    let bcf := comp bc f
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
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
    let mergedEval := fun (drawing : Drawing) =>
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
    let Parameter := ProjectionLabel a bc de f
    let Q := fun (p : MackeyDiagrams.Dot ade bcf) (w : (MackeyDiagrams.Word.basis mergedTop).carrier) =>
      MackeyDiagrams.Generator.mixedProduct a bc
        (MackeyDiagrams.Generator.mixedMultiplicationBasis a bc de f p w)
    let Qstar := fun (p : Parameter) =>
      MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
        (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
          (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
    let intersection := fun (p : MackeyDiagrams.Dot ade bcf) =>
      MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a) ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (MackeyDiagrams.Dot.element p)))
          (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom bc))
    let lower := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom ade)
    let terms := fun {X : Type u} (label : Finsupp X Complex) =>
      List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
    let finiteFibers := fun {K H P L : Subgroup U}
        (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
        (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
        (x : MackeyDiagrams.Dot (comp α η) (comp β θ)) =>
      ∀ z, Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ x w = z}
    let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
        (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
        (xs : List (Complex × ProjectionLabel a b r s))
        (ys : List (Complex × ProjectionLabel s c t f))
        (zs : List (Complex × MackeyDiagrams.Dot (comp r t) de)) =>
      MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a b r s xs) (drawId (up c)))
        (MackeyDiagrams.LabelledDrawing.vertical
          (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (down f))))
    let right := fun {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
        (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
        (ells : List (Complex × MackeyDiagrams.Dot bc (comp j w)))
        (ms : List (Complex × ProjectionLabel a j d v))
        (ns : List (Complex × ProjectionLabel v w e f)) =>
      MackeyDiagrams.LabelledDrawing.vertical
        (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c j w ells))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.compactProjection a j d v ms) (drawId (up w)))
          (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f ns)))
    let Left := Σ B : Subgroup U,
      Σ r : MackeyDiagrams.ConjEmbedding B G,
      Σ s : MackeyDiagrams.ConjEmbedding B D,
      Σ t : MackeyDiagrams.ConjEmbedding E B,
        Finsupp (ProjectionLabel a b r s) Complex ×
        Finsupp (ProjectionLabel s c t f) Complex ×
        MackeyDiagrams.DotLabel Complex (comp r t) de
    let Right := Σ B' : Subgroup U,
      Σ j : MackeyDiagrams.ConjEmbedding B' A,
      Σ v : MackeyDiagrams.ConjEmbedding C B',
      Σ w : MackeyDiagrams.ConjEmbedding F B',
        MackeyDiagrams.DotLabel Complex bc (comp j w) ×
        Finsupp (ProjectionLabel a j d v) Complex ×
        Finsupp (ProjectionLabel v w e f) Complex
    let leftDrawing : Left → Drawing :=
      fun ⟨_, r, s, t, xs, ys, zs⟩ =>
        left r s t (terms xs) (terms ys) (MackeyDiagrams.DotLabel.terms zs)
    let rightDrawing : Right → Drawing :=
      fun ⟨_, j, v, w, ells, ms, ns⟩ =>
        right j v w (MackeyDiagrams.DotLabel.terms ells) (terms ms) (terms ns)
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
    let expansion := fun (coeff : Finsupp Parameter Complex) =>
      Finsupp.sum coeff (fun p weight => weight • Qstar p)
    let leftEval := fun l : Left => eval (leftDrawing l)
    let rightEval := fun r : Right => eval (rightDrawing r)
    let leftClasses := Setoid.ker leftEval
    let rightClasses := Setoid.ker rightEval
    (∀ p : MackeyDiagrams.Dot ade bcf,
      lower ≤ intersection p ∧
      (finiteFibers a bc de f p ↔ Subgroup.FiniteIndex (Subgroup.subgroupOf lower (intersection p))) ∧
      (∀ (g : G) (h : F),
        Q p (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction de)
            (MackeyDiagrams.Biset.restriction f) g h) =
          MackeyDiagrams.ConjEmbedding.toHom a g * MackeyDiagrams.Dot.element p *
            MackeyDiagrams.ConjEmbedding.toHom bc h)) ∧
    (∀ (p : Parameter) (z : A),
      Qstar p (Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc z) 1) =
        Finset.sum (Set.Finite.toFinset (MackeyDiagrams.ProjectionDot.finite p (MackeyDiagrams.Generator.mixedPair a bc z)))
          (fun w => Finsupp.single w 1) ∧
      (z ∈ Set.range (Q (MackeyDiagrams.ProjectionDot.dot p)) →
        Nat.card {w : (MackeyDiagrams.Word.basis mergedTop).carrier // Q (MackeyDiagrams.ProjectionDot.dot p) w = z} =
          Subgroup.relIndex lower (intersection (MackeyDiagrams.ProjectionDot.dot p)))) ∧
    (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
        (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
        (x : ProjectionLabel a b r s) (y : ProjectionLabel s c t f)
        (z : MackeyDiagrams.Dot (comp r t) de),
      ∃! p : Parameter, mergedEval (left r s t [(1, x)] [(1, y)] [(1, z)]) = Qstar p) ∧
    (∀ {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
        (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
        (ell : MackeyDiagrams.Dot bc (comp j w)) (m : ProjectionLabel a j d v)
        (n : ProjectionLabel v w e f),
      ∃! p : Parameter, mergedEval (right j v w [(1, ell)] [(1, m)] [(1, n)]) = Qstar p) ∧
    (∀ l : Left, ∃ coeff : Finsupp Parameter Complex,
      mergedEval (leftDrawing l) = expansion coeff ∧
      (∀ other : Finsupp Parameter Complex,
        mergedEval (leftDrawing l) = expansion other → other = coeff) ∧
      ((∃ ds : List Right, eval (sumDrawings (List.map rightDrawing ds)) = leftEval l) ↔
        ∀ p ∈ Finsupp.support coeff, middleFinite p)) ∧
    (∀ r : Right, ∃! coeff : Finsupp Parameter Complex,
      mergedEval (rightDrawing r) = expansion coeff) ∧
    (∀ p : Parameter, middleFinite p →
      ∃ r : Right, mergedEval (rightDrawing r) = Qstar p) ∧
    (Subgroup.FiniteIndex (MonoidHom.range (hom d)) →
      ∀ l : Left, ∃ r : Right, rightEval r = leftEval l) ∧
    (∀ r : Right, ∃ ds : List Left, eval (sumDrawings (List.map leftDrawing ds)) = rightEval r) ∧
    (Subgroup.FiniteIndex (MonoidHom.range (hom de)) →
      ∀ r : Right, ∃ l : Left, leftEval l = rightEval r) ∧
    (Subgroup.FiniteIndex (MonoidHom.range (hom de)) ∨ Finite G →
      ∃ (replaceCase1 : Left → Right) (replaceCase2 : Right → Left)
        (replacement : Quotient leftClasses ≃ Quotient rightClasses),
        (∀ l : Left, rightEval (replaceCase1 l) = leftEval l ∧
          replacement (Quotient.mk leftClasses l) = Quotient.mk rightClasses (replaceCase1 l)) ∧
        (∀ r : Right, leftEval (replaceCase2 r) = rightEval r ∧
          Equiv.symm replacement (Quotient.mk rightClasses r) =
            Quotient.mk leftClasses (replaceCase2 r)))
