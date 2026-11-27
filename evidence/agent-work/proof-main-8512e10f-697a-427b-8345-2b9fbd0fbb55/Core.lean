import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
import Proofs.CaseTwoLeftProjectionConstruction
import Mathlib.GroupTheory.SemidirectProduct

set_option linter.unusedVariables false
namespace CaseTwoAudit

noncomputable abbrev swap : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (1 : ZMod 2)

noncomputable abbrev action : Multiplicative (ZMod 2) →* MulAut (Multiplicative Int × Multiplicative Int) :=
  let act := fun i : Multiplicative (ZMod 2) =>
    if i = 1 then 1 else (MulEquiv.prodComm : MulAut (Multiplicative Int × Multiplicative Int))
  { toFun := act
    map_one' := ite_eq_left rfl
    map_mul' := by
      have cases₂ : ∀ i : Multiplicative (ZMod 2), i = 1 ∨ i = swap := by
        intro i
        change (Multiplicative.toAdd i : Fin 2) = 0 ∨ Multiplicative.toAdd i = (1 : ZMod 2)
        exact (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) (Multiplicative.toAdd i)
      have hs : swap * swap = 1 := by decide
      have hn : swap ≠ 1 := by decide
      intro i j
      rcases cases₂ i with rfl | rfl <;> rcases cases₂ j with rfl | rfl <;>
        simp only [act, one_mul, mul_one, hs, ite_eq_left rfl, ite_eq_right hn]
      rfl }

noncomputable abbrev U :=
  SemidirectProduct (Multiplicative Int × Multiplicative Int) (Multiplicative (ZMod 2)) action

noncomputable abbrev A : Subgroup U :=
  ⊤

noncomputable abbrev G : Subgroup U :=
  MonoidHom.range (MonoidHom.comp
    (SemidirectProduct.inl (φ := action))
    (MonoidHom.inl (Multiplicative Int) (Multiplicative Int)))

noncomputable abbrev D :=
  G

noncomputable abbrev T : Subgroup U :=
  ⊥

noncomputable abbrev C :=
  T

noncomputable abbrev E :=
  T

noncomputable abbrev F :=
  T

noncomputable abbrev B' :=
  T

noncomputable abbrev τ : A :=
  ⟨SemidirectProduct.inr (φ := action) swap, Subgroup.mem_top _⟩

noncomputable abbrev incl :=
  fun {H K : Subgroup U} (h : H ≤ K) =>
    ({ toHom := Subgroup.inclusion h
       hasRepresentative := ⟨1, fun _ => by simp⟩ } : MackeyDiagrams.ConjEmbedding H K)

noncomputable abbrev a : MackeyDiagrams.ConjEmbedding G A :=
  incl le_top

noncomputable abbrev b : MackeyDiagrams.ConjEmbedding D A :=
  incl le_top

noncomputable abbrev c : MackeyDiagrams.ConjEmbedding F D :=
  incl bot_le

noncomputable abbrev d : MackeyDiagrams.ConjEmbedding C G :=
  incl bot_le

noncomputable abbrev e : MackeyDiagrams.ConjEmbedding E C :=
  incl le_rfl

noncomputable abbrev f : MackeyDiagrams.ConjEmbedding E F :=
  incl le_rfl

noncomputable abbrev u : MackeyDiagrams.ConjEmbedding B' A :=
  incl bot_le

noncomputable abbrev v : MackeyDiagrams.ConjEmbedding C B' :=
  incl le_rfl

noncomputable abbrev w : MackeyDiagrams.ConjEmbedding F B' :=
  incl le_rfl

noncomputable abbrev comp :=
  @MackeyDiagrams.ConjEmbedding.comp U _

noncomputable abbrev bc :=
  comp b c

noncomputable abbrev de :=
  comp d e

noncomputable abbrev up :=
  @MackeyDiagrams.Word.up U _

noncomputable abbrev down :=
  @MackeyDiagrams.Word.down U _

noncomputable abbrev tensor :=
  @MackeyDiagrams.Word.tensor U _

noncomputable abbrev bottom :=
  tensor (tensor (down a) (up b)) (up c)

noncomputable abbrev top :=
  tensor (tensor (up d) (up e)) (down f)

noncomputable abbrev mergedBottom :=
  tensor (down a) (up bc)

noncomputable abbrev mergedTop :=
  tensor (up de) (down f)

noncomputable abbrev drawId :=
  fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)

noncomputable abbrev splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
    (MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))

noncomputable abbrev mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
  MackeyDiagrams.LabelledDrawing.horizontal
    (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
    (drawId (down f))

noncomputable abbrev eval :=
  fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))

noncomputable abbrev atRight :=
  fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))

noncomputable abbrev ProjectionLabel :=
  fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ

noncomputable abbrev terms :=
  fun {X : Type} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))

noncomputable abbrev Qstar :=
  fun (p : ProjectionLabel a bc de f) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))

noncomputable abbrev left :=
  fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
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

noncomputable abbrev right :=
  fun
      (ells : MackeyDiagrams.DotLabel Complex bc (comp u w))
      (ms : Finsupp (ProjectionLabel a u d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c u w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a u d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))

noncomputable abbrev Drawing :=
  MackeyDiagrams.LabelledDrawing Complex bottom top

noncomputable abbrev IsLeftWith :=
  fun (allowed : Set A) (drawing : Drawing) =>
    ∃ (B : Subgroup U) (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de),
      (∀ x ∈ Finsupp.support xs,
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot x) ∈ allowed) ∧
      drawing = left r s t xs ys zs

noncomputable abbrev leftShape :=
  MackeyDiagrams.LabelledDrawing.planarShape
    (left (B := T) d (incl bot_le) (incl le_rfl) 0 0 0)

noncomputable abbrev sumDrawings :=
  fun (drawings : List Drawing) =>
    match drawings with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest

noncomputable abbrev basisVector :=
  fun p : A =>
    Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc p) (1 : Complex)

noncomputable abbrev line :=
  MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)

noncomputable abbrev swapCoset :=
  DoubleCoset.doubleCoset τ (line : Set A) (line : Set A)

noncomputable abbrev intersection :=
  fun x : A => line ⊓
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) line

end CaseTwoAudit
