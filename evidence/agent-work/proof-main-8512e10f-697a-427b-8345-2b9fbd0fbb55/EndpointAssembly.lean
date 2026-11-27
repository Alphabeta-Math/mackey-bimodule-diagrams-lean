import AssemblyPart
import FactorPart

noncomputable def CaseTwoReviewedType : Prop :=
  let swap : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
  let action : Multiplicative (ZMod 2) →* MulAut (Multiplicative Int × Multiplicative Int) :=
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
  let U := SemidirectProduct (Multiplicative Int × Multiplicative Int) (Multiplicative (ZMod 2)) action
  let A : Subgroup U := ⊤
  let G : Subgroup U := MonoidHom.range (MonoidHom.comp
    (SemidirectProduct.inl (φ := action))
    (MonoidHom.inl (Multiplicative Int) (Multiplicative Int)))
  let D := G
  let T : Subgroup U := ⊥
  let C := T
  let E := T
  let F := T
  let B' := T
  let τ : A := ⟨SemidirectProduct.inr (φ := action) swap, Subgroup.mem_top _⟩
  let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
    ({ toHom := Subgroup.inclusion h
       hasRepresentative := ⟨1, fun _ => by simp⟩ } : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := incl le_top
  let b : MackeyDiagrams.ConjEmbedding D A := incl le_top
  let c : MackeyDiagrams.ConjEmbedding F D := incl bot_le
  let d : MackeyDiagrams.ConjEmbedding C G := incl bot_le
  let e : MackeyDiagrams.ConjEmbedding E C := incl le_rfl
  let f : MackeyDiagrams.ConjEmbedding E F := incl le_rfl
  let u : MackeyDiagrams.ConjEmbedding B' A := incl bot_le
  let v : MackeyDiagrams.ConjEmbedding C B' := incl le_rfl
  let w : MackeyDiagrams.ConjEmbedding F B' := incl le_rfl
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
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
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let terms := fun {X : Type} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let Qstar := fun (p : ProjectionLabel a bc de f) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
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
  let right := fun
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
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
  let IsLeftWith := fun (allowed : Set A) (drawing : Drawing) =>
    ∃ (B : Subgroup U) (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de),
      (∀ x ∈ Finsupp.support xs,
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot x) ∈ allowed) ∧
      drawing = left r s t xs ys zs
  let leftShape := MackeyDiagrams.LabelledDrawing.planarShape
    (left (B := T) d (incl bot_le) (incl le_rfl) 0 0 0)
  let sumDrawings := fun (drawings : List Drawing) =>
    match drawings with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let basisVector := fun p : A =>
    Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc p) (1 : Complex)
  let line := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
  let swapCoset := DoubleCoset.doubleCoset τ (line : Set A) (line : Set A)
  let intersection := fun x : A => line ⊓
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) line
  Subgroup.index (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom v)) = 1 ∧
  Subgroup.index (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom f)) = 1 ∧
  (∀ x : A, (x ∈ line → intersection x = line) ∧
    (x ∈ swapCoset → intersection x = ⊥)) ∧
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D)
      (x : MackeyDiagrams.Dot (comp a r) (comp b s)),
      MackeyDiagrams.Dot.element x ∈ swapCoset →
      B = ⊥ ∧ ∀ y : MackeyDiagrams.Dot (comp a r) (comp b s),
        MackeyDiagrams.Dot.element y ∈ line →
        ¬ Set.Finite {j | MackeyDiagrams.Generator.mixedMultiplicationBasis a b r s y j =
          MackeyDiagrams.Generator.mixedPair a b (MackeyDiagrams.Dot.element y)}) ∧
  ∃ (ell : MackeyDiagrams.Dot bc (comp u w))
    (m₁ mτ : ProjectionLabel a u d v) (n : ProjectionLabel v w e f)
    (p₁ pτ : ProjectionLabel a bc de f),
    MackeyDiagrams.Dot.element ell = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m₁) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot mτ) = τ ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot n) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p₁) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot pτ) = τ ∧
    let rhs := right (Finsupp.single ell 1) (Finsupp.single m₁ 1 + Finsupp.single mτ 1)
      (Finsupp.single n 1)
    eval rhs = Qstar p₁ + Qstar pτ ∧
    eval rhs (basisVector 1) ≠ 0 ∧
    eval rhs (basisVector τ) ≠ 0 ∧
    (∀ (allowed : Set A) (drawings : List Drawing),
      (∀ drawing ∈ drawings, IsLeftWith allowed drawing) →
      eval (sumDrawings drawings) = eval rhs →
      (∃ x ∈ allowed, x ∈ line) ∧ (∃ x ∈ allowed, x ∈ swapCoset)) ∧
    (∃ l₁ lτ, IsLeftWith (line : Set A) l₁ ∧ IsLeftWith swapCoset lτ ∧
      eval l₁ = Qstar p₁ ∧ eval lτ = Qstar pτ ∧
      eval (MackeyDiagrams.LabelledDrawing.add l₁ lτ) = eval rhs) ∧
    (∀ replacement : MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex
        (MackeyDiagrams.Word.boundary bottom) (MackeyDiagrams.Word.boundary top) leftShape,
      MackeyDiagrams.ScopedDiagram.eval
        (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret replacement) ≠
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.ScopedDiagram.atBoundary
        (MackeyDiagrams.LabelledDrawing.interpret rhs)))


namespace CaseTwoAudit
open MackeyDiagrams

/-- Exact remaining connection. It identifies evaluation in the full planar fibre
with evaluation of the three typed compact stages. The Lean theorem below checks
only the assembly conditional on a proof of this proposition. -/
def CaseTwoLeftInversion : Prop :=
    ∀ replacement : LabelledDrawing.PlanarAtBoundary Complex bottom.boundary top.boundary leftShape,
      ∃ (B : Subgroup U) (r : ConjEmbedding B G) (s : ConjEmbedding B D)
        (t : ConjEmbedding T B) (xs : Finsupp (ProjectionLabel a b r s) Complex)
        (ys : Finsupp (ProjectionLabel s c t f) Complex)
        (zs : DotLabel Complex (comp r t) de),
        replacement.interpret.eval = (left r s t xs ys zs).interpret.atBoundary.eval

theorem endpoint_of_checked_inversion (normal : CaseTwoLeftInversion) :
    CaseTwoReviewedType := by
  classical
  have h₁ : eval rhs (basisVector 1) ≠ 0 := by
    intro h
    have hu := congrArg (fun x => x unitOut) h
    rw [rhs_probe_one] at hu
    exact one_ne_zero hu
  have hτ : eval rhs (basisVector τ) ≠ 0 := by
    intro h
    have hu := congrArg (fun x => x unitOut) h
    rw [rhs_probe_swap] at hu
    exact one_ne_zero hu
  -- Xiao, Example 6.3, archived pp. 22–24 and published pp. 24–26.
  -- The portal presents the calculations in prose without separate numbered
  -- steps. Lemma 6.3 and (6.1) determine the outer parameter and the fibre
  -- index. Theorem 6.4(2) supplies two summands via their full intersections.
  -- The finite combination in Example 6.3 is a statement about evaluated
  -- maps. The list fold is used only through its linear evaluation. The
  -- middle right dot and the two specified left drawings retain their scopes.
  refine ⟨cup_indices.1, cup_indices.2, intersect_calc, ?_, first, mid 1, mid τ, last,
    overall 1, overall τ, rfl, rfl, rfl, rfl, rfl, rfl,
    right_sum, h₁, hτ, allowed_crossings, two_left_drawings, ?_⟩
  · intro B r s x hx
    have hB := forced_bot r s x hx
    refine ⟨hB, ?_⟩
    subst B
    exact unbounded_line_fiber r s
  · intro replacement hrep
    obtain ⟨B,r,s,t,xs,ys,zs,hval⟩ := normal replacement
    have h : (left r s t xs ys zs).interpret.eval = rhs.interpret.eval :=
      (ScopedDiagram.eval_atBoundary_eq_iff _ _).mp (hval.symm.trans hrep)
    have hh : eval (left r s t xs ys zs) = eval rhs := by
      change (splitBottom.interpret.eval.vertical
          ((left r s t xs ys zs).interpret.eval.vertical mergeTop.interpret.eval)).toLinearMap =
        (splitBottom.interpret.eval.vertical
          (rhs.interpret.eval.vertical mergeTop.interpret.eval)).toLinearMap
      rw [h]
    exact canonical_ne r s t xs ys zs hh

end CaseTwoAudit

#print axioms CaseTwoAudit.endpoint_of_checked_inversion
