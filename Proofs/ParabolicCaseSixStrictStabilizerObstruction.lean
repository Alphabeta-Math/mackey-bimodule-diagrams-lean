import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.SupportedLeftOrbitProjectedStabilizer
import Proofs.ParabolicRightOrbitMultiplicity

set_option maxHeartbeats 2000000

open MackeyDiagrams

namespace CaseSixStrictAux

universe u

-- A weighted mark, framed on either side by a fixed diagram, evaluates
-- termwise. These two identities work on all balanced basis classes.
private theorem frameRight {U : Type u} [Group U] {K H J : Subgroup U}
    {p q : Word K H} {v w : Word H J}
    (right : Biset.Hom Complex v.basis w.basis)
    (terms : List (Complex × ScopedDiagram Complex p q)) :
    ((ScopedDiagram.linearCombination terms).eval.horizontal right).toLinearMap =
      (terms.map fun (c, d) => c • (d.eval.horizontal right).toLinearMap).sum := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z fun ⟨x, y⟩ => ?_
  change ((ScopedDiagram.linearCombination terms).eval.horizontal right).toLinearMap
    (Finsupp.single (p.basis.pair v.basis x y) r) = _
  rw [Biset.Hom.horizontal_single, ScopedDiagram.eval_linearCombination_apply]
  let frame := (Biset.pairLinear Complex q.basis w.basis).flip
    (right.toLinearMap (Finsupp.single y 1))
  change r • frame ((terms.map fun term => term.1 • term.2.eval.toLinearMap
      (Finsupp.single x 1)).sum) =
    (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))
      ((terms.map fun (c, d) => c • (d.eval.horizontal right).toLinearMap).sum)
  rw [map_list_sum frame, List.smul_sum,
    map_list_sum (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c, d⟩ _
  change r • frame (c • d.eval.toLinearMap (Finsupp.single x 1)) =
    c • (d.eval.horizontal right).toLinearMap (Finsupp.single (p.basis.pair v.basis x y) r)
  rw [map_smul, Biset.Hom.horizontal_single]
  exact smul_comm r c _

private theorem frameLeft {U : Type u} [Group U] {K H J : Subgroup U}
    {p q : Word K H} {v w : Word H J}
    (left : Biset.Hom Complex p.basis q.basis)
    (terms : List (Complex × ScopedDiagram Complex v w)) :
    (left.horizontal (ScopedDiagram.linearCombination terms).eval).toLinearMap =
      (terms.map fun (c, d) => c • (left.horizontal d.eval).toLinearMap).sum := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z fun ⟨x, y⟩ => ?_
  change (left.horizontal (ScopedDiagram.linearCombination terms).eval).toLinearMap
    (Finsupp.single (p.basis.pair v.basis x y) r) = _
  rw [Biset.Hom.horizontal_single, ScopedDiagram.eval_linearCombination_apply]
  let frame := Biset.pairLinear Complex q.basis w.basis (left.toLinearMap (Finsupp.single x 1))
  change r • frame ((terms.map fun term => term.1 • term.2.eval.toLinearMap
      (Finsupp.single y 1)).sum) =
    (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))
      ((terms.map fun (c, d) => c • (left.horizontal d.eval).toLinearMap).sum)
  rw [map_list_sum frame, List.smul_sum,
    map_list_sum (LinearMap.applyₗ (R := Complex) (Finsupp.single (p.basis.pair v.basis x y) r))]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c, d⟩ _
  change r • frame (c • d.eval.toLinearMap (Finsupp.single y 1)) =
    c • (left.horizontal d.eval).toLinearMap (Finsupp.single (p.basis.pair v.basis x y) r)
  rw [map_smul, Biset.Hom.horizontal_single]
  exact smul_comm r c _

-- Apply linearity to a weighted list of linear maps with a fixed input and
-- an arbitrary downstream linear functional. This also covers the empty list.
private theorem list_apply_zero {D M N : Type*}
    [AddCommMonoid M] [Module Complex M] [AddCommMonoid N] [Module Complex N]
    (terms : List (Complex × D)) (eval : D → M →ₗ[Complex] N)
    (x : M) (measure : N →ₗ[Complex] Complex)
    (zero : ∀ d : D, measure (eval d x) = 0) :
    measure (((terms.map fun term => term.1 • eval term.2).sum) x) = 0 := by
  induction terms with
  | nil => simp
  | cons d terms ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, zero, ih, smul_zero, add_zero]

private theorem stack_apply_zero {L M N V W X Y : Type*}
    [AddCommMonoid V] [Module Complex V] [AddCommMonoid W] [Module Complex W]
    [AddCommMonoid X] [Module Complex X] [AddCommMonoid Y] [Module Complex Y]
    (rs : List (Complex × L)) (ts : List (Complex × M)) (ss : List (Complex × N))
    (lower : L → V →ₗ[Complex] W) (middle : M → W →ₗ[Complex] X)
    (upper : N → X →ₗ[Complex] Y) (input : V) (measure : Y →ₗ[Complex] Complex)
    (zero : ∀ r t s, measure (upper s (middle t (lower r input))) = 0) :
    measure ((ss.map fun term => term.1 • upper term.2).sum
      ((ts.map fun term => term.1 • middle term.2).sum
        ((rs.map fun term => term.1 • lower term.2).sum input))) = 0 := by
  let mid := (ts.map fun term => term.1 • middle term.2).sum
  let top := (ss.map fun term => term.1 • upper term.2).sum
  change ((measure.comp top).comp mid) ((rs.map fun term => term.1 • lower term.2).sum input) = 0
  apply list_apply_zero rs lower input
  intro r
  change (measure.comp top) (mid (lower r input)) = 0
  apply list_apply_zero ts middle (lower r input)
  intro t
  change measure (top (middle t (lower r input))) = 0
  exact list_apply_zero ss upper _ measure (zero r t)

private theorem compose_weighted_list {V W X : Type*} [AddCommMonoid V] [Module Complex V]
    [AddCommMonoid W] [Module Complex W] [AddCommMonoid X] [Module Complex X]
    {D : Type*} (terms : List (Complex × D)) (after : W →ₗ[Complex] X)
    (stage : D → V →ₗ[Complex] W) (col : V) :
    after ((terms.map fun d => d.1 • stage d.2).sum col) =
      (terms.map fun d => d.1 • after.comp (stage d.2)).sum col := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, LinearMap.comp_apply, ih]

section LeftDrawing

variable {U : Type u} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (u : ConjEmbedding G B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)

private abbrev leftDrawing (rs : List (Complex × Dot (u.comp a) (v.comp b)))
    (ts : List (Complex × Dot (v.comp d) (w.comp f)))
    (ss : List (Complex × ProjectionDot.Mixed u w c e)) :
    LabelledDrawing Complex ((Word.up a).tensor ((Word.down b).tensor (.up d)))
      ((Word.up c).tensor ((Word.down e).tensor (.up f))) :=
  .vertical (.ordinary (.unassociate (.up a) (.down b) (.up d)))
    (.vertical (.horizontal (.mixedMultiplication u v a b rs) (.ordinary (.id (.up d))))
      (.vertical (.ordinary (.associate (.down u) (.up v) (.up d)))
        (.vertical (.horizontal (.ordinary (.id (.down u))) (.parallelUp v d w f ts))
          (.vertical (.ordinary (.unassociate (.down u) (.up w) (.up f)))
            (.vertical (.horizontal (.compactProjection u w c e ss) (.ordinary (.id (.up f))))
              (.ordinary (.associate (.up c) (.down e) (.up f))))))))

private noncomputable abbrev evaluate {K H : Subgroup U} {p q : Word K H}
    (drawing : LabelledDrawing Complex p q) := drawing.interpret.eval.toLinearMap

private theorem left_apply_zero
    (rs : List (Complex × Dot (u.comp a) (v.comp b)))
    (ts : List (Complex × Dot (v.comp d) (w.comp f)))
    (ss : List (Complex × ProjectionDot.Mixed u w c e))
    (x : ((Word.up a).tensor ((Word.down b).tensor (.up d))).basis.carrier →₀ Complex)
    (y : ((Word.up c).tensor ((Word.down e).tensor (.up f))).basis.carrier)
    (zero : ∀ r t s, evaluate (leftDrawing a b d c e f u v w [(1, r)] [(1, t)] [(1, s)]) x y = 0) :
    evaluate (leftDrawing a b d c e f u v w rs ts ss) x y = 0 := by
  let pre := (Diagram.unassociate (R := Complex) (.up a) (.down b) (.up d)).eval.toLinearMap
  let reassoc := (Diagram.associate (R := Complex) (.down u) (.up v) (.up d)).eval.toLinearMap
  let unassoc := (Diagram.unassociate (R := Complex) (.down u) (.up w) (.up f)).eval.toLinearMap
  let post := (Finsupp.lapply (R := Complex) y).comp
    (Diagram.associate (R := Complex) (.up c) (.down e) (.up f)).eval.toLinearMap
  let idD := (Diagram.id (R := Complex) (.up d)).eval
  let idU := (Diagram.id (R := Complex) (.down u)).eval
  let idF := (Diagram.id (R := Complex) (.up f)).eval
  let lower (r : Dot (u.comp a) (v.comp b)) : ScopedDiagram Complex _ _ :=
    .ordinary (.mixedMultiplication u v a b r)
  let middle (t : Dot (v.comp d) (w.comp f)) : ScopedDiagram Complex _ _ :=
    .ordinary (.parallelUp v d w f t)
  let upper (s : ProjectionDot.Mixed u w c e) : ScopedDiagram Complex _ _ :=
    .ordinary (.mixedProjection u w c e s.dot s.finite)
  have expansion (rs : List (Complex × Dot (u.comp a) (v.comp b)))
      (ts : List (Complex × Dot (v.comp d) (w.comp f)))
      (ss : List (Complex × ProjectionDot.Mixed u w c e)) :
      evaluate (leftDrawing a b d c e f u v w rs ts ss) x y =
        post ((ss.map fun s => s.1 • ((upper s.2).eval.horizontal idF).toLinearMap).sum
          ((ts.map fun t => t.1 • unassoc.comp (idU.horizontal (middle t.2).eval).toLinearMap).sum
            ((rs.map fun r => r.1 • reassoc.comp ((lower r.2).eval.horizontal idD).toLinearMap).sum
              (pre x)))) := by
    change post (((ScopedDiagram.linearCombination (ss.map fun s => (s.1, upper s.2))).eval.horizontal
      idF).toLinearMap (unassoc ((idU.horizontal
        (ScopedDiagram.linearCombination (ts.map fun t => (t.1, middle t.2))).eval).toLinearMap
        (reassoc (((ScopedDiagram.linearCombination (rs.map fun r => (r.1, lower r.2))).eval.horizontal
          idD).toLinearMap (pre x)))))) = _
    rw [frameRight, frameLeft, frameRight]
    simp only [List.map_map]
    change post ((ss.map fun s => s.1 • ((upper s.2).eval.horizontal idF).toLinearMap).sum
      (unassoc ((ts.map fun t => t.1 • (idU.horizontal (middle t.2).eval).toLinearMap).sum
        (reassoc ((rs.map fun r => r.1 • ((lower r.2).eval.horizontal idD).toLinearMap).sum
          (pre x)))))) = _
    rw [compose_weighted_list rs reassoc (fun r => ((lower r).eval.horizontal idD).toLinearMap) (pre x),
      compose_weighted_list ts unassoc (fun t => (idU.horizontal (middle t).eval).toLinearMap)]
  rw [expansion]
  refine stack_apply_zero rs ts ss
    (fun r => reassoc.comp ((lower r).eval.horizontal idD).toLinearMap)
    (fun t => unassoc.comp (idU.horizontal (middle t).eval).toLinearMap)
    (fun s => ((upper s).eval.horizontal idF).toLinearMap) (pre x) post ?_
  intro r t s
  simpa only [expansion, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_smul, add_zero] using zero r t s

end LeftDrawing

end CaseSixStrictAux


theorem ParabolicCaseSixStrictStabilizerObstruction : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (S : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
∀ {G A D F C E : Subgroup U},
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  ∀ (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
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
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis ga)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis gc)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  letI : MulAction (G × F) X.carrier :=
    { smul := MackeyDiagrams.Biset.act X
      one_smul := MackeyDiagrams.Biset.one_act X
      mul_smul := MackeyDiagrams.Biset.mul_act X }
  letI : MulAction (G × F) Y.carrier :=
    { smul := MackeyDiagrams.Biset.act Y
      one_smul := MackeyDiagrams.Biset.one_act Y
      mul_smul := MackeyDiagrams.Biset.mul_act Y }
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let project := Subgroup.map (MonoidHom.snd G F)
  let projectedPair := fun z : Pair => project (MulAction.stabilizer (G × F) z)
  let projectedSource := fun x : X.carrier => project (MulAction.stabilizer (G × F) x)
  let projectedTarget := fun y : Y.carrier => project (MulAction.stabilizer (G × F) y)
  let MatrixMap := (X.carrier →₀ Complex) →ₗ[Complex] (Y.carrier →₀ Complex)
  let coefficient := fun (M : MatrixMap) (z : Pair) =>
    M (Finsupp.single z.1 (1 : Complex)) z.2
  let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap
      (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
  let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let ProjectionLabel := fun {K L M H : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K M) (β : MackeyDiagrams.ConjEmbedding L M)
      (η : MackeyDiagrams.ConjEmbedding H K) (θ : MackeyDiagrams.ConjEmbedding H L) =>
    List (Complex × MackeyDiagrams.ProjectionDot.Mixed α β η θ)
  let LeftData :=
    Σ (B : Subgroup U) (u : MackeyDiagrams.ConjEmbedding G B)
      (v : MackeyDiagrams.ConjEmbedding D B) (w : MackeyDiagrams.ConjEmbedding E B),
      MackeyDiagrams.DotLabel Complex (comp u a) (comp v b) ×
      MackeyDiagrams.DotLabel Complex (comp v d) (comp w f) ×
      ProjectionLabel u w c e
  let leftDrawing : LeftData → MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨_, u, v, w, r, t, s⟩ =>
      let du := down u
      let uv := up v
      let uw := up w
      let lower := MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b
        (MackeyDiagrams.DotLabel.terms r)
      let middle := MackeyDiagrams.LabelledDrawing.parallelUp v d w f
        (MackeyDiagrams.DotLabel.terms t)
      let upper := MackeyDiagrams.LabelledDrawing.compactProjection u w c e s
      stack (ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
        (stack (juxtapose lower (ordinary (MackeyDiagrams.Diagram.id df)))
          (stack (ordinary (MackeyDiagrams.Diagram.associate du uv df))
            (stack (juxtapose (ordinary (MackeyDiagrams.Diagram.id du)) middle)
              (stack (ordinary (MackeyDiagrams.Diagram.unassociate du uw ef))
                (stack (juxtapose upper (ordinary (MackeyDiagrams.Diagram.id ef)))
                  (ordinary (MackeyDiagrams.Diagram.associate gc ce ef)))))))
  let rightDrawing := fun {B' : Subgroup U}
      (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C) (r : ProjectionLabel b d i j)
      (t : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
      (s : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j)) =>
    let ai := up i
    let fj := down j
    let ck := up k
    let lower := MackeyDiagrams.LabelledDrawing.compactProjection b d i j r
    let middle := MackeyDiagrams.LabelledDrawing.parallelUp a i c k
      (MackeyDiagrams.DotLabel.terms t)
    let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j
      (MackeyDiagrams.DotLabel.terms s)
    stack (juxtapose (ordinary (MackeyDiagrams.Diagram.id ga)) lower)
      (stack (ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
        (stack (juxtapose middle (ordinary (MackeyDiagrams.Diagram.id fj)))
          (stack (ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
            (juxtapose (ordinary (MackeyDiagrams.Diagram.id gc)) upper))))
  ∀ {B₀ : Subgroup U}, parabolic B₀ →
  ∀ (i₀ : MackeyDiagrams.ConjEmbedding B₀ A) (j₀ : MackeyDiagrams.ConjEmbedding B₀ F)
    (k₀ : MackeyDiagrams.ConjEmbedding B₀ C) (r₀ : MackeyDiagrams.ProjectionDot.Mixed b d i₀ j₀)
    (t₀ : MackeyDiagrams.Dot (comp a i₀) (comp c k₀))
    (s₀ : MackeyDiagrams.Dot (comp e k₀) (comp f j₀)),
  let z : Pair := (input 1 (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot r₀)),
    output (MackeyDiagrams.Dot.element t₀) (MackeyDiagrams.Dot.element s₀))
  let orbit := MulAction.orbit (G × F) z
  let orbitCoefficient := fun p : Pair =>
    @ite Complex (p ∈ orbit) (Classical.propDecidable (p ∈ orbit)) 1 0
  projectedPair z < projectedSource z.1 ⊓ projectedTarget z.2 →
  ∀ (N : Nat) (terms : Fin N → LeftData) (weights : Fin N → Complex),
    (∀ ν, parabolic (terms ν).1) →
    let leftSum : MackeyDiagrams.IndexedDrawing Complex bottom top (Fin N) :=
      ⟨Finset.univ, fun ν => MackeyDiagrams.LabelledDrawing.scale (weights ν) (leftDrawing (terms ν))⟩
    (¬ ∀ p : Pair, coefficient (MackeyDiagrams.IndexedDrawing.eval leftSum) p = orbitCoefficient p) ∧
    (∀ {B' : Subgroup U}, parabolic B' →
      ∀ (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
        (k : MackeyDiagrams.ConjEmbedding B' C) (r : ProjectionLabel b d i j)
        (t : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
        (s : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j)),
      let rightMap := evaluate (rightDrawing i j k r t s)
      coefficient rightMap z ≠ 0 →
      rightMap ≠ MackeyDiagrams.IndexedDrawing.eval leftSum)
) :=
(by
  classical
  intro finitary U blockSym parabolic G A D F C E hG hA hD hF hC hE
    a b d c e f up down tensor comp ga ad df gc ce ef bottom top X Y Pair input output
    project projectedPair projectedSource projectedTarget MatrixMap
    coefficient evaluate ordinary stack juxtapose ProjectionLabel LeftData leftDrawing rightDrawing
    B₀ hB₀ i₀ j₀ k₀ r₀ t₀ s₀ z orbit orbitCoefficient hstrict N terms weights hterms leftSum
  -- Xiao, Proposition 8.8, first assertion and first diagram
  -- (archived original p. 41 and revised published PDF p. 43).
  -- The online proof has one paragraph for this assertion, without numbered steps.
  -- Step 1 follows its invocation of Proposition 8.7 through the registered
  -- SupportedLeftOrbitProjectedStabilizer theorem. All seven groups are
  -- parabolic. Its upper projection certificate agrees by proof irrelevance
  -- with the one carried by each eligible projection term.
  have vanishes (n : Fin N) :
      coefficient (evaluate (leftDrawing (terms n))) z = 0 := by
    have hB := hterms n
    revert hB
    generalize terms n = term
    rcases term with ⟨B, u, v, w, rs, ts, ss⟩
    intro hB
    -- Step 2 follows the linear-label paragraph after Proposition 8.7
    -- and expands all three marks in the shared evaluator. This handles the supplied projection list directly,
    -- including repeated terms and their individual finite-fiber witnesses.
    -- EvaluationWithOneProjection gives a fiber formula on left-associated
    -- columns, with its weighted projection list built from a Finsupp.
    -- The local expansion instead preserves the actual list and outer
    -- associators. The singleton coefficient calculation is already proved
    -- in SupportedLeftOrbitProjectedStabilizer.
    apply CaseSixStrictAux.left_apply_zero a b d c e f u v w
      (DotLabel.terms rs) (DotLabel.terms ts) ss (Finsupp.single z.1 1) z.2
    intro r t s
    rcases SupportedLeftOrbitProjectedStabilizer hG hA hD hF hC hE hB
      a b d c e f u v w r t s.dot with
      ⟨finite, source, target, hsource, htarget, hsourceAct, htargetAct, hsupport, hstabilizer, _⟩
    by_contra hnonzero
    have heq : projectedPair z = projectedSource z.1 ⊓ projectedTarget z.2 :=
      (hstabilizer z hnonzero).1
    exact (ne_of_lt hstrict) heq
  -- Step 3 uses the actual indexed drawing evaluation. The right
  -- orbit indicator has coefficient one at its representative. For an
  -- arbitrary right drawing the nonzero coefficient is a hypothesis.
  -- ParabolicRightOrbitMultiplicity computes and normalizes singleton
  -- right terms separately.
  have hsum : coefficient (IndexedDrawing.eval leftSum) z = 0 := by
    change (IndexedDrawing.eval leftSum (Finsupp.single z.1 1)) z.2 = 0
    rw [IndexedDrawing.eval_apply, Finset.sum_apply']
    apply Finset.sum_eq_zero
    intro n hn
    change (weights n • evaluate (leftDrawing (terms n)) (Finsupp.single z.1 1)) z.2 = 0
    rw [Finsupp.smul_apply]
    change weights n • coefficient (evaluate (leftDrawing (terms n))) z = 0
    rw [vanishes, smul_zero]
  constructor
  · intro hall
    have hz : z ∈ orbit := ⟨1, Prod.ext (Biset.one_act X z.1) (Biset.one_act Y z.2)⟩
    have hone : orbitCoefficient z = 1 := ite_eq_left hz
    have h := hall z
    rw [hsum, hone] at h
    exact zero_ne_one h
  · intro B' hB' i j k r t s rightMap hnonzero heq
    apply hnonzero
    rw [heq, hsum]
)
