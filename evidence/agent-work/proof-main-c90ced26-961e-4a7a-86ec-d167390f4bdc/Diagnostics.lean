import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention

set_option maxHeartbeats 200000

namespace CaseSixRightShapeEvaluationAux

open MackeyDiagrams
open scoped BigOperators

private noncomputable def weighted {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} {ι : Type*} (I : Finset ι) (weight : ι → Complex)
    (term : ι → Diagram Complex p q) : ScopedDiagram Complex p q :=
  .linearCombination (I.toList.map fun i => (weight i, .ordinary (term i)))

private theorem weighted_apply {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} {ι : Type*} (I : Finset ι) (weight : ι → Complex)
    (term : ι → Diagram Complex p q) (z : p.basis.carrier →₀ Complex) :
    (weighted I weight term).eval.toLinearMap z =
      ∑ i ∈ I, weight i • (term i).eval.toLinearMap z := by
  rw [weighted, ScopedDiagram.eval_linearCombination_apply, List.map_map]
  exact Finset.sum_map_toList I _

private theorem frameLeft {U : Type*} [Group U] {K H J : Subgroup U}
    (p : Word K H) {q q' : Word H J} {ι : Type*}
    (I : Finset ι) (weight : ι → Complex) (term : ι → Diagram Complex q q') :
    ((Biset.Hom.id p.basis).horizontal (weighted I weight term).eval).toLinearMap =
      ∑ i ∈ I, weight i • ((Biset.Hom.id p.basis).horizontal (term i).eval).toLinearMap := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((Biset.Hom.id p.basis).horizontal (weighted I weight term).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) =
    (∑ i ∈ I, weight i • ((Biset.Hom.id p.basis).horizontal (term i).eval).toLinearMap)
      (Finsupp.single (p.basis.pair q.basis x y) r)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Biset.Hom.horizontal_single,
    weighted_apply, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, mul_comm r (weight i)]

private theorem frameRight {U : Type*} [Group U] {K H J : Subgroup U}
    {p p' : Word K H} (q : Word H J) {ι : Type*}
    (I : Finset ι) (weight : ι → Complex) (term : ι → Diagram Complex p p') :
    ((weighted I weight term).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap =
      ∑ i ∈ I, weight i • ((term i).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((weighted I weight term).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) =
    (∑ i ∈ I, weight i • ((term i).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap)
      (Finsupp.single (p.basis.pair q.basis x y) r)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Biset.Hom.horizontal_single,
    weighted_apply]
  let pair := (Biset.pairLinear Complex p'.basis q.basis).flip
    ((Biset.Hom.id q.basis).toLinearMap (Finsupp.single y 1))
  change r • pair (∑ i ∈ I, weight i • (term i).eval.toLinearMap (Finsupp.single x 1)) =
    ∑ i ∈ I, weight i • (r • pair ((term i).eval.toLinearMap (Finsupp.single x 1)))
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, mul_comm r (weight i)]


section
variable {U : Type*} [Group U] {G A D F C E B' : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (i : ConjEmbedding B' A) (j : ConjEmbedding B' F) (k : ConjEmbedding B' C)

private abbrev Inner := (Word.up i).tensor (.down j)
private abbrev Lower := Dot (b.comp i) (d.comp j)
private abbrev Middle := Dot (a.comp i) (c.comp k)
private abbrev Upper := Dot (e.comp k) (f.comp j)
private abbrev Bottom := (Word.up a).tensor ((Word.down b).tensor (.up d))
private abbrev Top := (Word.up c).tensor ((Word.down e).tensor (.up f))

private abbrev Fibers (r : Lower b d i j) :=
  ∀ x : D, Set.Finite {w | Generator.mixedProduct b d
    (Generator.mixedMultiplicationBasis b d i j r w) = x}

private def projectionDot (r : Lower b d i j) (hr : Fibers b d i j r) :
    ProjectionDot.Mixed b d i j :=
  ⟨r, fun z => (hr (Generator.mixedProduct b d z)).subset
    (fun _ hw => congrArg (Generator.mixedProduct b d) hw)⟩

private abbrev projection (r : ProjectionDot.Mixed b d i j) :
    Diagram Complex ((Word.down b).tensor (.up d)) (Inner i j) :=
  .mixedProjection b d i j r.dot r.finite

private abbrev parallel (t : Middle a c i k) :
    Diagram Complex ((Word.up a).tensor (.up i)) ((Word.up c).tensor (.up k)) :=
  .parallelUp a i c k t

private abbrev multiply (s : Upper e f j k) :
    Diagram Complex (Inner k j) ((Word.down e).tensor (.up f)) :=
  .mixedMultiplication e f k j s

private abbrev unassoc : Diagram Complex
    ((Word.up a).tensor (Inner i j)) (((Word.up a).tensor (.up i)).tensor (.down j)) :=
  .unassociate (.up a) (.up i) (.down j)

private abbrev assoc : Diagram Complex
    (((Word.up c).tensor (.up k)).tensor (.down j)) ((Word.up c).tensor (Inner k j)) :=
  .associate (.up c) (.up k) (.down j)

private noncomputable def drawing
    (lower : List (Complex × ProjectionDot.Mixed b d i j))
    (middle : List (Complex × Middle a c i k)) (upper : List (Complex × Upper e f j k)) :
    LabelledDrawing Complex (Bottom a b d) (Top c e f) :=
  .vertical
    (.horizontal (.ordinary (.id (.up a))) (.compactProjection b d i j lower))
    (.vertical (.ordinary (unassoc a i j))
      (.vertical (.horizontal (.parallelUp a i c k middle) (.ordinary (.id (.down j))))
        (.vertical (.ordinary (assoc c j k))
          (.horizontal (.ordinary (.id (.up c))) (.mixedMultiplication e f k j upper)))))

private noncomputable def input (g : G) (x : D) : (Bottom a b d).basis.carrier →₀ Complex :=
  Finsupp.single ((Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    g (Generator.mixedPair b d x)) 1

private noncomputable def output (t : Middle a c i k) (s : Upper e f j k)
    (g : G) (α : A) (h : F) : (Top c e f).basis.carrier →₀ Complex :=
  Finsupp.single ((Biset.induction c).pair ((Word.down e).tensor (.up f)).basis
    (g * a.toHom α * t.element) (Generator.mixedPair e f (s.element * f.toHom h))) 1

private noncomputable def column (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (Top c e f).basis.carrier →₀ Complex :=
  ∑ w ∈ (hr x).toFinset, output a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

private noncomputable def tail (t : Middle a c i k) (s : Upper e f j k) :
    Diagram Complex ((Word.up a).tensor (Inner i j)) (Top c e f) :=
  (unassoc a i j).vertical (((parallel a c i k t).horizontal (.id (.down j))).vertical
    ((assoc c j k).vertical ((Diagram.id (.up c)).horizontal (multiply e f j k s))))

private theorem tail_pair (t : Middle a c i k) (s : Upper e f j k) (g : G) (α : A) (h : F) :
    (tail a c e f i j k t s).eval.toLinearMap
      (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
        ((Biset.induction i).pair (Biset.restriction j) α h)) 1) =
    output a c e f i j k t s g α h := by
  -- Step 2 of the right-hand calculation: horizontal balancing is made explicit
  -- by reassociation. The shared merge, dot and split rules take basis vectors
  -- directly. InductionRestrictionMergesAndSplits packages these rules for
  -- chosen conjugators and group-algebra inputs.
  have hm : (parallel a c i k t).eval.toLinearMap
      (Finsupp.single ((Biset.induction a).pair (Biset.induction i) g α) 1) =
      Finsupp.single ((Biset.induction c).pair (Biset.induction k)
        (g * a.toHom α * t.element) 1) 1 := by
    change (Diagram.splitUp (R := Complex) c k).eval.toLinearMap
      ((Diagram.upDot t).eval.toLinearMap
        ((Diagram.mergeUp a i).eval.toLinearMap
          (Finsupp.single ((Biset.induction a).pair (Biset.induction i) g α) 1))) = _
    rw [Diagram.eval_mergeUp_single (R := Complex) a i g α 1,
      Diagram.eval_upDot_single (R := Complex) t (g * a.toHom α) 1,
      Diagram.eval_splitUp_single (R := Complex) c k (g * a.toHom α * t.element) 1]
  -- Step 3: the unit inserted by the split leaves just the upper dot and f(h).
  have hp : (multiply e f j k s).eval.toLinearMap
      (Finsupp.single ((Biset.induction k).pair (Biset.restriction j) (1 : C) h) 1) =
      Finsupp.single (Generator.mixedPair e f (s.element * f.toHom h)) 1 := by
    change (Generator.mixedMultiplication e f k j s Complex).toLinearMap _ = _
    rw [Generator.mixedMultiplication, Biset.Hom.ofFunction_single]
    change Finsupp.single (Generator.mixedPair e f (e.toHom 1 * s.element * f.toHom h)) 1 = _
    rw [map_one, one_mul]
  change ((Diagram.id (.up c)).horizontal (multiply e f j k s)).eval.toLinearMap
    ((assoc c j k).eval.toLinearMap
      (((parallel a c i k t).horizontal (Diagram.id (.down j))).eval.toLinearMap
        ((unassoc a i j).eval.toLinearMap
          (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
            ((Biset.induction i).pair (Biset.restriction j) α h)) 1)))) = _
  rw [Diagram.eval_unassociate_single (R := Complex) (.up a) (.up i) (.down j) g α h 1,
    Diagram.eval_horizontal_single (parallel a c i k t) (Diagram.id (.down j)),
    one_smul, Diagram.eval_id_apply, hm, Biset.pairLinear_single, one_mul,
    Diagram.eval_associate_single (R := Complex) (.up c) (.up k) (.down j),
    Diagram.eval_horizontal_single (Diagram.id (.up c)) (multiply e f j k s),
    one_smul, Diagram.eval_id_apply, hp, Biset.pairLinear_single, one_mul]
  rfl

private theorem projectionColumn (r : Lower b d i j) (hr : Fibers b d i j r) (x : D) :
    (projection b d i j (projectionDot b d i j r hr)).eval.toLinearMap
      (Finsupp.single (Generator.mixedPair b d x) 1) =
    ∑ w ∈ (hr x).toFinset, Finsupp.single w 1 := by
  -- Step 1: use the transfer column of Proposition 5.1 with the given finite
  -- group fiber. Use its basis supplier directly because the registered
  -- convention packages the trace and shape results together with the column.
  let dot := projectionDot b d i j r hr
  have hf : (dot.finite (Generator.mixedPair b d x)).toFinset = (hr x).toFinset := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    change Generator.mixedMultiplicationBasis b d i j r w = Generator.mixedPair b d x ↔
      Generator.mixedProduct b d (Generator.mixedMultiplicationBasis b d i j r w) = x
    constructor
    · intro hw
      rw [hw, Generator.mixedProduct_mixedPair]
    · intro hw
      apply (Generator.mixedEquiv b d).injective
      exact hw.trans (Generator.mixedProduct_mixedPair b d x).symm
  change (Generator.mixedProjection b d i j dot.dot Complex dot.finite).toLinearMap
    (Finsupp.single (Generator.mixedPair b d x) 1) = _
  rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul,
    Biset.Hom.transferBasis_sum, hf]

private theorem oneTerm (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (tail a c e f i j k t s).eval.toLinearMap
      (((Diagram.id (.up a)).horizontal (projection b d i j (projectionDot b d i j r hr))).eval.toLinearMap
        (input a b d g x)) =
    column a b d c e f i j k r hr t s g x := by
  trace "oneTerm entered"
  rw [input, Diagram.eval_horizontal_single (Diagram.id (.up a))
    (projection b d i j (projectionDot b d i j r hr)),
    one_smul, Diagram.eval_id_apply, projectionColumn b d i j r hr x, map_sum, map_sum]
  trace "expanded projection"
  unfold column
  apply Finset.sum_congr rfl
  intro w _
  rw [Biset.pairLinear_single, one_mul]
  have hw : (Biset.induction i).pair (Biset.restriction j) (Quotient.out w).1 (Quotient.out w).2 = w :=
    Quotient.out_eq' w
  trace "quotient representative checked"
  exact hw ▸ tail_pair a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

private theorem drawingVertical {U : Type*} [Group U] {K H : Subgroup U}
    {p q z : Word K H} (lower : LabelledDrawing Complex p q)
    (upper : LabelledDrawing Complex q z) (v : p.basis.carrier →₀ Complex) :
    (lower.vertical upper).interpret.eval.toLinearMap v =
      upper.interpret.eval.toLinearMap (lower.interpret.eval.toLinearMap v) := rfl

private theorem drawingHorizontal {U : Type*} [Group U] {K H J : Subgroup U}
    {p p' : Word K H} {q q' : Word H J} (left : LabelledDrawing Complex p p')
    (right : LabelledDrawing Complex q q') :
    (left.horizontal right).interpret.eval = left.interpret.eval.horizontal right.interpret.eval := rfl

private theorem drawingOrdinary {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} (diagram : Diagram Complex p q) :
    (LabelledDrawing.ordinary diagram).interpret.eval = diagram.eval := rfl

private theorem projectionWeighted {ι : Type*} (I : Finset ι) (weight : ι → Complex)
    (term : ι → ProjectionDot.Mixed b d i j) :
    (LabelledDrawing.compactProjection b d i j
      (I.toList.map fun u => (weight u, term u))).interpret =
      weighted I weight (fun u => projection b d i j (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem parallelWeighted {ι : Type*} (I : Finset ι) (weight : ι → Complex)
    (term : ι → Middle a c i k) :
    (LabelledDrawing.parallelUp a i c k (I.toList.map fun u => (weight u, term u))).interpret =
      weighted I weight (fun u => parallel a c i k (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem multiplyWeighted {ι : Type*} (I : Finset ι) (weight : ι → Complex)
    (term : ι → Upper e f j k) :
    (LabelledDrawing.mixedMultiplication e f k j (I.toList.map fun u => (weight u, term u))).interpret =
      weighted I weight (fun u => multiply e f j k (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem weightedCase {ι₁ ι₂ ι₃ : Type*}
    (I : Finset ι₁) (J : Finset ι₂) (K : Finset ι₃)
    (l : ι₁ → Complex) (m : ι₂ → Complex) (n : ι₃ → Complex)
    (r : ι₁ → Lower b d i j) (hr : ∀ u, Fibers b d i j (r u))
    (t : ι₂ → Middle a c i k) (s : ι₃ → Upper e f j k) (g : G) (x : D) :
    (drawing a b d c e f i j k
      (I.toList.map fun u => (l u, projectionDot b d i j (r u) (hr u)))
      (J.toList.map fun v => (m v, t v)) (K.toList.map fun w => (n w, s w))).interpret.eval.toLinearMap
        (input a b d g x) =
    ∑ u ∈ I, ∑ v ∈ J, ∑ w ∈ K,
      (l u * m v * n w) • column a b d c e f i j k (r u) (hr u) (t v) (s w) g x := by
  -- Step 4: linearity on the three supported labels. Use Finset-indexed sums
  -- through the shared, genuinely horizontal frames, then multiply the weights.
  simp only [drawing, drawingVertical, drawingHorizontal, drawingOrdinary,
    projectionWeighted, parallelWeighted, multiplyWeighted]
  trace_state
  done
end
end CaseSixRightShapeEvaluationAux
