import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention

set_option maxHeartbeats 2000000

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
  -- group fiber. The registered MixedCrossingFiniteFiberConvention packages
  -- trace and shape results with the column. Here transferBasis_sum and
  -- mixedEquiv identify the two fibers directly at the specified input.
  let dot := projectionDot b d i j r hr
  have hf : (dot.finite (Generator.mixedPair b d x)).toFinset = (hr x).toFinset := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
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
  rw [input, Diagram.eval_horizontal_single (Diagram.id (.up a))
    (projection b d i j (projectionDot b d i j r hr)),
    one_smul, Diagram.eval_id_apply, projectionColumn b d i j r hr x, map_sum, map_sum]
  unfold column
  apply Finset.sum_congr rfl
  intro w _
  rw [Biset.pairLinear_single, one_mul]
  have hw : (Biset.induction i).pair (Biset.restriction j) (Quotient.out w).1 (Quotient.out w).2 = w :=
    Quotient.out_eq' w
  calc
    _ = (tail a c e f i j k t s).eval.toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
          ((Biset.induction i).pair (Biset.restriction j) (Quotient.out w).1 (Quotient.out w).2)) 1) :=
      congrArg (fun v => (tail a c e f i j k t s).eval.toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g v) 1)) hw.symm
    _ = _ := tail_pair a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

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
  let project u := projectionDot b d i j (r u) (hr u)
  let D₁ := LabelledDrawing.compactProjection b d i j (I.toList.map fun u => (l u, project u))
  let D₂ := LabelledDrawing.parallelUp a i c k (J.toList.map fun v => (m v, t v))
  let D₃ := LabelledDrawing.mixedMultiplication e f k j (K.toList.map fun w => (n w, s w))
  change ((Biset.Hom.id (Word.up c).basis).horizontal D₃.interpret.eval).toLinearMap
    ((assoc c j k).eval.toLinearMap
      ((D₂.interpret.eval.horizontal (Biset.Hom.id (Word.down j).basis)).toLinearMap
        ((unassoc a i j).eval.toLinearMap
          (((Biset.Hom.id (Word.up a).basis).horizontal D₁.interpret.eval).toLinearMap
            (input a b d g x))))) = _
  have h₁ : D₁.interpret = weighted I l (fun u => projection b d i j (project u)) :=
    projectionWeighted b d i j I l project
  have h₂ : D₂.interpret = weighted J m (fun v => parallel a c i k (t v)) :=
    parallelWeighted a c i k J m t
  have h₃ : D₃.interpret = weighted K n (fun w => multiply e f j k (s w)) :=
    multiplyWeighted e f j k K n s
  rw [h₁, h₂, h₃]
  rw [frameLeft, frameRight, frameLeft]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  exact congrArg ((l u * m v * n w) • ·) (oneTerm a b d c e f i j k (r u) (hr u) (t v) (s w) g x)

end
end CaseSixRightShapeEvaluationAux

theorem CaseSixRightShapeEvaluation : (
∀ {U : Type*} [Group U] (G A D F C E B' : Subgroup U)
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E)
    (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
    (k : MackeyDiagrams.ConjEmbedding B' C),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let ga := up a
  let ad := down b
  let df := up d
  let ai := up i
  let fj := down j
  let gc := up c
  let ck := up k
  let ce := down e
  let ef := up f
  let bottom := tensor ga (tensor ad df)
  let top := tensor gc (tensor ce ef)
  let LowerDot := MackeyDiagrams.Dot (comp b i) (comp d j)
  let MiddleDot := MackeyDiagrams.Dot (comp a i) (comp c k)
  let UpperDot := MackeyDiagrams.Dot (comp e k) (comp f j)
  let FiberWord := tensor ai fj
  let q := fun (r : LowerDot) (w : (MackeyDiagrams.Word.basis FiberWord).carrier) =>
    MackeyDiagrams.Generator.mixedProduct b d
      (MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r w)
  let finiteFibers := fun (r : LowerDot) => ∀ x : D, Set.Finite {w | q r w = x}
  let projectionTerm := fun (r : LowerDot) (hr : finiteFibers r) =>
    (⟨r, fun z => Set.Finite.subset (hr (MackeyDiagrams.Generator.mixedProduct b d z))
      (fun _ hw => congrArg (MackeyDiagrams.Generator.mixedProduct b d) hw)⟩ :
        MackeyDiagrams.ProjectionDot.Mixed b d i j)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let rightDrawing := fun
      (lower : List (Complex × MackeyDiagrams.ProjectionDot.Mixed b d i j))
      (middle : List (Complex × MiddleDot)) (upper : List (Complex × UpperDot)) =>
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
  let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top)
      (g : G) (x : D) =>
    MackeyDiagrams.Biset.Hom.toLinearMap
      (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
      (Finsupp.single
        (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
          (MackeyDiagrams.Word.basis (tensor ad df)) g
          (MackeyDiagrams.Generator.mixedPair b d x)) 1)
  let formula := fun (r : LowerDot) (hr : finiteFibers r)
      (t : MiddleDot) (s : UpperDot) (g : G) (x : D) =>
    Finset.sum (Set.Finite.toFinset (hr x)) (fun w =>
      let representative : A × F := Quotient.out w
      Finsupp.single
        (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
          (MackeyDiagrams.Word.basis (tensor ce ef))
          (g * MackeyDiagrams.ConjEmbedding.toHom a representative.1 *
            MackeyDiagrams.Dot.element t)
          (MackeyDiagrams.Generator.mixedPair e f
            (MackeyDiagrams.Dot.element s *
              MackeyDiagrams.ConjEmbedding.toHom f representative.2))) (1 : Complex))
  (∀ (r : LowerDot) (hr : finiteFibers r) (t : MiddleDot) (s : UpperDot) (g : G) (x : D),
    evaluate (rightDrawing [(1, projectionTerm r hr)] [(1, t)] [(1, s)]) g x =
      formula r hr t s g x) ∧
  (∀ (R : MackeyDiagrams.DotLabel Complex (comp b i) (comp d j))
      (T : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
      (S : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j))
      (hR : ∀ r ∈ Finsupp.support R, finiteFibers r) (g : G) (x : D),
    let lowerSupport := Finset.attach (Finsupp.support R)
    let lowerTerms := List.map (fun r : {r // r ∈ Finsupp.support R} =>
      (R r.val, projectionTerm r.val (hR r.val r.property))) (Finset.toList lowerSupport)
    evaluate (rightDrawing lowerTerms (MackeyDiagrams.DotLabel.terms T)
      (MackeyDiagrams.DotLabel.terms S)) g x =
      Finset.sum lowerSupport (fun r =>
        Finset.sum (Finsupp.support T) (fun t =>
          Finset.sum (Finsupp.support S) (fun s =>
            (R r.val * T t * S s) • formula r.val (hR r.val r.property) t s g x))))
) :=
(by
  classical
  intro U inst G A D F C E B' a b d c e f i j k up down tensor comp ga ad df ai fj
    gc ck ce ef bottom top LowerDot MiddleDot UpperDot FiberWord q finiteFibers
    projectionTerm drawId rightDrawing evaluate formula
  -- Lemma 6.6, equation (6.4). The archived PDF gives the figure and equation
  -- on p. 25 and the right-hand calculation on p. 26. The revised published
  -- PDF gives them on pp. 27 and 28 respectively. The finite-fiber convention
  -- appears on archived p. 22 and revised p. 24. The PDFs have different hashes.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- This endpoint has no linked numbered Alphabeta proof. The steps below
  -- number the article's right-hand calculation and its extension to linear labels.
  constructor
  · intro r hr t s g x
    have h := CaseSixRightShapeEvaluationAux.weightedCase a b d c e f i j k
      ({()} : Finset Unit) ({()} : Finset Unit) ({()} : Finset Unit)
      (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => r) (fun _ => hr) (fun _ => t) (fun _ => s) g x
    simp only [Finset.toList_singleton, List.map_cons, List.map_nil,
      Finset.sum_singleton, mul_one, one_smul] at h
    exact h
  · intro R T S hR g x lowerSupport lowerTerms
    exact CaseSixRightShapeEvaluationAux.weightedCase a b d c e f i j k
      lowerSupport T.support S.support (fun r => R r.val) T S
      (fun r => r.val) (fun r => hR r.val r.property) id id g x)

#print axioms CaseSixRightShapeEvaluation
