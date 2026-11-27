import MackeyDiagrams.DrawingShape
import MackeyDiagrams.MixedIdentities
import MackeyDiagrams.StructuralBasis

namespace RingRight
open MackeyDiagrams
open scoped BigOperators
variable {R : Type*} [CommRing R]

section Singleton
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
    Diagram R ((Word.down b).tensor (.up d)) (Inner i j) :=
  .mixedProjection b d i j r.dot r.finite

private abbrev parallel (t : Middle a c i k) :
    Diagram R ((Word.up a).tensor (.up i)) ((Word.up c).tensor (.up k)) :=
  .parallelUp a i c k t

private abbrev multiply (s : Upper e f j k) :
    Diagram R (Inner k j) ((Word.down e).tensor (.up f)) :=
  .mixedMultiplication e f k j s

private abbrev unassoc : Diagram R
    ((Word.up a).tensor (Inner i j)) (((Word.up a).tensor (.up i)).tensor (.down j)) :=
  .unassociate (.up a) (.up i) (.down j)

private abbrev assoc : Diagram R
    (((Word.up c).tensor (.up k)).tensor (.down j)) ((Word.up c).tensor (Inner k j)) :=
  .associate (.up c) (.up k) (.down j)

noncomputable def drawing
    (lower : List (R × ProjectionDot.Mixed b d i j))
    (middle : List (R × Middle a c i k)) (upper : List (R × Upper e f j k)) :
    LabelledDrawing R (Bottom a b d) (Top c e f) :=
  .vertical
    (.horizontal (.ordinary (.id (.up a))) (.compactProjection b d i j lower))
    (.vertical (.ordinary (unassoc (R := R) a i j))
      (.vertical (.horizontal (.parallelUp a i c k middle) (.ordinary (.id (.down j))))
        (.vertical (.ordinary (assoc (R := R) c j k))
          (.horizontal (.ordinary (.id (.up c))) (.mixedMultiplication e f k j upper)))))

private noncomputable def input (g : G) (x : D) : (Bottom a b d).basis.carrier →₀ R :=
  Finsupp.single ((Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    g (Generator.mixedPair b d x)) 1

private noncomputable def output (t : Middle a c i k) (s : Upper e f j k)
    (g : G) (α : A) (h : F) : (Top c e f).basis.carrier →₀ R :=
  Finsupp.single ((Biset.induction c).pair ((Word.down e).tensor (.up f)).basis
    (g * a.toHom α * t.element) (Generator.mixedPair e f (s.element * f.toHom h))) 1

noncomputable def column (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (Top c e f).basis.carrier →₀ R :=
  ∑ w ∈ (hr x).toFinset, output (R := R) a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

private noncomputable def tail (t : Middle a c i k) (s : Upper e f j k) :
    Diagram R ((Word.up a).tensor (Inner i j)) (Top c e f) :=
  (unassoc (R := R) a i j).vertical (((parallel (R := R) a c i k t).horizontal (.id (.down j))).vertical
    ((assoc (R := R) c j k).vertical ((Diagram.id (.up c)).horizontal (multiply (R := R) e f j k s))))

private theorem tail_pair (t : Middle a c i k) (s : Upper e f j k) (g : G) (α : A) (h : F) :
    (tail (R := R) a c e f i j k t s).eval.toLinearMap
      (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
        ((Biset.induction i).pair (Biset.restriction j) α h)) 1) =
    output (R := R) a c e f i j k t s g α h := by
  -- Step 2 of the right-hand calculation: horizontal balancing is made explicit
  -- by reassociation. The shared merge, dot and split rules take basis vectors
  -- directly. InductionRestrictionMergesAndSplits packages these rules for
  -- chosen conjugators and group-algebra inputs.
  have hm : (parallel (R := R) a c i k t).eval.toLinearMap
      (Finsupp.single ((Biset.induction a).pair (Biset.induction i) g α) 1) =
      Finsupp.single ((Biset.induction c).pair (Biset.induction k)
        (g * a.toHom α * t.element) 1) 1 := by
    change (Diagram.splitUp (R := R) c k).eval.toLinearMap
      ((Diagram.upDot t).eval.toLinearMap
        ((Diagram.mergeUp a i).eval.toLinearMap
          (Finsupp.single ((Biset.induction a).pair (Biset.induction i) g α) 1))) = _
    rw [Diagram.eval_mergeUp_single (R := R) a i g α 1,
      Diagram.eval_upDot_single (R := R) t (g * a.toHom α) 1,
      Diagram.eval_splitUp_single (R := R) c k (g * a.toHom α * t.element) 1]
  -- Step 3: the unit inserted by the split leaves just the upper dot and f(h).
  have hp : (multiply (R := R) e f j k s).eval.toLinearMap
      (Finsupp.single ((Biset.induction k).pair (Biset.restriction j) (1 : C) h) 1) =
      Finsupp.single (Generator.mixedPair e f (s.element * f.toHom h)) 1 := by
    change (Generator.mixedMultiplication e f k j s R).toLinearMap _ = _
    rw [Generator.mixedMultiplication, Biset.Hom.ofFunction_single]
    change Finsupp.single (Generator.mixedPair e f (e.toHom 1 * s.element * f.toHom h)) 1 = _
    rw [map_one, one_mul]
  change ((Diagram.id (.up c)).horizontal (multiply (R := R) e f j k s)).eval.toLinearMap
    ((assoc (R := R) c j k).eval.toLinearMap
      (((parallel (R := R) a c i k t).horizontal (Diagram.id (.down j))).eval.toLinearMap
        ((unassoc (R := R) a i j).eval.toLinearMap
          (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
            ((Biset.induction i).pair (Biset.restriction j) α h)) 1)))) = _
  rw [Diagram.eval_unassociate_single (R := R) (.up a) (.up i) (.down j) g α h 1,
    Diagram.eval_horizontal_single (parallel (R := R) a c i k t) (Diagram.id (.down j)),
    one_smul, Diagram.eval_id_apply, hm, Biset.pairLinear_single, one_mul,
    Diagram.eval_associate_single (R := R) (.up c) (.up k) (.down j),
    Diagram.eval_horizontal_single (Diagram.id (.up c)) (multiply (R := R) e f j k s),
    one_smul, Diagram.eval_id_apply, hp, Biset.pairLinear_single, one_mul]
  rfl

private theorem projectionColumn (r : Lower b d i j) (hr : Fibers b d i j r) (x : D) :
    (projection (R := R) b d i j (projectionDot b d i j r hr)).eval.toLinearMap
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
  change (Generator.mixedProjection b d i j dot.dot R dot.finite).toLinearMap
    (Finsupp.single (Generator.mixedPair b d x) 1) = _
  rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul,
    Biset.Hom.transferBasis_sum, hf]

theorem oneTerm (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (tail (R := R) a c e f i j k t s).eval.toLinearMap
      (((Diagram.id (.up a)).horizontal (projection (R := R) b d i j (projectionDot b d i j r hr))).eval.toLinearMap
        (input (R := R) a b d g x)) =
    column (R := R) a b d c e f i j k r hr t s g x := by
  rw [input, Diagram.eval_horizontal_single (Diagram.id (.up a))
    (projection (R := R) b d i j (projectionDot b d i j r hr)),
    one_smul, Diagram.eval_id_apply, projectionColumn (R := R) b d i j r hr x, map_sum, map_sum]
  unfold column
  apply Finset.sum_congr rfl
  intro w _
  rw [Biset.pairLinear_single, one_mul]
  have hw : (Biset.induction i).pair (Biset.restriction j) (Quotient.out w).1 (Quotient.out w).2 = w :=
    Quotient.out_eq' w
  calc
    _ = (tail (R := R) a c e f i j k t s).eval.toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
          ((Biset.induction i).pair (Biset.restriction j) (Quotient.out w).1 (Quotient.out w).2)) 1) :=
      congrArg (fun v => (tail (R := R) a c e f i j k t s).eval.toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g v) 1)) hw.symm
    _ = _ := tail_pair a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2


end Singleton

section ListLinearity

variable {V W Z I : Type*} [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid Z]
variable [Module R V] [Module R W] [Module R Z]

private abbrev weightedMaps (terms : List (R × I)) (m : I → V →ₗ[R] W) :=
  (terms.map fun p => p.1 • m p.2).sum

private theorem weightedMaps_apply (terms : List (R × I)) (m : I → V →ₗ[R] W)
    (x : V) (T : W →ₗ[R] Z) :
    T (weightedMaps terms m x) = (terms.map fun p => p.1 • T (m p.2 x)).sum := by
  induction terms with
  | nil => simp [weightedMaps]
  | cons p terms ih =>
    simp only [weightedMaps, List.map_cons, List.sum_cons, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul]
    rw [ih]

theorem weightedMaps_comp_three
    {X₀ X₁ X₂ X₃ X₄ X₅ I₁ I₂ I₃ : Type*}
    [AddCommMonoid X₀] [AddCommMonoid X₁] [AddCommMonoid X₂]
    [AddCommMonoid X₃] [AddCommMonoid X₄] [AddCommMonoid X₅]
    [Module R X₀] [Module R X₁] [Module R X₂] [Module R X₃] [Module R X₄] [Module R X₅]
    (l : List (R × I₁)) (m : List (R × I₂)) (n : List (R × I₃))
    (P : I₁ → X₀ →ₗ[R] X₁) (Q : I₂ → X₂ →ₗ[R] X₃) (S : I₃ → X₄ →ₗ[R] X₅)
    (u : X₁ →ₗ[R] X₂) (v : X₃ →ₗ[R] X₄) (x : X₀) :
    weightedMaps n S (v (weightedMaps m Q (u (weightedMaps l P x)))) =
      (l.map fun r => (m.map fun t => (n.map fun s =>
        (r.1 * t.1 * s.1) • S s.2 (v (Q t.2 (u (P r.2 x))))).sum).sum).sum := by
  let T := (weightedMaps n S).comp (v.comp ((weightedMaps m Q).comp u))
  change T (weightedMaps l P x) = _
  rw [weightedMaps_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  let T' := (weightedMaps n S).comp v
  change r.1 • T' (weightedMaps m Q (u (P r.2 x))) = _
  rw [weightedMaps_apply, List.smul_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  change r.1 • (t.1 • weightedMaps n S (v (Q t.2 (u (P r.2 x))))) = _
  rw [smul_smul, ← LinearMap.id_apply (R := R) (weightedMaps n S _), weightedMaps_apply,
    List.smul_sum]
  simp only [List.map_map, LinearMap.id_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  exact smul_smul (r.1 * t.1) s.1 _

end ListLinearity

section DiagramLinearity
variable {U : Type*} [Group U] {K H J : Subgroup U} {I : Type*}

private noncomputable abbrev weighted {p q : Word K H} (terms : List (R × I))
    (diagr : I → Diagram R p q) :=
  ScopedDiagram.linearCombination (terms.map fun p => (p.1, .ordinary (diagr p.2)))

private theorem frameLeft (p : Word K H) {q q' : Word H J}
    (terms : List (R × I)) (diagr : I → Diagram R q q') :
    ((Biset.Hom.id p.basis).horizontal (weighted terms diagr).eval).toLinearMap =
      weightedMaps terms (fun i => ((Biset.Hom.id p.basis).horizontal (diagr i).eval).toLinearMap) := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((Biset.Hom.id p.basis).horizontal (weighted terms diagr).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) = _
  rw [Biset.Hom.horizontal_single]
  let pair := Biset.pairLinear R p.basis q'.basis ((Biset.Hom.id p.basis).toLinearMap
    (Finsupp.single x 1))
  let T := (LinearMap.lsmul R _ r).comp pair
  change T ((weighted terms diagr).eval.toLinearMap (Finsupp.single y 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, List.map_map, map_list_sum]
  rw [← LinearMap.id_apply (R := R) (weightedMaps _ _ _), weightedMaps_apply]
  simp only [List.map_map, LinearMap.id_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change T (term.1 • (diagr term.2).eval.toLinearMap (Finsupp.single y 1)) = term.1 •
    ((Biset.Hom.id p.basis).horizontal (diagr term.2).eval).toLinearMap
      (Finsupp.single (p.basis.pair q.basis x y) r)
  rw [Biset.Hom.horizontal_single]
  exact map_smul T term.1 _

private theorem frameRight {p p' : Word K H} (q : Word H J)
    (terms : List (R × I)) (diagr : I → Diagram R p p') :
    ((weighted terms diagr).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap =
      weightedMaps terms (fun i => ((diagr i).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap) := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((weighted terms diagr).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) = _
  rw [Biset.Hom.horizontal_single]
  let pair := (Biset.pairLinear R p'.basis q.basis).flip ((Biset.Hom.id q.basis).toLinearMap
    (Finsupp.single y 1))
  let T := (LinearMap.lsmul R _ r).comp pair
  change T ((weighted terms diagr).eval.toLinearMap (Finsupp.single x 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, List.map_map, map_list_sum]
  rw [← LinearMap.id_apply (R := R) (weightedMaps _ _ _), weightedMaps_apply]
  simp only [List.map_map, LinearMap.id_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change T (term.1 • (diagr term.2).eval.toLinearMap (Finsupp.single x 1)) = term.1 •
    ((diagr term.2).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap
      (Finsupp.single (p.basis.pair q.basis x y) r)
  rw [Biset.Hom.horizontal_single]
  exact map_smul T term.1 _

end DiagramLinearity

section FiniteLabels
variable {U : Type*} [Group U] {G A D F C E P : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)

private noncomputable abbrev listProjection (r : ProjectionDot.Mixed b d i j) :
    Diagram R ((Word.down b).tensor (.up d)) ((Word.up i).tensor (.down j)) :=
  .mixedProjection b d i j r.dot r.finite

private noncomputable abbrev middle (t : Middle a c i k) :
    Diagram R ((Word.up a).tensor (.up i)) ((Word.up c).tensor (.up k)) :=
  .parallelUp a i c k t

private noncomputable abbrev multiplication (s : Upper e f j k) :
    Diagram R ((Word.up k).tensor (.down j)) ((Word.down e).tensor (.up f)) :=
  .mixedMultiplication e f k j s

private noncomputable abbrev firstMap (r : ProjectionDot.Mixed b d i j) :=
  ((Biset.Hom.id (Word.up a).basis).horizontal (listProjection (R := R) b d i j r).eval).toLinearMap

private noncomputable abbrev secondMap (t : Middle a c i k) :=
  ((middle (R := R) a c i k t).eval.horizontal (Biset.Hom.id (Word.down j).basis)).toLinearMap

private noncomputable abbrev thirdMap (s : Upper e f j k) :=
  ((Biset.Hom.id (Word.up c).basis).horizontal (multiplication (R := R) e f j k s).eval).toLinearMap

private noncomputable abbrev unassocMap :=
  (Diagram.unassociate (R := R) (.up a) (.up i) (.down j)).eval.toLinearMap

private noncomputable abbrev assocMap :=
  (Diagram.associate (R := R) (.up c) (.up k) (.down j)).eval.toLinearMap

theorem drawing_eval
    (l : List (R × ProjectionDot.Mixed b d i j))
    (m : List (R × Middle a c i k)) (n : List (R × Upper e f j k))
    (x : (Bottom a b d).basis.carrier →₀ R) :
    (drawing a b d c e f i j k l m n).interpret.eval.toLinearMap x =
      weightedMaps n (thirdMap (R := R) c e f j k)
        (assocMap (R := R) c j k (weightedMaps m (secondMap (R := R) a c i j k)
          (unassocMap (R := R) a i j (weightedMaps l (firstMap (R := R) a b d i j) x)))) := by
  change ((Biset.Hom.id (Word.up c).basis).horizontal
      (weighted n (multiplication (R := R) e f j k)).eval).toLinearMap
    (assocMap (R := R) c j k (((weighted m (middle (R := R) a c i k)).eval.horizontal
      (Biset.Hom.id (Word.down j).basis)).toLinearMap
      (unassocMap (R := R) a i j (((Biset.Hom.id (Word.up a).basis).horizontal
        (weighted l (listProjection (R := R) b d i j)).eval).toLinearMap x)))) = _
  rw [frameLeft (.up a) l (listProjection (R := R) b d i j),
    frameRight (.down j) m (middle (R := R) a c i k), frameLeft (.up c) n (multiplication (R := R) e f j k)]


theorem eval_sum_singletons
    (l : List (R × ProjectionDot.Mixed b d i j))
    (m : List (R × Middle a c i k)) (n : List (R × Upper e f j k))
    (x : (Bottom a b d).basis.carrier →₀ R) :
    (drawing a b d c e f i j k l m n).interpret.eval.toLinearMap x =
      (l.map fun r => (m.map fun t => (n.map fun s => (r.1 * t.1 * s.1) •
        (drawing a b d c e f i j k [(1, r.2)] [(1, t.2)] [(1, s.2)]).interpret.eval.toLinearMap x
      ).sum).sum).sum := by
  rw [drawing_eval, weightedMaps_comp_three]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  rw [drawing_eval]
  simp only [weightedMaps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_smul, add_zero]

theorem eval_singleton_column
    (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (drawing (R := R) a b d c e f i j k
      [(1, projectionDot b d i j r hr)] [(1, t)] [(1, s)]).interpret.eval.toLinearMap
      (input (R := R) a b d g x) = column (R := R) a b d c e f i j k r hr t s g x := by
  rw [drawing_eval]
  simp only [weightedMaps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_smul, add_zero]
  exact oneTerm (R := R) a b d c e f i j k r hr t s g x

end FiniteLabels
end RingRight

#print axioms RingRight.weightedMaps_comp_three
#print axioms RingRight.oneTerm
#print axioms RingRight.eval_sum_singletons
#print axioms RingRight.eval_singleton_column
