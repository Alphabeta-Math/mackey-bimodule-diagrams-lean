import Proofs.ParabolicRightOrbitMultiplicity
import Proofs.ParabolicCaseFiveCoefficientOneExpansion
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Span

set_option maxHeartbeats 2000000

namespace SpanAudit
open MackeyDiagrams
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

private noncomputable def weighted {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Diagram R p q) : ScopedDiagram R p q :=
  .linearCombination (I.toList.map fun i => (weight i, .ordinary (term i)))

private theorem weighted_apply {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Diagram R p q) (z : p.basis.carrier →₀ R) :
    (weighted (R := R) I weight term).eval.toLinearMap z =
      ∑ i ∈ I, weight i • (term i).eval.toLinearMap z := by
  rw [weighted, ScopedDiagram.eval_linearCombination_apply, List.map_map]
  exact Finset.sum_map_toList I _

private theorem frameLeft {U : Type*} [Group U] {K H J : Subgroup U}
    (p : Word K H) {q q' : Word H J} {ι : Type*}
    (I : Finset ι) (weight : ι → R) (term : ι → Diagram R q q') :
    ((Biset.Hom.id (R := R) p.basis).horizontal (weighted (R := R) I weight term).eval).toLinearMap =
      ∑ i ∈ I, weight i • ((Biset.Hom.id (R := R) p.basis).horizontal (term i).eval).toLinearMap := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((Biset.Hom.id (R := R) p.basis).horizontal (weighted (R := R) I weight term).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) =
    (∑ i ∈ I, weight i • ((Biset.Hom.id (R := R) p.basis).horizontal (term i).eval).toLinearMap)
      (Finsupp.single (p.basis.pair q.basis x y) r)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Biset.Hom.horizontal_single,
    weighted_apply, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, mul_comm r (weight i)]

private theorem frameRight {U : Type*} [Group U] {K H J : Subgroup U}
    {p p' : Word K H} (q : Word H J) {ι : Type*}
    (I : Finset ι) (weight : ι → R) (term : ι → Diagram R p p') :
    ((weighted (R := R) I weight term).eval.horizontal (Biset.Hom.id (R := R) q.basis)).toLinearMap =
      ∑ i ∈ I, weight i • ((term i).eval.horizontal (Biset.Hom.id (R := R) q.basis)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((weighted (R := R) I weight term).eval.horizontal (Biset.Hom.id (R := R) q.basis)).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) =
    (∑ i ∈ I, weight i • ((term i).eval.horizontal (Biset.Hom.id (R := R) q.basis)).toLinearMap)
      (Finsupp.single (p.basis.pair q.basis x y) r)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Biset.Hom.horizontal_single,
    weighted_apply]
  let pair := (Biset.pairLinear R p'.basis q.basis).flip
    ((Biset.Hom.id (R := R) q.basis).toLinearMap (Finsupp.single y 1))
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

private noncomputable def drawing
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

private noncomputable def column (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (Top c e f).basis.carrier →₀ R :=
  ∑ w ∈ (hr x).toFinset, output (R := R) a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

private noncomputable def tail (t : Middle a c i k) (s : Upper e f j k) :
    Diagram R ((Word.up a).tensor (Inner i j)) (Top c e f) :=
  (unassoc (R := R) a i j).vertical (((parallel (R := R) a c i k t).horizontal (.id (.down j))).vertical
    ((assoc (R := R) c j k).vertical ((Diagram.id (R := R) (.up c)).horizontal (multiply (R := R) e f j k s))))

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
  change ((Diagram.id (R := R) (.up c)).horizontal (multiply (R := R) e f j k s)).eval.toLinearMap
    ((assoc (R := R) c j k).eval.toLinearMap
      (((parallel (R := R) a c i k t).horizontal (Diagram.id (R := R) (.down j))).eval.toLinearMap
        ((unassoc (R := R) a i j).eval.toLinearMap
          (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
            ((Biset.induction i).pair (Biset.restriction j) α h)) 1)))) = _
  rw [Diagram.eval_unassociate_single (R := R) (.up a) (.up i) (.down j) g α h 1,
    Diagram.eval_horizontal_single (R := R) (parallel (R := R) a c i k t) (Diagram.id (R := R) (.down j)),
    one_smul, Diagram.eval_id_apply, hm, Biset.pairLinear_single, one_mul,
    Diagram.eval_associate_single (R := R) (.up c) (.up k) (.down j),
    Diagram.eval_horizontal_single (R := R) (Diagram.id (R := R) (.up c)) (multiply (R := R) e f j k s),
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

private theorem oneTerm (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (tail (R := R) a c e f i j k t s).eval.toLinearMap
      (((Diagram.id (R := R) (.up a)).horizontal (projection (R := R) b d i j (projectionDot b d i j r hr))).eval.toLinearMap
        (input (R := R) a b d g x)) =
    column (R := R) a b d c e f i j k r hr t s g x := by
  rw [input, Diagram.eval_horizontal_single (R := R) (Diagram.id (R := R) (.up a))
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
    _ = _ := tail_pair (R := R) a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

private theorem projectionWeighted {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → ProjectionDot.Mixed b d i j) :
    (LabelledDrawing.compactProjection b d i j
      (I.toList.map fun u => (weight u, term u))).interpret =
      weighted (R := R) I weight (fun u => projection (R := R) b d i j (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem parallelWeighted {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Middle a c i k) :
    (LabelledDrawing.parallelUp a i c k (I.toList.map fun u => (weight u, term u))).interpret =
      weighted (R := R) I weight (fun u => parallel (R := R) a c i k (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem multiplyWeighted {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Upper e f j k) :
    (LabelledDrawing.mixedMultiplication e f k j (I.toList.map fun u => (weight u, term u))).interpret =
      weighted (R := R) I weight (fun u => multiply (R := R) e f j k (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem weightedCase {ι₁ ι₂ ι₃ : Type*}
    (I : Finset ι₁) (J : Finset ι₂) (K : Finset ι₃)
    (l : ι₁ → R) (m : ι₂ → R) (n : ι₃ → R)
    (r : ι₁ → Lower b d i j) (hr : ∀ u, Fibers b d i j (r u))
    (t : ι₂ → Middle a c i k) (s : ι₃ → Upper e f j k) (g : G) (x : D) :
    (drawing (R := R) a b d c e f i j k
      (I.toList.map fun u => (l u, projectionDot b d i j (r u) (hr u)))
      (J.toList.map fun v => (m v, t v)) (K.toList.map fun w => (n w, s w))).interpret.eval.toLinearMap
        (input (R := R) a b d g x) =
    ∑ u ∈ I, ∑ v ∈ J, ∑ w ∈ K,
      (l u * m v * n w) • column (R := R) a b d c e f i j k (r u) (hr u) (t v) (s w) g x := by
  -- Step 4: linearity on the three supported labels. Use Finset-indexed sums
  -- through the shared, genuinely horizontal frames, then multiply the weights.
  let project u := projectionDot b d i j (r u) (hr u)
  let D₁ := LabelledDrawing.compactProjection b d i j (I.toList.map fun u => (l u, project u))
  let D₂ := LabelledDrawing.parallelUp a i c k (J.toList.map fun v => (m v, t v))
  let D₃ := LabelledDrawing.mixedMultiplication e f k j (K.toList.map fun w => (n w, s w))
  change ((Biset.Hom.id (R := R) (Word.up c).basis).horizontal D₃.interpret.eval).toLinearMap
    ((assoc (R := R) c j k).eval.toLinearMap
      ((D₂.interpret.eval.horizontal (Biset.Hom.id (R := R) (Word.down j).basis)).toLinearMap
        ((unassoc (R := R) a i j).eval.toLinearMap
          (((Biset.Hom.id (R := R) (Word.up a).basis).horizontal D₁.interpret.eval).toLinearMap
            (input (R := R) a b d g x))))) = _
  have h₁ : D₁.interpret = weighted (R := R) I l (fun u => projection (R := R) b d i j (project u)) :=
    projectionWeighted (R := R) b d i j I l project
  have h₂ : D₂.interpret = weighted (R := R) J m (fun v => parallel (R := R) a c i k (t v)) :=
    parallelWeighted (R := R) a c i k J m t
  have h₃ : D₃.interpret = weighted (R := R) K n (fun w => multiply (R := R) e f j k (s w)) :=
    multiplyWeighted (R := R) e f j k K n s
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
  exact congrArg ((l u * m v * n w) • ·) (oneTerm (R := R) a b d c e f i j k (r u) (hr u) (t v) (s w) g x)


theorem singletonColumn (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (drawing (R := R) a b d c e f i j k
      [(1, projectionDot b d i j r hr)] [(1, t)] [(1, s)]).interpret.eval.toLinearMap
        (input (R := R) a b d g x) =
      column (R := R) a b d c e f i j k r hr t s g x := by
  have h := weightedCase (R := R) a b d c e f i j k
    ({()} : Finset Unit) ({()} : Finset Unit) ({()} : Finset Unit)
    (fun _ => (1 : R)) (fun _ => 1) (fun _ => 1)
    (fun _ => r) (fun _ => hr) (fun _ => t) (fun _ => s) g x
  simpa only [Finset.toList_singleton, List.map_cons, List.map_nil, Finset.sum_singleton,
    mul_one, one_smul] using h
end
end SpanAudit

namespace SpanAudit
open MackeyDiagrams
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

theorem projectedStabilizer_normalize {U G F X : Type*}
    [Group U] [Group G] [Group F] [MulAction (G × F) X]
    (ι : F →* U) (g : G) (x : X) :
    (MulAction.stabilizer (G × F) ((g, (1 : F)) • x)).map
        (ι.comp (MonoidHom.snd G F)) =
      (MulAction.stabilizer (G × F) x).map (ι.comp (MonoidHom.snd G F)) := by
  let f := ι.comp (MonoidHom.snd G F)
  have hf : f.comp (MulAut.conj (g, (1 : F))).toMonoidHom = f := by
    ext q
    change ι (1 * q.2 * 1⁻¹) = ι q.2
    simp
  change (MulAction.stabilizer (G × F) ((g, (1 : F)) • x)).map f = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, hf]

theorem indexTower {U : Type*} [Group U] {K L P : Subgroup U}
    [Finite P] (hKL : K ≤ L) (hLP : L ≤ P) :
    0 < L.relIndex P ∧ L.relIndex P ∣ K.relIndex P ∧ L.relIndex P ≤ K.relIndex P := by
  haveI : (L.subgroupOf P).FiniteIndex := inferInstance
  haveI : L.IsFiniteRelIndex P := ⟨Subgroup.index_ne_zero⟩
  have hpos : 0 < L.relIndex P := Subgroup.relIndex_pos
  have hdvd := Subgroup.relIndex_dvd_of_le_left (L := P) hKL
  haveI : (K.subgroupOf P).FiniteIndex := inferInstance
  haveI : K.IsFiniteRelIndex P := ⟨Subgroup.index_ne_zero⟩
  exact ⟨hpos, hdvd, Nat.le_of_dvd Subgroup.relIndex_pos hdvd⟩

theorem indexOne {U : Type*} [Group U] {L P : Subgroup U} {parabolic : Subgroup U → Prop}
    (h : IsGreatest {K : Subgroup U | K ≤ P ∧ parabolic K} L) :
    L.relIndex P = 1 ↔ parabolic P := by
  rw [Subgroup.relIndex_eq_one]
  exact ⟨fun hh => le_antisymm h.1.1 hh ▸ h.1.2, fun hP => h.2 ⟨le_rfl, hP⟩⟩

private abbrev Sinf := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
private abbrev ParabolicPerm (H : Subgroup (Equiv.Perm Nat)) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    H = ⨆ l, blockSym (blocks l)
private abbrev Parabolic (H : Subgroup Sinf) := ParabolicPerm (H.map Sinf.subtype)
private abbrev swaps (P : Subgroup Sinf) :=
  Subgroup.closure {σ : Sinf | σ ∈ P ∧ Equiv.Perm.IsSwap (σ : Equiv.Perm Nat)}

private theorem parabolic_finite {H : Subgroup Sinf} (hH : Parabolic H) : Finite H := by
  classical
  obtain ⟨n, blocks, _, _, hblocks⟩ := hH
  let X := Finset.univ.biUnion blocks
  have hsub : H.map Sinf.subtype ≤ blockSym X := by
    rw [hblocks]
    refine iSup_le fun i σ hs => ?_
    obtain ⟨τ, rfl⟩ := hs
    let σ : Equiv.Perm Nat := Equiv.Perm.ofSubtype τ
    have moved_mem (x : Nat) (hx : σ x ≠ x) : x ∈ X := by
      by_contra hn
      have hi : x ∉ blocks i := fun hx' => hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx'⟩)
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem τ hi)
    have preserves (x : Nat) : σ x ∈ X ↔ x ∈ X := by
      by_cases h : σ x = x
      · rw [h]
      · have hy : σ (σ x) ≠ σ x := fun hh => h (σ.injective hh)
        exact iff_of_true (moved_mem (σ x) hy) (moved_mem x h)
    exact ⟨σ.subtypePerm preserves, Equiv.Perm.ofSubtype_subtypePerm preserves moved_mem⟩
  let : Finite (blockSym X) :=
    (Set.finite_range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))).to_subtype
  exact Finite.of_injective
    (fun h : H => (⟨(h.val : Equiv.Perm Nat), hsub ⟨h.val, h.property, rfl⟩⟩ : blockSym X))
    (fun _ _ hh => Subtype.ext (Subtype.ext (congrArg (fun y : blockSym X => y.val) hh)))

private theorem parabolic_extremal (P : Subgroup Sinf) [Finite P] :
    IsGreatest {K : Subgroup Sinf | Parabolic K ∧ K ≤ P} (swaps P) := by
  classical
  let Q := P.map Sinf.subtype
  letI : Finite Q := Finite.of_surjective (fun p : P => (⟨p.val.val, ⟨p.val, p.property, rfl⟩⟩ : Q))
    (by rintro ⟨_, i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩)
  have hQ : Q ≤ Sinf := fun _ ⟨p, _, hp⟩ => hp ▸ p.property
  have unionWitness (H : Subgroup (Equiv.Perm Nat)) :
      ParabolicPerm H ↔ ∃ X : Finset Nat, ∃ (n : Nat) (blocks : Fin n → Finset Nat),
        (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
        (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ H = ⨆ l, blockSym (blocks l) := by
    constructor
    · rintro ⟨n, blocks, hn, hd, he⟩
      exact ⟨Finset.univ.biUnion blocks, n, blocks, hn, hd, by simp, he⟩
    · rintro ⟨_, n, blocks, hn, hd, _, he⟩
      exact ⟨n, blocks, hn, hd, he⟩
  have hmap : (swaps P).map Sinf.subtype =
      Subgroup.closure {σ | σ ∈ Q ∧ Equiv.Perm.IsSwap σ} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext σ
    constructor
    · rintro ⟨p, ⟨hp, hs⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hs⟩
    · rintro ⟨⟨p, hp, rfl⟩, hs⟩
      exact ⟨p, ⟨hp, hs⟩, rfl⟩
  have h := (ExtremalParabolicsOfFiniteGroup Q hQ).1
  rw [← hmap] at h
  refine ⟨⟨(unionWitness _).mpr h.1.1, ?_⟩, ?_⟩
  · exact (Subgroup.map_le_map_iff_of_injective Sinf.subtype_injective).mp h.1.2
  · intro K hK
    exact (Subgroup.map_le_map_iff_of_injective Sinf.subtype_injective).mp
      (h.2 ⟨(unionWitness _).mp hK.1, Subgroup.map_mono hK.2⟩)

private theorem conjugate_parabolic {B F : Subgroup Sinf} (j : ConjEmbedding B F)
    (hB : Parabolic B) : Parabolic ((F.subtype.comp j.toHom).range) := by
  classical
  obtain ⟨q, hq⟩ := j.hasRepresentative
  let conj := (MulAut.conj (q : Equiv.Perm Nat)).toMonoidHom
  have hmap : ((F.subtype.comp j.toHom).range).map Sinf.subtype =
      (B.map Sinf.subtype).map conj := by
    ext σ
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨p.val.val, ⟨p.val, p.property, rfl⟩, (congrArg Subtype.val (hq p)).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨j.toHom ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, congrArg Subtype.val (hq ⟨p, hp⟩)⟩
  have hcarrier : ∃ X : Finset Nat, ∃ (n : Nat) (blocks : Fin n → Finset Nat),
      (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
      (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ B.map Sinf.subtype = ⨆ l, blockSym (blocks l) := by
    obtain ⟨n, blocks, hn, hd, he⟩ := hB
    exact ⟨Finset.univ.biUnion blocks, n, blocks, hn, hd, by simp, he⟩
  obtain ⟨_, n, blocks, hn, hd, _, he⟩ := FiniteParabolicClosure.1 (B.map Sinf.subtype) hcarrier q
  exact ⟨n, blocks, hn, hd, hmap.trans he⟩

section Geometry

variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)

private abbrev word := (Word.up a).tensor ((Word.down b).tensor (.up d))
private abbrev point (g : G) (x : D) : (word a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b |>.tensor (.up d)).basis) g (Generator.mixedPair b d x)
private abbrev Pair := (word a b d).basis.carrier × (word c e f).basis.carrier
private abbrev action : MulAction (G × F) (Pair a b d c e f) where
  smul q z := ((word a b d).basis.act q z.1, (word c e f).basis.act q z.2)
  one_smul z := Prod.ext ((word a b d).basis.one_act z.1) ((word c e f).basis.one_act z.2)
  mul_smul q q' z := Prod.ext ((word a b d).basis.mul_act q q' z.1)
    ((word c e f).basis.mul_act q q' z.2)

private abbrev orbit (z : Pair a b d c e f) :=
  letI := action a b d c e f
  MulAction.orbit (G × F) z
private abbrev stabilizer (z : Pair a b d c e f) :=
  @MulAction.stabilizer (G × F) _ _ (action a b d c e f) z
private abbrev projectHom (G F : Subgroup U) := F.subtype.comp (MonoidHom.snd G F)
private abbrev projected (z : Pair a b d c e f) :=
  (stabilizer a b d c e f z).map (projectHom G F)
private abbrev base (r : D) (t : G) (s : E) : Pair a b d c e f :=
  (point a b d 1 r, point c e f t s)

private theorem point_surjective (z : (word a b d).basis.carrier) :
    ∃ g x, point a b d g x = z := by
  obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective y
  exact ⟨g, x, rfl⟩

private noncomputable abbrev coefficient (M : Biset.Hom R (word a b d).basis (word c e f).basis)
    (z : Pair a b d c e f) : R := M.toLinearMap (Finsupp.single z.1 1) z.2
private noncomputable abbrev matrix (O : Set (Pair a b d c e f)) (n : Nat)
    (z : Pair a b d c e f) : R := @ite _ (z ∈ O) (Classical.propDecidable _) n 0
private noncomputable abbrev eval (drawing : LabelledDrawing R (word a b d) (word c e f)) :=
  drawing.interpret.eval
private abbrev fiber (i : ConjEmbedding B A) (j : ConjEmbedding B F) :=
  ((Word.up i).tensor (.down j)).basis.carrier
private abbrev innerPoint (i : ConjEmbedding B A) (j : ConjEmbedding B F) (v : A × F) :
    fiber i j := (Biset.induction i).pair (Biset.restriction j) v.1 v.2
private abbrev lowerMap (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (r : Dot (b.comp i) (d.comp j)) := Generator.mixedMultiplicationBasis b d i j r
private abbrev outputOf (g : G) (t : G) (s : E) (v : A × F) :=
  point c e f (g * a.toHom v.1 * t) (s * f.toHom v.2)
private abbrev FiniteFibers (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (r : Dot (b.comp i) (d.comp j)) := ∀ z, Set.Finite {w | lowerMap b d i j r w = z}
private noncomputable abbrev hits (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (r : Dot (b.comp i) (d.comp j)) (t : G) (s : E) (g : G) (x : D)
    (y : (word c e f).basis.carrier) : Set (fiber i j) :=
  {w | lowerMap b d i j r w = Generator.mixedPair b d x ∧
    outputOf a c e f g t s (Quotient.out w) = y}

private theorem finite_of_bases [Finite A] [Finite F]
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) : Finite (fiber i j) :=
  Finite.of_surjective (innerPoint i j) (Quotient.exists_rep)

private theorem finiteFibers_of_bases [Finite A] [Finite F]
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (r : Dot (b.comp i) (d.comp j)) :
    FiniteFibers b d i j r := by
  letI := finite_of_bases i j
  exact fun _ => Set.toFinite _

private theorem act_point (q : G × F) (g : G) (x : D) :
    (word a b d).basis.act q (point a b d g x) =
      point a b d (q.1 * g) (x * (d.toHom q.2)⁻¹) := by
  change (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    (q.1 * g * (a.toHom 1)⁻¹)
    ((Biset.restriction b).pair (Biset.induction d)
      (b.toHom 1 * x * (1 : D)⁻¹) (1 * 1 * (d.toHom q.2)⁻¹)) = _
  simp only [map_one, inv_one, mul_one, one_mul, point]
  congr 1
  apply (Generator.mixedEquiv b d).injective
  change x * (d.toHom q.2)⁻¹ =
    Generator.mixedProduct b d (Generator.mixedPair b d (x * (d.toHom q.2)⁻¹))
  simp

private abbrev drawId {A F : Subgroup U} (p : Word A F) :=
  LabelledDrawing.ordinary (Diagram.id (R := R) p)

private noncomputable abbrev rightSingleton
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) (fin : FiniteFibers b d i j r) :
    LabelledDrawing R (word a b d) (word c e f) :=
  let ga := Word.up a
  let gc := Word.up c
  let ai := Word.up i
  let fj := Word.down j
  let ck := Word.up k
  let lower := LabelledDrawing.compactProjection (R := R) b d i j [(1, ⟨r, fin⟩)]
  let center := LabelledDrawing.parallelUp (R := R) a i c k [(1, t)]
  let upper := LabelledDrawing.mixedMultiplication (R := R) e f k j [(1, s)]
  LabelledDrawing.vertical
    (LabelledDrawing.horizontal (drawId ga) lower)
    (LabelledDrawing.vertical
      (LabelledDrawing.ordinary (Diagram.unassociate ga ai fj))
      (LabelledDrawing.vertical
        (LabelledDrawing.horizontal center (drawId fj))
        (LabelledDrawing.vertical
          (LabelledDrawing.ordinary (Diagram.associate gc ck fj))
          (LabelledDrawing.horizontal (drawId gc) upper))))

private theorem drawing_count
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) (fin : FiniteFibers b d i j r)
    (g : G) (x : D) (y : (word c e f).basis.carrier) :
    coefficient a b d c e f (eval a b d c e f (rightSingleton (R := R) a b d c e f i j k r t s fin))
        (point a b d g x, y) =
      (Nat.card (hits a b d c e f i j r t.element s.element g x y) : R) := by
  classical
  have eq (x' : D) (w : fiber i j) :
      Generator.mixedProduct b d (lowerMap b d i j r w) = x' ↔
        lowerMap b d i j r w = Generator.mixedPair b d x' := by
    constructor
    · intro he
      apply (Generator.mixedEquiv b d).injective
      exact he.trans (Generator.mixedProduct_mixedPair b d x').symm
    · intro he
      rw [he, Generator.mixedProduct_mixedPair]
  have h (x' : D) : Set.Finite {w | Generator.mixedProduct b d (lowerMap b d i j r w) = x'} :=
    (fin (Generator.mixedPair b d x')).subset (fun w hw => (eq x' w).mp hw)
  have hset : (h x).toFinset = (fin (Generator.mixedPair b d x)).toFinset := by
    ext w
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using eq x w
  let target : fiber i j → (word c e f).basis.carrier := fun w =>
    outputOf a c e f g t.element s.element (Quotient.out w)
  let column : Finset (fiber i j) := (fin (Generator.mixedPair b d x)).toFinset
  let H := hits a b d c e f i j r t.element s.element g x y
  have hf : H.Finite := (fin (Generator.mixedPair b d x)).subset fun _ hw => hw.1
  have hfilter : column.filter (fun w => target w = y) = hf.toFinset := by
    apply Finset.ext
    intro w
    simp only [Finset.mem_filter, column, Set.Finite.mem_toFinset] <;> rfl
  have supplied := singletonColumn (R := R) a b d c e f i j k r h t s g x
  change (rightSingleton (R := R) a b d c e f i j k r t s fin).interpret.eval.toLinearMap
    (Finsupp.single (point a b d g x) 1) =
      ∑ w ∈ (h x).toFinset, Finsupp.single (target w) 1 at supplied
  rw [hset] at supplied
  change (rightSingleton (R := R) a b d c e f i j k r t s fin).interpret.eval.toLinearMap
    (Finsupp.single (point a b d g x) 1) y = (Nat.card H : R)
  rw [supplied, Finset.sum_apply']
  simp only [Finsupp.single_apply, ← Finset.sum_filter]
  change (∑ w ∈ column.filter (fun w => target w = y), (1 : R)) = _
  letI := hf.fintype
  rw [hfilter, Finset.sum_const, nsmul_eq_mul, mul_one, Set.Finite.card_toFinset hf]
  exact congrArg (Nat.cast : Nat → R) (Nat.card_eq_fintype_card (α := H)).symm


private theorem normalize_exact (z : Pair a b d c e f) :
    ∃ (r : D) (t : G) (s : E),
      orbit a b d c e f (base a b d c e f r t s) = orbit a b d c e f z ∧
      projected a b d c e f (base a b d c e f r t s) = projected a b d c e f z := by
  obtain ⟨g, r, hg⟩ := point_surjective a b d z.1
  obtain ⟨t, s, ht⟩ := point_surjective c e f z.2
  let z₀ := base a b d c e f r (g⁻¹ * t) s
  letI := action a b d c e f
  have hz : (g, (1 : F)) • z₀ = z := by
    apply Prod.ext
    · change (word a b d).basis.act (g, 1) (point a b d 1 r) = z.1
      rw [act_point]
      simpa using hg
    · change (word c e f).basis.act (g, 1) (point c e f (g⁻¹ * t) s) = z.2
      rw [act_point]
      simpa using ht
  have hproj := projectedStabilizer_normalize F.subtype g z₀
  change projected a b d c e f ((g, (1 : F)) • z₀) = projected a b d c e f z₀ at hproj
  refine ⟨r, g⁻¹ * t, s, ?_, (hz ▸ hproj).symm⟩
  exact (MulAction.orbit_eq_iff.mpr ⟨(g, 1), hz⟩).symm

end Geometry

section ParabolicCase
variable {G A D F C E B : Subgroup Sinf}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)

private theorem projected_le (z : Pair a b d c e f) : projected a b d c e f z ≤ F := by
  rintro x ⟨q, _, rfl⟩
  exact q.2.property

private theorem projected_finite [Finite F] (z : Pair a b d c e f) :
    Finite (projected a b d c e f z) :=
  Finite.of_injective (Subgroup.inclusion (projected_le a b d c e f z))
    (Subgroup.inclusion_injective _)

private theorem rightLaw
    (hG : Parabolic G) (hA : Parabolic A) (hD : Parabolic D) (hF : Parabolic F)
    (hC : Parabolic C) (hE : Parabolic E) (hB : Parabolic B)
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) (fin : FiniteFibers b d i j r) :
    let z := base a b d c e f r.element t.element s.element
    let P := projected a b d c e f z
    let K := (F.subtype.comp j.toHom).range
    K ≤ P ∧ (swaps P).relIndex P ∣ K.relIndex P ∧
      ∀ z', coefficient a b d c e f (eval a b d c e f (rightSingleton (R := R) a b d c e f i j k r t s fin)) z' =
        matrix (R := R) a b d c e f (orbit a b d c e f z) (K.relIndex P) z' := by
  classical
  dsimp only
  let z := base a b d c e f r.element t.element s.element
  let P := projected a b d c e f z
  let K := (F.subtype.comp j.toHom).range
  have mult := (ParabolicRightOrbitMultiplicity G A D F C E hG hA hD hF hC hE
    a b d c e f).2.2.2.1 B hB ⟨i, j, k, r, t, s⟩
  have hKP : K ≤ P := mult.1
  haveI : Finite F := parabolic_finite hF
  haveI : Finite P := projected_finite a b d c e f z
  have hL := parabolic_extremal P
  have hKL := hL.2 ⟨conjugate_parabolic j hB, hKP⟩
  refine ⟨hKP, (indexTower hKL hL.1.2).2.1, ?_⟩
  rintro ⟨u, y⟩
  obtain ⟨g, x, rfl⟩ := point_surjective a b d u
  have hcount := mult.2.2 g x y
  change Nat.card (hits a b d c e f i j r t.element s.element g x y) =
    @ite Nat ((point a b d g x, y) ∈ orbit a b d c e f z) (Classical.propDecidable _)
      (K.relIndex P) 0 at hcount
  rw [drawing_count, hcount]
  by_cases hy : (point a b d g x, y) ∈ orbit a b d c e f z <;>
    simp [matrix, z, P, K, hy]

private abbrev RealizationAt (O : Set (Pair a b d c e f)) (P L : Subgroup Sinf) : Prop :=
    ∃ (i : ConjEmbedding L A) (j : ConjEmbedding L F) (k : ConjEmbedding L C)
      (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
      (s : Dot (e.comp k) (f.comp j)) (fin : FiniteFibers b d i j r),
      orbit a b d c e f (base a b d c e f r.element t.element s.element) = O ∧
      projected a b d c e f (base a b d c e f r.element t.element s.element) = P ∧
      (∀ h : L, (j.toHom h : Sinf) = (h : Sinf)) ∧
      ∀ z', coefficient a b d c e f (eval a b d c e f
        (rightSingleton (R := R) a b d c e f i j k r t s fin)) z' =
        matrix (R := R) a b d c e f O (L.relIndex P) z'

private theorem realizationAtNormalized
    (hG : Parabolic G) (hA : Parabolic A) (hD : Parabolic D) (hF : Parabolic F)
    (hC : Parabolic C) (hE : Parabolic E) (r : D) (t : G) (s : E) :
    let z₀ := base a b d c e f r t s
    let P := projected a b d c e f z₀
    RealizationAt (R := R) a b d c e f (orbit a b d c e f z₀) P (swaps P) := by
  classical
  intro z₀ P
  letI : Finite F := parabolic_finite hF
  letI : Finite A := parabolic_finite hA
  have supply := (ParabolicRightOrbitMultiplicity G A D F C E hG hA hD hF hC hE
    a b d c e f).2.2.1 r t s
  obtain ⟨full, hLabels, _, _, _, ⟨_, ⟨i, j, k, r', t', s'⟩, hPar, hRest, hInc, _⟩⟩ := supply.2
  have hRTS : (r'.element, t'.element, s'.element) = (r, t, s) := hRest.1.trans hLabels
  obtain ⟨hr, hts⟩ := Prod.mk.inj hRTS
  obtain ⟨ht, hs⟩ := Prod.mk.inj hts
  let fin := finiteFibers_of_bases b d i j r'
  have hrep : base a b d c e f r'.element t'.element s'.element = z₀ := by
    rw [hr, ht, hs]
  change ∀ h : swaps P, (j.toHom h : Sinf) = (h : Sinf) at hInc
  have hj : (F.subtype.comp j.toHom).range = swaps P := by
    ext q
    constructor
    · rintro ⟨u, rfl⟩
      change (j.toHom u : Sinf) ∈ swaps P
      rw [hInc u]
      exact u.property
    · intro hq
      exact ⟨⟨q, hq⟩, hInc ⟨q, hq⟩⟩
  have he := (rightLaw (R := R) a b d c e f hG hA hD hF hC hE hPar i j k r' t' s' fin).2.2
  change ∀ z', coefficient a b d c e f (eval a b d c e f
    (rightSingleton (R := R) a b d c e f i j k r' t' s' fin)) z' =
    matrix (R := R) a b d c e f (orbit a b d c e f
      (base a b d c e f r'.element t'.element s'.element))
      (((F.subtype.comp j.toHom).range).relIndex
        (projected a b d c e f (base a b d c e f r'.element t'.element s'.element))) z' at he
  rw [hrep, hj] at he
  refine ⟨i, j, k, r', t', s', fin, ?_, ?_, hInc, he⟩
  · rw [hrep]
  · rw [hrep]

private theorem realizeSwaps
    (hG : Parabolic G) (hA : Parabolic A) (hD : Parabolic D) (hF : Parabolic F)
    (hC : Parabolic C) (hE : Parabolic E) (z : Pair a b d c e f) :
    let P := projected a b d c e f z
    let L := swaps P
    IsGreatest {K : Subgroup Sinf | K ≤ P ∧ Parabolic K} L ∧
      RealizationAt (R := R) a b d c e f (orbit a b d c e f z) P L := by
  classical
  intro P L
  letI : Finite F := parabolic_finite hF
  letI : Finite P := projected_finite a b d c e f z
  have hL := parabolic_extremal P
  refine ⟨⟨⟨hL.1.2, hL.1.1⟩, fun K hK => hL.2 ⟨hK.2, hK.1⟩⟩, ?_⟩
  obtain ⟨r, t, s, ho, hp⟩ := normalize_exact a b d c e f z
  have he := realizationAtNormalized (R := R) a b d c e f hG hA hD hF hC hE r t s
  dsimp only at he
  rw [ho, hp] at he
  exact he

end ParabolicCase
end SpanAudit

#print axioms SpanAudit.realizeSwaps
