import MackeyDiagrams
import Proofs.ReplacementForTwoMultiplications

set_option maxHeartbeats 2000000

/-!
Ian Xiao, Example 6.4 and Theorem 6.5, Cases 3 and 4.
The archived original has the example on p. 25 and Theorem 6.5 on p. 24.
The published 28 November revision (SHA-256
813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61)
has them on pp. 27 and 26 respectively:
https://getcurious.cc/downloads/mackey-bimodules.pdf#page=27

The coordinator supplies Generator.mixedMultiplicationBasis (Mixed.lean:53)
and DotLabel.upDrawing_basis (DotLabels.lean:75). The former gives the
push-forward of each balanced pair by x * p * y at identity embeddings.
The latter gives the dot in the parallel merge, dot and split, with the
coefficient-one singleton reducing its finite sum to one column. The
intertwining equation for each mark follows from commutativity of C₂.
These columns use multiplication, so the projection fiber condition
does not enter. The associators transport pairs into and out of the
last-two-strand frame.

The published case numbers give the replacement directions. The plan has
no separate numbered Alphabeta Math proof for this example. The registered
ReplacementForTwoMultiplications gives existence of evaluation-preserving
replacements on these shapes. Its existential replacement maps alone
do not determine the labels of the explicit round trip, so the proof
uses the checked columns to compute the two multipliers in the specified
maps. Equality is checked on the entire triple balanced basis before
the boundary merge, using quotient induction and linearity. The original
and returned tuples are distinguished at the first marked label.
-/

namespace MixedMultiplicationRoundTrip
open MackeyDiagrams

universe u
variable {U : Type u} [CommGroup U] (K : Subgroup U)

private abbrev emb := ConjEmbedding.id K
private abbrev composed := (emb K).comp (emb K)
private abbrev up := Word.up (emb K)
private abbrev down := Word.down (emb K)
private abbrev bottom := ((up K).tensor (up K)).tensor (down K)
private abbrev top := ((down K).tensor (up K)).tensor (up K)

private def dot (p : K) : Dot (composed K) (composed K) :=
  ⟨p, fun h => mul_comm ((composed K).toHom h) p⟩

private noncomputable def weight (p : K) : DotLabel Complex (composed K) (composed K) :=
  Finsupp.single (dot K p) 1

private theorem identity_weight : DotLabel.identity (R := Complex) (composed K) = weight K 1 := by
  unfold DotLabel.identity weight
  rw [show Dot.id (composed K) = dot K 1 from Dot.ext rfl]

private theorem terms_weight (p : K) : (weight K p).terms = [(1, dot K p)] := by
  simp [DotLabel.terms, weight, Finsupp.support_single, Finset.toList_singleton]

variable {K}
private noncomputable abbrev run {a b : Word K K} (d : LabelledDrawing Complex a b) :=
  d.interpret.eval.toLinearMap

private abbrev pair (a b : Word K K) := a.basis.pair b.basis

private abbrev straight (a : Word K K) : LabelledDrawing Complex a a :=
  .ordinary (.id a)

private abbrev last (a : Word K K) {b c b' c' : Word K K}
    (d : LabelledDrawing Complex (b.tensor c) (b'.tensor c')) :
    LabelledDrawing Complex ((a.tensor b).tensor c) ((a.tensor b').tensor c') :=
  .vertical (.ordinary (.associate a b c))
    (.vertical (.horizontal (straight a) d) (.ordinary (.unassociate a b' c')))

private theorem stack_apply {a b c : Word K K} (d : LabelledDrawing Complex a b)
    (e : LabelledDrawing Complex b c) (x : a.basis.carrier →₀ Complex) :
    run (.vertical d e) x = run e (run d x) := rfl

private theorem first_column {a a' b : Word K K} (d : LabelledDrawing Complex a a')
    (x : a.basis.carrier) (x' : a'.basis.carrier) (y : b.basis.carrier)
    (hd : run d (Finsupp.single x 1) = Finsupp.single x' 1) :
    run (.horizontal d (straight b)) (Finsupp.single (pair a b x y) 1) =
      Finsupp.single (pair a' b x' y) 1 := by
  change (d.interpret.eval.horizontal (Diagram.id b).eval).toLinearMap _ = _
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply, hd,
    Biset.pairLinear_single, one_mul]

private theorem last_column {a b c b' c' : Word K K}
    (d : LabelledDrawing Complex (b.tensor c) (b'.tensor c'))
    (x : a.basis.carrier) (y : b.basis.carrier) (z : c.basis.carrier)
    (y' : b'.basis.carrier) (z' : c'.basis.carrier)
    (hd : run d (Finsupp.single (pair b c y z) 1) = Finsupp.single (pair b' c' y' z') 1) :
    run (last a d) (Finsupp.single (pair (a.tensor b) c (pair a b x y) z) 1) =
      Finsupp.single (pair (a.tensor b') c' (pair a b' x y') z') 1 := by
  change (Diagram.unassociate (R := Complex) a b' c').eval.toLinearMap
    (((Diagram.id a).eval.horizontal d.interpret.eval).toLinearMap
      ((Diagram.associate (R := Complex) a b c).eval.toLinearMap
        (Finsupp.single (pair (a.tensor b) c (pair a b x y) z) 1))) = _
  rw [Diagram.eval_associate_single, Biset.Hom.horizontal_single, one_smul,
    Diagram.eval_id_apply, hd, Biset.pairLinear_single, one_mul, Diagram.eval_unassociate_single]

private theorem singleton_eval {a b : Word K K} (d : Diagram Complex a b)
    (x : a.basis.carrier →₀ Complex) :
    (ScopedDiagram.linearCombination [(1, ScopedDiagram.ordinary d)]).eval.toLinearMap x =
      d.eval.toLinearMap x := by
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
  rfl

variable (K)
private noncomputable abbrev mixed (p : K) :=
  LabelledDrawing.mixedMultiplication (emb K) (emb K) (emb K) (emb K) (weight K p).terms

private noncomputable abbrev parallel (p : K) :=
  LabelledDrawing.parallelUp (emb K) (emb K) (emb K) (emb K) (weight K p).terms

private theorem mixed_column (p x y : K) :
    run (mixed K p) (Finsupp.single (pair (up K) (down K) x y) 1) =
      Finsupp.single (pair (down K) (up K) (x * p * y) 1) 1 := by
  change (ScopedDiagram.linearCombination ((weight K p).terms.map fun (c, d) =>
    (c, .ordinary (.mixedMultiplication (emb K) (emb K) (emb K) (emb K) d)))).eval.toLinearMap _ = _
  rw [terms_weight]
  change (ScopedDiagram.linearCombination [(1, .ordinary
    (.mixedMultiplication (emb K) (emb K) (emb K) (emb K) (dot K p)))]).eval.toLinearMap _ = _
  rw [singleton_eval]
  change (Generator.mixedMultiplication (R := Complex) (emb K) (emb K) (emb K) (emb K)
    (dot K p)).toLinearMap _ = _
  unfold Generator.mixedMultiplication
  rw [Biset.Hom.ofFunction_single]
  -- The route's mixedMultiplicationBasis is defined on the balanced quotient.
  rfl

private theorem parallel_column (p x y : K) :
    run (parallel K p) (Finsupp.single (pair (up K) (up K) x y) 1) =
      Finsupp.single (pair (up K) (up K) (x * y * p) 1) 1 := by
  change (ScopedDiagram.linearCombination ((weight K p).terms.map fun (c, d) =>
    (c, .ordinary (.parallelUp (emb K) (emb K) (emb K) (emb K) d)))).eval.toLinearMap _ = _
  rw [terms_weight]
  change (ScopedDiagram.linearCombination [(1, .ordinary
    (.parallelUp (emb K) (emb K) (emb K) (emb K) (dot K p)))]).eval.toLinearMap _ = _
  rw [singleton_eval, Diagram.parallelUp, Diagram.eval_vertical_apply,
    Diagram.eval_vertical_apply, Diagram.eval_mergeUp_single]
  have hd : (weight K p).upDrawing.interpret.eval.toLinearMap
      (Finsupp.single (x * y) 1) = ((weight K p).terms.map fun (c, d) =>
        c • Finsupp.single (x * y * d.element) (1 : Complex)).sum := by
    simpa only [DotLabel.terms, List.map_map, Function.comp_def] using
      DotLabel.upDrawing_basis (weight K p) (x * y)
  rw [terms_weight] at hd
  have hdot : (Diagram.upDot (R := Complex) (dot K p)).eval.toLinearMap
      (Finsupp.single (x * y) 1) = Finsupp.single (x * y * p) 1 := by
    rw [DotLabel.eval_upDrawing, Diagram.eval_linearUpDot_apply, weight, freeLift_single,
      one_smul] at hd
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, dot]
      using hd
  change (Diagram.splitUp (R := Complex) (emb K) (emb K)).eval.toLinearMap
    ((Diagram.upDot (dot K p)).eval.toLinearMap (Finsupp.single (x * y) 1)) = _
  rw [hdot, Diagram.eval_splitUp_single]

private noncomputable def left (p q r : K) : LabelledDrawing Complex (bottom K) (top K) :=
  .vertical (.horizontal (parallel K p) (straight (down K)))
    (.vertical (last (up K) (mixed K q)) (.horizontal (mixed K r) (straight (up K))))

private noncomputable def right (p q r : K) : LabelledDrawing Complex (bottom K) (top K) :=
  .vertical (last (up K) (mixed K p))
    (.vertical (.horizontal (mixed K q) (straight (up K))) (last (down K) (parallel K r)))

private abbrev triple {K : Subgroup U} (a b c : Word K K) (x : a.basis.carrier) (y : b.basis.carrier)
    (z : c.basis.carrier) := pair (a.tensor b) c (pair a b x y) z

private theorem left_column (p q r x y z : K) :
    run (left K p q r) (Finsupp.single (triple (up K) (up K) (down K) x y z) 1) =
      Finsupp.single (triple (down K) (up K) (up K) (x * y * p * r * (q * z)) 1 1) 1 := by
  unfold left
  rw [stack_apply, stack_apply]
  rw [first_column (b := down K) (parallel K p) _ _ z (parallel_column K p x y)]
  rw [last_column (a := up K) (b := up K) (c := down K) (b' := down K) (c' := up K)
    (mixed K q) (x * y * p) 1 z _ _ (mixed_column K q 1 z)]
  rw [first_column (b := up K) (mixed K r) _ _ 1
    (mixed_column K r (x * y * p) (1 * q * z))]
  rw [one_mul]

private theorem right_column (p q r x y z : K) :
    run (right K p q r) (Finsupp.single (triple (up K) (up K) (down K) x y z) 1) =
      Finsupp.single (triple (down K) (up K) (up K) (x * q * (y * p * z)) r 1) 1 := by
  unfold right
  rw [stack_apply, stack_apply]
  rw [last_column (a := up K) (b := up K) (c := down K) (b' := down K) (c' := up K)
    (mixed K p) x y z _ _ (mixed_column K p y z)]
  rw [first_column (b := up K) (mixed K q) _ _ 1 (mixed_column K q x (y * p * z))]
  rw [last_column (a := down K) (b := up K) (c := up K) (b' := up K) (c' := up K)
    (parallel K r) (x * q * (y * p * z)) 1 1 _ _ (parallel_column K r 1 1)]
  simp only [one_mul]

private abbrev split : LabelledDrawing Complex
    ((Word.up (composed K)).tensor (down K)) (bottom K) :=
  .horizontal (.trivalent (.splitUp (emb K) (emb K))) (straight (down K))

private abbrev merge : LabelledDrawing Complex (top K)
    ((down K).tensor (Word.up (composed K))) :=
  .vertical (.ordinary (.associate (down K) (up K) (up K)))
    (.horizontal (straight (down K)) (.trivalent (.mergeUp (emb K) (emb K))))

private theorem split_column :
    run (split K) (Finsupp.single (pair (Word.up (composed K)) (down K) 1 1) 1) =
      Finsupp.single (triple (up K) (up K) (down K) 1 1 1) 1 := by
  change (Diagram.horizontal (R := Complex) (Diagram.splitUp (emb K) (emb K))
    (Diagram.id (down K))).eval.toLinearMap _ = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_splitUp_single, Diagram.eval_id_apply,
    Biset.pairLinear_single, one_mul]

private theorem merge_column (x y z : K) :
    run (merge K) (Finsupp.single (triple (down K) (up K) (up K) x y z) 1) =
      Finsupp.single (pair (down K) (Word.up (composed K)) x (y * z)) 1 := by
  change (Diagram.horizontal (R := Complex) (Diagram.id (down K))
    (Diagram.mergeUp (emb K) (emb K))).eval.toLinearMap
      ((Diagram.associate (R := Complex) (down K) (up K) (up K)).eval.toLinearMap
        (Finsupp.single (triple (down K) (up K) (up K) x y z) 1)) = _
  rw [Diagram.eval_associate_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, Diagram.eval_mergeUp_single, Biset.pairLinear_single, one_mul]
  rfl

private noncomputable def multiplier (d : LabelledDrawing Complex (bottom K) (top K)) :
    MonoidAlgebra Complex K :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain (Generator.mixedProduct (emb K) (composed K))
    (run (.vertical (split K) (.vertical d (merge K)))
      (Finsupp.single (pair (Word.up (composed K)) (down K) 1 1) 1)))

private theorem left_multiplier (p : K) (hp : p * p = 1) :
    multiplier K (left K p 1 p) = 1 := by
  unfold multiplier
  rw [stack_apply, stack_apply, split_column, left_column, merge_column, Finsupp.mapDomain_single]
  change MonoidAlgebra.single ((1 * 1 * p * p * (1 * 1)) * (1 * 1)) (1 : Complex) = 1
  simpa only [one_mul, mul_one, hp] using
    (MonoidAlgebra.one_def (R := Complex) (M := K)).symm

private theorem right_multiplier :
    multiplier K (right K 1 1 1) = 1 := by
  unfold multiplier
  rw [stack_apply, stack_apply, split_column, right_column, merge_column, Finsupp.mapDomain_single]
  change MonoidAlgebra.single (((1 : K) * 1 * (1 * 1 * 1)) * (1 * 1)) (1 : Complex) = 1
  simpa only [one_mul] using (MonoidAlgebra.one_def (R := Complex) (M := K)).symm

private theorem weight_of_one :
    Finsupp.mapDomain (dot K) (MonoidAlgebra.coeff (1 : MonoidAlgebra Complex K)) = weight K 1 := by
  rw [MonoidAlgebra.one_def]
  change Finsupp.mapDomain (dot K) (Finsupp.single 1 (1 : Complex)) = _
  rw [Finsupp.mapDomain_single]
  rfl

private theorem weight_ne_one (p : K) (hp : p ≠ 1) : weight K p ≠ weight K 1 := by
  intro h
  have hdot : dot K p ≠ dot K 1 := fun hd => hp (congrArg Dot.element hd)
  have hc := congrArg (fun l : DotLabel Complex (composed K) (composed K) => l (dot K p)) h
  simp [weight, Finsupp.single_eq_of_ne hdot] at hc

private theorem left_same_eval (p : K) (hp : p * p = 1) :
    (left K 1 1 1).interpret.eval = (left K p 1 p).interpret.eval := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro xyz c
  have h : run (left K 1 1 1) (Finsupp.single xyz 1) =
      run (left K p 1 p) (Finsupp.single xyz 1) := by
    refine Quotient.inductionOn xyz (fun ⟨xy, z⟩ => ?_)
    refine Quotient.inductionOn xy (fun ⟨x, y⟩ => ?_)
    change run (left K 1 1 1) (Finsupp.single (triple (up K) (up K) (down K) x y z) 1) =
      run (left K p 1 p) (Finsupp.single (triple (up K) (up K) (down K) x y z) 1)
    rw [left_column, left_column]
    have hproduct : x * y * p * p * z = x * y * z := by
      rw [show x * y * p * p = x * y * (p * p) from mul_assoc (x * y) p p, hp, mul_one]
    simp only [one_mul, mul_one, hproduct]
  have hs : (Finsupp.single xyz c : (bottom K).basis.carrier →₀ Complex) =
      c • Finsupp.single xyz 1 := by rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul]
  exact congrArg (c • ·) h

end MixedMultiplicationRoundTrip

theorem MixedMultiplicationLabelsChangeOnRoundTrip : (
let U := Multiplicative (ZMod 2)
let K : Subgroup U := ⊤
let g : K := ⟨Multiplicative.ofAdd (1 : ZMod 2), Subgroup.mem_top _⟩
let i := MackeyDiagrams.ConjEmbedding.id K
let ii := MackeyDiagrams.ConjEmbedding.comp i i
let up := MackeyDiagrams.Word.up i
let down := MackeyDiagrams.Word.down i
let bottom := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.tensor up up) down
let top := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.tensor down up) up
let Weight := MackeyDiagrams.DotLabel Complex ii ii
let Labels := Weight × Weight × Weight
let Drawing := fun p q : MackeyDiagrams.Word K K => MackeyDiagrams.LabelledDrawing Complex p q
let ordinary := fun {p q : MackeyDiagrams.Word K K} (d : MackeyDiagrams.Diagram Complex p q) =>
  MackeyDiagrams.LabelledDrawing.ordinary d
let straight := fun p : MackeyDiagrams.Word K K => ordinary (MackeyDiagrams.Diagram.id p)
let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let mixed := fun w : Weight =>
  MackeyDiagrams.LabelledDrawing.mixedMultiplication i i i i (MackeyDiagrams.DotLabel.terms w)
let parallel := fun w : Weight =>
  MackeyDiagrams.LabelledDrawing.parallelUp i i i i (MackeyDiagrams.DotLabel.terms w)
let onLastTwo := fun (spectator p q p' q' : MackeyDiagrams.Word K K)
    (crossing : Drawing (MackeyDiagrams.Word.tensor p q) (MackeyDiagrams.Word.tensor p' q')) =>
  stack (ordinary (MackeyDiagrams.Diagram.associate spectator p q))
    (stack (juxtapose (straight spectator) crossing)
      (ordinary (MackeyDiagrams.Diagram.unassociate spectator p' q')))
let leftDrawing : Labels → Drawing bottom top := fun (x₁, x₂, x₃) =>
  stack (juxtapose (parallel x₁) (straight down))
    (stack (onLastTwo up up down down up (mixed x₂))
      (juxtapose (mixed x₃) (straight up)))
let rightDrawing : Labels → Drawing bottom top := fun (y₁, y₂, y₃) =>
  stack (onLastTwo up up down down up (mixed y₁))
    (stack (juxtapose (mixed y₂) (straight up))
      (onLastTwo down up up up up (parallel y₃)))
let splitBottom :=
  juxtapose (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp i i))
    (straight down)
let mergeTop :=
  stack (ordinary (MackeyDiagrams.Diagram.associate down up up))
    (juxtapose (straight down)
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp i i)))
let eval := fun {p q : MackeyDiagrams.Word K K} (drawing : Drawing p q) =>
  MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
let multiplier := fun (drawing : Drawing bottom top) =>
  MonoidAlgebra.ofCoeff
    (Finsupp.mapDomain (MackeyDiagrams.Generator.mixedProduct i ii)
      (MackeyDiagrams.Biset.Hom.toLinearMap
        (eval (stack splitBottom (stack drawing mergeTop)))
        (Finsupp.single
          (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction ii)
            (MackeyDiagrams.Biset.restriction i) 1 1) 1)))
let selfDot : K → MackeyDiagrams.Dot ii ii :=
  fun p => ⟨p, fun v => mul_comm (MackeyDiagrams.ConjEmbedding.toHom ii v) p⟩
let unitWeight : Weight := MackeyDiagrams.DotLabel.identity ii
let gWeight : Weight := Finsupp.single (selfDot g) 1
let asWeight := fun (M : MonoidAlgebra Complex K) =>
  Finsupp.mapDomain selfDot (MonoidAlgebra.coeff M)
let replaceCase3 : Labels → Labels :=
  fun l => (asWeight (multiplier (leftDrawing l)), unitWeight, unitWeight)
let replaceCase4 : Labels → Labels :=
  fun r => (unitWeight, unitWeight, asWeight (multiplier (rightDrawing r)))
let original : Labels := (gWeight, unitWeight, gWeight)
let units : Labels := (unitWeight, unitWeight, unitWeight)
let roundTrip := replaceCase4 (replaceCase3 original)
g ≠ 1 ∧ g ^ 2 = 1 ∧
  multiplier (leftDrawing original) = 1 ∧
  roundTrip = units ∧ roundTrip ≠ original ∧
  eval (leftDrawing roundTrip) = eval (leftDrawing original)
) :=
(open MackeyDiagrams MixedMultiplicationRoundTrip in
by
  intro U K g i ii up down bottom top Weight Labels Drawing ordinary straight stack juxtapose
    mixed parallel onLastTwo leftDrawing rightDrawing splitBottom mergeTop eval multiplier
    selfDot unitWeight gWeight asWeight replaceCase3 replaceCase4 original units roundTrip
  have hg : g ≠ 1 := by
    intro h
    have h' : (1 : ZMod 2) = 0 := congrArg (fun a : K => Multiplicative.toAdd (a : U)) h
    exact (by decide : (1 : ZMod 2) ≠ 0) h'
  have hgg : g * g = 1 := by
    apply Subtype.ext
    change Multiplicative.ofAdd ((1 : ZMod 2) + 1) = Multiplicative.ofAdd 0
    rfl
  have hunit : unitWeight = weight K 1 := identity_weight K
  have hleft : multiplier (leftDrawing original) = 1 := by
    change MixedMultiplicationRoundTrip.multiplier K (leftDrawing (weight K g, unitWeight, weight K g)) = 1
    rw [hunit]
    exact left_multiplier K g hgg
  have hright : multiplier (rightDrawing units) = 1 := by
    change MixedMultiplicationRoundTrip.multiplier K (rightDrawing (unitWeight, unitWeight, unitWeight)) = 1
    rw [hunit]
    exact right_multiplier K
  have hasWeight : asWeight 1 = unitWeight := (weight_of_one K).trans hunit.symm
  -- Case 3 puts the recovered multiplier at the bottom mixed mark.
  have hcase3 : replaceCase3 original = units := by
    change (asWeight (multiplier (leftDrawing original)), unitWeight, unitWeight) = units
    rw [hleft, hasWeight]
  -- Case 4 puts the recovered multiplier at the top mixed mark.
  have hcase4 : replaceCase4 units = units := by
    change (unitWeight, unitWeight, asWeight (multiplier (rightDrawing units))) = units
    rw [hright, hasWeight]
  have htrip : roundTrip = units := by
    change replaceCase4 (replaceCase3 original) = units
    rw [hcase3, hcase4]
  refine ⟨hg, by simpa only [pow_two] using hgg, hleft, htrip, ?_, ?_⟩
  · rw [htrip]
    intro h
    have hfirst := congrArg (fun l : Labels => l.1) h
    change unitWeight = weight K g at hfirst
    exact weight_ne_one K g hg (hfirst.symm.trans hunit)
  · rw [htrip]
    change eval (leftDrawing (unitWeight, unitWeight, unitWeight)) =
      eval (leftDrawing (weight K g, unitWeight, weight K g))
    rw [hunit]
    exact left_same_eval K g hgg)

#print axioms MixedMultiplicationLabelsChangeOnRoundTrip
