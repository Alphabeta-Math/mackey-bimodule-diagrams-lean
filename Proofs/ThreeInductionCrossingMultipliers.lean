import Mathlib.Algebra.MonoidAlgebra.Support
import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

/-!
Ian Xiao, *Bimodule String Diagrams and the Generalized Mackey Decomposition*,
§ 6.1, pp. 19–20, fixed-boundary setup and proof of Lemma 6.1.
The route has no verified Alphabeta counterpart with numbered proof steps.

InductionRestrictionMergesAndSplits gives the merge formula after choosing
representatives of the symbolic embeddings. GroupElementDotCriterion gives
right-linearity for basis multipliers and evaluation of each eligible group dot.
The inverse merge and split lemmas and the associator basis rule identify the
two ways of merging three strands. Horizontal composition then evaluates on
balanced pairs and eval_linearUpDot_apply extends group-dot evaluation to
finite labels at the single marked vertex.

For support, the article expands the three labels. Here containment of the
product support gives contributing factors, with their eligibility inherited
from the typed dot labels. This also covers zero labels and canceled terms.
-/

namespace ThreeInductionMultiplierProof

open MackeyDiagrams
open scoped Pointwise

noncomputable section

variable {U : Type*} [Group U]
variable {P Q Q' S S' T : Subgroup U}

private abbrev GA (P : Subgroup U) := MonoidAlgebra Complex P

private abbrev along (a : ConjEmbedding Q P) :=
  MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom

private abbrev dotValue {a b : ConjEmbedding Q P} (x : DotLabel Complex a b) : GA P :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element x)

private abbrev merge (a : ConjEmbedding Q P) (b : ConjEmbedding S Q) :=
  (Diagram.mergeUp (R := Complex) a b).eval

private abbrev split (a : ConjEmbedding Q P) (b : ConjEmbedding S Q) :=
  (Diagram.splitUp (R := Complex) a b).eval

private abbrev straight (a : ConjEmbedding Q P) :=
  Biset.Hom.id (R := Complex) (Word.up a).basis

private abbrev dot {a b : ConjEmbedding Q P} (x : DotLabel Complex a b) :=
  x.upDrawing.interpret.eval

private abbrev assoc (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) :=
  (Diagram.associate (R := Complex) (.up a) (.up b) (.up c)).eval

private abbrev unassoc (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) :=
  (Diagram.unassociate (R := Complex) (.up a) (.up b) (.up c)).eval

private abbrev pair (a : ConjEmbedding Q P) (b : ConjEmbedding S Q) :=
  Biset.pairLinear Complex (Word.up a).basis (Word.up b).basis

private def mergeThree (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) :=
  ((merge a b).horizontal (straight c)).vertical (merge (a.comp b) c)

private def splitThree (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) :=
  (split (a.comp b) c).vertical ((split a b).horizontal (straight c))

private theorem mergeSplit (a : ConjEmbedding Q P) (b : ConjEmbedding S Q) :
    (merge a b).vertical (split a b) = Biset.Hom.id _ :=
  Diagram.mergeUp_splitUp a b

private theorem splitMerge (a : ConjEmbedding Q P) (b : ConjEmbedding S Q) :
    (split a b).vertical (merge a b) = Biset.Hom.id _ :=
  Diagram.splitUp_mergeUp a b

private theorem mergeThree_splitThree (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) :
    (mergeThree a b c).vertical (splitThree a b c) = Biset.Hom.id _ := by
  unfold mergeThree splitThree
  refine Biset.Hom.cancel_middle _ _ _ _ (mergeSplit _ _) ?_
  rw [Biset.Hom.horizontal_vertical, mergeSplit, Biset.Hom.id_vertical,
    Biset.Hom.horizontal_id]

private theorem mergeThree_assoc (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) :
    mergeThree a b c = (assoc a b c).vertical
      (((straight a).horizontal (merge b c)).vertical (merge a (b.comp c))) := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro t r
  refine Quotient.inductionOn t (fun xy => ?_)
  rcases xy with ⟨xy, z⟩
  refine Quotient.inductionOn xy (fun xy => ?_)
  rcases xy with ⟨x, y⟩
  let A := Word.up a
  let B := Word.up b
  let C := Word.up c
  let input := Finsupp.single ((A.basis.tensor B.basis).pair C.basis
    (A.basis.pair B.basis x y) z) r
  change (merge (a.comp b) c).toLinearMap
      (((Diagram.horizontal (Diagram.mergeUp (R := Complex) a b) (Diagram.id C)).eval).toLinearMap input) =
    (merge a (b.comp c)).toLinearMap
      (((Diagram.horizontal (Diagram.id A) (Diagram.mergeUp (R := Complex) b c)).eval).toLinearMap
        ((assoc a b c).toLinearMap input))
  dsimp only [input]
  rw [Diagram.eval_horizontal_single (Diagram.mergeUp a b) (Diagram.id C),
    Diagram.eval_mergeUp_single, Diagram.eval_id_apply, Biset.pairLinear_single, one_mul]
  simp only [map_smul]
  rw [Diagram.eval_mergeUp_single, Diagram.eval_associate_single A B C,
    Diagram.eval_horizontal_single (Diagram.id A) (Diagram.mergeUp b c),
    Diagram.eval_id_apply, Diagram.eval_mergeUp_single, Biset.pairLinear_single, one_mul]
  simp only [map_smul]
  rw [Diagram.eval_mergeUp_single]
  simp only [ConjEmbedding.comp_apply, map_mul, mul_assoc]

private theorem splitThree_assoc (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) :
    (splitThree a b c).vertical (assoc a b c) =
      (split a (b.comp c)).vertical ((straight a).horizontal (split b c)) := by
  let m := ((straight a).horizontal (merge b c)).vertical (merge a (b.comp c))
  let s := (split a (b.comp c)).vertical ((straight a).horizontal (split b c))
  have hm : m.vertical s = Biset.Hom.id _ := by
    refine Biset.Hom.cancel_middle _ _ _ _ (mergeSplit _ _) ?_
    rw [Biset.Hom.horizontal_vertical, mergeSplit, Biset.Hom.id_vertical,
      Biset.Hom.horizontal_id]
  have hs : (splitThree a b c).vertical (mergeThree a b c) = Biset.Hom.id _ := by
    unfold splitThree mergeThree
    simp only [Biset.Hom.vertical_assoc]
    rw [← Biset.Hom.vertical_assoc ((split a b).horizontal (straight c)),
      Biset.Hom.horizontal_vertical, splitMerge, Biset.Hom.id_vertical,
      Biset.Hom.horizontal_id, Biset.Hom.id_vertical, splitMerge]
  have step : (splitThree a b c).vertical (assoc a b c) =
      ((splitThree a b c).vertical (mergeThree a b c)).vertical s := by
    rw [mergeThree_assoc]
    change (splitThree a b c).vertical (assoc a b c) =
      ((splitThree a b c).vertical ((assoc a b c).vertical m)).vertical s
    rw [Biset.Hom.vertical_assoc, Biset.Hom.vertical_assoc (assoc a b c), ←
      Biset.Hom.vertical_assoc (splitThree a b c), hm, Biset.Hom.vertical_id]
  rw [hs] at step
  exact step

private theorem mergePair (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (x : GA P) (y : GA Q) :
    (merge a b).toLinearMap (pair a b x.coeff y.coeff) = (x * along a y).coeff := by
  obtain ⟨r, hr⟩ := a.hasRepresentative
  obtain ⟨s, hs⟩ := b.hasRepresentative
  have hr' (q : Q) : r * (q : U) * r⁻¹ ∈ P := hr q ▸ (a.toHom q).property
  have hs' (q : S) : s * (q : U) * s⁻¹ ∈ Q := hs q ▸ (b.toHom q).property
  have ha : a = ConjEmbedding.ofConjugator r hr' :=
    ConjEmbedding.ext (MonoidHom.ext (fun q => Subtype.ext (hr q)))
  have hb : b = ConjEmbedding.ofConjugator s hs' :=
    ConjEmbedding.ext (MonoidHom.ext (fun q => Subtype.ext (hs q)))
  subst a
  subst b
  exact ((InductionRestrictionMergesAndSplits S Q P r s hr' hs').2.1 x y).1

private theorem splitPair (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (x : GA P) :
    (split a b).toLinearMap x.coeff = pair a b x.coeff (1 : GA Q).coeff := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    simp only [MonoidAlgebra.coeff_zero, map_zero, LinearMap.zero_apply]
  | add y z hy hz =>
    simp only [MonoidAlgebra.coeff_add, map_add, LinearMap.add_apply, hy, hz]
  | single g r =>
    change (split a b).toLinearMap (Finsupp.single g r) =
      pair a b (Finsupp.single g r) (Finsupp.single 1 1)
    rw [Biset.pairLinear_single, mul_one]
    exact Diagram.eval_splitUp_single a b g r

private theorem dotEval {a b : ConjEmbedding Q P} (x : DotLabel Complex a b) (z : GA P) :
    (dot x).toLinearMap z.coeff = (z * dotValue x).coeff := by
  change x.upDrawing.interpret.eval.toLinearMap z.coeff = _
  rw [DotLabel.eval_upDrawing, Diagram.eval_linearUpDot_apply]
  unfold dotValue
  induction x using Finsupp.induction_linear with
  | zero =>
    simp
  | add f g hf hg =>
    simp only [map_add, hf, hg, Finsupp.mapDomain_add, MonoidAlgebra.ofCoeff_add,
      mul_add, MonoidAlgebra.coeff_add]
  | single d r =>
    rw [freeLift_single, Finsupp.mapDomain_single]
    obtain ⟨u, hu⟩ := a.hasRepresentative
    obtain ⟨v, hv⟩ := b.hasRepresentative
    have hu' (q : Q) : u * (q : U) * u⁻¹ ∈ P := hu q ▸ (a.toHom q).property
    have hv' (q : Q) : v * (q : U) * v⁻¹ ∈ P := hv q ▸ (b.toHom q).property
    have ha : a = ConjEmbedding.ofConjugator u hu' :=
      ConjEmbedding.ext (MonoidHom.ext (fun q => Subtype.ext (hu q)))
    have hb : b = ConjEmbedding.ofConjugator v hv' :=
      ConjEmbedding.ext (MonoidHom.ext (fun q => Subtype.ext (hv q)))
    subst a
    subst b
    rw [((GroupElementDotCriterion Q P u v hu' hv').2.2.1 d z).1]
    have h : (MonoidAlgebra.single d.element r : GA P) =
        r • MonoidAlgebra.single d.element 1 := by simp [MonoidAlgebra.smul_single]
    change r • (z * MonoidAlgebra.single d.element 1).coeff =
      (z * MonoidAlgebra.single d.element r).coeff
    rw [h, mul_smul_comm]
    rfl

private abbrev cross {a : ConjEmbedding Q P} {b : ConjEmbedding S Q}
    {a' : ConjEmbedding Q' P} {b' : ConjEmbedding S Q'}
    (x : DotLabel Complex (a.comp b) (a'.comp b')) :=
  (merge a b).vertical ((dot x).vertical (split a' b'))

private abbrev leftCross (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q') (c : ConjEmbedding T S)
    (x : DotLabel Complex (a.comp b) (a'.comp b')) :=
  (cross (a := a) (b := b) (a' := a') (b' := b') x).horizontal (straight c)

private abbrev rightCross (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) (b' : ConjEmbedding S' Q) (c' : ConjEmbedding T S')
    (x : DotLabel Complex (b.comp c) (b'.comp c')) :=
  (assoc a b c).vertical (((straight a).horizontal
    (cross (a := b) (b := c) (a' := b') (b' := c') x)).vertical (unassoc a b' c'))

private theorem cross_cancel (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q')
    (x : DotLabel Complex (a.comp b) (a'.comp b')) :
    (split a b).vertical ((cross x).vertical (merge a' b')) = dot x := by
  simp only [cross, Biset.Hom.vertical_assoc]
  rw [← Biset.Hom.vertical_assoc (split a b), splitMerge, Biset.Hom.id_vertical,
    splitMerge, Biset.Hom.vertical_id]

-- Section 6.1, proof of Lemma 6.1. A crossing on the left contributes the
-- dot itself. The split–merge equalities identify its two merged boundaries.
private theorem leftCross_rule (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q') (c : ConjEmbedding T S)
    (x : DotLabel Complex (a.comp b) (a'.comp b')) (z : GA P) :
    ((splitThree a b c).vertical ((leftCross a b a' b' c x).vertical
      (mergeThree a' b' c))).toLinearMap z.coeff = (z * dotValue x).coeff := by
  have h : (splitThree a b c).vertical ((leftCross a b a' b' c x).vertical
      (mergeThree a' b' c)) = (split (a.comp b) c).vertical
        (((dot x).horizontal (straight c)).vertical (merge (a'.comp b') c)) := by
    unfold splitThree mergeThree leftCross
    simp only [Biset.Hom.vertical_assoc]
    rw [← Biset.Hom.vertical_assoc ((_ : Biset.Hom Complex _ _).horizontal (straight c))
          ((merge a' b').horizontal (straight c)),
      Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical,
      ← Biset.Hom.vertical_assoc ((split a b).horizontal (straight c)),
      Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical, cross_cancel]
  rw [h]
  change (merge (a'.comp b') c).toLinearMap
    (((dot x).horizontal (straight c)).toLinearMap
      ((split (a.comp b) c).toLinearMap z.coeff)) = _
  rw [splitPair, Biset.Hom.horizontal_pairLinear, dotEval]
  change (merge (a'.comp b') c).toLinearMap
    (pair (a'.comp b') c (z * dotValue x).coeff (1 : GA S).coeff) = _
  rw [mergePair, map_one, mul_one]

-- On the right we associate before crossing. The merge evaluates the right
-- label through the exterior embedding, including when its coefficients cancel.
set_option backward.isDefEq.respectTransparency false in
private theorem rightCross_rule (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) (b' : ConjEmbedding S' Q) (c' : ConjEmbedding T S')
    (x : DotLabel Complex (b.comp c) (b'.comp c')) (z : GA P) :
    ((splitThree a b c).vertical ((rightCross a b c b' c' x).vertical
      (mergeThree a b' c'))).toLinearMap z.coeff = (z * along a (dotValue x)).coeff := by
  have finish : (unassoc a b' c').vertical (mergeThree a b' c') =
      ((straight a).horizontal (merge b' c')).vertical (merge a (b'.comp c')) := by
    rw [mergeThree_assoc]
    have cancel : (unassoc a b' c').vertical (assoc a b' c') = Biset.Hom.id _ :=
      Biset.unassociate_associate
    rw [← Biset.Hom.vertical_assoc (unassoc a b' c'), cancel, Biset.Hom.id_vertical]
  have h : (splitThree a b c).vertical ((rightCross a b c b' c' x).vertical
      (mergeThree a b' c')) = (split a (b.comp c)).vertical
        (((straight a).horizontal (dot x)).vertical (merge a (b'.comp c'))) := by
    unfold rightCross
    simp only [Biset.Hom.vertical_assoc]
    rw [finish, ← Biset.Hom.vertical_assoc (splitThree a b c),
      splitThree_assoc]
    simp only [Biset.Hom.vertical_assoc]
    rw [
      ← Biset.Hom.vertical_assoc ((straight a).horizontal (cross x)),
      Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical,
      ← Biset.Hom.vertical_assoc ((straight a).horizontal (split b c)),
      Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical, cross_cancel]
  rw [h]
  change (merge a (b'.comp c')).toLinearMap
    (((straight a).horizontal (dot x)).toLinearMap
      ((split a (b.comp c)).toLinearMap z.coeff)) = _
  rw [splitPair, Biset.Hom.horizontal_pairLinear, dotEval, one_mul]
  change (merge a (b'.comp c')).toLinearMap
    (pair a (b'.comp c') z.coeff (dotValue x).coeff) = _
  rw [mergePair]

private abbrev Supported {a b : ConjEmbedding Q P} (x : GA P) :=
  ∀ p ∈ x.coeff.support, ∀ q, a.toHom q * p = p * b.toHom q

-- The article expands triples of dots. Membership in the support of a product
-- gives a contributing pair even when other terms cancel in the coefficient.
private theorem supportedMul {a b c : ConjEmbedding Q P} {x y : GA P}
    (hx : Supported (a := a) (b := b) x) (hy : Supported (a := b) (b := c) y) :
    Supported (a := a) (b := c) (x * y) := by
  classical
  intro p hp q
  obtain ⟨s, hs, t, ht, rfl⟩ :=
    Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset x y hp)
  simp only [← mul_assoc, hx s hs q]
  rw [mul_assoc s, hy t ht q, ← mul_assoc]

private theorem supportedDot {a b : ConjEmbedding Q P} (x : DotLabel Complex a b) :
    Supported (a := a) (b := b) (dotValue x) := by
  classical
  intro p hp
  change p ∈ (Finsupp.mapDomain Dot.element x).support at hp
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
  exact d.intertwines

private theorem supportedLeft (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q') (c : ConjEmbedding T S)
    (x : DotLabel Complex (a.comp b) (a'.comp b')) :
    Supported (a := (a.comp b).comp c) (b := (a'.comp b').comp c) (dotValue x) :=
  fun p hp t => supportedDot x p hp (c.toHom t)

private theorem supportedRight (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (c : ConjEmbedding T S) (b' : ConjEmbedding S' Q) (c' : ConjEmbedding T S')
    (x : DotLabel Complex (b.comp c) (b'.comp c')) :
    Supported (a := (a.comp b).comp c) (b := (a.comp b').comp c')
      (along a (dotValue x)) := by
  classical
  intro p hp t
  change p ∈ (Finsupp.mapDomain a.toHom (dotValue x).coeff).support at hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
  simpa only [map_mul, ConjEmbedding.comp_apply] using congrArg a.toHom (supportedDot x q hq t)

private theorem merged_vertical {A B C D E F : Biset P T}
    (s : Biset.Hom Complex A B) (d : Biset.Hom Complex B C)
    (m : Biset.Hom Complex C D) (t : Biset.Hom Complex D C)
    (e : Biset.Hom Complex C E) (n : Biset.Hom Complex E F)
    (h : m.vertical t = Biset.Hom.id _) :
    s.vertical ((d.vertical e).vertical n) =
      (s.vertical (d.vertical m)).vertical (t.vertical (e.vertical n)) := by
  simp only [Biset.Hom.vertical_assoc]
  rw [← Biset.Hom.vertical_assoc m, h, Biset.Hom.id_vertical]

private theorem leftAct (a : ConjEmbedding Q P) (g : P) (z : GA P) :
    (Word.up a).basis.actLinear Complex (g, 1) z.coeff =
      (MonoidAlgebra.single g 1 * z).coeff := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [MonoidAlgebra.coeff_add, map_add, mul_add, hx, hy]
  | single x r =>
    rw [MonoidAlgebra.coeff_single, Biset.actLinear_single,
      MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.coeff_single]
    change Finsupp.single (g * x * (a.toHom 1)⁻¹) r = Finsupp.single (g * x) r
    simp

private theorem evalAtOne {a b : ConjEmbedding Q P}
    (f : Biset.Hom Complex (Word.up a).basis (Word.up b).basis) (z : GA P) :
    MonoidAlgebra.ofCoeff (f.toLinearMap z.coeff) =
      z * MonoidAlgebra.ofCoeff (f.toLinearMap (1 : GA P).coeff) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [MonoidAlgebra.coeff_add, map_add, MonoidAlgebra.ofCoeff_add, add_mul, hx, hy]
  | single g r =>
    have he := f.commutes (g, 1) (1 : GA P).coeff
    have h₁ := leftAct a g (1 : GA P)
    rw [mul_one] at h₁
    rw [h₁] at he
    have h₂ := leftAct b g (MonoidAlgebra.ofCoeff (f.toLinearMap (1 : GA P).coeff))
    rw [MonoidAlgebra.coeff_ofCoeff] at h₂
    rw [h₂] at he
    have hr : (MonoidAlgebra.single g r : GA P) = r • MonoidAlgebra.single g 1 := by
      simp [MonoidAlgebra.smul_single]
    rw [hr, smul_mul_assoc]
    change MonoidAlgebra.ofCoeff (f.toLinearMap
        (r • (MonoidAlgebra.single g 1 : GA P).coeff)) = _
    rw [map_smul, he]
    rfl

private theorem threeStage {a b c d : ConjEmbedding T P} {W X Y Z : Biset P T}
    (s₀ : Biset.Hom Complex (Word.up a).basis W)
    (m₁ : Biset.Hom Complex X (Word.up b).basis)
    (s₁ : Biset.Hom Complex (Word.up b).basis X)
    (m₂ : Biset.Hom Complex Y (Word.up c).basis)
    (s₂ : Biset.Hom Complex (Word.up c).basis Y)
    (m₃ : Biset.Hom Complex Z (Word.up d).basis)
    (f : Biset.Hom Complex W X) (g : Biset.Hom Complex X Y)
    (h : Biset.Hom Complex Y Z)
    (i₁ : m₁.vertical s₁ = Biset.Hom.id _) (i₂ : m₂.vertical s₂ = Biset.Hom.id _)
    (r₁ r₂ r₃ : GA P)
    (e₁ : ∀ z : GA P, (s₀.vertical (f.vertical m₁)).toLinearMap z.coeff = (z * r₁).coeff)
    (e₂ : ∀ z : GA P, (s₁.vertical (g.vertical m₂)).toLinearMap z.coeff = (z * r₂).coeff)
    (e₃ : ∀ z : GA P, (s₂.vertical (h.vertical m₃)).toLinearMap z.coeff = (z * r₃).coeff) :
    MonoidAlgebra.ofCoeff
      ((s₀.vertical ((f.vertical (g.vertical h)).vertical m₃)).toLinearMap (1 : GA P).coeff) =
      r₁ * r₂ * r₃ := by
  rw [merged_vertical s₀ f m₁ s₁ (g.vertical h) m₃ i₁,
    merged_vertical s₁ g m₂ s₂ h m₃ i₂]
  change MonoidAlgebra.ofCoeff ((s₂.vertical (h.vertical m₃)).toLinearMap
    ((s₁.vertical (g.vertical m₂)).toLinearMap
      ((s₀.vertical (f.vertical m₁)).toLinearMap (1 : GA P).coeff))) = _
  rw [e₁, one_mul, e₂, e₃, MonoidAlgebra.ofCoeff_coeff]

private theorem recoverEvaluation {a b : ConjEmbedding T P} {W X : Biset P T}
    (s : Biset.Hom Complex (Word.up a).basis W)
    (m₀ : Biset.Hom Complex W (Word.up a).basis)
    (m : Biset.Hom Complex X (Word.up b).basis)
    (s₁ : Biset.Hom Complex (Word.up b).basis X)
    (hs : m₀.vertical s = Biset.Hom.id _) (hm : m.vertical s₁ = Biset.Hom.id _)
    (f g : Biset.Hom Complex W X) :
    f = g ↔ MonoidAlgebra.ofCoeff
        ((s.vertical (f.vertical m)).toLinearMap (1 : GA P).coeff) =
      MonoidAlgebra.ofCoeff ((s.vertical (g.vertical m)).toLinearMap (1 : GA P).coeff) := by
  constructor
  · rintro rfl
    rfl
  · intro e
    have hc : s.vertical (f.vertical m) = s.vertical (g.vertical m) := by
      apply Biset.Hom.ext
      apply LinearMap.ext
      intro w
      let z : GA P := MonoidAlgebra.ofCoeff w
      have hz := (evalAtOne (s.vertical (f.vertical m)) z).trans
        ((congrArg (fun x => z * x) e).trans (evalAtOne (s.vertical (g.vertical m)) z).symm)
      exact congrArg MonoidAlgebra.coeff hz
    have he := congrArg (fun k : Biset.Hom Complex (Word.up a).basis (Word.up b).basis =>
      (m₀.vertical k).vertical s₁) hc
    simpa only [Biset.Hom.vertical_assoc, ← Biset.Hom.vertical_assoc m, hm, Biset.Hom.id_vertical,
      Biset.Hom.vertical_id, ← Biset.Hom.vertical_assoc m₀ s, hs] using he

private theorem centralizer_iff {a b : ConjEmbedding T P} {u v : U}
    (ha : ∀ t : T, (a.toHom t : U) = u * (t : U) * u⁻¹)
    (hb : ∀ t : T, (b.toHom t : U) = v * (t : U) * v⁻¹) (p : P) :
    (∀ t : T, a.toHom t * p = p * b.toHom t) ↔
      u⁻¹ * (p : U) * v ∈ Subgroup.centralizer (T : Set U) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    have he : (u * t * u⁻¹) * (p : U) = (p : U) * (v * t * v⁻¹) := by
      simpa only [Subgroup.coe_mul, ha, hb] using congrArg Subtype.val (h ⟨t, ht⟩)
    calc
      t * (u⁻¹ * (p : U) * v) = u⁻¹ * ((u * t * u⁻¹) * (p : U)) * v := by group
      _ = u⁻¹ * ((p : U) * (v * t * v⁻¹)) * v := by rw [he]
      _ = (u⁻¹ * (p : U) * v) * t := by group
  · intro h t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]
    calc
      (u * (t : U) * u⁻¹) * (p : U) = u * ((t : U) * (u⁻¹ * (p : U) * v)) * v⁻¹ := by group
      _ = u * ((u⁻¹ * (p : U) * v) * (t : U)) * v⁻¹ := by rw [h _ t.property]
      _ = (p : U) * (v * (t : U) * v⁻¹) := by group

end

end ThreeInductionMultiplierProof

open ThreeInductionMultiplierProof MackeyDiagrams


theorem ThreeInductionCrossingMultipliers : (∀ {U : Type*} [Group U] (G A D F C E : Subgroup U)
    (repGA repAD repDF repGC repCE repEF : U)
    (hGA : ∀ a : A, repGA * (a : U) * repGA⁻¹ ∈ G)
    (hAD : ∀ d : D, repAD * (d : U) * repAD⁻¹ ∈ A)
    (hDF : ∀ f : F, repDF * (f : U) * repDF⁻¹ ∈ D)
    (hGC : ∀ c : C, repGC * (c : U) * repGC⁻¹ ∈ G)
    (hCE : ∀ e : E, repCE * (e : U) * repCE⁻¹ ∈ C)
    (hEF : ∀ f : F, repEF * (f : U) * repEF⁻¹ ∈ E),
  let ga := MackeyDiagrams.ConjEmbedding.ofConjugator repGA hGA
  let ad := MackeyDiagrams.ConjEmbedding.ofConjugator repAD hAD
  let df := MackeyDiagrams.ConjEmbedding.ofConjugator repDF hDF
  let gc := MackeyDiagrams.ConjEmbedding.ofConjugator repGC hGC
  let ce := MackeyDiagrams.ConjEmbedding.ofConjugator repCE hCE
  let ef := MackeyDiagrams.ConjEmbedding.ofConjugator repEF hEF
  let u := repGA * repAD * repDF
  let v := repGC * repCE * repEF
  let bottomPair := MackeyDiagrams.ConjEmbedding.comp ga ad
  let topPair := MackeyDiagrams.ConjEmbedding.comp gc ce
  let bottomEmbedding := MackeyDiagrams.ConjEmbedding.comp bottomPair df
  let topEmbedding := MackeyDiagrams.ConjEmbedding.comp topPair ef
  let word := fun {P Q S T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (c : MackeyDiagrams.ConjEmbedding T S) =>
    MackeyDiagrams.Word.tensor
      (MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b))
      (MackeyDiagrams.Word.up c)
  let bottom := word ga ad df
  let top := word gc ce ef
  let straight := fun {P Q : Subgroup U} (a : MackeyDiagrams.ConjEmbedding Q P) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
  let merge := fun {P Q S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.mergeUp a b)
  let split := fun {P Q S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.splitUp a b)
  let splitBottom :=
    MackeyDiagrams.LabelledDrawing.vertical (split bottomPair df)
      (MackeyDiagrams.LabelledDrawing.horizontal (split ga ad) (straight df))
  let mergeTop :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (merge gc ce) (straight ef))
      (merge topPair ef)
  let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let mergedEvaluation := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top)
      (z : MonoidAlgebra Complex G) =>
    MonoidAlgebra.ofCoeff
      (MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.interpret
            (MackeyDiagrams.LabelledDrawing.vertical splitBottom
              (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
        (MonoidAlgebra.coeff z))
  let multiplier := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    mergedEvaluation drawing 1
  let along := fun {H K : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H K) =>
    MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom a)
  let dotValue := fun {H K : Subgroup U} {a b : MackeyDiagrams.ConjEmbedding H K}
      (weights : MackeyDiagrams.DotLabel Complex a b) =>
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain (MackeyDiagrams.Dot.element (a := a) (b := b)) weights)
  let allowed := fun p : G => u⁻¹ * (p : U) * v ∈ Subgroup.centralizer (F : Set U)
  let realizes := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top)
      (formula : MonoidAlgebra Complex G) =>
    multiplier drawing = formula ∧
      ∀ p ∈ Finsupp.support (MonoidAlgebra.coeff (multiplier drawing)), allowed p
  let crossing := fun {P Q Q' S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
        (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
    MackeyDiagrams.LabelledDrawing.vertical (merge a b)
      (MackeyDiagrams.LabelledDrawing.vertical (MackeyDiagrams.DotLabel.upDrawing weights)
        (split a' b'))
  let crossLeft := fun {P Q Q' S T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
      (c : MackeyDiagrams.ConjEmbedding T S)
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
        (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
    MackeyDiagrams.LabelledDrawing.horizontal (crossing a b a' b' weights)
      (straight c)
  let crossRight := fun {P Q S S' T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P)
      (b : MackeyDiagrams.ConjEmbedding S Q) (c : MackeyDiagrams.ConjEmbedding T S)
      (b' : MackeyDiagrams.ConjEmbedding S' Q) (c' : MackeyDiagrams.ConjEmbedding T S')
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp b c)
        (MackeyDiagrams.ConjEmbedding.comp b' c')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.associate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b)
          (MackeyDiagrams.Word.up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (straight a)
          (crossing b c b' c' weights))
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.unassociate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b')
            (MackeyDiagrams.Word.up c'))))
  (∀ f : F,
    (MackeyDiagrams.ConjEmbedding.toHom bottomEmbedding f : U) = u * (f : U) * u⁻¹ ∧
    (MackeyDiagrams.ConjEmbedding.toHom topEmbedding f : U) = v * (f : U) * v⁻¹) ∧
  (∀ (map : LinearMap (RingHom.id (MonoidAlgebra Complex G)) (MonoidAlgebra Complex G)
      (MonoidAlgebra Complex G)) (z : MonoidAlgebra Complex G),
    map z = z * map 1) ∧
  (∀ (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) (z : MonoidAlgebra Complex G),
    mergedEvaluation drawing z = z * multiplier drawing) ∧
  (∀ d e : MackeyDiagrams.LabelledDrawing Complex bottom top,
    evaluate d = evaluate e ↔ multiplier d = multiplier e) ∧
  (∀ p : G,
    let rightMul := fun z : MonoidAlgebra Complex G => z * MonoidAlgebra.single p 1
    let rightLinear := ∀ (z : MonoidAlgebra Complex G) (r : MonoidAlgebra Complex F),
      rightMul (z * along bottomEmbedding r) = rightMul z * along topEmbedding r
    let intertwines := ∀ f : F,
      (u * (f : U) * u⁻¹) * (p : U) = (p : U) * (v * (f : U) * v⁻¹)
    (rightLinear ↔ intertwines) ∧ (intertwines ↔ allowed p)) ∧
  (∀ (B : Subgroup U) (gb : MackeyDiagrams.ConjEmbedding B G)
      (bd : MackeyDiagrams.ConjEmbedding D B) (be : MackeyDiagrams.ConjEmbedding E B)
      (x₁ : MackeyDiagrams.DotLabel Complex bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd))
      (x₂ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp bd df)
        (MackeyDiagrams.ConjEmbedding.comp be ef))
      (x₃ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp gb be) topPair),
    let left := MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ad gb bd df x₁)
      (MackeyDiagrams.LabelledDrawing.vertical (crossRight gb bd df be ef x₂) (crossLeft gb be gc ce ef x₃))
    realizes left (dotValue x₁ * along gb (dotValue x₂) * dotValue x₃)) ∧
  (∀ (B' : Subgroup U) (ab' : MackeyDiagrams.ConjEmbedding B' A)
      (cb' : MackeyDiagrams.ConjEmbedding B' C) (b'f : MackeyDiagrams.ConjEmbedding F B')
      (y₁ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ad df)
        (MackeyDiagrams.ConjEmbedding.comp ab' b'f))
      (y₂ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ga ab')
        (MackeyDiagrams.ConjEmbedding.comp gc cb'))
      (y₃ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp cb' b'f)
        (MackeyDiagrams.ConjEmbedding.comp ce ef)),
    let right := MackeyDiagrams.LabelledDrawing.vertical (crossRight ga ad df ab' b'f y₁)
      (MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ab' gc cb' b'f y₂) (crossRight gc cb' b'f ce ef y₃))
    realizes right (along ga (dotValue y₁) * dotValue y₂ * along gc (dotValue y₃)))) :=
(by
  classical
  intro U inst G A D F C E repGA repAD repDF repGC repCE repEF
    hGA hAD hDF hGC hCE hEF ga ad df gc ce ef u v bottomPair topPair
    bottomEmbedding topEmbedding word bottom top straightDrawing mergeDrawing splitDrawing
    splitBottom mergeTop evaluate mergedEvaluation multiplier alongBoundary dotValueBoundary
    allowed realizes crossing crossLeft crossRight
  have hBottom (f : F) : (bottomEmbedding.toHom f : U) = u * (f : U) * u⁻¹ := by
    simp only [bottomEmbedding, bottomPair, ga, ad, df, u, ConjEmbedding.comp_apply,
      ConjEmbedding.ofConjugator_apply]
    group
  have hTop (f : F) : (topEmbedding.toHom f : U) = v * (f : U) * v⁻¹ := by
    simp only [topEmbedding, topPair, gc, ce, ef, v, ConjEmbedding.comp_apply,
      ConjEmbedding.ofConjugator_apply]
    group
  have hu (f : F) : u * (f : U) * u⁻¹ ∈ G := hBottom f ▸ (bottomEmbedding.toHom f).property
  have hv (f : F) : v * (f : U) * v⁻¹ ∈ G := hTop f ▸ (topEmbedding.toHom f).property
  have hbe : bottomEmbedding = ConjEmbedding.ofConjugator u hu :=
    ConjEmbedding.ext (MonoidHom.ext (fun f => Subtype.ext (hBottom f)))
  have hte : topEmbedding = ConjEmbedding.ofConjugator v hv :=
    ConjEmbedding.ext (MonoidHom.ext (fun f => Subtype.ext (hTop f)))
  -- Fixed-boundary part of the proof of Lemma 6.1. Evaluate at the regular
  -- generator and use the inverse trivalent maps to recover the original map.
  refine ⟨fun f => ⟨hBottom f, hTop f⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro map z
    calc
      map z = map (z • 1) := congrArg map (mul_one z).symm
      _ = z * map 1 := map.map_smul z 1
  · intro drawing z
    exact evalAtOne ((splitThree ga ad df).vertical
      (drawing.interpret.eval.vertical (mergeThree gc ce ef))) z
  · intro d e
    exact recoverEvaluation (a := bottomEmbedding) (b := topEmbedding) (splitThree ga ad df) (mergeThree ga ad df)
      (mergeThree gc ce ef) (splitThree gc ce ef) (mergeThree_splitThree ga ad df)
      (mergeThree_splitThree gc ce ef) d.interpret.eval e.interpret.eval
  · intro p rightMul rightLinear intertwines
    have he : (∀ f : F, bottomEmbedding.toHom f * p = p * topEmbedding.toHom f) ↔
        intertwines := by
      constructor
      · intro h f
        simpa only [intertwines, Subgroup.coe_mul, hBottom, hTop] using
          congrArg Subtype.val (h f)
      · intro h f
        apply Subtype.ext
        simpa only [Subgroup.coe_mul, hBottom, hTop] using h f
    refine ⟨?_, he.symm.trans (centralizer_iff hBottom hTop p)⟩
    have hl := ((GroupElementDotCriterion F G u v hu hv).2.1 p).1
    have hright : rightLinear ↔ ∀ f : F, bottomEmbedding.toHom f * p = p * topEmbedding.toHom f := by
      dsimp only [rightLinear, rightMul, alongBoundary]
      rw [hbe, hte]
      exact hl
    exact hright.trans he
  -- Diagram order is bottom to top in the two shapes of Section 6.1.
  -- Each eligible summand stays eligible under whiskering and multiplication.
  · intro B gb bd be x₁ x₂ x₃ left
    have formula : multiplier left = dotValue x₁ * along gb (dotValue x₂) * dotValue x₃ :=
      threeStage (a := bottomEmbedding) (b := (gb.comp bd).comp df)
        (c := (gb.comp be).comp ef) (d := topEmbedding)
        (splitThree ga ad df) (mergeThree gb bd df) (splitThree gb bd df)
        (mergeThree gb be ef) (splitThree gb be ef) (mergeThree gc ce ef)
        (leftCross ga ad gb bd df x₁) (rightCross gb bd df be ef x₂)
        (leftCross gb be gc ce ef x₃)
        (mergeThree_splitThree gb bd df) (mergeThree_splitThree gb be ef)
        _ _ _ (leftCross_rule ga ad gb bd df x₁) (rightCross_rule gb bd df be ef x₂)
        (leftCross_rule gb be gc ce ef x₃)
    refine ⟨formula, ?_⟩
    intro p hp
    rw [formula] at hp
    have hs := supportedMul (supportedMul (supportedLeft ga ad gb bd df x₁)
      (supportedRight gb bd df be ef x₂)) (supportedLeft gb be gc ce ef x₃)
    exact (centralizer_iff hBottom hTop p).mp (hs p hp)
  · intro B' ab' cb' b'f y₁ y₂ y₃ right
    have formula : multiplier right = along ga (dotValue y₁) * dotValue y₂ * along gc (dotValue y₃) :=
      threeStage (a := bottomEmbedding) (b := (ga.comp ab').comp b'f)
        (c := (gc.comp cb').comp b'f) (d := topEmbedding)
        (splitThree ga ad df) (mergeThree ga ab' b'f) (splitThree ga ab' b'f)
        (mergeThree gc cb' b'f) (splitThree gc cb' b'f) (mergeThree gc ce ef)
        (rightCross ga ad df ab' b'f y₁) (leftCross ga ab' gc cb' b'f y₂)
        (rightCross gc cb' b'f ce ef y₃)
        (mergeThree_splitThree ga ab' b'f) (mergeThree_splitThree gc cb' b'f)
        _ _ _ (rightCross_rule ga ad df ab' b'f y₁) (leftCross_rule ga ab' gc cb' b'f y₂)
        (rightCross_rule gc cb' b'f ce ef y₃)
    refine ⟨formula, ?_⟩
    intro p hp
    rw [formula] at hp
    have hs := supportedMul (supportedMul (supportedRight ga ad df ab' b'f y₁)
      (supportedLeft ga ab' gc cb' b'f y₂)) (supportedRight gc cb' b'f ce ef y₃)
    exact (centralizer_iff hBottom hTop p).mp (hs p hp)
)
