import Mathlib.Algebra.MonoidAlgebra.Support
import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

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
  rw [hs, Biset.Hom.id_vertical] at step
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

private theorem threeStage {a b c d : ConjEmbedding T P} {W X Y Z : Word P T}
    (s₀ : Biset.Hom Complex (Word.up a).basis W.basis)
    (m₁ : Biset.Hom Complex X.basis (Word.up b).basis)
    (s₁ : Biset.Hom Complex (Word.up b).basis X.basis)
    (m₂ : Biset.Hom Complex Y.basis (Word.up c).basis)
    (s₂ : Biset.Hom Complex (Word.up c).basis Y.basis)
    (m₃ : Biset.Hom Complex Z.basis (Word.up d).basis)
    (f : Biset.Hom Complex W.basis X.basis) (g : Biset.Hom Complex X.basis Y.basis)
    (h : Biset.Hom Complex Y.basis Z.basis)
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

private theorem recoverEvaluation {a b : ConjEmbedding T P} {W X : Word P T}
    (s : Biset.Hom Complex (Word.up a).basis W.basis)
    (m₀ : Biset.Hom Complex W.basis (Word.up a).basis)
    (m : Biset.Hom Complex X.basis (Word.up b).basis)
    (s₁ : Biset.Hom Complex (Word.up b).basis X.basis)
    (hs : m₀.vertical s = Biset.Hom.id _) (hm : m.vertical s₁ = Biset.Hom.id _)
    (f g : Biset.Hom Complex W.basis X.basis) :
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
