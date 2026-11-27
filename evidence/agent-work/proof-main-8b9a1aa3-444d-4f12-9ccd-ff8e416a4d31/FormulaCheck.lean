import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.FiniteParabolicJoinBlocks
namespace OverlapReplacementAux

open MackeyDiagrams MackeyDiagrams.Generator
open scoped BigOperators

noncomputable section

variable {U : Type} [Group U] {D E B : Subgroup U}

private abbrev T (U : Type) [Group U] : Subgroup U := ⊥
private abbrev a (U : Type) [Group U] := ConjEmbedding.id (T U)
private abbrev incl {H K : Subgroup U} (h : H ≤ K) : ConjEmbedding H K :=
  ⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩
private abbrev fromBot (H : Subgroup U) := incl (show T U ≤ H from bot_le)

private theorem bot_one (z : T U) : z = 1 :=
  Subtype.ext (Subgroup.mem_bot.mp z.property)

private abbrev dot {H : Subgroup U} {α β : ConjEmbedding (T U) H} (x : H) : Dot α β :=
  ⟨x, fun y => by simp [bot_one y]⟩

private abbrev qLeft (hEB : E ≤ B)
    (p : ((Word.up (a U)).tensor (Word.down (fromBot E))).basis.carrier) :=
  mixedProduct (fromBot B) (incl hEB)
    (mixedMultiplicationBasis (fromBot B) (incl hEB) (a U) (fromBot E) (dot 1) p)

private abbrev qRight (r : D)
    (p : ((Word.up (a U)).tensor (Word.down (a U))).basis.carrier) :=
  mixedProduct (fromBot D) (fromBot D)
    (mixedMultiplicationBasis (fromBot D) (fromBot D) (a U) (a U) (dot r) p)

private abbrev qLeftPoint (y : E) :
    ((Word.up (a U)).tensor (Word.down (fromBot E))).basis.carrier :=
  (Biset.induction (a U)).pair (Biset.restriction (fromBot E)) 1 y

private abbrev qRightPoint (U : Type) [Group U] :
    ((Word.up (a U)).tensor (Word.down (a U))).basis.carrier :=
  (Biset.induction (a U)).pair (Biset.restriction (a U)) 1 1

private theorem left_representative (p : ((Word.up (a U)).tensor
    (Word.down (fromBot E))).basis.carrier) : ∃ y : E, p = qLeftPoint y := by
  refine Quotient.inductionOn p (fun ⟨z, y⟩ => ?_)
  exact ⟨y, congrArg (fun t => (Biset.induction (a U)).pair (Biset.restriction (fromBot E)) t y)
    (bot_one z)⟩

private theorem right_representative (p : ((Word.up (a U)).tensor
    (Word.down (a U))).basis.carrier) : p = qRightPoint U := by
  refine Quotient.inductionOn p (fun ⟨y, z⟩ => ?_)
  change (Biset.induction (a U)).pair (Biset.restriction (a U)) y z = _
  rw [bot_one y, bot_one z]

private theorem qLeft_eq (hEB : E ≤ B) (y : E) :
    qLeft hEB (qLeftPoint y) = (incl hEB).toHom y := by
  change mixedProduct _ _ (mixedPair (fromBot B) (incl hEB)
    ((fromBot B).toHom 1 * 1 * (incl hEB).toHom y)) = _
  rw [mixedProduct_mixedPair, map_one, one_mul, one_mul]

private theorem qRight_eq (r : D) (p : ((Word.up (a U)).tensor
    (Word.down (a U))).basis.carrier) : qRight r p = r := by
  rw [right_representative p]
  change mixedProduct _ _ (mixedPair (fromBot D) (fromBot D)
    ((fromBot D).toHom 1 * r * (fromBot D).toHom 1)) = _
  rw [mixedProduct_mixedPair, map_one, one_mul, mul_one]

private theorem qLeft_injective (hEB : E ≤ B) : Function.Injective (qLeft hEB) := by
  intro p p' hp
  obtain ⟨y, rfl⟩ := left_representative p
  obtain ⟨y', rfl⟩ := left_representative p'
  rw [qLeft_eq, qLeft_eq] at hp
  exact congrArg qLeftPoint ((incl hEB).injective hp)

private theorem qRight_injective (r : D) : Function.Injective (qRight r) :=
  fun p p' _ => (right_representative p).trans (right_representative p').symm

private theorem finite_fiber {X Y : Type} {f : X → Y} (hf : Function.Injective f) (y : Y) :
    Set.Finite {x | f x = y} := by
  by_cases h : ∃ x, f x = y
  · obtain ⟨x, hx⟩ := h
    exact (Set.finite_singleton x).subset (fun z hz => Set.mem_singleton_iff.mpr
      (hf (hz.trans hx.symm)))
  · exact Set.finite_empty.subset (fun z hz => (h ⟨z, hz⟩).elim)

private theorem finite_mixed {L K H M : Subgroup U}
    (α : ConjEmbedding K M) (β : ConjEmbedding H M)
    (γ : ConjEmbedding L K) (δ : ConjEmbedding L H) (d : Dot (α.comp γ) (β.comp δ))
    (h : ∀ z, Set.Finite {p | mixedProduct α β (mixedMultiplicationBasis α β γ δ d p) = z})
    (z : _) : Set.Finite {p | mixedMultiplicationBasis α β γ δ d p = z} :=
  (h (mixedProduct α β z)).subset (fun _ hp => congrArg (mixedProduct α β) hp)

private abbrev drawId {H K : Subgroup U} (p : Word H K) :=
  LabelledDrawing.ordinary (Diagram.id (R := Complex) p)

private abbrev atLeft {K J J' L M : Subgroup U}
    {p : Word K J} {q : Word J L} {p' : Word K J'} {q' : Word J' L}
    (tail : Word L M) (cross : LabelledDrawing Complex (p.tensor q) (p'.tensor q')) :=
  LabelledDrawing.vertical (.ordinary (.unassociate p q tail))
    (.vertical (.horizontal cross (drawId tail)) (.ordinary (.associate p' q' tail)))

private abbrev middle (hDB : D ≤ B) (hEB : E ≤ B) (r : D) (s : E) :
    Dot ((incl hDB).comp (fromBot D)) ((incl hEB).comp (fromBot E)) :=
  dot (((incl hDB).toHom r)⁻¹ * (incl hEB).toHom s)

private abbrev leftUpper (hEB : E ≤ B) :
    ProjectionDot.Mixed (fromBot B) (incl hEB) (a U) (fromBot E) :=
  ⟨dot 1, finite_mixed _ _ _ _ _ (finite_fiber (qLeft_injective hEB))⟩

private abbrev rightLower (r : D) :
    ProjectionDot.Mixed (fromBot D) (fromBot D) (a U) (a U) :=
  ⟨dot r, finite_mixed _ _ _ _ _ (finite_fiber (qRight_injective r))⟩

private abbrev left (hDB : D ≤ B) (hEB : E ≤ B) (r : D) (s : E) :=
  LabelledDrawing.vertical
    (atLeft (.up (fromBot D)) (.mixedMultiplication (fromBot B) (incl hDB) (a U) (fromBot D)
      [(1, dot 1)]))
    (.vertical (.horizontal (drawId (.down (fromBot B)))
      (.parallelUp (incl hDB) (fromBot D) (incl hEB) (fromBot E) [(1, middle hDB hEB r s)]))
      (atLeft (.up (fromBot E)) (.compactProjection (fromBot B) (incl hEB) (a U) (fromBot E)
        [(1, leftUpper hEB)])))

private abbrev right (r : D) (s : E) :=
  LabelledDrawing.vertical
    (.horizontal (drawId (.up (a U))) (.compactProjection (fromBot D) (fromBot D) (a U) (a U)
      [(1, rightLower r)]))
    (.vertical
      (atLeft (.down (a U)) (.parallelUp (a U) (a U) (a U) (a U) [(1, dot 1)]))
      (.horizontal (drawId (.up (a U))) (.mixedMultiplication (fromBot E) (fromBot E) (a U) (a U)
        [(1, dot s)])))

private abbrev basisVector {H : Subgroup U} (x : H) :=
  Finsupp.single (Biset.pair (Biset.induction (a U))
    (Word.basis ((Word.down (fromBot H)).tensor (.up (fromBot H)))) 1
    (mixedPair (fromBot H) (fromBot H) x)) (1 : Complex)

private abbrev ev {H K : Subgroup U} {p q : Word H K} (drawing : LabelledDrawing Complex p q) :=
  drawing.interpret.eval.toLinearMap

private abbrev location (hDB : D ≤ B) (hEB : E ≤ B) (r x : D) (s : E) :=
  (incl hDB).toHom x * (((incl hDB).toHom r)⁻¹ * (incl hEB).toHom s)

-- Example 8.7 (archived p. 42, published 28 November revision p. 44).
-- Lemma 6.6, steps 1–3 of (6.3): multiply, translate by r⁻¹s, and project.
-- The compiled formula starts and ends with the first two strands bracketed
-- together. The two exterior associators transport its column to the
-- right-bracketed basis used by the example.
private theorem left_formula (hDB : D ≤ B) (hEB : E ≤ B) (r x : D) (s : E) :
    ev (left hDB hEB r s) (basisVector x) =
      (Diagram.associate (R := Complex) (.up (a U)) (.down (fromBot E)) (.up (fromBot E))).eval.toLinearMap
        (∑ p ∈ (finite_fiber (qLeft_injective hEB) (location hDB hEB r x s)).toFinset,
          Finsupp.single (((Word.up (a U)).tensor (.down (fromBot E))).basis.pair
            (Word.up (fromBot E)).basis p 1) 1) := by
  let p := Word.up (a U)
  let q' := Word.down (fromBot D)
  let t := Word.up (fromBot D)
  let lower := LabelledDrawing.mixedMultiplication (fromBot B) (incl hDB) (a U) (fromBot D)
    (R := Complex) [(1, dot 1)]
  let mid := LabelledDrawing.parallelUp (incl hDB) (fromBot D) (incl hEB) (fromBot E)
    (R := Complex) [(1, middle hDB hEB r s)]
  let upper := LabelledDrawing.compactProjection (fromBot B) (incl hEB) (a U) (fromBot E)
    (R := Complex) [(1, leftUpper hEB)]
  let source := LabelledDrawing.vertical (.horizontal lower (drawId t))
    (.vertical (.ordinary (.associate (.down (fromBot B)) (.up (incl hDB)) t))
      (.vertical (.horizontal (drawId (.down (fromBot B))) mid)
        (.vertical (.ordinary (.unassociate (.down (fromBot B)) (.up (incl hEB)) (.up (fromBot E))))
          (.horizontal upper (drawId (.up (fromBot E)))))))
  let finish := (Diagram.associate (R := Complex) (.up (a U)) (.down (fromBot E))
    (.up (fromBot E))).eval.toLinearMap
  let fiber := fun z : B =>
    ∑ y ∈ (finite_fiber (qLeft_injective hEB) z).toFinset,
      Finsupp.single (((Word.up (a U)).tensor (.down (fromBot E))).basis.pair
        (Word.up (fromBot E)).basis y 1) (1 : Complex)
  change finish (ev source ((Diagram.unassociate (R := Complex) p q' t).eval.toLinearMap
    (Finsupp.single (p.basis.pair (q'.basis.tensor t.basis) 1 (q'.basis.pair t.basis x 1)) 1))) =
      finish (fiber (location hDB hEB r x s))
  rw [Diagram.eval_unassociate_single (R := Complex) p q' t 1 x 1 1]
  have h := ((EvaluationWithOneProjection (a U) (fromBot D) (fromBot D)
    (a U) (fromBot E) (fromBot E)).1 (fromBot B) (incl hDB) (incl hEB)).1
      (dot 1) (middle hDB hEB r s) (dot 1) (finite_fiber (qLeft_injective hEB)) 1 x
  have h' : ev source
      (Finsupp.single ((p.basis.tensor q'.basis).pair t.basis (p.basis.pair q'.basis 1 x) 1) 1) =
      fiber ((fromBot B).toHom 1 * 1 * (incl hDB).toHom x *
        (middle hDB hEB r s).element) := h
  rw [h', map_one, one_mul, one_mul]
  rfl

private theorem left_solution (hDB : D ≤ B) (hEB : E ≤ B)
    (hdis : ∀ z : U, z ∈ D → z ∈ E → z = 1) (r x : D) (s y : E) :
    (incl hEB).toHom y = location hDB hEB r x s ↔ x = r ∧ y = s := by
  constructor
  · intro h
    have h' : (y : U) = (x : U) * ((r : U)⁻¹ * (s : U)) := congrArg Subtype.val h
    have heq : (x : U) * (r : U)⁻¹ = (y : U) * (s : U)⁻¹ := by rw [h']; group
    have hone := hdis ((x : U) * (r : U)⁻¹)
      (D.mul_mem x.property (D.inv_mem r.property))
      (heq ▸ E.mul_mem y.property (E.inv_mem s.property))
    have hx : x = r := Subtype.ext (mul_inv_eq_one.mp hone)
    subst x
    exact ⟨rfl, (incl hEB).injective (by simpa [location, mul_assoc] using h)⟩
  · rintro ⟨rfl, rfl⟩
    simp [location, ← mul_assoc]

private theorem left_column (hDB : D ≤ B) (hEB : E ≤ B)
    (hdis : ∀ z : U, z ∈ D → z ∈ E → z = 1) (r x : D) (s : E) :
    ev (left hDB hEB r s) (basisVector x) =
      @ite _ (x = r) (Classical.propDecidable (x = r)) (basisVector s) 0 := by
  classical
  rw [left_formula]
  by_cases hx : x = r
  · have h : (finite_fiber (qLeft_injective hEB) (location hDB hEB r x s)).toFinset =
        {qLeftPoint s} := by
      ext p
      obtain ⟨y, rfl⟩ := left_representative p
      rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
      change qLeft hEB (qLeftPoint y) = location hDB hEB r x s ↔ qLeftPoint y = qLeftPoint s
      rw [qLeft_eq, left_solution hDB hEB hdis, hx, true_and]
      constructor
      · exact congrArg qLeftPoint
      · intro hp
        exact (incl hEB).injective (by simpa only [qLeft_eq] using congrArg (qLeft hEB) hp)
    rw [if_pos hx, h, Finset.sum_singleton]
    exact Diagram.eval_associate_single (.up (a U)) (.down (fromBot E)) (.up (fromBot E)) 1 s 1 1
  · have h : (finite_fiber (qLeft_injective hEB) (location hDB hEB r x s)).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨y, rfl⟩ := left_representative p
      rw [Set.Finite.mem_toFinset] at hp
      change qLeft hEB (qLeftPoint y) = location hDB hEB r x s at hp
      rw [qLeft_eq, left_solution hDB hEB hdis] at hp
      exact hx hp.1
    rw [if_neg hx, h, Finset.sum_empty, map_zero]

-- Lemma 6.6, steps 1–3 of (6.4): take the fiber over x, act by the
-- identity middle label, and multiply by s. All three labels here and on
-- the left are coefficient-one singletons, so the weighted step 4
-- contributes no further factor.
private theorem right_column (r x : D) (s : E) :
    ev (right r s) (basisVector x) =
      @ite _ (x = r) (Classical.propDecidable (x = r)) (basisVector s) 0 := by
  classical
  have h := ((EvaluationWithOneProjection (a U) (fromBot D) (fromBot D)
    (a U) (fromBot E) (fromBot E)).2 (T U) (a U) (a U) (a U)).1
      (dot r) (finite_fiber (qRight_injective r)) (dot 1) (dot s) 1 x
  let output := fun p : ((Word.up (a U)).tensor (Word.down (a U))).basis.carrier =>
    Finsupp.single (Biset.pair (Biset.induction (a U))
      (Word.basis ((Word.down (fromBot E)).tensor (.up (fromBot E))))
      (1 * (a U).toHom (Quotient.out p).1 * 1)
      (mixedPair (fromBot E) (fromBot E) (s * (fromBot E).toHom (Quotient.out p).2)))
      (1 : Complex)
  have h' : ev (right r s) (basisVector x) =
      ∑ p ∈ (finite_fiber (qRight_injective r) x).toFinset, output p := h
  rw [h']
  by_cases hx : x = r
  · have he : (finite_fiber (qRight_injective r) x).toFinset = {qRightPoint U} := by
      ext p
      rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
      change qRight r p = x ↔ p = qRightPoint U
      rw [qRight_eq, hx]
      exact ⟨fun _ => right_representative p, fun _ => rfl⟩
    rw [if_pos hx, he, Finset.sum_singleton]
    simp only [output, bot_one (Quotient.out (qRightPoint U)).1,
      bot_one (Quotient.out (qRightPoint U)).2, map_one, mul_one]
    rfl
  · have he : (finite_fiber (qRight_injective r) x).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rw [Set.Finite.mem_toFinset] at hp
      change qRight r p = x at hp
      rw [qRight_eq] at hp
      exact hx hp.symm
    rw [if_neg hx, he, Finset.sum_empty]

private theorem diagrams_eq (hDB : D ≤ B) (hEB : E ≤ B)
    (hdis : ∀ z : U, z ∈ D → z ∈ E → z = 1) (r : D) (s : E) :
    (left hDB hEB r s).interpret.eval = (right r s).interpret.eval := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro t c
  refine Quotient.inductionOn t (fun ⟨g, w⟩ => ?_)
  let x := mixedProduct (fromBot D) (fromBot D) w
  change ev (left hDB hEB r s) (Finsupp.single ((Word.up (a U)).basis.pair _ g w) c) =
    ev (right r s) (Finsupp.single ((Word.up (a U)).basis.pair _ g w) c)
  rw [bot_one g, ← mixedPair_mixedProduct (fromBot D) (fromBot D) w]
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  exact congrArg (c • ·) ((left_column hDB hEB hdis r x s).trans (right_column r x s).symm)

end

end OverlapReplacementAux
