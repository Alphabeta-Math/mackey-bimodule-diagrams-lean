import MackeyDiagrams.PlanarShape
import Proofs.EvaluationWithOneProjection

set_option maxHeartbeats 2000000

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

-- Every marked label below has a single eligible term. Its adjacent
-- source embeddings start at the trivial subgroup.
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

-- The left projection has at most one preimage since its product
-- parameter is the inclusion E → B. The right projection is defined on
-- a one-point balanced product. Both supply actual finite-fiber witnesses.
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

private theorem left_positions (hDB : D ≤ B) (hEB : E ≤ B) (r : D) (s : E) :
    PlanarCode.encode (left hDB hEB r s).erase.geometry =
      [.vertex 0 .mixedMultiplication, .vertex 1 .parallelUp, .vertex 0 .mixedProjection] := rfl

private theorem right_positions (r : D) (s : E) :
    PlanarCode.encode (right r s).erase.geometry =
      [.vertex 1 .mixedProjection, .vertex 0 .parallelUp, .vertex 1 .mixedMultiplication] := rfl

private theorem left_boundary (hDB : D ≤ B) (hEB : E ≤ B) (r : D) (s : E) :
    ((left hDB hEB r s).planarShape.bottom, (left hDB hEB r s).planarShape.top) =
      ([true, false, true], [true, false, true]) := rfl

private theorem right_boundary (r : D) (s : E) :
    ((right r s).planarShape.bottom, (right r s).planarShape.top) =
      ([true, false, true], [true, false, true]) := rfl

end
end OverlapReplacementAux
