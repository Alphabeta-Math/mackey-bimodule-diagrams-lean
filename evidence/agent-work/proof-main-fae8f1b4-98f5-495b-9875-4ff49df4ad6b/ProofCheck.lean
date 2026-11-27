import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.FiniteParabolicJoinBlocks
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

private abbrev location (hDB : D ≤ B) (hEB : E ≤ B) (r x : D) (s : E) :=
  (incl hDB).toHom x * (((incl hDB).toHom r)⁻¹ * (incl hEB).toHom s)

-- Ian Xiao, Example 8.7, archived source/mackey-bimodules.pdf p. 42
-- and published 28 November revision p. 44 (SHA-256
-- e7712567f611d36713fb4dbf45f8b1aeefea022ea2e403462529850ebe290cc8).
-- https://getcurious.cc/downloads/mackey-bimodules.pdf
-- The checked EvaluationWithOneProjection supplies both column formulas.
-- Its singleton branches incorporate the transfer calculation and parallel
-- right multiplication. We compute the projection fibers explicitly using
-- mixedMultiplicationBasis on balanced pairs. The trivial source makes
-- each dot eligible. The group-valued fibers supply the finiteness of the
-- balanced-target fibers required by the compact projection constructors.
-- In Lemma 6.6 (archived p. 25, published p. 27), the three operations
-- yielding (6.3) are multiplication, right translation, and projection.
-- Here they give v(x), then v(x) * (v(r)⁻¹ * w(s)), then the fiber of w.
-- The supplier brackets the first two strands together. The exterior
-- associators transport its column to the right-bracketed basis.
-- Alphabeta Math, "Associativity of tensor products for compatible
-- bimodules", steps 2.1 and 2.2, construct the two directions by
-- balancing on generators. At these typed biset boundaries the project
-- rules eval_unassociate_single and eval_associate_single already give
-- the two basis actions, which suffice to transport the supplier's column.
-- https://alphabetamath.cc/item/thm-associativity-of-balanced-tensor-products
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
      rw [qLeft_eq, left_solution hDB hEB hdis]
      constructor
      · exact fun hp => congrArg qLeftPoint hp.2
      · intro hp
        exact ⟨hx, (incl hEB).injective (by simpa only [qLeft_eq] using congrArg (qLeft hEB) hp)⟩
    rw [ite_eq_left hx, h, Finset.sum_singleton]
    exact Diagram.eval_associate_single (.up (a U)) (.down (fromBot E)) (.up (fromBot E)) 1 s 1 1
  · have h : (finite_fiber (qLeft_injective hEB) (location hDB hEB r x s)).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨y, rfl⟩ := left_representative p
      rw [Set.Finite.mem_toFinset] at hp
      change qLeft hEB (qLeftPoint y) = location hDB hEB r x s at hp
      rw [qLeft_eq, left_solution hDB hEB hdis] at hp
      exact hx hp.1
    rw [ite_eq_right hx, h, Finset.sum_empty, map_zero]

-- The three operations yielding (6.4) are projection, right translation,
-- and multiplication. The projection has only the candidate [1, 1], whose
-- product parameter is r. Translation is by 1, and multiplication
-- on the surviving pair gives s. The projection parameter r is the
-- multiplication dot, corresponding to trace dot r⁻¹ by the convention
-- on p. 24 of the published revision. Each label on either side has one
-- term with coefficient 1, so the singleton formulas apply.
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
    rw [ite_eq_left hx, he, Finset.sum_singleton]
    simp only [output, bot_one (Quotient.out (qRightPoint U)).1,
      bot_one (Quotient.out (qRightPoint U)).2, map_one, mul_one]
  · have he : (finite_fiber (qRight_injective r) x).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rw [Set.Finite.mem_toFinset] at hp
      change qRight r p = x at hp
      rw [qRight_eq] at hp
      exact hx hp.symm
    rw [ite_eq_right hx, he, Finset.sum_empty]

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

-- Alphabeta Math, "Every finite permutation is a product of transpositions",
-- step 1.1 checks a product of swaps pointwise. Each factor fixes all points
-- outside its endpoints. Here closure inside the point stabilizer captures
-- that observation directly for either generator, including arbitrary inverses.
-- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
-- A permutation in both cyclic subgroups fixes every point other than 2.
-- Injectivity forces it to fix 2 as well. The registered FiniteParabolicJoinBlocks
-- identifies joins via connected components of two partitions. The endpoint
-- defines B directly as the image of the three-point symmetric group, so the
-- argument uses swap extension for the inclusions and stabilizers for the intersection.
private theorem closure_swap_fixes {S : Subgroup (Equiv.Perm Nat)} {t x : S}
    {i j n : Nat} (ht : (t : Equiv.Perm Nat) = Equiv.swap i j)
    (hx : x ∈ Subgroup.closure {t}) (hni : n ≠ i) (hnj : n ≠ j) :
    (x : Equiv.Perm Nat) n = n := by
  let stab := (MulAction.stabilizer (Equiv.Perm Nat) n).comap (Subgroup.subtype S)
  have hle : Subgroup.closure {t} ≤ stab := (Subgroup.closure_le stab).mpr (by
    apply Set.singleton_subset_iff.mpr
    change (t : Equiv.Perm Nat) n = n
    rw [ht]
    exact Equiv.swap_apply_of_ne_of_ne hni hnj)
  exact hle hx

private theorem overlapping_swaps {S : Subgroup (Equiv.Perm Nat)} {t u x : S}
    (ht : (t : Equiv.Perm Nat) = Equiv.swap 1 2)
    (hu : (u : Equiv.Perm Nat) = Equiv.swap 2 3)
    (hx : x ∈ Subgroup.closure {t}) (hy : x ∈ Subgroup.closure {u}) : x = 1 := by
  have hfix (n : Nat) (hn : n ≠ 2) : (x : Equiv.Perm Nat) n = n := by
    by_cases h : n = 1
    · exact closure_swap_fixes hu hy hn (by omega)
    · exact closure_swap_fixes ht hx h hn
  apply Subtype.ext
  apply Equiv.ext
  intro n
  change (x : Equiv.Perm Nat) n = n
  by_cases hn : n = 2
  · subst n
    by_contra h
    have he := hfix ((x : Equiv.Perm Nat) 2) h
    exact h ((x : Equiv.Perm Nat).injective he)
  · exact hfix n hn

end

end OverlapReplacementAux

theorem CaseSixReplacementThroughOverlappingBlocks : (
let P := Equiv.Perm Nat
let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let T : Subgroup U := ⊥
let swap := fun (i j : Nat) (hij : i ≠ j) =>
  (⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩ : U)
let swap12 := swap 1 2 (by decide)
let swap23 := swap 2 3 (by decide)
let D : Subgroup U := Subgroup.closure {swap12}
let E : Subgroup U := Subgroup.closure {swap23}
let points : Finset Nat := {1, 2, 3}
let extend := Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ points)
let B : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) (MonoidHom.range extend)
let includeConj := fun {H K : Subgroup U} (h : H ≤ K) =>
  (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
let a := MackeyDiagrams.ConjEmbedding.id T
let b := includeConj (show T ≤ D from bot_le)
let e := includeConj (show T ≤ E from bot_le)
let u := includeConj (show T ≤ B from bot_le)
let v := includeConj (show D ≤ B by
  apply (Subgroup.closure_le B).mpr
  apply Set.singleton_subset_iff.mpr
  change ∃ p, extend p = Equiv.swap 1 2
  exact ⟨Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩)
let w := includeConj (show E ≤ B by
  apply (Subgroup.closure_le B).mpr
  apply Set.singleton_subset_iff.mpr
  change ∃ p, extend p = Equiv.swap 2 3
  exact ⟨Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩)
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let straight := fun {K L : Subgroup U} (p : MackeyDiagrams.Word K L) =>
  ordinary (MackeyDiagrams.Diagram.id p)
let bottom := tensor (up a) (tensor (down b) (up b))
let top := tensor (up a) (tensor (down e) (up e))
let atLeft := fun {K J J' L M : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
    (tail : MackeyDiagrams.Word L M)
    (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
  vertical (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
    (vertical (horizontal crossing (straight tail))
      (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
let dot := fun {H : Subgroup U} {α β : MackeyDiagrams.ConjEmbedding T H} (x : H) =>
  (⟨x, fun y => by
    have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.mp y.property)
    simp [hy]⟩ : MackeyDiagrams.Dot α β)
let lowerLeft : MackeyDiagrams.Dot (comp u a) (comp v b) := dot 1
let upperLeft : MackeyDiagrams.Dot (comp u a) (comp w e) := dot 1
let middleRight : MackeyDiagrams.Dot (comp a a) (comp a a) := dot 1
let finiteFibers := fun {X Y : Type} (q : X → Y) => ∀ z, Set.Finite {y | q y = z}
let basisVector := fun {H : Subgroup U} (h : MackeyDiagrams.ConjEmbedding T H) (x : H) =>
  Finsupp.single
    (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor (down h) (up h))) 1
      (MackeyDiagrams.Generator.mixedPair h h x)) (1 : Complex)
∀ (r : D) (s : E),
  let lowerRight : MackeyDiagrams.Dot (comp b a) (comp b a) := dot r
  let upperRight : MackeyDiagrams.Dot (comp e a) (comp e a) := dot s
  let middleLeft : MackeyDiagrams.Dot (comp v b) (comp w e) :=
    dot ((MackeyDiagrams.ConjEmbedding.toHom v r)⁻¹ * MackeyDiagrams.ConjEmbedding.toHom w s)
  ∃ (hRight : finiteFibers
        (MackeyDiagrams.Generator.mixedMultiplicationBasis b b a a lowerRight))
    (hLeft : finiteFibers
        (MackeyDiagrams.Generator.mixedMultiplicationBasis u w a e upperLeft)),
    let left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical
        (atLeft (up b) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b
          [(1, lowerLeft)]))
        (vertical
          (horizontal (straight (down u))
            (MackeyDiagrams.LabelledDrawing.parallelUp v b w e [(1, middleLeft)]))
          (atLeft (up e) (MackeyDiagrams.LabelledDrawing.compactProjection u w a e
            [(1, ⟨upperLeft, hLeft⟩)])))
    let right : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical
        (horizontal (straight (up a))
          (MackeyDiagrams.LabelledDrawing.compactProjection b b a a
            [(1, ⟨lowerRight, hRight⟩)]))
        (vertical
          (atLeft (down a) (MackeyDiagrams.LabelledDrawing.parallelUp a a a a
            [(1, middleRight)]))
          (horizontal (straight (up a))
            (MackeyDiagrams.LabelledDrawing.mixedMultiplication e e a a
              [(1, upperRight)])))
    let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
    evaluate left = evaluate right ∧
      ∀ x : D,
        MackeyDiagrams.Biset.Hom.toLinearMap (evaluate right) (basisVector b x) =
          @ite _ (x = r) (Classical.propDecidable (x = r)) (basisVector e s) 0
) :=
(by
  intro P finitary U T swap swap12 swap23 D E points extend B includeConj a b e u v w
    up down tensor comp vertical horizontal ordinary straight bottom top atLeft dot lowerLeft
    upperLeft middleRight finiteFibers basisVector r s lowerRight upperRight middleLeft
  -- The two block transpositions are extensions of swaps on the subtype
  -- {1, 2, 3}. The pinned mathlib swap extension theorem proves membership
  -- in the image defining B, and subgroup closure gives the inclusions.
  have hDB : D ≤ B := by
    apply (Subgroup.closure_le B).mpr
    apply Set.singleton_subset_iff.mpr
    change ∃ p, extend p = Equiv.swap 1 2
    exact ⟨Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  have hEB : E ≤ B := by
    apply (Subgroup.closure_le B).mpr
    apply Set.singleton_subset_iff.mpr
    change ∃ p, extend p = Equiv.swap 2 3
    exact ⟨Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩
  have hdis : ∀ z : U, z ∈ D → z ∈ E → z = 1 :=
    fun _ hzD hzE => OverlapReplacementAux.overlapping_swaps rfl rfl hzD hzE
  refine ⟨(OverlapReplacementAux.rightLower r).2, (OverlapReplacementAux.leftUpper hEB).2, ?_⟩
  change (OverlapReplacementAux.left hDB hEB r s).interpret.eval =
    (OverlapReplacementAux.right r s).interpret.eval ∧ _
  exact ⟨OverlapReplacementAux.diagrams_eq hDB hEB hdis r s,
    fun x => OverlapReplacementAux.right_column r x s⟩)

#print axioms CaseSixReplacementThroughOverlappingBlocks
