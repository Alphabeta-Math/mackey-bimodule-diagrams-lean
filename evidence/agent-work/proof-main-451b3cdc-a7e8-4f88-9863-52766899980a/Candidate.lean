import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.FiniteParabolicJoinOfFamily

set_option maxHeartbeats 2000000

namespace CaseSixJoinAux

open MackeyDiagrams
open MackeyDiagrams.Generator
open scoped BigOperators

noncomputable section

variable {U : Type} [Group U] {G A D C E B GE : Subgroup U}

private def incl {H K : Subgroup U} (h : H ≤ K) : ConjEmbedding H K :=
  ⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩

private abbrev a (hAG : A ≤ G) := incl hAG
private abbrev b (hA : D ⊓ GE = A) := incl (show A ≤ D by rw [← hA]; exact inf_le_left)
private abbrev c (hC : G ⊓ E = C) := incl (show C ≤ G by rw [← hC]; exact inf_le_left)
private abbrev e (hC : G ⊓ E = C) := incl (show C ≤ E by rw [← hC]; exact inf_le_right)
private abbrev d (D : Subgroup U) := incl (show (⊥ : Subgroup U) ≤ D from bot_le)
private abbrev f (E : Subgroup U) := incl (show (⊥ : Subgroup U) ≤ E from bot_le)
private abbrev i (A : Subgroup U) := incl (show (⊥ : Subgroup U) ≤ A from bot_le)
private abbrev j (U : Type) [Group U] := ConjEmbedding.id (⊥ : Subgroup U)
private abbrev k (C : Subgroup U) := incl (show (⊥ : Subgroup U) ≤ C from bot_le)

private abbrev q {H K L M : Subgroup U} (α : ConjEmbedding K M) (β : ConjEmbedding L M)
    (γ : ConjEmbedding H K) (δ : ConjEmbedding H L) (dot : Dot (α.comp γ) (β.comp δ)) :=
  fun p => mixedProduct α β (mixedMultiplicationBasis α β γ δ dot p)

private theorem finite_of_product {H K L M : Subgroup U}
    (α : ConjEmbedding K M) (β : ConjEmbedding L M)
    (γ : ConjEmbedding H K) (δ : ConjEmbedding H L) (dot : Dot (α.comp γ) (β.comp δ))
    (h : ∀ z, Set.Finite {p | q α β γ δ dot p = z}) :
    ∀ z, Set.Finite {p | mixedMultiplicationBasis α β γ δ dot p = z} :=
  fun z => (h (mixedProduct α β z)).subset
    (fun _ hp => congrArg (mixedProduct α β) hp)

private def lo (hAG : A ≤ G) (hA : D ⊓ GE = A) (hGB : G ≤ B) (hDB : D ≤ B) :
    Dot ((incl hGB).comp (a hAG)) ((incl hDB).comp (b hA)) :=
  ⟨1, fun x => by
    simpa only [mul_one, one_mul] using
      (show ((incl hGB).comp (a hAG)).toHom x =
        ((incl hDB).comp (b hA)).toHom x from rfl)⟩

private def hi (hC : G ⊓ E = C) (hGB : G ≤ B) (hEB : E ≤ B) :
    Dot ((incl hGB).comp (c hC)) ((incl hEB).comp (e hC)) :=
  ⟨1, fun x => by
    simpa only [mul_one, one_mul] using
      (show ((incl hGB).comp (c hC)).toHom x =
        ((incl hEB).comp (e hC)).toHom x from rfl)⟩

private abbrev RDot (hA : D ⊓ GE = A) := Dot ((b hA).comp (i A)) ((d D).comp (j U))
private abbrev TDot (hAG : A ≤ G) (hC : G ⊓ E = C) := Dot ((a hAG).comp (i A)) ((c hC).comp (k C))
private abbrev SDot (hC : G ⊓ E = C) := Dot ((e hC).comp (k C)) ((f E).comp (j U))
private abbrev MDot (hDB : D ≤ B) (hEB : E ≤ B) := Dot ((incl hDB).comp (d D)) ((incl hEB).comp (f E))

private def mid (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (r : RDot hA) (t : TDot hAG hC) (s : SDot hC) : MDot hDB hEB :=
  ⟨((incl hDB).toHom r.element)⁻¹ * (incl hGB).toHom t.element * (incl hEB).toHom s.element,
    fun x => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.property)
      simp [hx]⟩

private theorem left_pair_q (hC : G ⊓ E = C) (hGB : G ≤ B) (hEB : E ≤ B)
    (g : G) (y : E) :
    q (incl hGB) (incl hEB) (c hC) (e hC) (hi hC hGB hEB)
        ((Biset.induction (c hC)).pair (Biset.restriction (e hC)) g y) =
      (incl hGB).toHom g * (incl hEB).toHom y := by
  change mixedProduct (incl hGB) (incl hEB) (mixedPair (incl hGB) (incl hEB)
    ((incl hGB).toHom g * 1 * (incl hEB).toHom y)) = _
  rw [mixedProduct_mixedPair, mul_one]

-- Proposition 8.8, second assertion, step 1: G ∩ E = C makes each
-- factorization unique as a balanced class. Its two representatives
-- differ by the same element of C, in inverse slots.
private theorem left_inj (hC : G ⊓ E = C) (hGB : G ≤ B) (hEB : E ≤ B) :
    Function.Injective (q (incl hGB) (incl hEB) (c hC) (e hC) (hi hC hGB hEB)) := by
  intro p₁ p₂
  refine Quotient.inductionOn₂ p₁ p₂ (fun ⟨g₁,y₁⟩ ⟨g₂,y₂⟩ hp => ?_)
  change q (incl hGB) (incl hEB) (c hC) (e hC) (hi hC hGB hEB) (Biset.pair _ _ g₁ y₁) =
    q (incl hGB) (incl hEB) (c hC) (e hC) (hi hC hGB hEB) (Biset.pair _ _ g₂ y₂) at hp
  rw [left_pair_q, left_pair_q] at hp
  have hp' : (g₁ : U) * (y₁ : U) = (g₂ : U) * (y₂ : U) := congrArg Subtype.val hp
  have hab : (g₂ : U)⁻¹ * (g₁ : U) = (y₂ : U) * (y₁ : U)⁻¹ := by
    calc
      _ = (g₂ : U)⁻¹ * ((g₁ : U) * (y₁ : U)) * (y₁ : U)⁻¹ := by group
      _ = _ := by rw [hp']; group
  let z : C := ⟨(g₂ : U)⁻¹ * (g₁ : U), by
    rw [← hC]
    exact ⟨G.mul_mem (G.inv_mem g₂.property) g₁.property,
      hab ▸ E.mul_mem y₂.property (E.inv_mem y₁.property)⟩⟩
  apply Quotient.sound
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    change 1 * (g₁ : U) * ((g₂ : U)⁻¹ * (g₁ : U))⁻¹ = (g₂ : U)
    group
  · apply Subtype.ext
    change ((g₂ : U)⁻¹ * (g₁ : U)) * (y₁ : U) * 1⁻¹ = (y₂ : U)
    rw [hab]
    group

private theorem right_pair_q (hA : D ⊓ GE = A) (r : RDot hA) (x : A)
    (z : (⊥ : Subgroup U)) :
    q (b hA) (d D) (i A) (j U) r
        ((Biset.induction (i A)).pair (Biset.restriction (j U)) x z) =
      (b hA).toHom x * r.element := by
  have hz : z = 1 := Subtype.ext (Subgroup.mem_bot.mp z.property)
  subst z
  change mixedProduct (b hA) (d D) (mixedPair (b hA) (d D)
    ((b hA).toHom x * r.element * (d D).toHom 1)) = _
  rw [mixedProduct_mixedPair, map_one, mul_one]

private theorem right_inj (hA : D ⊓ GE = A) (r : RDot hA) :
    Function.Injective (q (b hA) (d D) (i A) (j U) r) := by
  intro p₁ p₂
  refine Quotient.inductionOn₂ p₁ p₂ (fun ⟨x₁,z₁⟩ ⟨x₂,z₂⟩ hp => ?_)
  change q (b hA) (d D) (i A) (j U) r (Biset.pair _ _ x₁ z₁) =
    q (b hA) (d D) (i A) (j U) r (Biset.pair _ _ x₂ z₂) at hp
  rw [right_pair_q, right_pair_q] at hp
  have hx := (b hA).injective (mul_right_cancel hp)
  have hz₁ : z₁ = 1 := Subtype.ext (Subgroup.mem_bot.mp z₁.property)
  have hz₂ : z₂ = 1 := Subtype.ext (Subgroup.mem_bot.mp z₂.property)
  rw [hx, hz₁, hz₂]

private theorem finite_injective {X Y : Type} {f : X → Y} (hf : Function.Injective f) (y : Y) :
    Set.Finite {x | f x = y} := by
  by_cases h : ∃ x, f x = y
  · obtain ⟨x, hx⟩ := h
    apply (Set.finite_singleton x).subset
    exact fun z hz => Set.mem_singleton_iff.mpr (hf (hz.trans hx.symm))
  · apply Set.finite_empty.subset
    exact fun z hz => (h ⟨z, hz⟩).elim


private abbrev drawId {H K : Subgroup U} (p : Word H K) :=
  LabelledDrawing.ordinary (Diagram.id (R := Complex) p)

private abbrev atLeft {K J J' L M : Subgroup U}
    {p : Word K J} {q : Word J L} {p' : Word K J'} {q' : Word J' L}
    (tail : Word L M) (cross : LabelledDrawing Complex (p.tensor q) (p'.tensor q')) :=
  LabelledDrawing.vertical (.ordinary (.unassociate p q tail))
    (.vertical (.horizontal cross (drawId tail)) (.ordinary (.associate p' q' tail)))

private abbrev left (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (midTerms : List (Complex × MDot hDB hEB)) :=
  LabelledDrawing.vertical
    (atLeft (.up (d D)) (.mixedMultiplication (incl hGB) (incl hDB) (a hAG) (b hA)
      [(1, lo hAG hA hGB hDB)]))
    (.vertical (.horizontal (drawId (.down (incl hGB)))
      (.parallelUp (incl hDB) (d D) (incl hEB) (f E) midTerms))
      (atLeft (.up (f E)) (.compactProjection (incl hGB) (incl hEB) (c hC) (e hC)
        [(1, ⟨hi hC hGB hEB, finite_of_product _ _ _ _ _
          (finite_injective (left_inj hC hGB hEB))⟩)])))

private abbrev rightTerm (hA : D ⊓ GE = A) (r : RDot hA) :
    ProjectionDot.Mixed (b hA) (d D) (i A) (j U) :=
  ⟨r, finite_of_product _ _ _ _ _ (finite_injective (right_inj hA r))⟩

private abbrev rightWithTerms (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (rs : List (Complex × ProjectionDot.Mixed (b hA) (d D) (i A) (j U)))
    (ts : List (Complex × TDot hAG hC)) (ss : List (Complex × SDot hC)) :=
  LabelledDrawing.vertical
    (.horizontal (drawId (.up (a hAG))) (.compactProjection (b hA) (d D) (i A) (j U) rs))
    (.vertical
      (atLeft (.down (j U)) (.parallelUp (a hAG) (i A) (c hC) (k C) ts))
      (.horizontal (drawId (.up (c hC))) (.mixedMultiplication (e hC) (f E) (k C) (j U) ss)))

private abbrev right (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (rs : List (Complex × RDot hA)) (ts : List (Complex × TDot hAG hC))
    (ss : List (Complex × SDot hC)) :=
  rightWithTerms hAG hA hC (rs.map fun (z, r) => (z, rightTerm hA r)) ts ss

private abbrev input (hAG : A ≤ G) (hA : D ⊓ GE = A) (g : G) (x : D) :=
  (Word.up (a hAG)).basis.pair ((Word.down (b hA)).tensor (.up (d D))).basis g
    (mixedPair (b hA) (d D) x)

private abbrev output (hC : G ⊓ E = C) (g : G) (y : E) :=
  (Word.up (c hC)).basis.pair ((Word.down (e hC)).tensor (.up (f E))).basis g
    (mixedPair (e hC) (f E) y)

private abbrev Out (hC : G ⊓ E = C) :=
  (((Word.up (c hC)).tensor ((Word.down (e hC)).tensor (.up (f E)))).basis.carrier →₀ Complex)

private abbrev ev {H K : Subgroup U} {p q : Word H K} (drawing : LabelledDrawing Complex p q) :=
  drawing.interpret.eval.toLinearMap

private def leftCol (hC : G ⊓ E = C) (hGB : G ≤ B) (hEB : E ≤ B) (z : B) : Out hC :=
  (Diagram.associate (R := Complex) (.up (c hC)) (.down (e hC)) (.up (f E))).eval.toLinearMap
    (∑ p ∈ (finite_injective (left_inj hC hGB hEB) z).toFinset,
      Finsupp.single (((Word.up (c hC)).tensor (.down (e hC))).basis.pair
        (Word.up (f E)).basis p 1) 1)

private def rightCol (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (r : RDot hA) (t : TDot hAG hC) (s : SDot hC) (g : G) (x : D) : Out hC :=
  ∑ p ∈ (finite_injective (right_inj hA r) x).toFinset,
    Finsupp.single (output hC (g * (a hAG).toHom (Quotient.out p).1 * t.element)
      (s.element * (f E).toHom (Quotient.out p).2)) 1

private theorem leftCol_pair (hC : G ⊓ E = C) (hGB : G ≤ B) (hEB : E ≤ B)
    (g : G) (y : E) (z : B) (hz : (incl hGB).toHom g * (incl hEB).toHom y = z) :
    leftCol hC hGB hEB z = Finsupp.single (output hC g y) 1 := by
  classical
  let p := (Biset.induction (c hC)).pair (Biset.restriction (e hC)) g y
  have hp : q (incl hGB) (incl hEB) (c hC) (e hC) (hi hC hGB hEB) p = z :=
    (left_pair_q hC hGB hEB g y).trans hz
  have hs : (finite_injective (left_inj hC hGB hEB) z).toFinset = {p} := by
    ext y
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
    change q _ _ _ _ _ y = z ↔ y = p
    exact ⟨fun hy => left_inj hC hGB hEB (hy.trans hp.symm), fun hy => hy ▸ hp⟩
  rw [leftCol, hs, Finset.sum_singleton]
  change (Diagram.associate (R := Complex) (.up (c hC)) (.down (e hC))
    (.up (f E))).eval.toLinearMap (Finsupp.single (((Word.up (c hC)).tensor (.down (e hC))).basis.pair
      (Word.up (f E)).basis ((Word.up (c hC)).basis.pair (Word.down (e hC)).basis g y) 1) 1) = _
  exact Diagram.eval_associate_single (.up (c hC)) (.down (e hC)) (.up (f E)) g y 1 1

private theorem rightCol_pair (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (r : RDot hA) (t : TDot hAG hC) (s : SDot hC) (g : G) (x : D) (y : A)
    (hy : (b hA).toHom y * r.element = x) :
    rightCol hAG hA hC r t s g x =
      Finsupp.single (output hC (g * (a hAG).toHom y * t.element) s.element) 1 := by
  classical
  let p := (Biset.induction (i A)).pair (Biset.restriction (j U)) y 1
  have hp : q (b hA) (d D) (i A) (j U) r p = x :=
    (right_pair_q hA r y 1).trans hy
  have hs : (finite_injective (right_inj hA r) x).toFinset = {p} := by
    ext z
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
    change q _ _ _ _ _ z = x ↔ z = p
    exact ⟨fun hz => right_inj hA r (hz.trans hp.symm), fun hz => hz ▸ hp⟩
  rw [rightCol, hs, Finset.sum_singleton]
  have h₁ : (Quotient.out p).1 = y := by
    have heq := congrArg (q (b hA) (d D) (i A) (j U) r) (Quotient.out_eq' p)
    change q _ _ _ _ _ (Biset.pair _ _ (Quotient.out p).1 (Quotient.out p).2) =
      q _ _ _ _ _ (Biset.pair _ _ y 1) at heq
    rw [right_pair_q, right_pair_q] at heq
    exact (b hA).injective (mul_right_cancel heq)
  have h₂ : (Quotient.out p).2 = 1 :=
    Subtype.ext (Subgroup.mem_bot.mp (Quotient.out p).2.property)
  rw [h₁, h₂, map_one, mul_one]

-- Step 2 of the calculation for the second assertion of Proposition 8.8.
-- Equation (6.4) gives the right projection column. The left column is
-- Equation (6.3), with basis reassociation to the same ordered boundary.
-- Both fibers are empty when xr⁻¹ is outside A, and otherwise give one
-- common basis vector. GE being a subgroup is used for both implications.
private theorem columns (hGE : (GE : Set U) = Set.image2 (fun g e : U => g * e) (G : Set U) (E : Set U))
    (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (r : RDot hA) (t : TDot hAG hC) (s : SDot hC) (g : G) (x : D) :
    leftCol hC hGB hEB ((incl hGB).toHom g * (incl hDB).toHom x *
      (mid hAG hA hC hGB hDB hEB r t s).element) =
      rightCol hAG hA hC r t s g x := by
  classical
  have gmem (v : G) : (v : U) ∈ GE := by
    change (v : U) ∈ (GE : Set U)
    rw [hGE]
    exact ⟨v, v.property, 1, E.one_mem, mul_one _⟩
  have emem (v : E) : (v : U) ∈ GE := by
    change (v : U) ∈ (GE : Set U)
    rw [hGE]
    exact ⟨1, G.one_mem, v, v.property, one_mul _⟩
  let w := (incl hGB).toHom g * (incl hDB).toHom x *
    (mid hAG hA hC hGB hDB hEB r t s).element
  by_cases hn : (x : U) * (r.element : U)⁻¹ ∈ GE
  · let y : A := ⟨(x : U) * (r.element : U)⁻¹, by
        exact hA ▸ (show (x : U) * (r.element : U)⁻¹ ∈ D ⊓ GE from
          ⟨D.mul_mem x.property (D.inv_mem r.element.property), hn⟩)⟩
    rw [leftCol_pair hC hGB hEB (g * (a hAG).toHom y * t.element) s.element,
      rightCol_pair hAG hA hC r t s g x y]
    · apply Subtype.ext
      change (x : U) * (r.element : U)⁻¹ * (r.element : U) = (x : U)
      group
    · apply Subtype.ext
      change (g : U) * ((x : U) * (r.element : U)⁻¹) * (t.element : U) * (s.element : U) =
        (g : U) * (x : U) * ((r.element : U)⁻¹ * (t.element : U) * (s.element : U))
      group
  · have hL : (finite_injective (left_inj hC hGB hEB) w).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      change q _ _ _ _ _ z = w at hz
      refine Quotient.inductionOn z (fun ⟨g',y'⟩ hz => ?_) hz
      change q _ _ _ _ _ (Biset.pair _ _ g' y') = w at hz
      rw [left_pair_q] at hz
      have hv : (g' : U) * (y' : U) =
          (g : U) * (x : U) * ((r.element : U)⁻¹ * (t.element : U) * (s.element : U)) :=
        congrArg Subtype.val hz
      apply hn
      have hw : (x : U) * (r.element : U)⁻¹ =
          (g : U)⁻¹ * ((g' : U) * (y' : U)) * (s.element : U)⁻¹ * (t.element : U)⁻¹ := by
        rw [hv]
        group
      rw [hw]
      exact GE.mul_mem (GE.mul_mem (GE.mul_mem (GE.inv_mem (gmem g))
        (GE.mul_mem (gmem g') (emem y'))) (GE.inv_mem (emem s.element)))
        (GE.inv_mem (gmem t.element))
    have hR : (finite_injective (right_inj hA r) x).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      change q _ _ _ _ _ z = x at hz
      refine Quotient.inductionOn z (fun ⟨y,z'⟩ hz => ?_) hz
      change q _ _ _ _ _ (Biset.pair _ _ y z') = x at hz
      rw [right_pair_q] at hz
      have hv : (y : U) * (r.element : U) = (x : U) := congrArg Subtype.val hz
      apply hn
      rw [← hv, mul_inv_cancel_right]
      exact (show (y : U) ∈ D ⊓ GE from hA.symm ▸ y.property).2
    change leftCol hC hGB hEB w = _
    rw [leftCol, hL, rightCol, hR, Finset.sum_empty, Finset.sum_empty, map_zero]


private theorem left_one (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B) (m : MDot hDB hEB) (g : G) (x : D) :
    ev (left hAG hA hC hGB hDB hEB [(1, m)]) (Finsupp.single (input hAG hA g x) 1) =
      leftCol hC hGB hEB ((incl hGB).toHom g * (incl hDB).toHom x * m.element) := by
  let p := Word.up (a hAG)
  let q' := Word.down (b hA)
  let t := Word.up (d D)
  have h := ((EvaluationWithOneProjection (a hAG) (b hA) (d D) (c hC) (e hC) (f E)).1
    (incl hGB) (incl hDB) (incl hEB)).1 (lo hAG hA hGB hDB) m
      (hi hC hGB hEB) (finite_injective (left_inj hC hGB hEB)) g x
  have hin := Diagram.eval_unassociate_single (R := Complex) p q' t g x 1 1
  let lower := LabelledDrawing.mixedMultiplication (incl hGB) (incl hDB) (a hAG) (b hA)
    (R := Complex) [(1, lo hAG hA hGB hDB)]
  let upper := LabelledDrawing.compactProjection (incl hGB) (incl hEB) (c hC) (e hC)
    (R := Complex) [(1, ⟨hi hC hGB hEB, finite_of_product _ _ _ _ _
      (finite_injective (left_inj hC hGB hEB))⟩)]
  let middle := LabelledDrawing.parallelUp (incl hDB) (d D) (incl hEB) (f E)
    (R := Complex) [(1, m)]
  let source := LabelledDrawing.vertical (.horizontal lower (drawId t))
    (.vertical (.ordinary (.associate (.down (incl hGB)) (.up (incl hDB)) t))
      (.vertical (.horizontal (drawId (.down (incl hGB))) middle)
        (.vertical (.ordinary (.unassociate (.down (incl hGB)) (.up (incl hEB)) (.up (f E))))
          (.horizontal upper (drawId (.up (f E)))))))
  let finish := (Diagram.associate (R := Complex) (.up (c hC)) (.down (e hC)) (.up (f E))).eval.toLinearMap
  change finish (ev source ((Diagram.unassociate (R := Complex) p q' t).eval.toLinearMap
    (Finsupp.single (p.basis.pair (q'.basis.tensor t.basis) g (q'.basis.pair t.basis x 1)) 1))) = _
  rw [hin]
  let fiber := fun z : B =>
    ∑ y ∈ (finite_injective (left_inj hC hGB hEB) z).toFinset,
      Finsupp.single (((Word.up (c hC)).tensor (.down (e hC))).basis.pair (Word.up (f E)).basis y 1)
        (1 : Complex)
  have h' : ev source (Finsupp.single ((p.basis.tensor q'.basis).pair t.basis (p.basis.pair q'.basis g x) 1) 1) =
      fiber ((incl hGB).toHom g * (lo hAG hA hGB hDB).element * (incl hDB).toHom x * m.element) := h
  rw [show (lo hAG hA hGB hDB).element = 1 from rfl, mul_one] at h'
  exact congrArg finish h' 

private theorem right_one (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (r : RDot hA) (t : TDot hAG hC) (s : SDot hC) (g : G) (x : D) :
    ev (right hAG hA hC [(1, r)] [(1, t)] [(1, s)]) (Finsupp.single (input hAG hA g x) 1) =
      rightCol hAG hA hC r t s g x :=
  ((EvaluationWithOneProjection (a hAG) (b hA) (d D) (c hC) (e hC) (f E)).2
    (⊥ : Subgroup U) (i A) (j U) (k C)).1 r
      (finite_injective (right_inj hA r)) t s g x

private theorem framed_weighted {K H J : Subgroup U} {p : Word K H} {q q' : Word H J}
    {I : Type} (S : Finset I) (w : I → Complex) (T : I → Diagram Complex q q') :
    ((Biset.Hom.id p.basis).horizontal
      (ScopedDiagram.linearCombination (S.toList.map fun i => (w i, .ordinary (T i)))).eval).toLinearMap =
      ∑ i ∈ S, w i • ((Biset.Hom.id p.basis).horizontal (T i).eval).toLinearMap := by
  have h (v : q.basis.carrier →₀ Complex) :
      (ScopedDiagram.linearCombination (S.toList.map fun i => (w i, .ordinary (T i)))).eval.toLinearMap v =
        ∑ i ∈ S, w i • (T i).eval.toLinearMap v := by
    rw [ScopedDiagram.eval_linearCombination_apply, List.map_map]
    exact Finset.sum_map_toList S _
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((Biset.Hom.id p.basis).horizontal
    (ScopedDiagram.linearCombination (S.toList.map fun i => (w i, .ordinary (T i)))).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) = _
  have he (i : I) := Biset.Hom.horizontal_single (Biset.Hom.id p.basis) (T i).eval x y r
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Biset.Hom.horizontal_single,
    h, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = w i • ((Biset.Hom.id p.basis).horizontal (T i).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r)
  rw [he i, smul_smul, smul_smul, mul_comm r]

set_option maxHeartbeats 1500000 in
private theorem left_linear (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (M : DotLabel Complex ((incl hDB).comp (d D)) ((incl hEB).comp (f E))) (g : G) (x : D) :
    ev (left hAG hA hC hGB hDB hEB M.terms) (Finsupp.single (input hAG hA g x) 1) =
      M.sum (fun m z => z • leftCol hC hGB hEB ((incl hGB).toHom g * (incl hDB).toHom x * m.element)) := by
  let start := (atLeft (.up (d D)) (.mixedMultiplication (incl hGB) (incl hDB) (a hAG) (b hA)
    [(1, lo hAG hA hGB hDB)])).interpret.eval.toLinearMap (Finsupp.single (input hAG hA g x) 1)
  let finish := ev (atLeft (.up (f E)) (.compactProjection (incl hGB) (incl hEB) (c hC) (e hC)
    [(1, ⟨hi hC hGB hEB, finite_of_product _ _ _ _ _
      (finite_injective (left_inj hC hGB hEB))⟩)]))
  let T := Diagram.parallelUp (R := Complex) (incl hDB) (d D) (incl hEB) (f E)
  let X := (Word.down (incl hGB)).basis
  have hmid : (Biset.Hom.horizontal (Biset.Hom.id X)
      (LabelledDrawing.parallelUp (incl hDB) (d D) (incl hEB) (f E) M.terms).interpret.eval).toLinearMap =
      ∑ m ∈ M.support, M m • (Biset.Hom.horizontal (Biset.Hom.id X) (T m).eval).toLinearMap := by
    simpa only [DotLabel.terms, LabelledDrawing.interpret, List.map_map, Function.comp_def] using
      (framed_weighted (p := .down (incl hGB)) M.support M T)
  change finish ((Biset.Hom.horizontal (Biset.Hom.id X)
    (LabelledDrawing.parallelUp (incl hDB) (d D) (incl hEB) (f E) M.terms).interpret.eval).toLinearMap start) = _
  rw [hmid]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  have hm := framed_weighted (p := .down (incl hGB)) ({()} : Finset Unit)
    (fun _ => (1 : Complex)) (fun _ => T m)
  simp only [Finset.toList_singleton, List.map_cons, List.map_nil, Finset.sum_singleton, one_smul] at hm
  rw [← hm]
  exact left_one hAG hA hC hGB hDB hEB m g x

set_option maxHeartbeats 1500000 in
private theorem right_linear (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (rs : DotLabel Complex ((b hA).comp (i A)) ((d D).comp (j U)))
    (ts : DotLabel Complex ((a hAG).comp (i A)) ((c hC).comp (k C)))
    (ss : DotLabel Complex ((e hC).comp (k C)) ((f E).comp (j U))) (g : G) (x : D) :
    ev (right hAG hA hC rs.terms ts.terms ss.terms) (Finsupp.single (input hAG hA g x) 1) =
      rs.sum (fun r cr => ts.sum (fun t ct => ss.sum (fun s cs =>
        (cr * ct * cs) • rightCol hAG hA hC r t s g x))) := by
  let project := fun r : RDot hA => Diagram.mixedProjection (R := Complex)
    (b hA) (d D) (i A) (j U) r (rightTerm hA r).finite
  let attached := rs.support.attach.toList.map fun r => (rs r.val, rightTerm hA r.val)
  let plain := rs.terms.map fun (z, r) => (z, rightTerm hA r)
  let frame := fun terms => ev (LabelledDrawing.horizontal (drawId (.up (a hAG)))
    (LabelledDrawing.compactProjection (b hA) (d D) (i A) (j U) terms))
  have hplain : frame plain = ∑ r ∈ rs.support, rs r •
      ((Biset.Hom.id (Word.up (a hAG)).basis).horizontal (project r).eval).toLinearMap := by
    change ((Biset.Hom.id (Word.up (a hAG)).basis).horizontal
      (LabelledDrawing.compactProjection (b hA) (d D) (i A) (j U) plain).interpret.eval).toLinearMap = _
    simpa only [plain, DotLabel.terms, LabelledDrawing.interpret, List.map_map, Function.comp_def]
      using framed_weighted (p := .up (a hAG)) rs.support rs project
  have hatt : frame attached = ∑ r ∈ rs.support.attach, rs r.val •
      ((Biset.Hom.id (Word.up (a hAG)).basis).horizontal (project r.val).eval).toLinearMap := by
    change ((Biset.Hom.id (Word.up (a hAG)).basis).horizontal
      (LabelledDrawing.compactProjection (b hA) (d D) (i A) (j U) attached).interpret.eval).toLinearMap = _
    simpa only [attached, LabelledDrawing.interpret, List.map_map, Function.comp_def]
      using framed_weighted (p := .up (a hAG)) rs.support.attach
        (fun r => rs r.val) (fun r => project r.val)
  have hframe : frame plain = frame attached := by
    rw [hplain, hatt]
    exact (Finset.sum_attach rs.support (fun r => rs r •
      ((Biset.Hom.id (Word.up (a hAG)).basis).horizontal (project r).eval).toLinearMap)).symm
  have he : ev (rightWithTerms hAG hA hC plain ts.terms ss.terms) =
      ev (rightWithTerms hAG hA hC attached ts.terms ss.terms) :=
    congrArg (fun L => (ev (LabelledDrawing.vertical
      (atLeft (.down (j U)) (.parallelUp (a hAG) (i A) (c hC) (k C) ts.terms))
      (.horizontal (drawId (.up (c hC))) (.mixedMultiplication (e hC) (f E) (k C) (j U) ss.terms)))).comp L)
      hframe
  change ev (rightWithTerms hAG hA hC plain ts.terms ss.terms) _ = _
  rw [he]
  have h := ((EvaluationWithOneProjection (a hAG) (b hA) (d D) (c hC) (e hC) (f E)).2
    (⊥ : Subgroup U) (i A) (j U) (k C)).2 rs ts ss
    (fun r _ => finite_injective (right_inj hA r)) g x
  have h' : ev (rightWithTerms hAG hA hC attached ts.terms ss.terms)
      (Finsupp.single (input hAG hA g x) 1) =
    ∑ r ∈ rs.support.attach, ∑ t ∈ ts.support, ∑ s ∈ ss.support,
      (rs r.val * ts t * ss s) • rightCol hAG hA hC r.val t s g x := h
  rw [h']
  exact Finset.sum_attach rs.support (fun r => ∑ t ∈ ts.support, ∑ s ∈ ss.support,
    (rs r * ts t * ss s) • rightCol hAG hA hC r t s g x)

private theorem ext_input (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    {p₁ p₂ : LabelledDrawing Complex
      ((Word.up (a hAG)).tensor ((Word.down (b hA)).tensor (.up (d D))))
      ((Word.up (c hC)).tensor ((Word.down (e hC)).tensor (.up (f E))))}
    (h : ∀ (g : G) (x : D), ev p₁ (Finsupp.single (input hAG hA g x) 1) =
      ev p₂ (Finsupp.single (input hAG hA g x) 1)) :
    p₁.interpret.eval = p₂.interpret.eval := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro t z
  refine Quotient.inductionOn t (fun ⟨g, w⟩ => ?_)
  let x := mixedProduct (b hA) (d D) w
  have hw := mixedPair_mixedProduct (b hA) (d D) w
  change ev p₁ (Finsupp.single ((Word.up (a hAG)).basis.pair _ g w) z) =
    ev p₂ (Finsupp.single ((Word.up (a hAG)).basis.pair _ g w) z)
  rw [← hw]
  change ev p₁ (Finsupp.single (input hAG hA g x) z) =
    ev p₂ (Finsupp.single (input hAG hA g x) z)
  rw [← Finsupp.smul_single_one, map_smul, map_smul, h]

private noncomputable abbrev middleLabel (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (rs : DotLabel Complex ((b hA).comp (i A)) ((d D).comp (j U)))
    (ts : DotLabel Complex ((a hAG).comp (i A)) ((c hC).comp (k C)))
    (ss : DotLabel Complex ((e hC).comp (k C)) ((f E).comp (j U))) :
    DotLabel Complex ((incl hDB).comp (d D)) ((incl hEB).comp (f E)) :=
  rs.sum fun r cr => ts.sum fun t ct => ss.sum fun s cs =>
    Finsupp.single (mid hAG hA hC hGB hDB hEB r t s) (cr * ct * cs)

private theorem singleton_eq (hGE : (GE : Set U) = Set.image2 (fun g e : U => g * e) (G : Set U) (E : Set U))
    (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (r : RDot hA) (t : TDot hAG hC) (s : SDot hC) :
    (left hAG hA hC hGB hDB hEB [(1, mid hAG hA hC hGB hDB hEB r t s)]).interpret.eval =
      (right hAG hA hC [(1, r)] [(1, t)] [(1, s)]).interpret.eval := by
  apply ext_input hAG hA hC
  intro g x
  rw [left_one, right_one]
  exact columns hGE hAG hA hC hGB hDB hEB r t s g x

-- Step 3: expanding the three right labels produces the product of their
-- coefficients. Evaluating the middle left label is linear even when several
-- triples produce the same eligible dot, so their coefficients add there.
set_option maxHeartbeats 1500000 in
private theorem weighted_eq (hGE : (GE : Set U) = Set.image2 (fun g e : U => g * e) (G : Set U) (E : Set U))
    (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (rs : DotLabel Complex ((b hA).comp (i A)) ((d D).comp (j U)))
    (ts : DotLabel Complex ((a hAG).comp (i A)) ((c hC).comp (k C)))
    (ss : DotLabel Complex ((e hC).comp (k C)) ((f E).comp (j U))) :
    (left hAG hA hC hGB hDB hEB
      (middleLabel hAG hA hC hGB hDB hEB rs ts ss).terms).interpret.eval =
      (right hAG hA hC rs.terms ts.terms ss.terms).interpret.eval := by
  apply ext_input hAG hA hC
  intro g x
  have hl := left_linear hAG hA hC hGB hDB hEB
    (middleLabel hAG hA hC hGB hDB hEB rs ts ss) g x
  have hr := right_linear hAG hA hC rs ts ss g x
  refine hl.trans (Eq.trans ?_ hr.symm)
  let L := fun m : MDot hDB hEB =>
    leftCol hC hGB hEB ((incl hGB).toHom g * (incl hDB).toHom x * m.element)
  change freeLift Complex L (middleLabel hAG hA hC hGB hDB hEB rs ts ss) = _
  simp only [middleLabel, map_finsuppSum, freeLift_single]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg ((rs r * ts t * ss s) • ·) (columns hGE hAG hA hC hGB hDB hEB r t s g x)

private abbrev Parabolic (H : Subgroup (Equiv.Perm Nat)) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H = iSup (fun i => MonoidHom.range
      (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ blocks i)))

-- Step 4: apply the registered finite-family result in the full permutation
-- group, where its partition hypotheses are stated. Taking the union of
-- the displayed blocks supplies its finite ground set.
private theorem parabolic_sup {H K : Subgroup (Equiv.Perm Nat)}
    (hH : Parabolic H) (hK : Parabolic K) : Parabolic (H ⊔ K) := by
  let P := Equiv.Perm Nat
  let family : Bool → Subgroup P := fun i => if i then K else H
  have data (m : Bool) : Parabolic (family m) := by
    cases m
    · exact hH
    · exact hK
  have supplied := FiniteParabolicJoinOfFamily family (by
    intro m
    obtain ⟨n, blocks, hn, hd, hm⟩ := data m
    exact ⟨(Finset.univ : Finset (Fin n)).biUnion blocks, n, blocks,
      hn, hd, fun x => by simp only [Finset.mem_biUnion, Finset.mem_univ, true_and], hm⟩)
  have result := supplied.1.1.1
  have eq : (⨆ m, family m) = H ⊔ K := by
    apply le_antisymm
    · apply iSup_le
      intro m
      cases m
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup family false) (le_iSup family true)
  rw [← Subgroup.iSup_eq_closure, eq] at result
  obtain ⟨_, n, blocks, hn, hd, _, hm⟩ := result
  exact ⟨n, blocks, hn, hd, hm⟩

end
end CaseSixJoinAux

set_option maxHeartbeats 2000000 in
theorem ParabolicCaseSixReplacementThroughJoin : (
let P := Equiv.Perm Nat
let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let F : Subgroup U := ⊥
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H =
      iSup (fun i => MonoidHom.range
        (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ blocks i)))
∀ {G A D C E : Subgroup U},
  parabolic G → parabolic A → parabolic D → parabolic C → parabolic E →
  ∀ (GE : Subgroup U),
    (GE : Set U) = Set.image2 (fun g e : U => g * e) (G : Set U) (E : Set U) →
    ∀ (hA : D ⊓ GE = A) (hC : G ⊓ E = C) (hAG : A ≤ G),
  let B := (G ⊔ D) ⊔ E
  let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
    (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
  let a := incl hAG
  let b := incl (show A ≤ D by rw [← hA]; exact inf_le_left)
  let d := incl (show F ≤ D from bot_le)
  let c := incl (show C ≤ G by rw [← hC]; exact inf_le_left)
  let e := incl (show C ≤ E by rw [← hC]; exact inf_le_right)
  let f := incl (show F ≤ E from bot_le)
  let u := incl (show G ≤ B from le_trans le_sup_left le_sup_left)
  let v := incl (show D ≤ B from le_trans le_sup_right le_sup_left)
  let w := incl (show E ≤ B from le_sup_right)
  let i := incl (show F ≤ A from bot_le)
  let j := MackeyDiagrams.ConjEmbedding.id F
  let k := incl (show F ≤ C from bot_le)
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    ordinary (MackeyDiagrams.Diagram.id p)
  let bottom := tensor (up a) (tensor (down b) (up d))
  let top := tensor (up c) (tensor (down e) (up f))
  let atLeft := fun {K J J' L M : Subgroup U}
      {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
      {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
      (tail : MackeyDiagrams.Word L M)
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
    stack (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
      (stack (juxtapose crossing (drawId tail))
        (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
  let finiteFibers := fun {H K L M : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K M) (β : MackeyDiagrams.ConjEmbedding L M)
      (γ : MackeyDiagrams.ConjEmbedding H K) (δ : MackeyDiagrams.ConjEmbedding H L)
      (dot : MackeyDiagrams.Dot (comp α γ) (comp β δ)) =>
    ∀ z, Set.Finite {y | MackeyDiagrams.Generator.mixedMultiplicationBasis α β γ δ dot y = z}
  let lowerOne : MackeyDiagrams.Dot (comp u a) (comp v b) :=
    ⟨1, fun x => by simpa only [mul_one, one_mul] using
      (show MackeyDiagrams.ConjEmbedding.toHom (comp u a) x =
        MackeyDiagrams.ConjEmbedding.toHom (comp v b) x from rfl)⟩
  let upperOne : MackeyDiagrams.Dot (comp u c) (comp w e) :=
    ⟨1, fun x => by simpa only [mul_one, one_mul] using
      (show MackeyDiagrams.ConjEmbedding.toHom (comp u c) x =
        MackeyDiagrams.ConjEmbedding.toHom (comp w e) x from rfl)⟩
  let RightLower := MackeyDiagrams.Dot (comp b i) (comp d j)
  let RightMiddle := MackeyDiagrams.Dot (comp a i) (comp c k)
  let RightUpper := MackeyDiagrams.Dot (comp e k) (comp f j)
  let LeftMiddle := MackeyDiagrams.Dot (comp v d) (comp w f)
  let middleDot := fun (r : RightLower) (t : RightMiddle) (s : RightUpper) =>
    let z := (MackeyDiagrams.ConjEmbedding.toHom v (MackeyDiagrams.Dot.element r))⁻¹ *
      MackeyDiagrams.ConjEmbedding.toHom u (MackeyDiagrams.Dot.element t) *
      MackeyDiagrams.ConjEmbedding.toHom w (MackeyDiagrams.Dot.element s)
    (⟨z, fun x => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.property)
      simp [hx]⟩ : LeftMiddle)
  ∃ (hLeft : finiteFibers u w c e upperOne)
    (hRight : ∀ r : RightLower, finiteFibers b d i j r),
  let leftDrawing := fun (middle : List (Complex × LeftMiddle)) =>
    (stack
      (atLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b [(1, lowerOne)]))
      (stack (juxtapose (drawId (down u)) (MackeyDiagrams.LabelledDrawing.parallelUp v d w f middle))
        (atLeft (up f) (MackeyDiagrams.LabelledDrawing.compactProjection u w c e
          [(1, ⟨upperOne, hLeft⟩)]))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let rightDrawing := fun
      (lower : List (Complex × MackeyDiagrams.ProjectionDot.Mixed b d i j))
      (middle : List (Complex × RightMiddle)) (upper : List (Complex × RightUpper)) =>
    (stack
      (juxtapose (drawId (up a)) (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
      (stack (atLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i c k middle))
        (juxtapose (drawId (up c)) (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j upper))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let rightProjectionTerm := fun (r : RightLower) =>
    (⟨r, hRight r⟩ : MackeyDiagrams.ProjectionDot.Mixed b d i j)
  let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  parabolic B ∧
    (∀ (r : RightLower) (t : RightMiddle) (s : RightUpper),
      evaluate (leftDrawing [(1, middleDot r t s)]) =
        evaluate (rightDrawing [(1, rightProjectionTerm r)] [(1, t)] [(1, s)])) ∧
    (∀ (rs : MackeyDiagrams.DotLabel Complex (comp b i) (comp d j))
        (ts : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
        (ss : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j)),
      let middleLabel : MackeyDiagrams.DotLabel Complex (comp v d) (comp w f) :=
        Finsupp.sum rs (fun r cr =>
          Finsupp.sum ts (fun t ct =>
            Finsupp.sum ss (fun s cs => Finsupp.single (middleDot r t s) (cr * ct * cs))))
      let lowerTerms := List.map (fun (term : Complex × RightLower) =>
        (Prod.fst term, rightProjectionTerm (Prod.snd term))) (MackeyDiagrams.DotLabel.terms rs)
      evaluate (leftDrawing (MackeyDiagrams.DotLabel.terms middleLabel)) =
        evaluate (rightDrawing lowerTerms (MackeyDiagrams.DotLabel.terms ts)
          (MackeyDiagrams.DotLabel.terms ss)))
) :=
by
  classical
  -- Xiao, Proposition 8.8, second assertion and lower diagram, archived
  -- source/mackey-bimodules.pdf p. 41 (SHA-256
  -- bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and published 28 November revision p. 43 (SHA-256
  -- 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- This endpoint has no linked numbered Alphabeta proof. The numbered
  -- comments in the helpers follow the article calculation. The Lean drawings
  -- use explicit associators and finite-fiber witnesses to compare evaluations
  -- at the same boundary, as in the revision's diagram notation.
  intro P finitary U F parabolic G A D C E hG _ hD _ hE GE hGE hA hC hAG
    B incl a b d c e f u v w i j k up down tensor comp stack juxtapose ordinary
    drawId bottom top atLeft finiteFibers lowerOne upperOne RightLower RightMiddle
    RightUpper LeftMiddle middleDot
  have hGB : G ≤ B := le_trans le_sup_left le_sup_left
  have hDB : D ≤ B := le_trans le_sup_right le_sup_left
  have hEB : E ≤ B := le_sup_right
  have hLeft := CaseSixJoinAux.finite_of_product u w c e upperOne
    (CaseSixJoinAux.finite_injective (CaseSixJoinAux.left_inj hC hGB hEB))
  have hRight (r : RightLower) := CaseSixJoinAux.finite_of_product b d i j r
    (CaseSixJoinAux.finite_injective (CaseSixJoinAux.right_inj hA r))
  refine ⟨hLeft, hRight, ?_⟩
  intro leftDrawing rightDrawing rightProjectionTerm evaluate
  refine ⟨?_, ?_, ?_⟩
  · change CaseSixJoinAux.Parabolic (((G ⊔ D) ⊔ E).map finitary.subtype)
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact CaseSixJoinAux.parabolic_sup (CaseSixJoinAux.parabolic_sup hG hD) hE
  · intro r t s
    exact CaseSixJoinAux.singleton_eq hGE hAG hA hC hGB hDB hEB r t s
  · intro rs ts ss middleLabel lowerTerms
    exact CaseSixJoinAux.weighted_eq hGE hAG hA hC hGB hDB hEB rs ts ss

#print axioms ParabolicCaseSixReplacementThroughJoin
