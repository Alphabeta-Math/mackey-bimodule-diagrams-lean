import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.FiniteParabolicJoinOfFamily

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

-- With trivial F, the right internal subgroup at the embedding into F
-- is trivial. On the left the middle dot's source is F, so every term of
-- the prescribed r⁻¹ts label satisfies the intertwining equation.
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


-- The two parts of EvaluationWithOneProjection supply the article's
-- fiber sums. Its left formula brackets the first two strands together,
-- so the input and output associators below account for the different
-- parentheses at the endpoint. The finite witnesses are the same by
-- proof irrelevance.
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

private abbrev scopedWeighted {H J : Subgroup U} {q q' : Word H J}
    {I : Type} (T : I → Diagram Complex q q') (xs : List (Complex × I)) :=
  ScopedDiagram.linearCombination (xs.map fun (z, i) => (z, .ordinary (T i)))

private theorem framed_columns {K H J : Subgroup U} {p : Word K H} {q q' : Word H J}
    {I : Type} (S : Finset I) (w : I → Complex) (T : I → Diagram Complex q q')
    (v : (p.basis.tensor q.basis).carrier →₀ Complex)
    {V : Type} [AddCommMonoid V] [Module Complex V]
    (finish : ((p.basis.tensor q'.basis).carrier →₀ Complex) →ₗ[Complex] V) :
    finish (((Biset.Hom.id p.basis).horizontal
      (scopedWeighted T (S.toList.map fun i => (w i, i))).eval).toLinearMap v) =
      ∑ i ∈ S, w i • finish (((Biset.Hom.id p.basis).horizontal
        (scopedWeighted T [(1, i)]).eval).toLinearMap v) := by
  have h := framed_weighted (p := p) S w T
  simp only [scopedWeighted, List.map_map, Function.comp_def]
  rw [h]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hm := framed_weighted (p := p) ({()} : Finset Unit)
    (fun _ => (1 : Complex)) (fun _ => T i)
  simp only [Finset.toList_singleton, List.map_cons, List.map_nil, Finset.sum_singleton, one_smul] at hm
  exact congrArg (fun L => w i • finish (L v)) hm.symm

private theorem left_linear (hAG : A ≤ G) (hA : D ⊓ GE = A) (hC : G ⊓ E = C)
    (hGB : G ≤ B) (hDB : D ≤ B) (hEB : E ≤ B)
    (M : DotLabel Complex ((incl hDB).comp (d D)) ((incl hEB).comp (f E))) (g : G) (x : D) :
    ev (left hAG hA hC hGB hDB hEB M.terms) (Finsupp.single (input hAG hA g x) 1) =
      M.sum (fun m z => z • leftCol hC hGB hEB ((incl hGB).toHom g * (incl hDB).toHom x * m.element)) := by
  let start := ev (atLeft (.up (d D)) (.mixedMultiplication (incl hGB) (incl hDB) (a hAG) (b hA)
    [(1, lo hAG hA hGB hDB)])) (Finsupp.single (input hAG hA g x) 1)
  let finish := ev (atLeft (.up (f E)) (.compactProjection (incl hGB) (incl hEB) (c hC) (e hC)
    [(1, ⟨hi hC hGB hEB, finite_of_product _ _ _ _ _
      (finite_injective (left_inj hC hGB hEB))⟩)]))
  let T := Diagram.parallelUp (R := Complex) (incl hDB) (d D) (incl hEB) (f E)
  have h : ev (left hAG hA hC hGB hDB hEB M.terms) (Finsupp.single (input hAG hA g x) 1) =
      ∑ m ∈ M.support, M m •
        ev (left hAG hA hC hGB hDB hEB [(1, m)]) (Finsupp.single (input hAG hA g x) 1) :=
    framed_columns (p := .down (incl hGB)) M.support M T start finish
  refine h.trans (Finset.sum_congr rfl ?_)
  intro m _
  exact congrArg (M m • ·) (left_one hAG hA hC hGB hDB hEB m g x)

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
