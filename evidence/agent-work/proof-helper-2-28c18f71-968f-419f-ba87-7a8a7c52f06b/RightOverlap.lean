import Mathlib.GroupTheory.Perm.Support
import MackeyDiagrams.DrawingShape
import Proofs.EvaluationWithOneProjection

namespace CaseSixOverlapRight
open MackeyDiagrams
noncomputable section

variable {U : Type*} [Group U] {D E : Subgroup U}

abbrev T : Subgroup U := ⊥
abbrev a : ConjEmbedding (T (U := U)) T := ConjEmbedding.id T

theorem botElement (y : T (U := U)) : y = 1 :=
  Subtype.ext (Subgroup.mem_bot.mp y.property)

def trivialDot {H : Subgroup U} {α β : ConjEmbedding (T (U := U)) H}
    (z : H) : Dot α β :=
  ⟨z, fun y => by rw [botElement y]; simp⟩

abbrev Fiber (U : Type*) [Group U] :=
  ((Biset.induction (a (U := U))).tensor (Biset.restriction a)).carrier

abbrev fiberUnit : Fiber U := (Biset.induction a).pair (Biset.restriction a) 1 1

theorem fiberElement (w : Fiber U) : w = fiberUnit := by
  refine Quotient.inductionOn w ?_
  rintro ⟨y, z⟩
  change (Biset.induction a).pair (Biset.restriction a) y z = fiberUnit
  rw [botElement y, botElement z]

variable (b : ConjEmbedding (T (U := U)) D) (e : ConjEmbedding (T (U := U)) E)

abbrev q (r : D) (w : Fiber U) : D :=
  Generator.mixedProduct b b
    (Generator.mixedMultiplicationBasis b b a a (trivialDot r) w)

theorem q_eq (r : D) (w : Fiber U) : q b r w = r := by
  rw [fiberElement w]
  change (b.toHom 1 * r * b.toHom 1) * 1 = r
  simp only [map_one, one_mul, mul_one]

theorem finiteProduct (r x : D) : Set.Finite {w : Fiber U | q b r w = x} :=
  (Set.finite_singleton fiberUnit).subset (fun w _ => fiberElement w)

theorem finiteProjection (r : D)
    (z : ((Biset.restriction b).tensor (Biset.induction b)).carrier) :
    Set.Finite {w | Generator.mixedMultiplicationBasis b b a a (trivialDot r) w = z} :=
  (finiteProduct b r (Generator.mixedProduct b b z)).subset
    (fun _ hw => congrArg (Generator.mixedProduct b b) hw)

abbrev upW := @Word.up U _
abbrev downW := @Word.down U _
abbrev tensor := @Word.tensor U _
abbrev stack := @LabelledDrawing.vertical U _ Complex _
abbrev beside := @LabelledDrawing.horizontal U _ Complex _
abbrev ordinary := @LabelledDrawing.ordinary U _ Complex _
abbrev straight {K L : Subgroup U} (p : Word K L) := ordinary (Diagram.id p)

abbrev atLeft {K J J' L M : Subgroup U}
    {p : Word K J} {q : Word J L} {p' : Word K J'} {q' : Word J' L}
    (tail : Word L M)
    (crossing : LabelledDrawing Complex (tensor p q) (tensor p' q')) :=
  stack (ordinary (Diagram.unassociate p q tail))
    (stack (beside crossing (straight tail)) (ordinary (Diagram.associate p' q' tail)))

abbrev bottom := tensor (upW a) (tensor (downW b) (upW b))
abbrev top := tensor (upW a) (tensor (downW e) (upW e))

abbrev basisVector {H : Subgroup U} (h : ConjEmbedding (T (U := U)) H) (x : H) :=
  Finsupp.single
    (Biset.pair (Biset.induction a) (Word.basis (tensor (downW h) (upW h)))
      1 (Generator.mixedPair h h x)) (1 : Complex)

abbrev right (r : D) (s : E)
    (hRight : ∀ z, Set.Finite
      {w | Generator.mixedMultiplicationBasis b b a a (trivialDot r) w = z}) :
    LabelledDrawing Complex (bottom b) (top e) :=
  stack
    (beside (straight (upW a))
      (LabelledDrawing.compactProjection b b a a [(1, ⟨trivialDot r, hRight⟩)]))
    (stack
      (atLeft (downW a) (LabelledDrawing.parallelUp a a a a [(1, trivialDot 1)]))
      (beside (straight (upW a))
        (LabelledDrawing.mixedMultiplication e e a a [(1, trivialDot s)])))

abbrev evaluate {p q : Word (T (U := U)) T} (drawing : LabelledDrawing Complex p q) :=
  Biset.Hom.toLinearMap (ScopedDiagram.eval (LabelledDrawing.interpret drawing))

theorem membership (r x : D) (w : Fiber U) :
    w ∈ (finiteProduct b r x).toFinset ↔ x = r := by
  classical
  rw [Set.Finite.mem_toFinset]
  change q b r w = x ↔ x = r
  rw [q_eq, eq_comm]

theorem fiberSum (r : D) (s : E) (x : D) :
    (∑ w ∈ (finiteProduct b r x).toFinset,
      (let rep : T × T := Quotient.out w
       Finsupp.single ((Biset.induction a).pair ((downW e).tensor (upW e)).basis
          (1 * a.toHom rep.1 * 1)
          (Generator.mixedPair e e (s * e.toHom rep.2))) (1 : Complex))) =
      @ite _ (x = r) (Classical.propDecidable (x = r)) (basisVector e s) 0 := by
  classical
  by_cases hx : x = r
  · have hs : (finiteProduct b r x).toFinset = {fiberUnit} := by
      ext w
      rw [membership, Finset.mem_singleton]
      exact ⟨fun _ => fiberElement w, fun _ => hx⟩
    rw [ite_eq_left hx, hs, Finset.sum_singleton]
    have hrep : (Quotient.out (fiberUnit (U := U)) : T × T) = (1, 1) :=
      Prod.ext (botElement _) (botElement _)
    simp only [hrep, map_one, mul_one]
  · have hs : (finiteProduct b r x).toFinset = ∅ := by
      ext w
      simp only [membership, hx, Finset.notMem_empty]
    rw [ite_eq_right hx, hs, Finset.sum_empty]

theorem rightColumn (r : D) (s : E) (x : D)
    (hRight : ∀ z, Set.Finite
      {w | Generator.mixedMultiplicationBasis b b a a (trivialDot r) w = z}) :
    evaluate (right b e r s hRight) (basisVector b x) =
      @ite _ (x = r) (Classical.propDecidable (x = r)) (basisVector e s) 0 := by
  classical
  have h := ((EvaluationWithOneProjection a b b a e e).2 T a a a).1
    (trivialDot r) (finiteProduct b r) (trivialDot 1) (trivialDot s) 1 x
  change evaluate (right b e r s hRight) (basisVector b x) =
    ∑ w ∈ (finiteProduct b r x).toFinset,
      (let rep : T × T := Quotient.out w
       Finsupp.single ((Biset.induction a).pair ((downW e).tensor (upW e)).basis
          (1 * a.toHom rep.1 * 1)
          (Generator.mixedPair e e (s * e.toHom rep.2))) (1 : Complex)) at h
  exact h.trans (fiberSum b e r s x)

-- Direct connection to the reviewed endpoint's right-hand clause.
theorem endpointRight : let P := Equiv.Perm Nat
let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let T : Subgroup U := ⊥
let swap := fun (i j : Nat) (hij : i ≠ j) =>
  (⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩ : U)
let swap12 := swap 1 2 (by decide)
let swap23 := swap 2 3 (by decide)
let D : Subgroup U := Subgroup.closure {swap12}
let E : Subgroup U := Subgroup.closure {swap23}
let includeConj := fun {H K : Subgroup U} (h : H ≤ K) =>
  (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
let a := MackeyDiagrams.ConjEmbedding.id T
let b := includeConj (show T ≤ D from bot_le)
let e := includeConj (show T ≤ E from bot_le)
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
  ∃ (hRight : finiteFibers
        (MackeyDiagrams.Generator.mixedMultiplicationBasis b b a a lowerRight)),
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
      ∀ x : D,
        MackeyDiagrams.Biset.Hom.toLinearMap (evaluate right) (basisVector b x) =
          @ite _ (x = r) (Classical.propDecidable (x = r)) (basisVector e s) 0 := by
  dsimp only
  intro r s
  refine ⟨finiteProjection _ r, ?_⟩
  intro x
  exact rightColumn _ _ r s x (finiteProjection _ r)

end
end CaseSixOverlapRight

#print axioms CaseSixOverlapRight.endpointRight
