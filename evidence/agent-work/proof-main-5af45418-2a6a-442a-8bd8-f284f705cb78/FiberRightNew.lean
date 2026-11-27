import MackeyDiagrams
import Proofs.EvaluationWithOneProjection

set_option maxHeartbeats 400000

namespace CaseFiveTwoTermsProof
open MackeyDiagrams
noncomputable section

private abbrev U := Multiplicative (ZMod 2)

private abbrev g : U := Multiplicative.ofAdd (1 : ZMod 2)

private abbrev T : Subgroup U := ⊥

private abbrev P : Subgroup U := ⊤

private abbrev a := ConjEmbedding.id T

private abbrev b : ConjEmbedding T P :=
  { toHom := Subgroup.inclusion bot_le
    hasRepresentative := ⟨1, fun _ => by simp⟩ }

private abbrev p := ConjEmbedding.id P

private abbrev comp := @ConjEmbedding.comp U _

private abbrev up := @Word.up U _

private abbrev down := @Word.down U _

private abbrev tensor := @Word.tensor U _

private abbrev boundary := tensor (up a) (tensor (down b) (up b))

private abbrev openRight := tensor (tensor (up a) (up a)) (down a)

private abbrev apex := tensor (up (comp a a)) (down a)

private abbrev drawId := fun {K H : Subgroup U} (w : Word K H) =>
  LabelledDrawing.ordinary (Diagram.id (R := Complex) w)

private abbrev associate := fun {K H J F : Subgroup U}
    (x : Word K H) (y : Word H J)
    (z : Word J F) =>
  LabelledDrawing.ordinary (Diagram.associate (R := Complex) x y z)

private abbrev unassociate := fun {K H J F : Subgroup U}
    (x : Word K H) (y : Word H J)
    (z : Word J F) =>
  LabelledDrawing.ordinary (Diagram.unassociate (R := Complex) x y z)

private abbrev projectionTerm := fun {K H M L : Subgroup U}
    (f : ConjEmbedding K M) (h : ConjEmbedding H M)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (d : Dot (comp f l) (comp h r)) =>
  ({ dot := d
     finite := fun z => by
       let : Finite U := inferInstanceAs (Finite (ZMod 2))
       let : Finite ((Word.basis (tensor (up l) (down r))).carrier) := by
         change Finite (Quotient (Biset.balance
           (Biset.induction l) (Biset.restriction r)))
         infer_instance
       exact Set.toFinite {w | Generator.mixedMultiplicationBasis f h l r d w = z}
    } : ProjectionDot.Mixed f h l r)

private abbrev leftUnit : Dot (comp b a) (comp p b) :=
  { element := 1
    intertwines := fun h => by
      have hh : h = 1 := Subsingleton.elim _ _
      simp [hh] }

private abbrev leftDrawing := fun
    (r : DotLabel Complex (comp b a) (comp p b))
    (t : DotLabel Complex (comp p b) (comp p b))
    (s : DotLabel Complex (comp b a) (comp p b)) =>
  let lower := LabelledDrawing.mixedMultiplication b p a b
    (DotLabel.terms r)
  let middle := LabelledDrawing.parallelUp p b p b
    (DotLabel.terms t)
  let upper := LabelledDrawing.compactProjection b p a b
    (List.map (fun cs => (cs.1, projectionTerm b p a b cs.2)) (DotLabel.terms s))
  (LabelledDrawing.vertical (unassociate (up a) (down b) (up b))
    (LabelledDrawing.vertical
      (LabelledDrawing.horizontal lower (drawId (up b)))
      (LabelledDrawing.vertical (associate (down b) (up p) (up b))
        (LabelledDrawing.vertical
          (LabelledDrawing.horizontal (drawId (down b)) middle)
          (LabelledDrawing.vertical (unassociate (down b) (up p) (up b))
            (LabelledDrawing.vertical
              (LabelledDrawing.horizontal upper (drawId (up b)))
              (associate (up a) (down b) (up b))))))) :
    LabelledDrawing Complex boundary boundary)

private abbrev left := leftDrawing (Finsupp.single leftUnit 1)
  (DotLabel.identity (R := Complex) (comp p b)) (Finsupp.single leftUnit 1)

private abbrev rightBelow := fun (r : DotLabel Complex (comp b a) (comp b a)) =>
  let lower := LabelledDrawing.compactProjection b b a a
    (List.map (fun cr => (cr.1, projectionTerm b b a a cr.2)) (DotLabel.terms r))
  (LabelledDrawing.vertical
    (LabelledDrawing.horizontal (drawId (up a)) lower)
    (unassociate (up a) (up a) (down a)) :
    LabelledDrawing Complex boundary openRight)

private abbrev rightAbove := fun
    (t : DotLabel Complex (comp a a) (comp a a))
    (s : DotLabel Complex (comp b a) (comp b a)) =>
  let middle := LabelledDrawing.parallelUp a a a a (DotLabel.terms t)
  let upper := LabelledDrawing.mixedMultiplication b b a a (DotLabel.terms s)
  (LabelledDrawing.vertical
    (LabelledDrawing.horizontal middle (drawId (down a)))
    (LabelledDrawing.vertical (associate (up a) (up a) (down a))
      (LabelledDrawing.horizontal (drawId (up a)) upper)) :
    LabelledDrawing Complex openRight boundary)

private abbrev rightDrawing := fun
    (r : DotLabel Complex (comp b a) (comp b a))
    (t : DotLabel Complex (comp a a) (comp a a))
    (s : DotLabel Complex (comp b a) (comp b a)) =>
  LabelledDrawing.vertical (rightBelow r) (rightAbove t s)

private abbrev eval := fun {w w' : Word T T} (drawing : LabelledDrawing Complex w w') =>
  Biset.Hom.toLinearMap
    (ScopedDiagram.eval (LabelledDrawing.interpret drawing))

private abbrev mergeToApex : Diagram Complex openRight apex :=
  Diagram.horizontal (Diagram.mergeUp a a)
    (Diagram.id (down a))

private abbrev splitFromApex : Diagram Complex apex openRight :=
  Diagram.horizontal (Diagram.splitUp a a)
    (Diagram.id (down a))

private abbrev toApex := fun r => LinearMap.comp
  (Biset.Hom.toLinearMap (Diagram.eval mergeToApex))
  (eval (rightBelow r))

private abbrev fromApex := fun t s => LinearMap.comp (eval (rightAbove t s))
  (Biset.Hom.toLinearMap (Diagram.eval splitFromApex))

private abbrev rightDot := fun x : U =>
  ({ element := Subgroup.topEquiv.symm x
     intertwines := fun h => by
       have hh : h = 1 := Subsingleton.elim _ _
       simp [hh] } : Dot (comp b a) (comp b a))

private abbrev singletonRight := fun r s : U =>
  rightDrawing (Finsupp.single (rightDot r) 1)
    (DotLabel.identity (R := Complex) (comp a a)) (Finsupp.single (rightDot s) 1)

private abbrev basis := fun x : U =>
  Finsupp.single
    (Biset.pair (Biset.induction a)
      (Word.basis (tensor (down b) (up b))) 1
      (Generator.mixedPair b b (Subgroup.topEquiv.symm x))) (1 : Complex)

private abbrev shortcut (x : P) : boundary.basis.carrier :=
  (Biset.induction a).pair (Word.basis (tensor (down b) (up b))) 1
    (Generator.mixedPair b b x)

private theorem shortcut_surjective : Function.Surjective shortcut := by
  intro z
  refine Quotient.inductionOn z (fun xy => ?_)
  obtain ⟨u, y⟩ := xy
  have hu : u = (1 : T) := Subsingleton.elim _ _
  subst u
  exact ⟨Generator.mixedProduct b b y, congrArg
    ((Biset.induction a).pair _ 1) (Generator.mixedPair_mixedProduct b b y)⟩

private theorem shortcut_injective : Function.Injective shortcut := by
  intro x y h
  have he := congrArg (Biset.leftUnitBasis (Word.basis (tensor (down b) (up b)))) h
  change (Word.basis (tensor (down b) (up b))).act 1 (Generator.mixedPair b b x) =
    (Word.basis (tensor (down b) (up b))).act 1 (Generator.mixedPair b b y) at he
  simp only [Biset.one_act] at he
  exact (Generator.mixedEquiv b b).symm.injective he

private theorem basis_ext {A : Type*} [AddCommMonoid A] [Module Complex A]
    {f h : (boundary.basis.carrier →₀ Complex) →ₗ[Complex] A}
    (onBasis : ∀ x, f (basis x) = h (basis x)) : f = h := by
  apply Finsupp.lhom_ext'
  intro z
  apply LinearMap.ext_ring
  obtain ⟨x, rfl⟩ := shortcut_surjective z
  exact onBasis (Subgroup.topEquiv x)

private theorem terms_one {H K : Subgroup U} {e f : ConjEmbedding H K} (d : Dot e f) :
    DotLabel.terms (Finsupp.single d (1 : Complex)) = [(1, d)] := by
  classical
  simp [DotLabel.terms]

private theorem lift_fiber_left (x : P) :
    {w | Generator.mixedProduct b p (Generator.mixedMultiplicationBasis b p a b leftUnit w) = x} =
      {(Biset.induction a).pair (Biset.restriction b) 1 x} := by
  ext w
  refine Quotient.inductionOn w (fun xy => ?_)
  obtain ⟨u, y⟩ := xy
  have hu : u = (1 : T) := Subsingleton.elim _ _
  subst u
  change Generator.mixedProduct b p (Generator.mixedPair b p (b.toHom 1 * 1 * p.toHom y)) = x ↔
    ((Biset.induction a).pair (Biset.restriction b) 1 y) ∈
      ({(Biset.induction a).pair (Biset.restriction b) 1 x} : Set _)
  simp only [Generator.mixedProduct_mixedPair, map_one, one_mul, Set.mem_singleton_iff]
  change y = x ↔ _
  constructor
  · exact congrArg ((Biset.induction a).pair _ 1)
  · intro h
    have hxy := congrArg (Biset.leftUnitBasis (Biset.restriction b)) h
    change b.toHom 1 * y * (1 : P)⁻¹ = b.toHom 1 * x * (1 : P)⁻¹ at hxy
    simpa using hxy

private abbrev xP (x : U) : P := Subgroup.topEquiv.symm x

private theorem lower_fiber (r x : U) :
    {w | Generator.mixedProduct b b (Generator.mixedMultiplicationBasis b b a a (rightDot r) w) = xP x} =
      if x = r then {(Biset.induction a).pair (Biset.restriction a) 1 1} else ∅ := by
  classical
  ext w
  refine Quotient.inductionOn w (fun xy => ?_)
  have hxy : xy = (1, 1) := Subsingleton.elim _ _
  rw [hxy]
  change Generator.mixedProduct b b (Generator.mixedPair b b (b.toHom 1 * xP r * b.toHom 1)) =
    xP x ↔ (Biset.induction a).pair (Biset.restriction a) 1 1 ∈
      (if x = r then {(Biset.induction a).pair (Biset.restriction a) 1 1} else ∅)
  simp only [Generator.mixedProduct_mixedPair, map_one, one_mul, mul_one]
  by_cases hx : x = r
  · subst x
    simp
  · simp [hx, show xP r ≠ xP x from fun h => hx (Subgroup.topEquiv.symm.injective h).symm]

-- Equation (6.4), steps 1–3 of the compiled right-shape calculation.
-- The first crossing has a single possible preimage; the upper multiplication
-- inserts its own label independently of the label that selected the input.
private theorem right_column (r s x : U) :
    eval (singletonRight r s) (basis x) = if x = r then basis s else 0 := by
  classical
  let fiber (z : P) :=
    {w | Generator.mixedProduct b b (Generator.mixedMultiplicationBasis b b a a (rightDot r) w) = z}
  have hf (z : P) : (fiber z).Finite := by
    have h := lower_fiber r (Subgroup.topEquiv z)
    change fiber z = _ at h
    rw [h]
    split
    · exact Set.finite_singleton _
    · exact Set.finite_empty
  have h := ((EvaluationWithOneProjection a b b a b b).2 T a a a).1
    (rightDot r) hf (Dot.id (comp a a)) (rightDot s) 1 (xP x)
  let lowerPoint := (Biset.induction a).pair (Biset.restriction a) 1 1
  have hNative : eval (singletonRight r s) (basis x) =
      ∑ w ∈ (hf (xP x)).toFinset, Finsupp.single
        ((Biset.induction a).pair (Word.basis (tensor (down b) (up b)))
          (1 * a.toHom (Quotient.out w).1 * (Dot.id (comp a a)).element)
          (Generator.mixedPair b b ((rightDot s).element * b.toHom (Quotient.out w).2))) 1 := by
    unfold singletonRight rightDrawing rightBelow rightAbove DotLabel.identity
    simp only [terms_one, List.map_cons, List.map_nil]
    exact h
  have hPoint (w : (Word.basis (tensor (up a) (down a))).carrier) :
      Finsupp.single ((Biset.induction a).pair (Word.basis (tensor (down b) (up b)))
        (1 * a.toHom (Quotient.out w).1 * (Dot.id (comp a a)).element)
        (Generator.mixedPair b b ((rightDot s).element * b.toHom (Quotient.out w).2)))
        (1 : Complex) = basis s := by
    rw [show (Quotient.out w).1 = (1 : T) from Subsingleton.elim _ _,
      show (Quotient.out w).2 = (1 : T) from Subsingleton.elim _ _]
    simp only [map_one, mul_one, Dot.id]
  have hfinite : (hf (xP x)).toFinset = if x = r then {lowerPoint} else ∅ := by
    ext w
    rw [Set.Finite.mem_toFinset]
    change w ∈ fiber (xP x) ↔ _
    rw [show fiber (xP x) = _ from lower_fiber r x]
    by_cases hx : x = r <;> simp [hx, lowerPoint]
  rw [hNative, hfinite]
  by_cases hx : x = r
  · simp only [hx, ite_true, Finset.sum_singleton, hPoint]
  · simp only [hx, ite_false, Finset.sum_empty]


end
end CaseFiveTwoTermsProof
