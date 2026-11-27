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

private abbrev leftFiber (z : P) :=
  {w | Generator.mixedProduct b p (Generator.mixedMultiplicationBasis b p a b leftUnit w) = z}

private theorem finite_leftFiber (z : P) : (leftFiber z).Finite := by
  change {w | Generator.mixedProduct b p
    (Generator.mixedMultiplicationBasis b p a b leftUnit w) = z}.Finite
  rw [lift_fiber_left]
  exact Set.finite_singleton _

private abbrev pairWord := tensor (up a) (down b)

private abbrev leftPoint (x : U) := pairWord.basis.pair (Biset.induction b)
  ((Biset.induction a).pair (Biset.restriction b) 1 (xP x)) 1

private abbrev nativeLeft :=
  LabelledDrawing.vertical
    (LabelledDrawing.horizontal (LabelledDrawing.mixedMultiplication b p a b [(1, leftUnit)])
      (drawId (up b)))
    (LabelledDrawing.vertical (associate (down b) (up p) (up b))
      (LabelledDrawing.vertical
        (LabelledDrawing.horizontal (drawId (down b))
          (LabelledDrawing.parallelUp p b p b [(1, Dot.id (comp p b))]))
        (LabelledDrawing.vertical (unassociate (down b) (up p) (up b))
          (LabelledDrawing.horizontal
            (LabelledDrawing.compactProjection b p a b [(1, projectionTerm b p a b leftUnit)])
            (drawId (up b))))))

-- Equation (6.3), steps 1–3 of the compiled left-shape calculation.
private theorem native_left_column (x : U) :
    eval nativeLeft (Finsupp.single (leftPoint x) 1) = Finsupp.single (leftPoint x) 1 := by
  classical
  have h := ((EvaluationWithOneProjection a b b a b b).1 b p p).1
    leftUnit (Dot.id (comp p b)) leftUnit finite_leftFiber 1 (xP x)
  let z := b.toHom 1 * leftUnit.element * p.toHom (xP x) * (Dot.id (comp p b)).element
  change eval nativeLeft (Finsupp.single (leftPoint x) 1) =
    ∑ w ∈ (finite_leftFiber z).toFinset,
      Finsupp.single (pairWord.basis.pair (Biset.induction b) w 1) 1 at h
  have hz : z = xP x := by
    change b.toHom 1 * 1 * xP x * 1 = _
    simp
  have hfinite : (finite_leftFiber (xP x)).toFinset =
      {(Biset.induction a).pair (Biset.restriction b) 1 (xP x)} := by
    ext w
    rw [Set.Finite.mem_toFinset]
    change w ∈ leftFiber (xP x) ↔ _
    rw [show leftFiber (xP x) = _ from lift_fiber_left (xP x)]
    simp
  rw [hz, hfinite, Finset.sum_singleton] at h
  exact h

private abbrev leftIn := unassociate (up a) (down b) (up b)
private abbrev leftOut := associate (up a) (down b) (up b)

private theorem left_stack :
    left.interpret.eval =
      (leftIn.interpret.eval.vertical nativeLeft.interpret.eval).vertical leftOut.interpret.eval := by
  unfold left leftDrawing DotLabel.identity nativeLeft
  simp only [terms_one, List.map_cons, List.map_nil] <;> rfl

-- The associators carry the same representatives to and from the
-- supplier's left-associated tensor word.
private theorem left_column (x : U) : eval left (basis x) = basis x := by
  have hi : eval leftIn (basis x) = Finsupp.single (leftPoint x) 1 :=
    Diagram.eval_unassociate_single (R := Complex) (up a) (down b) (up b) 1 (xP x) 1 1
  have ho : eval leftOut (Finsupp.single (leftPoint x) 1) = basis x :=
    Diagram.eval_associate_single (R := Complex) (up a) (down b) (up b) 1 (xP x) 1 1
  calc
    eval left (basis x) = eval leftOut (eval nativeLeft (eval leftIn (basis x))) :=
      congrArg (fun m : Biset.Hom Complex boundary.basis boundary.basis => m.toLinearMap (basis x))
        left_stack
    _ = eval leftOut (eval nativeLeft (Finsupp.single (leftPoint x) 1)) :=
      congrArg (fun v => eval leftOut (eval nativeLeft v)) hi
    _ = eval leftOut (Finsupp.single (leftPoint x) 1) :=
      congrArg (fun v => eval leftOut v) (native_left_column x)
    _ = basis x := ho


end
end CaseFiveTwoTermsProof
