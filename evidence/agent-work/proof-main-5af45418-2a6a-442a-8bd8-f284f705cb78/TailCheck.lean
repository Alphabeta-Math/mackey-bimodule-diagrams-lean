import MackeyDiagrams
import Proofs.EvaluationWithOneProjection

set_option maxHeartbeats 2000000

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

private def apex_equiv : apex.basis.carrier ≃ Unit := by
  let z : apex.basis.carrier :=
    (Biset.induction (comp a a)).pair (Biset.restriction a) 1 1
  refine ⟨fun _ => (), fun _ => z, ?_, fun _ => Subsingleton.elim _ _⟩
  intro v
  refine Quotient.inductionOn v (fun xy => ?_)
  have hxy : xy = (1, 1) := Subsingleton.elim _ _
  exact congrArg (Quotient.mk _) hxy.symm

private theorem merge_split :
    mergeToApex.eval.vertical splitFromApex.eval = Biset.Hom.id openRight.basis := by
  change ((Diagram.mergeUp (R := Complex) a a).eval.horizontal
      (Biset.Hom.id ((down a).basis))).vertical
    ((Diagram.splitUp (R := Complex) a a).eval.horizontal (Biset.Hom.id ((down a).basis))) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.vertical (Diagram.mergeUp (R := Complex) a a) (Diagram.splitUp a a)).eval).horizontal
    (Biset.Hom.id ((down a).basis)) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

-- The intermediate word still has three wires. Merge and split give the
-- article's shorter basis model of the same intermediate linear space.
-- For Step 4 the same factorization works for all three finite linear labels,
-- since each whole crossing is already a linear map with this typed boundary.
set_option maxHeartbeats 400000 in
private theorem factor (r : DotLabel Complex (comp b a) (comp b a))
    (t : DotLabel Complex (comp a a) (comp a a))
    (s : DotLabel Complex (comp b a) (comp b a)) :
    eval (rightDrawing r t s) = LinearMap.comp (fromApex t s) (toApex r) := by
  have h (v : openRight.basis.carrier →₀ Complex) :
      splitFromApex.eval.toLinearMap (mergeToApex.eval.toLinearMap v) = v := by
    exact congrArg (fun f : Biset.Hom Complex openRight.basis openRight.basis => f.toLinearMap v)
      merge_split
  ext v : 1
  change eval (rightAbove t s) (eval (rightBelow r) v) =
    eval (rightAbove t s)
      (splitFromApex.eval.toLinearMap (mergeToApex.eval.toLinearMap (eval (rightBelow r) v)))
  rw [h]

private theorem g_ne_one : g ≠ 1 := by
  change (1 : ZMod 2) ≠ 0
  exact one_ne_zero

private theorem two_elements (x : U) : x = 1 ∨ x = g := by
  let y : ZMod 2 := Multiplicative.toAdd x
  have hy := ZMod.val_lt y
  have hy' : y.val = 0 ∨ y.val = 1 := by omega
  rcases hy' with h | h
  · left
    change y = 0
    exact ZMod.val_injective 2 (h.trans ZMod.val_zero.symm)
  · right
    change y = 1
    exact ZMod.val_injective 2 (h.trans (ZMod.val_one'' (by decide : (2 : ℕ) ≠ 1)).symm)

-- The two basis columns are independent. Any composite through the apex
-- would express both as scalar multiples of the same column.
set_option maxHeartbeats 400000 in
private theorem apex_obstruction
    (left_column : ∀ x : U, eval left (basis x) = basis x)
    (A : (boundary.basis.carrier →₀ Complex) →ₗ[Complex] (apex.basis.carrier →₀ Complex))
    (B : (apex.basis.carrier →₀ Complex) →ₗ[Complex] (boundary.basis.carrier →₀ Complex)) :
    B.comp A ≠ eval left := by
  classical
  let z := apex_equiv.symm ()
  let v := B (Finsupp.single z 1)
  have hscale (w : apex.basis.carrier →₀ Complex) :
      w = w z • Finsupp.single z (1 : Complex) := by
    apply Finsupp.ext
    intro q
    have hq : q = z := apex_equiv.injective (Subsingleton.elim _ _)
    subst q
    simp
  intro h
  have hcol (x : U) : (A (basis x)) z • v = basis x := by
    calc
      (A (basis x)) z • v = B (A (basis x)) := by
        rw [← map_smul]
        exact congrArg B (hscale (A (basis x))).symm
      _ = eval left (basis x) := LinearMap.congr_fun h (basis x)
      _ = basis x := left_column x
  have hx : shortcut (xP g) ≠ shortcut (xP 1) := by
    exact fun h => g_ne_one (Subgroup.topEquiv.symm.injective (shortcut_injective h))
  have eval_one := congrArg (fun w : boundary.basis.carrier →₀ Complex =>
    w (shortcut (xP 1))) (hcol 1)
  have eval_cross := congrArg (fun w : boundary.basis.carrier →₀ Complex =>
    w (shortcut (xP 1))) (hcol g)
  have eval_g := congrArg (fun w : boundary.basis.carrier →₀ Complex =>
    w (shortcut (xP g))) (hcol g)
  change (A (basis 1)) z * v (shortcut (xP 1)) =
    Finsupp.single (shortcut (xP 1)) 1 (shortcut (xP 1)) at eval_one
  change (A (basis g)) z * v (shortcut (xP 1)) =
    Finsupp.single (shortcut (xP g)) 1 (shortcut (xP 1)) at eval_cross
  change (A (basis g)) z * v (shortcut (xP g)) =
    Finsupp.single (shortcut (xP g)) 1 (shortcut (xP g)) at eval_g
  rw [Finsupp.single_eq_same] at eval_one eval_g
  rw [Finsupp.single_eq_of_ne hx.symm] at eval_cross
  exact (mul_ne_zero (left_ne_zero_of_mul (eval_g.trans_ne one_ne_zero))
    (right_ne_zero_of_mul (eval_one.trans_ne one_ne_zero))) eval_cross

-- The two disjoint diagonal matrix units sum to the identity on the basis.
set_option maxHeartbeats 400000 in
private theorem two_term_identity
    (left_column : ∀ x : U, eval left (basis x) = basis x)
    (right_column : ∀ r s x : U, eval (singletonRight r s) (basis x) = if x = r then basis s else 0) :
    eval left = eval (LabelledDrawing.add (singletonRight 1 1) (singletonRight g g)) := by
  classical
  apply basis_ext
  intro x
  change eval left (basis x) =
    eval (singletonRight 1 1) (basis x) + eval (singletonRight g g) (basis x)
  rw [left_column, right_column, right_column]
  rcases two_elements x with h | h
  · subst x
    simp [Ne.symm g_ne_one]
  · subst x
    simp [g_ne_one]


end
end CaseFiveTwoTermsProof
