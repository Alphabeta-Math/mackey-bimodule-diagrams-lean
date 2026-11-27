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

private theorem eval_stack {K H : Subgroup U} {w w' w'' : Word K H}
    (d : LabelledDrawing Complex w w') (e : LabelledDrawing Complex w' w'') :
    (d.vertical e).interpret.eval = d.interpret.eval.vertical e.interpret.eval := rfl

-- Equation (6.3), steps 1–3 of the compiled left-shape calculation.
-- Its input and output are left-associated. The two associators in the
-- reviewed drawing carry the same basis representatives to and from that form.
private theorem left_column (x : U) : eval left (basis x) = basis x := by
  classical
  let fiber (z : P) :=
    {w | Generator.mixedProduct b p (Generator.mixedMultiplicationBasis b p a b leftUnit w) = z}
  have hf (z : P) : (fiber z).Finite := by
    dsimp only [fiber]
    rw [lift_fiber_left]
    exact Set.finite_singleton _
  let native :=
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
  let pairWord := tensor (up a) (down b)
  let nativePoint := pairWord.basis.pair (Biset.induction b)
    ((Biset.induction a).pair (Biset.restriction b) 1 (xP x)) 1
  have h := ((EvaluationWithOneProjection a b b a b b).1 b p p).1
    leftUnit (Dot.id (comp p b)) leftUnit hf 1 (xP x)
  have hNative : eval native (Finsupp.single nativePoint 1) =
      ∑ w ∈ (hf (xP x)).toFinset, Finsupp.single (pairWord.basis.pair (Biset.induction b) w 1) 1 := by
    let z := b.toHom 1 * leftUnit.element * p.toHom (xP x) * (Dot.id (comp p b)).element
    change eval native (Finsupp.single nativePoint 1) =
      ∑ w ∈ (hf z).toFinset, Finsupp.single (pairWord.basis.pair (Biset.induction b) w 1) 1 at h
    have hz : z = xP x := by
      change b.toHom 1 * 1 * xP x * 1 = _
      simp
    rw [hz] at h
    exact h
  have hfinite : (hf (xP x)).toFinset =
      {(Biset.induction a).pair (Biset.restriction b) 1 (xP x)} := by
    ext w
    rw [Set.Finite.mem_toFinset]
    change w ∈ fiber (xP x) ↔ _
    rw [show fiber (xP x) = _ from lift_fiber_left (xP x)]
    simp
  rw [hfinite, Finset.sum_singleton] at hNative
  have hStack : left.interpret.eval =
      (((unassociate (up a) (down b) (up b)).interpret.eval).vertical native.interpret.eval).vertical
        (associate (up a) (down b) (up b)).interpret.eval := by
    simp only [DotLabel.identity, terms_one, List.map_cons, List.map_nil, native,
      eval_stack, Biset.Hom.vertical_assoc]
  have hi : (Diagram.unassociate (R := Complex) (up a) (down b) (up b)).eval.toLinearMap (basis x) =
      Finsupp.single nativePoint 1 := by
    exact Diagram.eval_unassociate_single (R := Complex) (up a) (down b) (up b) 1 (xP x) 1 1
  have ho : (Diagram.associate (R := Complex) (up a) (down b) (up b)).eval.toLinearMap
      (Finsupp.single nativePoint 1) = basis x := by
    exact Diagram.eval_associate_single (R := Complex) (up a) (down b) (up b) 1 (xP x) 1 1
  unfold eval
  rw [hStack]
  change (Diagram.associate (R := Complex) (up a) (down b) (up b)).eval.toLinearMap (eval native
    ((Diagram.unassociate (R := Complex) (up a) (down b) (up b)).eval.toLinearMap (basis x))) = _
  rw [hi, hNative]
  exact ho

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
    simpa only [singletonRight, rightDrawing, rightBelow, rightAbove, DotLabel.identity, terms_one,
      List.map_cons, List.map_nil, eval, eval_stack, Biset.Hom.vertical_assoc] using h
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
private theorem apex_obstruction
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
private theorem two_term_identity :
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

theorem CaseFiveRequiresTwoTerms : (
let U := Multiplicative (ZMod 2)
let g : U := Multiplicative.ofAdd (1 : ZMod 2)
let T : Subgroup U := ⊥
let P : Subgroup U := ⊤
let a := MackeyDiagrams.ConjEmbedding.id T
let b : MackeyDiagrams.ConjEmbedding T P :=
  { toHom := Subgroup.inclusion bot_le
    hasRepresentative := ⟨1, fun _ => by simp⟩ }
let p := MackeyDiagrams.ConjEmbedding.id P
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let boundary := tensor (up a) (tensor (down b) (up b))
let openRight := tensor (tensor (up a) (up a)) (down a)
let apex := tensor (up (comp a a)) (down a)
let drawId := fun {K H : Subgroup U} (w : MackeyDiagrams.Word K H) =>
  MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) w)
let associate := fun {K H J F : Subgroup U}
    (x : MackeyDiagrams.Word K H) (y : MackeyDiagrams.Word H J)
    (z : MackeyDiagrams.Word J F) =>
  MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate (R := Complex) x y z)
let unassociate := fun {K H J F : Subgroup U}
    (x : MackeyDiagrams.Word K H) (y : MackeyDiagrams.Word H J)
    (z : MackeyDiagrams.Word J F) =>
  MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate (R := Complex) x y z)
let projectionTerm := fun {K H M L : Subgroup U}
    (f : MackeyDiagrams.ConjEmbedding K M) (h : MackeyDiagrams.ConjEmbedding H M)
    (l : MackeyDiagrams.ConjEmbedding L K) (r : MackeyDiagrams.ConjEmbedding L H)
    (d : MackeyDiagrams.Dot (comp f l) (comp h r)) =>
  ({ dot := d
     finite := fun z => by
       let : Finite U := inferInstanceAs (Finite (ZMod 2))
       let : Finite ((MackeyDiagrams.Word.basis (tensor (up l) (down r))).carrier) := by
         change Finite (Quotient (MackeyDiagrams.Biset.balance
           (MackeyDiagrams.Biset.induction l) (MackeyDiagrams.Biset.restriction r)))
         infer_instance
       exact Set.toFinite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis f h l r d w = z}
    } : MackeyDiagrams.ProjectionDot.Mixed f h l r)
let leftUnit : MackeyDiagrams.Dot (comp b a) (comp p b) :=
  { element := 1
    intertwines := fun h => by
      have hh : h = 1 := Subsingleton.elim _ _
      simp [hh] }
let leftDrawing := fun
    (r : MackeyDiagrams.DotLabel Complex (comp b a) (comp p b))
    (t : MackeyDiagrams.DotLabel Complex (comp p b) (comp p b))
    (s : MackeyDiagrams.DotLabel Complex (comp b a) (comp p b)) =>
  let lower := MackeyDiagrams.LabelledDrawing.mixedMultiplication b p a b
    (MackeyDiagrams.DotLabel.terms r)
  let middle := MackeyDiagrams.LabelledDrawing.parallelUp p b p b
    (MackeyDiagrams.DotLabel.terms t)
  let upper := MackeyDiagrams.LabelledDrawing.compactProjection b p a b
    (List.map (fun cs => (cs.1, projectionTerm b p a b cs.2)) (MackeyDiagrams.DotLabel.terms s))
  (MackeyDiagrams.LabelledDrawing.vertical (unassociate (up a) (down b) (up b))
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal lower (drawId (up b)))
      (MackeyDiagrams.LabelledDrawing.vertical (associate (down b) (up p) (up b))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down b)) middle)
          (MackeyDiagrams.LabelledDrawing.vertical (unassociate (down b) (up p) (up b))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.horizontal upper (drawId (up b)))
              (associate (up a) (down b) (up b))))))) :
    MackeyDiagrams.LabelledDrawing Complex boundary boundary)
let left := leftDrawing (Finsupp.single leftUnit 1)
  (MackeyDiagrams.DotLabel.identity (R := Complex) (comp p b)) (Finsupp.single leftUnit 1)
let rightBelow := fun (r : MackeyDiagrams.DotLabel Complex (comp b a) (comp b a)) =>
  let lower := MackeyDiagrams.LabelledDrawing.compactProjection b b a a
    (List.map (fun cr => (cr.1, projectionTerm b b a a cr.2)) (MackeyDiagrams.DotLabel.terms r))
  (MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal (drawId (up a)) lower)
    (unassociate (up a) (up a) (down a)) :
    MackeyDiagrams.LabelledDrawing Complex boundary openRight)
let rightAbove := fun
    (t : MackeyDiagrams.DotLabel Complex (comp a a) (comp a a))
    (s : MackeyDiagrams.DotLabel Complex (comp b a) (comp b a)) =>
  let middle := MackeyDiagrams.LabelledDrawing.parallelUp a a a a (MackeyDiagrams.DotLabel.terms t)
  let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication b b a a (MackeyDiagrams.DotLabel.terms s)
  (MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal middle (drawId (down a)))
    (MackeyDiagrams.LabelledDrawing.vertical (associate (up a) (up a) (down a))
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (up a)) upper)) :
    MackeyDiagrams.LabelledDrawing Complex openRight boundary)
let rightDrawing := fun
    (r : MackeyDiagrams.DotLabel Complex (comp b a) (comp b a))
    (t : MackeyDiagrams.DotLabel Complex (comp a a) (comp a a))
    (s : MackeyDiagrams.DotLabel Complex (comp b a) (comp b a)) =>
  MackeyDiagrams.LabelledDrawing.vertical (rightBelow r) (rightAbove t s)
let eval := fun {w w' : MackeyDiagrams.Word T T} (drawing : MackeyDiagrams.LabelledDrawing Complex w w') =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
let mergeToApex : MackeyDiagrams.Diagram Complex openRight apex :=
  MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeUp a a)
    (MackeyDiagrams.Diagram.id (down a))
let splitFromApex : MackeyDiagrams.Diagram Complex apex openRight :=
  MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.splitUp a a)
    (MackeyDiagrams.Diagram.id (down a))
let toApex := fun r => LinearMap.comp
  (MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval mergeToApex))
  (eval (rightBelow r))
let fromApex := fun t s => LinearMap.comp (eval (rightAbove t s))
  (MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval splitFromApex))
let rightDot := fun x : U =>
  ({ element := Subgroup.topEquiv.symm x
     intertwines := fun h => by
       have hh : h = 1 := Subsingleton.elim _ _
       simp [hh] } : MackeyDiagrams.Dot (comp b a) (comp b a))
let singletonRight := fun r s : U =>
  rightDrawing (Finsupp.single (rightDot r) 1)
    (MackeyDiagrams.DotLabel.identity (R := Complex) (comp a a)) (Finsupp.single (rightDot s) 1)
let basis := fun x : U =>
  Finsupp.single
    (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor (down b) (up b))) 1
      (MackeyDiagrams.Generator.mixedPair b b (Subgroup.topEquiv.symm x))) (1 : Complex)
eval left = LinearMap.id ∧
  Nonempty ((MackeyDiagrams.Word.basis apex).carrier ≃ Unit) ∧
  (∀ (r : MackeyDiagrams.DotLabel Complex (comp b a) (comp b a))
      (t : MackeyDiagrams.DotLabel Complex (comp a a) (comp a a))
      (s : MackeyDiagrams.DotLabel Complex (comp b a) (comp b a)),
    eval (rightDrawing r t s) = LinearMap.comp (fromApex t s) (toApex r) ∧
    eval (rightDrawing r t s) ≠ eval left) ∧
  eval left = eval (MackeyDiagrams.LabelledDrawing.add (singletonRight 1 1) (singletonRight g g)) ∧
  (∀ r s x : U,
    eval (singletonRight r s) (basis x) = if x = r then basis s else 0)
) :=
(by
  classical
  -- Xiao, Example 6.5, archived PDF p. 27 and 28 November revision p. 29.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- EvaluationWithOneProjection supplies both finite-fiber columns, (6.3) and (6.4).
  refine ⟨?_, ⟨CaseFiveTwoTermsProof.apex_equiv⟩, ?_,
    CaseFiveTwoTermsProof.two_term_identity, CaseFiveTwoTermsProof.right_column⟩
  · apply CaseFiveTwoTermsProof.basis_ext
    exact CaseFiveTwoTermsProof.left_column
  · intro r t s
    refine ⟨CaseFiveTwoTermsProof.factor r t s, ?_⟩
    rw [CaseFiveTwoTermsProof.factor r t s]
    exact CaseFiveTwoTermsProof.apex_obstruction
      (CaseFiveTwoTermsProof.toApex r) (CaseFiveTwoTermsProof.fromApex t s))

#print axioms CaseFiveRequiresTwoTerms
