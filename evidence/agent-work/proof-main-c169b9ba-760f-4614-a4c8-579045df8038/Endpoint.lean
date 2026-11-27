import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention
import Proofs.MixedCrossingFiberMaps

set_option maxHeartbeats 2000000

namespace EvaluationForTwoProjectionsAux

open MackeyDiagrams
open scoped BigOperators

universe u
noncomputable section
set_option maxHeartbeats 1500000

private abbrev Vec (X : Type*) := X →₀ Complex

-- A contravariant basis map acts by precomposition on coefficients.
private def Pulls {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X) : Prop :=
  ∀ v, L v y = v x

private theorem pulls_single {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X)
    (h : ∀ i : X, L (Finsupp.single i 1) y = Finsupp.single i (1 : Complex) x) :
    Pulls L y x := by
  let l := (Finsupp.lapply y : Vec Y →ₗ[Complex] Complex).comp L
  have he : l = (Finsupp.lapply x : Vec X →ₗ[Complex] Complex) := by
    apply Finsupp.lhom_ext
    intro i w
    have hs : Finsupp.single i w = w • Finsupp.single i (1 : Complex) := by
      simp [Finsupp.smul_single]
    rw [hs, map_smul, map_smul]
    exact congrArg (w • ·) (h i)
  exact fun v => LinearMap.congr_fun he v

private theorem pulls_of_single {X Y : Type*} {L : Vec X →ₗ[Complex] Vec Y}
    {forward : X → Y} {x : X} {y : Y} (inv : ∀ i, forward i = y ↔ i = x)
    (h : ∀ i : X, L (Finsupp.single i 1) = Finsupp.single (forward i) 1) :
    Pulls L y x := by
  classical
  apply pulls_single
  intro i
  rw [h i]
  simp only [Finsupp.single_apply, inv]

private theorem pulls_mixed {U : Type u} [Group U] {K H P L : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (d : ConjEmbedding L K) (e : ConjEmbedding L H)
    (p : ProjectionDot.Mixed a b d e)
    (y : ((Word.up d).tensor (.down e)).basis.carrier) :
    Pulls (Diagram.mixedProjection (R := Complex) a b d e p.dot p.finite).eval.toLinearMap
      y (Generator.mixedMultiplicationBasis a b d e p.dot y) := by
  classical
  apply pulls_single
  intro i
  change (Biset.Hom.transfer Complex (Generator.mixedMultiplicationBasis a b d e p.dot)
    (Generator.mixedMultiplication_equivariant a b d e p.dot) p.finite).toLinearMap
      (Finsupp.single i 1) y = _
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_apply, Finsupp.single_apply]
  by_cases h : i = Generator.mixedMultiplicationBasis a b d e p.dot y
  · simp [h]
  · simp [h, Ne.symm h]

section Balanced
variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {X X' : Biset K H} {Y Y' : Biset H J}

-- The unchanged strand makes the balancing parameter unique at a fixed output
-- representative. Thus no orbit multiplicity is introduced by tensoring a pullback.
private theorem pulls_horizontal_right (L : Biset.Hom Complex X X')
    (free : ∀ (s : Y.carrier) (h : H), Y.act (h, 1) s = s → h = 1)
    {x' : X'.carrier} {x : X.carrier} (hx : Pulls L.toLinearMap x' x) (s : Y.carrier) :
    Pulls (L.horizontal (Biset.Hom.id Y)).toLinearMap (X'.pair Y x' s) (X.pair Y x s) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨i,t⟩ => ?_)
  change (L.horizontal (Biset.Hom.id Y)).toLinearMap (Finsupp.single (X.pair Y i t) 1)
    (X'.pair Y x' s) = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
    (Finsupp.single t 1) (X'.pair Y x' s) = Finsupp.single (X.pair Y i t) 1 (X.pair Y x s)
  by_cases ht : ∃ h : H, Y.act (h, 1) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y i t = X.pair Y (X.act (1,h) i) s := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single s 1) (X'.pair Y x' s) = v x' := by
      apply pulls_single ((Biset.pairLinear Complex X' Y).flip (Finsupp.single s 1))
      intro j
      change Biset.pairLinear Complex X' Y (Finsupp.single j 1) (Finsupp.single s 1)
        (X'.pair Y x' s) = _
      rw [Biset.pairLinear_single, mul_one]
      have hi : X'.pair Y j s = X'.pair Y x' s ↔ j = x' := by
        constructor
        · intro hp
          obtain ⟨k, hk, hs⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (X'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    -- Rechoose the input representative before using the horizontal basis formula.
    have hre := congrArg (fun w => (L.horizontal (Biset.Hom.id Y)).toLinearMap
      (Finsupp.single w 1) (X'.pair Y x' s)) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
      (Finsupp.single t 1) (X'.pair Y x' s) =
      Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single (X.act (1,h) i) 1))
      (Finsupp.single s 1) (X'.pair Y x' s) at hre
    rw [hre, heval, hx _ , he]
    have hi : X.pair Y (X.act (1,h) i) s = X.pair Y x s ↔ X.act (1,h) i = x := by
      constructor
      · intro hp
        obtain ⟨k, hk, hs⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (X.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single t 1) (X'.pair Y x' s) = 0 := by
      have he : (Finsupp.lapply (X'.pair Y x' s) : Vec (X'.tensor Y).carrier →ₗ[Complex] Complex).comp
          ((Biset.pairLinear Complex X' Y).flip (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X' Y (Finsupp.single j r) (Finsupp.single t 1)
          (X'.pair Y x' s) = 0
        rw [Biset.pairLinear_single, mul_one, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, _, hk⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, _, hk⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

private theorem pulls_horizontal_left (L : Biset.Hom Complex Y Y')
    (free : ∀ (s : X.carrier) (h : H), X.act (1, h) s = s → h = 1)
    {y' : Y'.carrier} {y : Y.carrier} (hy : Pulls L.toLinearMap y' y) (s : X.carrier) :
    Pulls ((Biset.Hom.id X).horizontal L).toLinearMap (X.pair Y' s y') (X.pair Y s y) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨t,i⟩ => ?_)
  change ((Biset.Hom.id X).horizontal L).toLinearMap (Finsupp.single (X.pair Y t i) 1)
    (X.pair Y' s y') = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
    (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') = Finsupp.single (X.pair Y t i) 1 (X.pair Y s y)
  by_cases ht : ∃ h : H, X.act (1, h) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y t i = X.pair Y s (Y.act (h,1) i) := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single s 1) v (X.pair Y' s y') = v y' := by
      apply pulls_single (Biset.pairLinear Complex X Y' (Finsupp.single s 1))
      intro j
      rw [Biset.pairLinear_single, one_mul]
      have hi : X.pair Y' s j = X.pair Y' s y' ↔ j = y' := by
        constructor
        · intro hp
          obtain ⟨k, hs, hk⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (Y'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    have hre := congrArg (fun w => ((Biset.Hom.id X).horizontal L).toLinearMap
      (Finsupp.single w 1) (X.pair Y' s y')) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
      (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') =
      Biset.pairLinear Complex X Y' (Finsupp.single s 1)
      (L.toLinearMap (Finsupp.single (Y.act (h,1) i) 1)) (X.pair Y' s y') at hre
    rw [hre, heval, hy _ , he]
    have hi : X.pair Y s (Y.act (h,1) i) = X.pair Y s y ↔ Y.act (h,1) i = y := by
      constructor
      · intro hp
        obtain ⟨k, hs, hk⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (Y.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single t 1) v (X.pair Y' s y') = 0 := by
      have he : (Finsupp.lapply (X.pair Y' s y') : Vec (X.tensor Y').carrier →ₗ[Complex] Complex).comp
          (Biset.pairLinear Complex X Y' (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X Y' (Finsupp.single t 1) (Finsupp.single j r)
          (X.pair Y' s y') = 0
        rw [Biset.pairLinear_single, one_mul, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, hk, _⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, hk, _⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

end Balanced

end
end EvaluationForTwoProjectionsAux

namespace EvaluationForTwoProjectionsAux
open MackeyDiagrams
open scoped BigOperators
universe u
noncomputable section
set_option maxHeartbeats 2000000

variable {U : Type u} [Group U]
variable {K H J L M : Subgroup U}

private abbrev ev {p q : Word K H} (d : LabelledDrawing Complex p q) := d.interpret.eval.toLinearMap

private abbrev drawId (p : Word K H) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private abbrev before {p q r : Word K H} (d : LabelledDrawing Complex p q)
    (e : LabelledDrawing Complex q r) := LabelledDrawing.vertical d e

private abbrev atLeft {p q : Word K H} (d : LabelledDrawing Complex p q)
    (r : Word H J) := LabelledDrawing.horizontal d (drawId r)

private abbrev atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :=
  before (.ordinary (.associate p q r))
    (before (.horizontal (drawId p) d) (.ordinary (.unassociate p q' r')))

private abbrev pair (p : Word K H) (q : Word H J) := p.basis.pair q.basis

private abbrev triple (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :=
  pair (p.tensor q) r (pair p q x y) z

private theorem pulls_before {p q r : Word K H}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex q r}
    {z : r.basis.carrier} {y : q.basis.carrier} {x : p.basis.carrier}
    (he : Pulls (ev e) z y) (hd : Pulls (ev d) y x) : Pulls (ev (before d e)) z x := by
  intro v
  change ev e (ev d v) z = _
  rw [he _, hd _]

private theorem pulls_assoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.associate p q r))) (pair p (q.tensor r) x (pair q r y z))
      (triple p q r x y z) := by
  let i := Biset.associateBasisEquiv p.basis q.basis r.basis
  have hi : ∀ v : _, i v = i (triple p q r x y z) ↔ v = triple p q r x y z :=
    fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨xy,t⟩ => ?_)
  exact Quotient.inductionOn xy (fun ⟨s,w⟩ => Diagram.eval_associate_single p q r s w t 1)

private theorem pulls_unassoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.unassociate p q r))) (triple p q r x y z)
      (pair p (q.tensor r) x (pair q r y z)) := by
  let i := (Biset.associateBasisEquiv p.basis q.basis r.basis).symm
  have hi : ∀ v : _, i v = i (pair p (q.tensor r) x (pair q r y z)) ↔
      v = pair p (q.tensor r) x (pair q r y z) := fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨s,yz⟩ => ?_)
  exact Quotient.inductionOn yz (fun ⟨w,t⟩ => Diagram.eval_unassociate_single p q r s w t 1)

private theorem pulls_atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    {d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')}
    (free : ∀ (s : p.basis.carrier) (h : H), p.basis.act (1, h) s = s → h = 1)
    (s : p.basis.carrier) {x : q'.basis.carrier} {y : r'.basis.carrier}
    {x' : q.basis.carrier} {y' : r.basis.carrier}
    (hd : Pulls (ev d) (pair q' r' x y) (pair q r x' y')) :
    Pulls (ev (atRight p d)) (triple p q' r' s x y) (triple p q r s x' y') := by
  apply pulls_before (pulls_before (pulls_unassoc p q' r' s x y) ?_)
    (pulls_assoc p q r s x' y')
  exact pulls_horizontal_left d.interpret.eval free hd s

private theorem free_up_left (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.induction a).act (h, 1) s = s) : h = 1 := by
  change h * s * (a.toHom 1)⁻¹ = s at eq
  simpa using mul_right_cancel (show h * s = 1 * s by simpa using eq)

private theorem free_up_right (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.induction a).act (1, h) s = s) : h = 1 := by
  change 1 * s * (a.toHom h)⁻¹ = s at eq
  apply a.injective
  have he : (a.toHom h)⁻¹ = 1 :=
    mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_right (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.restriction a).act (1, h) s = s) : h = 1 := by
  change a.toHom 1 * s * h⁻¹ = s at eq
  have he : h⁻¹ = 1 := mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_left (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.restriction a).act (h, 1) s = s) : h = 1 := by
  change a.toHom h * s * (1 : K)⁻¹ = s at eq
  apply a.injective
  exact mul_right_cancel (show a.toHom h * s = a.toHom 1 * s by simpa using eq)

private theorem up_balance (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    pair (Word.up a) (Word.up b) (x * a.toHom y) 1 = pair (Word.up a) (Word.up b) x y := by
  simpa [pair, Word.basis, Biset.induction] using
    (Biset.induction a).pair_balance (Biset.induction b) y x 1

private theorem pulls_merge (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) :
    Pulls (ev (.trivalent (.mergeUp a b))) x (pair (Word.up a) (Word.up b) x 1) := by
  have hi (w : ((Word.up a).tensor (.up b)).basis.carrier) (z : K) :
      Generator.mergeUpBasis a b w = z ↔ w = pair (Word.up a) (Word.up b) z 1 := by
    refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
    change s * a.toHom t = z ↔ pair (Word.up a) (Word.up b) s t = _
    constructor
    · rintro rfl
      exact (up_balance a b s t).symm
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom t = z * a.toHom 1 at eq
      simpa using eq
  apply pulls_of_single (fun w => hi w x)
  intro w
  refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
  exact Diagram.eval_mergeUp_single a b s t 1

private theorem pulls_split (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    Pulls (ev (.trivalent (.splitUp a b))) (pair (Word.up a) (Word.up b) x y) (x * a.toHom y) := by
  apply pulls_single
  intro s
  change (Diagram.splitUp (R := Complex) a b).eval.toLinearMap (Finsupp.single s 1)
    (pair (Word.up a) (Word.up b) x y) = _
  rw [Diagram.eval_splitUp_single]
  classical
  have hi : pair (Word.up a) (Word.up b) s 1 = pair (Word.up a) (Word.up b) x y ↔
      s = x * a.toHom y := by
    constructor
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom 1 = x * a.toHom y at eq
      simpa using eq
    · rintro rfl
      exact up_balance a b x y
  simp only [Finsupp.single_apply, hi]

private theorem sum_eval (p q : Word K H) (xs : List (Complex × Diagram Complex p q)) :
    (ScopedDiagram.linearCombination (xs.map fun (c,d) => (c, ScopedDiagram.ordinary d))).eval.toLinearMap =
      (xs.map fun (c,d) => c • d.eval.toLinearMap).sum := by
  apply LinearMap.ext
  intro v
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c,d⟩
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply]
    rw [ih]
    rfl

private theorem singleton_mixed (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d) :
    ev (.compactProjection a b c d [(1,p)]) =
      (Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem singleton_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) :
    ev (.parallelUp a b c d [(1,p)]) =
      (Diagram.parallelUp (R := Complex) a b c d p).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.parallelUp (R := Complex) a b c d p)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem pulls_compact (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d)
    (x : K) (y : J) :
    Pulls (ev (.compactProjection a b c d [(1,p)])) (pair (Word.up c) (Word.down d) x y)
      (Generator.mixedPair a b (a.toHom x * p.dot.element * b.toHom y)) := by
  rw [singleton_mixed]
  exact pulls_mixed a b c d p _

private theorem pulls_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) (x : K) (y : J) :
    Pulls (ev (.parallelUp a b c d [(1,p)])) (pair (Word.up c) (Word.up d) x y)
      (pair (Word.up a) (Word.up b) (x * c.toHom y * p.element⁻¹) 1) := by
  rw [singleton_parallel]
  intro v
  change ev (.trivalent (.splitUp c d))
    ((Diagram.upDot (R := Complex) p).eval.toLinearMap (ev (.trivalent (.mergeUp a b)) v))
    (pair (Word.up c) (Word.up d) x y) = _
  rw [pulls_split c d x y _]
  have he : Pulls (Diagram.upDot (R := Complex) p).eval.toLinearMap
      (x * c.toHom y) (x * c.toHom y * p.element⁻¹) := by
    refine pulls_of_single (forward := fun z : K => z * p.element)
      ?_ (fun z => Diagram.eval_upDot_single p z 1)
    intro s
    exact eq_mul_inv_iff_mul_eq.symm
  rw [he _, pulls_merge a b _ _]

end
end EvaluationForTwoProjectionsAux

namespace EvaluationForTwoProjectionsAux

open MackeyDiagrams

universe u
noncomputable section
set_option maxHeartbeats 2500000

section Index
variable {U : Type u} [Group U] {K H P L : Subgroup U}
variable (a : ConjEmbedding K P) (b : ConjEmbedding H P)
variable (d : ConjEmbedding L K) (e : ConjEmbedding L H)
variable (p : Dot (a.comp d) (b.comp e))

private abbrev intersection :=
  a.toHom.range ⊓ Subgroup.map (MulAut.conj p.element).toMonoidHom b.toHom.range

private abbrev q := Generator.mixedMultiplicationBasis a b d e p

private theorem lower_le : (a.comp d).toHom.range ≤ intersection a b d e p := by
  rintro _ ⟨l, rfl⟩
  refine ⟨⟨d.toHom l, rfl⟩, b.toHom (e.toHom l), ⟨e.toHom l, rfl⟩, ?_⟩
  change p.element * b.toHom (e.toHom l) * p.element⁻¹ = a.toHom (d.toHom l)
  have h := p.intertwines l
  change a.toHom (d.toHom l) * p.element = p.element * b.toHom (e.toHom l) at h
  rw [← h, mul_inv_cancel_right]

private abbrev HasIndexFormula : Prop :=
    ((∀ z, Set.Finite {w | q a b d e p w = z}) ↔
      ((a.comp d).toHom.range.subgroupOf (intersection a b d e p)).FiniteIndex) ∧
    (∀ z : P, z ∈ Set.range (Generator.mixedProduct a b ∘ q a b d e p) →
      (∀ z, Set.Finite {w | q a b d e p w = z}) →
      Nat.card {w // Generator.mixedProduct a b (q a b d e p w) = z} =
        (a.comp d).toHom.range.relIndex (intersection a b d e p))

private theorem embedding_eq_of_rep {A B : Subgroup U} (i : ConjEmbedding A B) (s : U)
    (hi : ∀ x : A, (i.toHom x : U) = s * (x : U) * s⁻¹) :
    i = ConjEmbedding.ofConjugator s (fun x => hi x ▸ (i.toHom x).property) :=
  ConjEmbedding.ext (MonoidHom.ext (fun x => Subtype.ext (hi x)))

-- Lemma 6.3, equation (6.1). Proposition 5.1 is supplied for representative
-- conjugators. As in the registered finite-fiber convention, choose the
-- inner-left representative to realize the actual typed dot and use the
-- quotient's representative section. Then transport the relative index back
-- along the injective inclusion of the outer group.
private theorem index_formula : HasIndexFormula a b d e p := by
  classical
  obtain ⟨α, hα⟩ := a.hasRepresentative
  obtain ⟨β, hβ⟩ := b.hasRepresentative
  obtain ⟨ε, hε⟩ := e.hasRepresentative
  let δ : U := α⁻¹ * (p.element : U) * (β * ε)
  have hδ (l : L) : (d.toHom l : U) = δ * (l : U) * δ⁻¹ := by
    have h := congrArg (fun x : P => (x : U)) (p.intertwines l)
    change (a.toHom (d.toHom l) : U) * (p.element : U) =
      (p.element : U) * (b.toHom (e.toHom l) : U) at h
    rw [hα, hβ, hε] at h
    calc
      (d.toHom l : U) =
          α⁻¹ * ((α * (d.toHom l : U) * α⁻¹) * (p.element : U)) *
            (p.element : U)⁻¹ * α := by group
      _ = α⁻¹ * ((p.element : U) * (β * (ε * (l : U) * ε⁻¹) * β⁻¹)) *
            (p.element : U)⁻¹ * α := by rw [h]
      _ = δ * (l : U) * δ⁻¹ := by dsimp [δ]; group
  have hquot : (α * δ) * (β * ε)⁻¹ = (p.element : U) := by dsimp [δ]; group
  have ha (k : K) : α * (k : U) * α⁻¹ ∈ P := hα k ▸ (a.toHom k).property
  have hb (h : H) : β * (h : U) * β⁻¹ ∈ P := hβ h ▸ (b.toHom h).property
  have hd (l : L) : δ * (l : U) * δ⁻¹ ∈ K := hδ l ▸ (d.toHom l).property
  have he (l : L) : ε * (l : U) * ε⁻¹ ∈ H := hε l ▸ (e.toHom l).property
  have hp : (α * δ) * (β * ε)⁻¹ ∈ P := hquot ▸ p.element.property
  let a' := ConjEmbedding.ofConjugator α ha
  let b' := ConjEmbedding.ofConjugator β hb
  let d' := ConjEmbedding.ofConjugator δ hd
  let e' := ConjEmbedding.ofConjugator ε he
  let p' : Dot (a'.comp d') (b'.comp e') :=
    Dot.ofRepresentatives (α * δ) (β * ε)
      (by intro x; change α * (δ * (x : U) * δ⁻¹) * α⁻¹ = _; group)
      (by intro x; change β * (ε * (x : U) * ε⁻¹) * β⁻¹ = _; group) hp
  have move
      (a₁ : ConjEmbedding K P) (b₁ : ConjEmbedding H P) (d₁ : ConjEmbedding L K)
      (e₁ : ConjEmbedding L H) (p₁ : Dot (a₁.comp d₁) (b₁.comp e₁))
      (ha₁ : a = a₁) (hb₁ : b = b₁) (hd₁ : d = d₁) (he₁ : e = e₁)
      (hp₁ : (p₁.element : U) = (p.element : U))
      (result : HasIndexFormula a₁ b₁ d₁ e₁ p₁) : HasIndexFormula a b d e p := by
    cases ha₁
    cases hb₁
    cases hd₁
    cases he₁
    have hh : p₁ = p := Dot.ext (Subtype.ext hp₁)
    subst p₁
    exact result
  refine move a' b' d' e' p' (embedding_eq_of_rep a α hα) (embedding_eq_of_rep b β hβ)
    (embedding_eq_of_rep d δ hδ) (embedding_eq_of_rep e ε hε) hquot ?_
  let lower := (a'.comp d').toHom.range
  let upper := intersection a' b' d' e' p'
  let lowerU := Subgroup.map (MulAut.conj (α * δ)).toMonoidHom L
  let upperU := Subgroup.map (MulAut.conj α).toMonoidHom K ⊓
    Subgroup.map (MulAut.conj ((p'.element : U) * β)).toMonoidHom H
  have hlo : lower.map P.subtype = lowerU := by
    rw [MonoidHom.map_range]
    ext x
    change (∃ l : L, α * (δ * (l : U) * δ⁻¹) * α⁻¹ = x) ↔
      ∃ y ∈ L, (α * δ) * y * (α * δ)⁻¹ = x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, l.property, by group⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, by group⟩
  have hup : upper.map P.subtype = upperU := by
    rw [show upper = a'.toHom.range ⊓ Subgroup.map (MulAut.conj p'.element).toMonoidHom
      b'.toHom.range from rfl, Subgroup.map_inf _ _ _ Subtype.val_injective,
      MonoidHom.map_range, Subgroup.map_map, MonoidHom.map_range]
    congr 1
    · ext x
      change (∃ k : K, α * (k : U) * α⁻¹ = x) ↔ ∃ y ∈ K, α * y * α⁻¹ = x
      exact ⟨fun ⟨k, hk⟩ => ⟨k, k.property, hk⟩, fun ⟨k, hk, hx⟩ => ⟨⟨k, hk⟩, hx⟩⟩
    · ext x
      change (∃ h : H, (p'.element : U) * (β * (h : U) * β⁻¹) * (p'.element : U)⁻¹ = x) ↔
        ∃ y ∈ H, ((p'.element : U) * β) * y * ((p'.element : U) * β)⁻¹ = x
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨h, h.property, by group⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨⟨h, hh⟩, by group⟩
  -- Mathlib.GroupTheory.Index at the project's pinned revision supplies
  -- relIndex_map_map_of_injective; the injectivity here is subtype injectivity.
  have hi := Subgroup.relIndex_map_map_of_injective lower upper
    (f := P.subtype) Subtype.val_injective
  rw [hlo, hup] at hi
  have hfi : lowerU.IsFiniteRelIndex upperU ↔ (lower.subgroupOf upper).FiniteIndex := by
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Subgroup.finiteIndex_iff, hi]
    rfl
  have supplier := MixedCrossingFiberMaps K H P L α β δ ε ha hb hd he hp
    (fun j => j.out) DoubleCoset.out_eq'
  obtain ⟨_, _, _, hrange, hcard, hfinite, _⟩ := supplier
  refine ⟨hfinite.trans hfi, ?_⟩
  intro z hz hf
  have hc := hcard z (hrange ▸ hz) (hfinite.mp hf)
  exact hc.trans hi

end Index
end
end EvaluationForTwoProjectionsAux

namespace EvaluationForTwoProjectionsAux
open MackeyDiagrams
universe u
noncomputable section
set_option maxHeartbeats 2400000

variable {U : Type u} [Group U] {G A D F C E B B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A)
  (c : ConjEmbedding F D) (d : ConjEmbedding C G)
  (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev bottom := ((Word.down a).tensor (.up b)).tensor (.up c)
private abbrev top := ((Word.up d).tensor (.up e)).tensor (.down f)
private abbrev mergedBottom := (Word.down a).tensor (.up (b.comp c))
private abbrev mergedTop := (Word.up (d.comp e)).tensor (.down f)

private abbrev splitBottom : LabelledDrawing Complex (mergedBottom a b c) (bottom a b c) :=
  before (.horizontal (drawId (.down a)) (.trivalent (.splitUp b c)))
    (.ordinary (.unassociate (.down a) (.up b) (.up c)))

private abbrev mergeTop : LabelledDrawing Complex (top d e f) (mergedTop d e f) :=
  .horizontal (.trivalent (.mergeUp d e)) (drawId (.down f))

private abbrev mergedEval (drawing : LabelledDrawing Complex (bottom a b c) (top d e f)) :=
  ev (before (splitBottom a b c) (before drawing (mergeTop d e f)))

private abbrev leftDrawing (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B)
    (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × Dot (r.comp t) (d.comp e))) :=
  before (atLeft (.compactProjection a b r s xs) (.up c))
    (before (atRight (.up r) (.compactProjection s c t f ys))
      (atLeft (.parallelUp r t d e zs) (.down f)))

private abbrev rightDrawing (u' : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B')
    (ells : List (Complex × Dot (b.comp c) (u'.comp w)))
    (ms : List (Complex × ProjectionDot.Mixed a u' d v))
    (ns : List (Complex × ProjectionDot.Mixed v w e f)) :=
  before (atRight (.down a) (.parallelUp b c u' w ells))
    (before (atLeft (.compactProjection a u' d v ms) (.up w))
      (atRight (.up d) (.compactProjection v w e f ns)))

private theorem pulls_splitBottom (x y : A) (z : D) :
    Pulls (ev (splitBottom a b c)) (triple (.down a) (.up b) (.up c) x y z)
      (pair (.down a) (.up (b.comp c)) x (y * b.toHom z)) := by
  apply pulls_before (pulls_unassoc (.down a) (.up b) (.up c) x y z)
  exact pulls_horizontal_left (X := Biset.restriction a) (Diagram.splitUp (R := Complex) b c).eval (free_down_right a)
    (pulls_split b c y z) x

private theorem pulls_mergeTop (g : G) (h : F) :
    Pulls (ev (mergeTop d e f)) (pair (.up (d.comp e)) (.down f) g h)
      (triple (.up d) (.up e) (.down f) g 1 h) := by
  exact pulls_horizontal_right (Y := Biset.restriction f) (Diagram.mergeUp (R := Complex) d e).eval
    (free_down_left f) (pulls_merge d e g) h

private theorem mixedPair_coord {K H P : Subgroup U}
    (α : ConjEmbedding K P) (β : ConjEmbedding H P) (x y : P) :
    pair (.down α) (.up β) x y = Generator.mixedPair α β (x * y) := by
  apply (Generator.mixedEquiv α β).injective
  change x * y = Generator.mixedProduct α β (Generator.mixedPair α β (x * y))
  rw [Generator.mixedProduct_mixedPair]

private def leftDot {r : ConjEmbedding B G} {s : ConjEmbedding B D} {t : ConjEmbedding E B}
    (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) : Dot (a.comp (d.comp e)) ((b.comp c).comp f) where
  element := a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element
  intertwines := by
    intro j
    have hz := congrArg a.toHom (z.inverse.intertwines j)
    have hx := x.dot.intertwines (t.toHom j)
    have hy := congrArg b.toHom (y.dot.intertwines j)
    simp only [Dot.inverse, ConjEmbedding.comp_apply, map_mul] at hz hx hy
    simp only [ConjEmbedding.comp_apply]
    calc
      a.toHom (d.toHom (e.toHom j)) * (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element) =
          (a.toHom (d.toHom (e.toHom j)) * a.toHom z.element⁻¹) *
            x.dot.element * b.toHom y.dot.element := by simp only [mul_assoc]
      _ = (a.toHom z.element⁻¹ * a.toHom (r.toHom (t.toHom j))) *
            x.dot.element * b.toHom y.dot.element := by rw [hz]
      _ = a.toHom z.element⁻¹ * (a.toHom (r.toHom (t.toHom j)) * x.dot.element) *
            b.toHom y.dot.element := by simp only [mul_assoc]
      _ = a.toHom z.element⁻¹ * x.dot.element *
            (b.toHom (s.toHom (t.toHom j)) * b.toHom y.dot.element) := by rw [hx]; simp only [mul_assoc]
      _ = (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element) *
            b.toHom (c.toHom (f.toHom j)) := by rw [hy]; simp only [mul_assoc]

private def rightDot {u' : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'}
    (ell : Dot (b.comp c) (u'.comp w))
    (m : ProjectionDot.Mixed a u' d v) (n : ProjectionDot.Mixed v w e f) :
    Dot (a.comp (d.comp e)) ((b.comp c).comp f) where
  element := m.dot.element * u'.toHom n.dot.element * ell.element⁻¹
  intertwines := by
    intro j
    have hm := m.dot.intertwines (e.toHom j)
    have hn := congrArg u'.toHom (n.dot.intertwines j)
    have hl := ell.inverse.intertwines (f.toHom j)
    simp only [Dot.inverse, ConjEmbedding.comp_apply, map_mul] at hm hn hl
    simp only [ConjEmbedding.comp_apply]
    calc
      a.toHom (d.toHom (e.toHom j)) * (m.dot.element * u'.toHom n.dot.element * ell.element⁻¹) =
          (a.toHom (d.toHom (e.toHom j)) * m.dot.element) *
            u'.toHom n.dot.element * ell.element⁻¹ := by simp only [mul_assoc]
      _ = m.dot.element * (u'.toHom (v.toHom (e.toHom j)) * u'.toHom n.dot.element) *
            ell.element⁻¹ := by rw [hm]; simp only [mul_assoc]
      _ = m.dot.element * u'.toHom n.dot.element *
            (u'.toHom (w.toHom (f.toHom j)) * ell.element⁻¹) := by rw [hn]; simp only [mul_assoc]
      _ = (m.dot.element * u'.toHom n.dot.element * ell.element⁻¹) *
            b.toHom (c.toHom (f.toHom j)) := by rw [hl]; simp only [mul_assoc]

-- Lemma 6.3, left backward calculation. At each stage the linear coefficient
-- is evaluated at its unique backwards coordinate. The fixed strands act
-- freely at the balancing interfaces, so rebracketing retains the fiber sum.
private theorem pulls_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f (leftDot a b c d e f x y z)
        (pair (.up (d.comp e)) (.down f) g h)) := by
  let g' := g * z.element⁻¹
  let y' := y.dot.element * c.toHom h
  let x' := a.toHom g' * x.dot.element * b.toHom y'
  have step₃ : Pulls (ev (atLeft (.parallelUp r t d e [(1,z)]) (.down f)))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up r) (.up t) (.down f) g' 1 h) := by
    have hp := pulls_parallel r t d e z g 1
    simp only [map_one, mul_one] at hp
    exact pulls_horizontal_right (Y := Biset.restriction f) _ (free_down_left f) hp h
  have step₂ : Pulls (ev (atRight (.up r) (.compactProjection s c t f [(1,y)])))
      (triple (.up r) (.up t) (.down f) g' 1 h) (triple (.up r) (.down s) (.up c) g' y' 1) := by
    apply pulls_atRight (.up r) (free_up_right r) g'
    have hp := pulls_compact s c t f y 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₁ : Pulls (ev (atLeft (.compactProjection a b r s [(1,x)]) (.up c)))
      (triple (.up r) (.down s) (.up c) g' y' 1) (triple (.down a) (.up b) (.up c) x' 1 1) :=
    pulls_horizontal_right _ (free_up_left c) (pulls_compact a b r s x g' y') _
  have step₀ := pulls_splitBottom a b c x' 1 1
  simp only [map_one, mul_one] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * (leftDot a b c d e f x y z).element * (b.comp c).toHom h))
  have hc : x' = a.toHom g * (leftDot a b c d e f x y z).element * (b.comp c).toHom h := by
    simp only [x', g', y', leftDot, ConjEmbedding.comp_apply, map_mul, mul_assoc]
  rw [← hc]
  exact out

-- Lemma 6.3, right backward calculation. The parallel vertex contributes
-- right multiplication by ell⁻¹. Its reversed intertwining equation
-- moves that factor through the right boundary action.
private theorem pulls_right {u' : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (u'.comp w))
    (m : ProjectionDot.Mixed a u' d v) (n : ProjectionDot.Mixed v w e f)
    (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (rightDrawing a b c d e f u' v w [(1,ell)] [(1,m)] [(1,n)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f (rightDot a b c d e f ell m n)
        (pair (.up (d.comp e)) (.down f) g h)) := by
  let n' := n.dot.element * w.toHom h
  let m' := a.toHom g * m.dot.element * u'.toHom n'
  have step₃ : Pulls (ev (atRight (.up d) (.compactProjection v w e f [(1,n)])))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up d) (.down v) (.up w) g n' 1) := by
    apply pulls_atRight (.up d) (free_up_right d) g
    have hp := pulls_compact v w e f n 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₂ : Pulls (ev (atLeft (.compactProjection a u' d v [(1,m)]) (.up w)))
      (triple (.up d) (.down v) (.up w) g n' 1) (triple (.down a) (.up u') (.up w) m' 1 1) :=
    pulls_horizontal_right _ (free_up_left w) (pulls_compact a u' d v m g n') _
  have step₁ : Pulls (ev (atRight (.down a) (.parallelUp b c u' w [(1,ell)])))
      (triple (.down a) (.up u') (.up w) m' 1 1)
      (triple (.down a) (.up b) (.up c) m' ell.element⁻¹ 1) := by
    apply pulls_atRight (.down a) (free_down_right a) m'
    simpa only [map_one, mul_one, one_mul] using pulls_parallel b c u' w ell 1 1
  have step₀ := pulls_splitBottom a b c m' ell.element⁻¹ 1
  simp only [map_one, mul_one] at step₀
  rw [mixedPair_coord a (b.comp c) m' ell.element⁻¹] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * (rightDot a b c d e f ell m n).element * (b.comp c).toHom h))
  have hel := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at hel
  have hc : m' * ell.element⁻¹ =
      a.toHom g * (rightDot a b c d e f ell m n).element * (b.comp c).toHom h := by
    simp only [m', n', rightDot, ConjEmbedding.comp_apply, map_mul, mul_assoc, hel]
  rw [← hc]
  exact out

private abbrev Parameter := ProjectionDot.Mixed a (b.comp c) (d.comp e) f

private abbrev qstar (p : Parameter a b c d e f) :=
  (Diagram.mixedProjection (R := Complex) a (b.comp c) (d.comp e) f p.dot p.finite).eval.toLinearMap

-- A fiber is contained in the support of the corresponding evaluated column.
-- This gives the finite-composite witness without choosing an enumeration of
-- intermediate points and proves the exact transfer equation on all inputs.
private theorem of_pulls (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f))
    (L : Vec (mergedBottom a b c).basis.carrier →ₗ[Complex] Vec (mergedTop d e f).basis.carrier)
    (hl : ∀ g h, Pulls L (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p
        (pair (.up (d.comp e)) (.down f) g h))) :
    ∃ p' : Parameter a b c d e f, L = qstar a b c d e f p' := by
  classical
  have pull (y : (mergedTop d e f).basis.carrier) :
      Pulls L y (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p y) :=
    Quotient.inductionOn y (fun ⟨g,h⟩ => hl g h)
  have finite (x : (mergedBottom a b c).basis.carrier) :
      Set.Finite {y | Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p y = x} := by
    apply (L (Finsupp.single x 1)).support.finite_toSet.subset
    intro y hy
    change Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p y = x at hy
    exact Finsupp.mem_support_iff.mpr (by rw [pull y _, hy, Finsupp.single_eq_same]; exact one_ne_zero)
  refine ⟨⟨p, finite⟩, ?_⟩
  apply LinearMap.ext
  intro z
  apply Finsupp.ext
  intro y
  rw [pull y _]
  exact (pulls_mixed a (b.comp c) (d.comp e) f ⟨p, finite⟩ y z).symm

end
end EvaluationForTwoProjectionsAux

namespace EvaluationForTwoProjectionsAux
open MackeyDiagrams
universe u
noncomputable section
set_option maxHeartbeats 2400000

private def weighted {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (s : I → M) (xs : List (Complex × I)) : M :=
  (xs.map fun x => x.1 • s x.2).sum

private theorem map_weighted {I M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (L : M →ₗ[Complex] N) (s : I → M) (xs : List (Complex × I)) :
    L (weighted s xs) = weighted (fun i => L (s i)) xs := by
  unfold weighted
  rw [map_list_sum, List.map_map]
  simp only [Function.comp_def, map_smul]

private theorem weighted_mem {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (S : Submodule Complex M) (s : I → M) (xs : List (Complex × I))
    (hs : ∀ i, s i ∈ S) : weighted s xs ∈ S := by
  unfold weighted
  apply list_sum_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact S.smul_mem t.1 (hs t.2)

private def preapply {M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (x : M) : (M →ₗ[Complex] N) →ₗ[Complex] N where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def composeAround
    {M N P Q : Type*} [AddCommMonoid M] [Module Complex M] [AddCommMonoid N] [Module Complex N]
    [AddCommMonoid P] [Module Complex P] [AddCommMonoid Q] [Module Complex Q]
    (pre : M →ₗ[Complex] N) (post : P →ₗ[Complex] Q) :
    (N →ₗ[Complex] P) →ₗ[Complex] (M →ₗ[Complex] Q) where
  toFun f := post.comp (f.comp pre)
  map_add' g h := by
    change post.comp ((g + h).comp pre) = post.comp (g.comp pre) + post.comp (h.comp pre)
    rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r g := by
    change post.comp ((r • g).comp pre) = r • post.comp (g.comp pre)
    rw [LinearMap.smul_comp, LinearMap.comp_smul]

section WeightedCrossings
variable {U : Type u} [Group U] {K H J L M : Subgroup U}

private theorem weighted_compact (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (xs : List (Complex × ProjectionDot.Mixed a b c d)) :
    ev (.compactProjection a b c d xs) =
      weighted (fun p => ev (.compactProjection a b c d [(1,p)])) xs := by
  have hs := sum_eval ((Word.down a).tensor (.up b)) ((Word.up c).tensor (.down d))
    (xs.map fun t => (t.1, Diagram.mixedProjection (R := Complex) a b c d t.2.dot t.2.finite))
  simp only [List.map_map] at hs
  rw [show weighted (fun p => ev (.compactProjection a b c d [(1,p)])) xs =
      weighted (fun p => (Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite).eval.toLinearMap)
        xs from congrArg (fun s => weighted s xs) (funext (singleton_mixed a b c d))]
  exact hs

private theorem weighted_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (xs : List (Complex × Dot (a.comp b) (c.comp d))) :
    ev (.parallelUp a b c d xs) =
      weighted (fun p => ev (.parallelUp a b c d [(1,p)])) xs := by
  have hs := sum_eval ((Word.up a).tensor (.up b)) ((Word.up c).tensor (.up d))
    (xs.map fun t => (t.1, Diagram.parallelUp (R := Complex) a b c d t.2))
  simp only [List.map_map] at hs
  rw [show weighted (fun p => ev (.parallelUp a b c d [(1,p)])) xs =
      weighted (fun p => (Diagram.parallelUp (R := Complex) a b c d p).eval.toLinearMap)
        xs from congrArg (fun s => weighted s xs) (funext (singleton_parallel a b c d))]
  exact hs

private theorem weighted_atLeft {I : Type*} {p q : Word K H} {r : Word H J}
    (S : LabelledDrawing Complex p q) (s : I → LabelledDrawing Complex p q) (xs : List (Complex × I))
    (he : ev S = weighted (fun i => ev (s i)) xs) :
    ev (atLeft S r) = weighted (fun i => ev (atLeft (s i) r)) xs := by
  apply Finsupp.lhom_ext
  intro w c
  refine Quotient.inductionOn w (fun ⟨x,y⟩ => ?_)
  let T := c • (((Biset.pairLinear Complex q.basis r.basis).flip
    (Finsupp.single y 1)).comp (preapply (Finsupp.single x (1 : Complex))))
  have col (d : LabelledDrawing Complex p q) :
      ev (atLeft d r) (Finsupp.single (pair p r x y) c) = T (ev d) := by
    exact Biset.Hom.horizontal_single d.interpret.eval (Biset.Hom.id r.basis) x y c
  change ev (atLeft S r) (Finsupp.single (pair p r x y) c) =
    preapply (Finsupp.single (pair p r x y) c) (weighted (fun i => ev (atLeft (s i) r)) xs)
  rw [col S, he, map_weighted T, map_weighted]
  exact congrArg (fun v => weighted v xs) (funext fun i => (col (s i)).symm)

private theorem weighted_atRight {I : Type*} (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    (S : LabelledDrawing Complex (q.tensor r) (q'.tensor r'))
    (s : I → LabelledDrawing Complex (q.tensor r) (q'.tensor r')) (xs : List (Complex × I))
    (he : ev S = weighted (fun i => ev (s i)) xs) :
    ev (atRight p S) = weighted (fun i => ev (atRight p (s i))) xs := by
  let first := ev (.ordinary (.associate p q r))
  let last := ev (.ordinary (.unassociate p q' r'))
  let frame := composeAround first last
  have mid : ev (.horizontal (drawId p) S) =
      weighted (fun i => ev (.horizontal (drawId p) (s i))) xs := by
    apply Finsupp.lhom_ext
    intro w c
    refine Quotient.inductionOn w (fun ⟨x,y⟩ => ?_)
    let T := c • ((Biset.pairLinear Complex p.basis (q'.tensor r').basis
      (Finsupp.single x 1)).comp (preapply (Finsupp.single y (1 : Complex))))
    have col (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :
        ev (.horizontal (drawId p) d) (Finsupp.single (pair p (q.tensor r) x y) c) = T (ev d) := by
      exact Biset.Hom.horizontal_single (Biset.Hom.id p.basis) d.interpret.eval x y c
    change ev (.horizontal (drawId p) S) (Finsupp.single (pair p (q.tensor r) x y) c) =
      preapply (Finsupp.single (pair p (q.tensor r) x y) c)
        (weighted (fun i => ev (.horizontal (drawId p) (s i))) xs)
    rw [col S, he, map_weighted T, map_weighted]
    exact congrArg (fun v => weighted v xs) (funext fun i => (col (s i)).symm)
  have hframe (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :
      ev (atRight p d) = frame (ev (.horizontal (drawId p) d)) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hframe S, mid, map_weighted frame]
  exact congrArg (fun v => weighted v xs) (funext fun i => (hframe (s i)).symm)

end WeightedCrossings

section Coefficients
variable {U : Type u} [Group U] {G A D F C E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private theorem parameter_ext (p q : Parameter a b c d e f)
    (h : p.dot.element = q.dot.element) : p = q := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  have he : p = q := Dot.ext h
  subst q
  rfl

private abbrev readCoefficient (p : Parameter a b c d e f) :=
  (Finsupp.lapply (pair (.up (d.comp e)) (.down f) 1 1) : Vec (mergedTop d e f).basis.carrier →ₗ[Complex] Complex).comp
    (preapply (Finsupp.single (Generator.mixedPair a (b.comp c) p.dot.element) (1 : Complex)))

private theorem qstar_delta (p q : Parameter a b c d e f) [Decidable (q = p)] :
    readCoefficient a b c d e f p (qstar a b c d e f q) = if q = p then 1 else 0 := by
  classical
  change qstar a b c d e f q (Finsupp.single (Generator.mixedPair a (b.comp c) p.dot.element) 1)
    (pair (.up (d.comp e)) (.down f) 1 1) = _
  rw [pulls_mixed a (b.comp c) (d.comp e) f q _ _]
  change (Finsupp.single (Generator.mixedPair a (b.comp c) p.dot.element) (1 : Complex))
    (Generator.mixedPair a (b.comp c) (a.toHom 1 * q.dot.element * (b.comp c).toHom 1)) = _
  by_cases h : q = p
  · subst q
    simp only [map_one, one_mul, mul_one, Finsupp.single_eq_same]
    simp
  · have he : p.dot.element ≠ q.dot.element := fun eq => h (parameter_ext a b c d e f p q eq).symm
    have hi : Generator.mixedPair a (b.comp c) p.dot.element ≠
        Generator.mixedPair a (b.comp c) q.dot.element :=
      fun eq => he ((Generator.mixedEquiv a (b.comp c)).symm.injective eq)
    simp only [map_one, one_mul, mul_one, Finsupp.single_apply, ite_eq_right hi, ite_eq_right h]

private abbrev combination := Finsupp.linearCombination Complex (qstar a b c d e f)

-- Lemma 6.3, last sentence. Probe the [1,1] coefficient at the input
-- whose group value is p. Distinct typed Parameters have distinct values.
private theorem read_combination (p : Parameter a b c d e f) (coeff : Vec (Parameter a b c d e f)) :
    readCoefficient a b c d e f p (combination a b c d e f coeff) = coeff p := by
  classical
  have he : (readCoefficient a b c d e f p).comp (combination a b c d e f) = Finsupp.lapply p := by
    apply Finsupp.lhom_ext
    intro q w
    change readCoefficient a b c d e f p (combination a b c d e f (Finsupp.single q w)) =
      Finsupp.single q w p
    rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index (by simp), map_smul, qstar_delta]
    by_cases h : q = p <;> simp [h, smul_eq_mul]
  exact LinearMap.congr_fun he coeff

private theorem combination_injective : Function.Injective (combination a b c d e f) := by
  intro x y h
  apply Finsupp.ext
  intro p
  rw [← read_combination a b c d e f p x, ← read_combination a b c d e f p y, h]

private theorem qstar_injective : Function.Injective (qstar a b c d e f) := by
  classical
  intro x y h
  have he := congrArg (readCoefficient a b c d e f y) h
  rw [qstar_delta, qstar_delta, ite_eq_left rfl] at he
  by_contra hxy
  rw [ite_eq_right hxy] at he
  exact zero_ne_one he

end Coefficients
end
end EvaluationForTwoProjectionsAux

namespace EvaluationForTwoProjectionsAux
open MackeyDiagrams
universe u
noncomputable section
set_option maxHeartbeats 2400000

-- Lemma 6.3, finite label expansion. Three applications of linearity group
-- the products of the weights in the range of the finitely supported
-- coefficient map. In particular an empty label contributes the zero map.
private theorem weighted_stack_mem {I J K M N P Q S T : Type*}
    [AddCommMonoid M] [Module Complex M] [AddCommMonoid N] [Module Complex N]
    [AddCommMonoid P] [Module Complex P] [AddCommMonoid Q] [Module Complex Q]
    [AddCommMonoid S] [Module Complex S] [AddCommMonoid T] [Module Complex T]
    (V : Submodule Complex (M →ₗ[Complex] T)) (pre : M →ₗ[Complex] N) (post : S →ₗ[Complex] T)
    (x : I → (N →ₗ[Complex] P)) (y : J → (P →ₗ[Complex] Q)) (z : K → (Q →ₗ[Complex] S))
    (xs : List (Complex × I)) (ys : List (Complex × J)) (zs : List (Complex × K))
    (h : ∀ i j k, post.comp ((z k).comp ((y j).comp ((x i).comp pre))) ∈ V) :
    post.comp ((weighted z zs).comp ((weighted y ys).comp ((weighted x xs).comp pre))) ∈ V := by
  let tail := post.comp ((weighted z zs).comp (weighted y ys))
  change composeAround pre tail (weighted x xs) ∈ V
  rw [map_weighted]
  apply weighted_mem
  intro i
  let head := (x i).comp pre
  let tail' := post.comp (weighted z zs)
  change composeAround head tail' (weighted y ys) ∈ V
  rw [map_weighted]
  apply weighted_mem
  intro j
  change composeAround ((y j).comp head) post (weighted z zs) ∈ V
  rw [map_weighted]
  apply weighted_mem
  intro k
  exact h i j k

section Assembly
variable {U : Type u} [Group U] {G A D F C E B B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private theorem evaluate_shape {I J K : Type u} {v w : Word G F}
    (D₁ : List (Complex × I) → LabelledDrawing Complex (bottom a b c) v)
    (D₂ : List (Complex × J) → LabelledDrawing Complex v w)
    (D₃ : List (Complex × K) → LabelledDrawing Complex w (top d e f))
    (h₁ : ∀ xs, ev (D₁ xs) = weighted (fun i => ev (D₁ [(1,i)])) xs)
    (h₂ : ∀ ys, ev (D₂ ys) = weighted (fun j => ev (D₂ [(1,j)])) ys)
    (h₃ : ∀ zs, ev (D₃ zs) = weighted (fun k => ev (D₃ [(1,k)])) zs)
    (h : ∀ i j k, ∃ p : Parameter a b c d e f,
      mergedEval a b c d e f (before (D₁ [(1,i)]) (before (D₂ [(1,j)]) (D₃ [(1,k)]))) =
        qstar a b c d e f p) :
    (∀ i j k, ∃! p : Parameter a b c d e f,
      mergedEval a b c d e f (before (D₁ [(1,i)]) (before (D₂ [(1,j)]) (D₃ [(1,k)]))) =
        qstar a b c d e f p) ∧
    (∀ xs ys zs, ∃! coeff : Vec (Parameter a b c d e f),
      mergedEval a b c d e f (before (D₁ xs) (before (D₂ ys) (D₃ zs))) =
        coeff.sum (fun p weight => weight • qstar a b c d e f p)) := by
  constructor
  · intro i j k
    obtain ⟨p, hp⟩ := h i j k
    exact ⟨p, hp, fun q hq => qstar_injective a b c d e f (hq.symm.trans hp)⟩
  · intro xs ys zs
    let value := mergedEval a b c d e f (before (D₁ xs) (before (D₂ ys) (D₃ zs)))
    let pre := ev (splitBottom a b c)
    let post := ev (mergeTop d e f)
    let W := combination a b c d e f
    have hvalue : value ∈ W.range := by
      change post.comp ((ev (D₃ zs)).comp ((ev (D₂ ys)).comp ((ev (D₁ xs)).comp pre))) ∈ W.range
      rw [h₁ xs, h₂ ys, h₃ zs]
      apply weighted_stack_mem
      intro i j k
      obtain ⟨p, hp⟩ := h i j k
      change mergedEval a b c d e f (before (D₁ [(1,i)]) (before (D₂ [(1,j)]) (D₃ [(1,k)]))) ∈ W.range
      rw [hp]
      refine ⟨Finsupp.single p 1, ?_⟩
      rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index (by simp), one_smul]
    obtain ⟨coeff, hc⟩ := hvalue
    have hc' : value = W coeff := hc.symm
    refine ⟨coeff, ?_, ?_⟩
    · change value = coeff.sum (fun p weight => weight • qstar a b c d e f p)
      exact hc'.trans (Finsupp.linearCombination_apply Complex coeff)
    · intro coeff' h'
      apply combination_injective a b c d e f
      change W coeff' = W coeff
      rw [← hc', Finsupp.linearCombination_apply]
      exact h'.symm

private theorem left_shape (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B) :
    (∀ x y z, ∃! p : Parameter a b c d e f,
      mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]) =
        qstar a b c d e f p) ∧
    (∀ xs ys zs, ∃! coeff : Vec (Parameter a b c d e f),
      mergedEval a b c d e f (leftDrawing a b c d e f r s t xs ys zs) =
        coeff.sum (fun p weight => weight • qstar a b c d e f p)) := by
  refine evaluate_shape a b c d e f
    (fun xs => atLeft (.compactProjection a b r s xs) (.up c))
    (fun ys => atRight (.up r) (.compactProjection s c t f ys))
    (fun zs => atLeft (.parallelUp r t d e zs) (.down f)) ?_ ?_ ?_ ?_
  · intro xs
    exact weighted_atLeft _ _ xs (weighted_compact a b r s xs)
  · intro ys
    exact weighted_atRight _ _ _ ys (weighted_compact s c t f ys)
  · intro zs
    exact weighted_atLeft _ _ zs (weighted_parallel r t d e zs)
  · intro x y z
    exact of_pulls a b c d e f (leftDot a b c d e f x y z) _ (pulls_left a b c d e f x y z)

private theorem right_shape (u' : ConjEmbedding B' A) (v : ConjEmbedding C B') (w : ConjEmbedding F B') :
    (∀ ell m n, ∃! p : Parameter a b c d e f,
      mergedEval a b c d e f (rightDrawing a b c d e f u' v w [(1,ell)] [(1,m)] [(1,n)]) =
        qstar a b c d e f p) ∧
    (∀ ells ms ns, ∃! coeff : Vec (Parameter a b c d e f),
      mergedEval a b c d e f (rightDrawing a b c d e f u' v w ells ms ns) =
        coeff.sum (fun p weight => weight • qstar a b c d e f p)) := by
  refine evaluate_shape a b c d e f
    (fun ells => atRight (.down a) (.parallelUp b c u' w ells))
    (fun ms => atLeft (.compactProjection a u' d v ms) (.up w))
    (fun ns => atRight (.up d) (.compactProjection v w e f ns)) ?_ ?_ ?_ ?_
  · intro ells
    exact weighted_atRight _ _ _ ells (weighted_parallel b c u' w ells)
  · intro ms
    exact weighted_atLeft _ _ ms (weighted_compact a u' d v ms)
  · intro ns
    exact weighted_atRight _ _ _ ns (weighted_compact v w e f ns)
  · intro ell m n
    exact of_pulls a b c d e f (rightDot a b c d e f ell m n) _ (pulls_right a b c d e f ell m n)

end Assembly
end
end EvaluationForTwoProjectionsAux

universe u

theorem EvaluationForTwoProjections : (∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let ade := comp a de
  let bcf := comp bc f
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let finiteFibers := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.Dot (comp α η) (comp β θ)) =>
    ∀ z, Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ x w = z}
  let Parameter := MackeyDiagrams.ProjectionDot.Mixed a bc de f
  let Q := fun (p : MackeyDiagrams.Dot ade bcf) (w : (MackeyDiagrams.Word.basis mergedTop).carrier) =>
    MackeyDiagrams.Generator.mixedProduct a bc
      (MackeyDiagrams.Generator.mixedMultiplicationBasis a bc de f p w)
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let intersection := fun (p : MackeyDiagrams.Dot ade bcf) =>
    MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a) ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (MackeyDiagrams.Dot.element p)))
        (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom bc))
  let lower := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom ade)
  let terms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let evaluates := fun {X Y Z : Type u}
      (drawing : List (Complex × X) → List (Complex × Y) → List (Complex × Z) →
        MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    (∀ (x : X) (y : Y) (z : Z), ∃! p : Parameter,
      eval (drawing [(1, x)] [(1, y)] [(1, z)]) = Qstar p) ∧
    (∀ (xs : Finsupp X Complex) (ys : Finsupp Y Complex) (zs : Finsupp Z Complex),
      ∃! coeff : Finsupp Parameter Complex,
        eval (drawing (terms xs) (terms ys) (terms zs)) =
          Finsupp.sum coeff (fun p weight => weight • Qstar p))
  (∀ p : MackeyDiagrams.Dot ade bcf,
    lower ≤ intersection p ∧
    (finiteFibers a bc de f p ↔ Subgroup.FiniteIndex (Subgroup.subgroupOf lower (intersection p))) ∧
    (∀ (g : G) (h : F),
      Q p (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction de)
          (MackeyDiagrams.Biset.restriction f) g h) =
        MackeyDiagrams.ConjEmbedding.toHom a g * MackeyDiagrams.Dot.element p *
          MackeyDiagrams.ConjEmbedding.toHom bc h)) ∧
  (∀ (p : Parameter) (z : A),
    Qstar p (Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc z) 1) =
      Finset.sum (Set.Finite.toFinset (MackeyDiagrams.ProjectionDot.finite p (MackeyDiagrams.Generator.mixedPair a bc z)))
        (fun w => Finsupp.single w 1) ∧
    (z ∈ Set.range (Q (MackeyDiagrams.ProjectionDot.dot p)) →
      Nat.card {w : (MackeyDiagrams.Word.basis mergedTop).carrier // Q (MackeyDiagrams.ProjectionDot.dot p) w = z} =
        Subgroup.relIndex lower (intersection (MackeyDiagrams.ProjectionDot.dot p)))) ∧
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B),
    evaluates (fun
      (xs : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b r s))
      (ys : List (Complex × MackeyDiagrams.ProjectionDot.Mixed s c t f))
      (zs : List (Complex × MackeyDiagrams.Dot (comp r t) de)) =>
      MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a b r s xs) (drawId (up c)))
        (MackeyDiagrams.LabelledDrawing.vertical
          (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (down f)))))) ∧
  (∀ {B' : Subgroup U} (u' : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B'),
    evaluates (fun
      (ells : List (Complex × MackeyDiagrams.Dot bc (comp u' w)))
      (ms : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a u' d v))
      (ns : List (Complex × MackeyDiagrams.ProjectionDot.Mixed v w e f)) =>
      MackeyDiagrams.LabelledDrawing.vertical
        (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c u' w ells))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.compactProjection a u' d v ms) (drawId (up w)))
          (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f ns)))))) :=
(by
  classical
  intro U inst G A D F C E a b c d e f up down tensor comp bc de ade bcf bottom top
    mergedBottom mergedTop drawId splitBottom mergeTop eval atRight finiteFibers Parameter Q Qstar
    intersection lower terms evaluates
  -- Xiao, §6.2.1, Lemma 6.3 and (6.1), archived original p. 22 and
  -- revised published PDF p. 24. The Alphabeta Math article reproduces
  -- the proof in prose. Its backward calculations are checked separately
  -- in pulls_left and pulls_right. The shared basis formulas implement the
  -- induction merge and split on these typed words directly, so the larger
  -- conjugator-form InductionRestrictionMergesAndSplits is unnecessary here.
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    have index := EvaluationForTwoProjectionsAux.index_formula a bc de f p
    have hcolumns := (MixedCrossingFiniteFiberConvention (U := U)).2.1 a bc de f p
    exact ⟨EvaluationForTwoProjectionsAux.lower_le a bc de f p, index.1, hcolumns.1⟩
  · intro p z
    constructor
    · change (MackeyDiagrams.Biset.Hom.transfer Complex
        (MackeyDiagrams.Generator.mixedMultiplicationBasis a bc de f p.dot)
        (MackeyDiagrams.Generator.mixedMultiplication_equivariant a bc de f p.dot)
        p.finite).toLinearMap (Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc z) 1) = _
      rw [MackeyDiagrams.Biset.Hom.transfer_single, one_smul]
      exact MackeyDiagrams.Biset.Hom.transferBasis_sum Complex _ _ _
    · intro hz
      exact (EvaluationForTwoProjectionsAux.index_formula a bc de f p.dot).2 z hz p.finite
  · intro B r s t
    have h := EvaluationForTwoProjectionsAux.left_shape a b c d e f r s t
    exact ⟨h.1, fun xs ys zs => h.2 (terms xs) (terms ys) (terms zs)⟩
  · intro B' u' v w
    have h := EvaluationForTwoProjectionsAux.right_shape a b c d e f u' v w
    exact ⟨h.1, fun ells ms ns => h.2 (terms ells) (terms ms) (terms ns)⟩)
#print axioms EvaluationForTwoProjections
