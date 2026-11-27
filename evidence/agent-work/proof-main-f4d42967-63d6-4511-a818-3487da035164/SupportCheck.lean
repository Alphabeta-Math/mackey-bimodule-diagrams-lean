import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
-- Local versions of the private balanced evaluation lemmas in the compiled
-- prerequisite EvaluationForTwoProjections. They keep the same typed words
-- and isolate the Case 2 calculation with its specified output parameter.
namespace CaseTwoLeftProjectionConstructionAux

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
end CaseTwoLeftProjectionConstructionAux

namespace CaseTwoLeftProjectionConstructionAux
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
end CaseTwoLeftProjectionConstructionAux

namespace CaseTwoLeftProjectionConstructionAux
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


-- Lemma 6.3, left backward calculation. At each stage the linear coefficient
-- is evaluated at its unique backwards coordinate. The fixed strands act
-- freely at the balancing interfaces, so rebracketing retains the fiber sum.
private theorem pulls_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f))
    (hx : x.dot.element = p.element) (hy : y.dot.element = 1) (hz : z.element = 1)
    (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p
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
    (a.toHom g * p.element * (b.comp c).toHom h))
  have hc : x' = a.toHom g * p.element * (b.comp c).toHom h := by
    simp [x', g', y', hx, hy, hz, ConjEmbedding.comp_apply]
  rw [← hc]
  exact out



private abbrev Parameter := ProjectionDot.Mixed a (b.comp c) (d.comp e) f

private abbrev qstar (p : Parameter a b c d e f) :=
  (Diagram.mixedProjection (R := Complex) a (b.comp c) (d.comp e) f p.dot p.finite).eval.toLinearMap

-- The outer parameter already has finite fibers. Compare coefficients at
-- each balanced output pair to identify the evaluated map with its transfer.
private theorem unitLeftEval {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) (p : Parameter a b c d e f)
    (hx : x.dot.element = p.dot.element) (hy : y.dot.element = 1) (hz : z.element = 1) :
    mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]) =
      qstar a b c d e f p := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro w
  refine Quotient.inductionOn w (fun ⟨g,h⟩ => ?_)
  exact (pulls_left a b c d e f x y z p.dot hx hy hz g h v).trans
    ((pulls_mixed a (b.comp c) (d.comp e) f p _ v).symm)

end
end CaseTwoLeftProjectionConstructionAux


namespace CaseTwoLeftProjectionConstructionAux
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



end WeightedCrossings

private theorem weighted_terms {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (coeff : I →₀ Complex) (term : I → M) :
    weighted term (coeff.support.toList.map (fun i => (coeff i, i))) =
      coeff.sum (fun i c => c • term i) := by
  classical
  unfold weighted Finsupp.sum
  rw [List.map_map]
  exact (Finset.sum_map_toList _ _).symm

end
end CaseTwoLeftProjectionConstructionAux

namespace CaseTwoLeftProjectionConstructionAux

open MackeyDiagrams
universe u
noncomputable section

variable {U : Type u} [Group U]

private abbrev crossingIntersection {K H P : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P) (p : P) : Subgroup P :=
  a.toHom.range ⊓ Subgroup.map (MulAut.conj p).toMonoidHom b.toHom.range

private abbrev FiberSize {X Y : Type u} (q : X → Y) (n : Nat) :=
  ∀ z ∈ Set.range q, Nat.card {w : X // q w = z} = n

section FiberIndex

variable {K H P L : Subgroup U}
variable (a : ConjEmbedding K P) (b : ConjEmbedding H P)
  (d : ConjEmbedding L K) (e : ConjEmbedding L H)

-- Lemma 6.3 and (6.1). Insert identity embeddings to use the registered
-- calculation for a single crossing. mixedEquiv changes only its target
-- coordinates, so the fiber subtypes have the same cardinality.
private theorem crossingIndex (p : Dot (a.comp d) (b.comp e)) :
    (a.comp d).toHom.range ≤ crossingIntersection a b p.element ∧
      ((∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b d e p w = z}) ↔
        ((a.comp d).toHom.range.subgroupOf (crossingIntersection a b p.element)).FiniteIndex) := by
  have h := (EvaluationForTwoProjections a b (ConjEmbedding.id H) d (ConjEmbedding.id L) e).1 p
  exact ⟨h.1, h.2.1⟩

private theorem crossingFiberSize (p : ProjectionDot.Mixed a b d e) :
    FiberSize (Generator.mixedMultiplicationBasis a b d e p.dot)
      ((a.comp d).toHom.range.relIndex (crossingIntersection a b p.dot.element)) := by
  intro z hz
  have hinj := (Generator.mixedEquiv a b).injective
  have h := (EvaluationForTwoProjections a b (ConjEmbedding.id H) d (ConjEmbedding.id L) e).2.1 p
    (Generator.mixedProduct a b z) |>.2 (by obtain ⟨w, rfl⟩ := hz; exact ⟨w, rfl⟩)
  refine (Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))).trans h
  exact ⟨congrArg (Generator.mixedProduct a b), fun he => hinj he⟩

private theorem crossingCardBound (p : ProjectionDot.Mixed a b d e) (n : Nat)
    (h : (a.comp d).toHom.range.relIndex (crossingIntersection a b p.dot.element) ≤ n) :
    ∀ z, Nat.card {w // Generator.mixedMultiplicationBasis a b d e p.dot w = z} ≤ n := by
  intro z
  by_cases hz : z ∈ Set.range (Generator.mixedMultiplicationBasis a b d e p.dot)
  · rw [crossingFiberSize a b d e p z hz]
    exact h
  · have empty : IsEmpty {w // Generator.mixedMultiplicationBasis a b d e p.dot w = z} :=
      ⟨fun w => hz ⟨w.1, w.2⟩⟩
    exact (Nat.card_eq_zero.mpr (Or.inl empty)).le.trans (Nat.zero_le n)

end FiberIndex

private theorem rangeComp_le {K H P : Subgroup U} (a : ConjEmbedding H P)
    (b : ConjEmbedding K H) : (a.comp b).toHom.range ≤ a.toHom.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨b.toHom x, rfl⟩

private theorem compId {U₁ U₂ : Subgroup U} (a : ConjEmbedding U₁ U₂) : a.comp (ConjEmbedding.id U₁) = a := by
  apply ConjEmbedding.ext
  exact MonoidHom.ext fun _ => rfl

private def unitDot {K H : Subgroup U} {a b : ConjEmbedding K H} (h : a = b) : Dot a b where
  element := 1
  intertwines x := by subst b; simp

section FullIntersection

variable {G A D F E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (de : ConjEmbedding E G) (f : ConjEmbedding E F)

private abbrev internalGroup (p : A) :=
  (Subgroup.comap a.toHom (crossingIntersection a b p)).map G.subtype

-- Theorem 6.4(2), full-intersection construction. B is a subgroup of the
-- ambient group in the drawing syntax, so transport the comap along G.subtype.
private theorem transportedEmbeddings (p : Dot (a.comp de) ((b.comp c).comp f)) :
    let B := internalGroup a b p.element
    ∃ (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B),
      (∀ v : B, (r.toHom v : U) = (v : U)) ∧
      (∀ v : B, b.toHom (s.toHom v) = p.element⁻¹ * a.toHom (r.toHom v) * p.element) ∧
      r.comp t = de ∧ s.comp t = c.comp f ∧
      (a.comp r).toHom.range = crossingIntersection a b p.element := by
  let I := crossingIntersection a b p.element
  let J := I.comap a.toHom
  let B := J.map G.subtype
  have hBG : B ≤ G := by
    rintro _ ⟨v, _, rfl⟩
    exact v.property
  let r : ConjEmbedding B G :=
    ⟨Subgroup.inclusion hBG, ⟨1, fun _ => by simp⟩⟩
  have hr (v : B) : a.toHom (r.toHom v) ∈ I := by
    obtain ⟨w, hw, hval⟩ := v.property
    have eq : r.toHom v = w := Subtype.ext hval.symm
    rw [eq]
    exact hw
  obtain ⟨α, hα⟩ := a.hasRepresentative
  obtain ⟨β, hβ⟩ := b.hasRepresentative
  let σ : U := β⁻¹ * (p.element : U)⁻¹ * α
  have candidate (v : B) :
      ∃ w : D, (w : U) = σ * (v : U) * σ⁻¹ ∧
        b.toHom w = p.element⁻¹ * a.toHom (r.toHom v) * p.element := by
    obtain ⟨y, ⟨w, rfl⟩, hy⟩ := (hr v).2
    change p.element * b.toHom w * p.element⁻¹ = a.toHom (r.toHom v) at hy
    have hw : b.toHom w = p.element⁻¹ * a.toHom (r.toHom v) * p.element := by rw [← hy]; group
    refine ⟨w, ?_, hw⟩
    have he := congrArg (fun x : A => (x : U)) hw
    change (b.toHom w : U) = (p.element : U)⁻¹ * (a.toHom (r.toHom v) : U) * (p.element : U) at he
    rw [hβ, hα] at he
    change β * (w : U) * β⁻¹ =
      (p.element : U)⁻¹ * (α * (v : U) * α⁻¹) * (p.element : U) at he
    calc
      (w : U) = β⁻¹ * (β * (w : U) * β⁻¹) * β := by group
      _ = σ * (v : U) * σ⁻¹ := by rw [he]; dsimp [σ]; group
  let s : ConjEmbedding B D := ConjEmbedding.ofConjugator σ (fun v => by
    obtain ⟨w, hw, _⟩ := candidate v
    exact hw ▸ w.property)
  have hs (v : B) : b.toHom (s.toHom v) = p.element⁻¹ * a.toHom (r.toHom v) * p.element := by
    obtain ⟨w, hw, he⟩ := candidate v
    have eq : s.toHom v = w := Subtype.ext hw.symm
    rw [eq, he]
  have hlo := (crossingIndex a (b.comp c) de f p).1
  have hI : crossingIntersection a (b.comp c) p.element ≤ I :=
    inf_le_inf_left _ (Subgroup.map_mono (rangeComp_le b c))
  have ht (v : E) : (de.toHom v : U) ∈ B :=
    ⟨de.toHom v, hI (hlo ⟨v, rfl⟩), rfl⟩
  let t : ConjEmbedding E B := ⟨(G.subtype.comp de.toHom).codRestrict B ht, de.hasRepresentative⟩
  have hrt : r.comp t = de := ConjEmbedding.ext (MonoidHom.ext fun _ => rfl)
  have hst : s.comp t = c.comp f := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro v
    apply b.injective
    change b.toHom (s.toHom (t.toHom v)) = b.toHom (c.toHom (f.toHom v))
    rw [hs]
    change p.element⁻¹ * a.toHom (de.toHom v) * p.element = _
    have hp := p.intertwines v
    change a.toHom (de.toHom v) * p.element = p.element * b.toHom (c.toHom (f.toHom v)) at hp
    rw [mul_assoc, hp, inv_mul_cancel_left]
  refine ⟨r, s, t, fun _ => rfl, hs, hrt, hst, ?_⟩
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact hr v
  · intro x hx
    obtain ⟨v, hv⟩ := hx.1
    refine ⟨⟨v, ⟨v, ?_, rfl⟩⟩, hv⟩
    change a.toHom v ∈ I
    rwa [hv]

private theorem transportedIndex (p : Dot (a.comp de) ((b.comp c).comp f))
    {B : Subgroup U} (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
    (hs : ∀ v : B, b.toHom (s.toHom v) = p.element⁻¹ * a.toHom (r.toHom v) * p.element)
    (hrt : r.comp t = de) (hI : (a.comp r).toHom.range = crossingIntersection a b p.element) :
    (s.comp t).toHom.range.relIndex (s.toHom.range ⊓ c.toHom.range) =
      (a.comp de).toHom.range.relIndex (crossingIntersection a (b.comp c) p.element) := by
  let φ : D →* A := (MulAut.conj p.element).toMonoidHom.comp b.toHom
  have hφ : Function.Injective φ := (MulAut.conj p.element).injective.comp b.injective
  have hrs (v : B) : φ (s.toHom v) = a.toHom (r.toHom v) := by
    change p.element * b.toHom (s.toHom v) * p.element⁻¹ = _
    rw [hs]
    group
  have hsMap : s.toHom.range.map φ = (a.comp r).toHom.range := by
    rw [← MonoidHom.range_comp]
    congr 1
    exact MonoidHom.ext hrs
  have htMap : (s.comp t).toHom.range.map φ = (a.comp de).toHom.range := by
    rw [← MonoidHom.range_comp, ← hrt]
    congr 1
    exact MonoidHom.ext fun v => hrs (t.toHom v)
  have hcMap : c.toHom.range.map φ =
      (b.comp c).toHom.range.map (MulAut.conj p.element).toMonoidHom := by
    rw [← Subgroup.map_map, ← MonoidHom.range_comp]
    rfl
  have hcLe := Subgroup.map_mono (f := (MulAut.conj p.element).toMonoidHom) (rangeComp_le b c)
  have upperMap : (s.toHom.range ⊓ c.toHom.range).map φ =
      crossingIntersection a (b.comp c) p.element := by
    rw [Subgroup.map_inf _ _ _ hφ, hsMap, hI, hcMap]
    change (_ ⊓ _) ⊓ _ = a.toHom.range ⊓ _
    rw [inf_assoc, inf_eq_right.mpr hcLe]
  rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, htMap, upperMap]

end FullIntersection

end
end CaseTwoLeftProjectionConstructionAux
namespace CaseTwoLeftProjectionConstructionAux

open MackeyDiagrams
universe u
noncomputable section

variable {U : Type u} [Group U]
variable {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private theorem mkFinite {K H P L : Subgroup U}
    (α : ConjEmbedding K P) (β : ConjEmbedding H P)
    (η : ConjEmbedding L K) (θ : ConjEmbedding L H) (p : Dot (α.comp η) (β.comp θ))
    (h : (α.comp η).toHom.range.relIndex (crossingIntersection α β p.element) ≠ 0) :
    ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis α β η θ p w = z} :=
  (crossingIndex α β η θ p).2.mpr (Subgroup.finiteIndex_iff.mpr h)

private theorem crossingIntersection_one {K H P : Subgroup U}
    (α : ConjEmbedding K P) (β : ConjEmbedding H P) :
    crossingIntersection α β 1 = α.toHom.range ⊓ β.toHom.range := by
  change α.toHom.range ⊓ Subgroup.map _ β.toHom.range = _
  have h : (MulAut.conj (1 : P)).toMonoidHom = MonoidHom.id P :=
    MonoidHom.ext fun x => by simp
  rw [h, Subgroup.map_id]

private def lowerDot (p : Parameter a b c d e f)
    (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (hs : ∀ v : B,
      b.toHom (s.toHom v) = p.dot.element⁻¹ * a.toHom (r.toHom v) * p.dot.element) :
    Dot (a.comp r) (b.comp s) where
  element := p.dot.element
  intertwines v := by
    change a.toHom (r.toHom v) * p.dot.element = p.dot.element * b.toHom (s.toHom v)
    rw [hs, ← mul_assoc p.dot.element, mul_inv_cancel, one_mul]

private theorem fullCrossings (p : Parameter a b c d e f)
    (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
    (hs : ∀ v : B, b.toHom (s.toHom v) = p.dot.element⁻¹ * a.toHom (r.toHom v) * p.dot.element)
    (hrt : r.comp t = d.comp e) (hst : s.comp t = c.comp f)
    (hI : (a.comp r).toHom.range = crossingIntersection a b p.dot.element) :
    ∃ (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
      (z : Dot (r.comp t) (d.comp e)),
      x.dot.element = p.dot.element ∧ y.dot.element = 1 ∧ z.element = 1 ∧
      FiberSize (Generator.mixedMultiplicationBasis a b r s x.dot) 1 ∧
      FiberSize (Generator.mixedMultiplicationBasis s c t f y.dot)
        ((a.comp (d.comp e)).toHom.range.relIndex (crossingIntersection a (b.comp c) p.dot.element)) := by
  let xDot := lowerDot a b c d e f p r s hs
  have hx : (a.comp r).toHom.range.relIndex (crossingIntersection a b xDot.element) = 1 := by
    change (a.comp r).toHom.range.relIndex (crossingIntersection a b p.dot.element) = 1
    rw [hI, Subgroup.relIndex_self]
  let x : ProjectionDot.Mixed a b r s := ⟨xDot, mkFinite a b r s xDot (by rw [hx]; decide)⟩
  let yDot : Dot _ _ := unitDot hst
  have hy : (s.comp t).toHom.range.relIndex (crossingIntersection s c yDot.element) =
      (a.comp (d.comp e)).toHom.range.relIndex (crossingIntersection a (b.comp c) p.dot.element) := by
    change (s.comp t).toHom.range.relIndex (crossingIntersection s c 1) = _
    rw [crossingIntersection_one]
    exact transportedIndex a b c (d.comp e) f p.dot r s t hs hrt hI
  have houter := (crossingIndex a (b.comp c) (d.comp e) f p.dot).2.mp p.finite
  let y : ProjectionDot.Mixed s c t f :=
    ⟨yDot, mkFinite s c t f yDot (by rw [hy]; exact houter.index_ne_zero)⟩
  refine ⟨x, y, unitDot hrt, rfl, rfl, rfl, ?_, ?_⟩
  · rw [← hx]
    exact crossingFiberSize a b r s x
  · rw [← hy]
    exact crossingFiberSize s c t f y

-- Theorem 6.4(2), common region E. The first intermediate subgroup lies
-- between the image of E and a(G). The finite ambient index gives a
-- nonzero index throughout this tower and bounds the first fiber size.
private theorem commonLower (h : (d.comp e).toHom.range.FiniteIndex)
    (p : Parameter a b c d e f) :
    ∃ x : ProjectionDot.Mixed a b (d.comp e) (c.comp f), x.dot.element = p.dot.element ∧
      ∀ z, Nat.card {w // Generator.mixedMultiplicationBasis a b (d.comp e) (c.comp f) x.dot w = z} ≤
        (d.comp e).toHom.range.index := by
  let de := d.comp e
  let cf := c.comp f
  let xDot : Dot (a.comp de) (b.comp cf) := p.dot
  let L := (a.comp de).toHom.range
  let M := crossingIntersection a b xDot.element
  let H := a.toHom.range
  have hlm : L ≤ M := (crossingIndex a b de cf xDot).1
  have hmh : M ≤ H := inf_le_left
  have hwhole : L.relIndex H = de.toHom.range.index := by
    change (a.toHom.comp de.toHom).range.relIndex a.toHom.range = de.toHom.range.index
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map a.toHom,
      Subgroup.relIndex_map_map_of_injective _ _ a.injective, Subgroup.relIndex_top_right]
  have hnonzero : L.relIndex H ≠ 0 := hwhole ▸ h.index_ne_zero
  have hpart : L.relIndex M ≠ 0 := by
    intro hz
    have hmul := Subgroup.relIndex_mul_relIndex L M H hlm hmh
    rw [hz, zero_mul] at hmul
    exact hnonzero hmul.symm
  let x : ProjectionDot.Mixed a b de cf := ⟨xDot, mkFinite a b de cf xDot hpart⟩
  refine ⟨x, rfl, crossingCardBound a b de cf x _ ?_⟩
  exact (Subgroup.relIndex_le_of_le_right hmh hnonzero).trans_eq hwhole

private theorem commonUpper :
    let t := ConjEmbedding.id E
    ∃ y : ProjectionDot.Mixed (c.comp f) c t f,
      y.dot.element = 1 ∧ FiberSize (Generator.mixedMultiplicationBasis (c.comp f) c t f y.dot) 1 := by
  let cf := c.comp f
  let t := ConjEmbedding.id E
  let yDot : Dot (cf.comp t) (c.comp f) := unitDot (compId cf)
  have hy : (cf.comp t).toHom.range.relIndex (crossingIntersection cf c yDot.element) = 1 := by
    change (cf.comp t).toHom.range.relIndex (crossingIntersection cf c 1) = 1
    rw [crossingIntersection_one, compId, inf_eq_left.mpr (rangeComp_le c f), Subgroup.relIndex_self]
  let y : ProjectionDot.Mixed cf c t f := ⟨yDot, mkFinite cf c t f yDot (by rw [hy]; decide)⟩
  refine ⟨y, rfl, ?_⟩
  rw [← hy]
  exact crossingFiberSize cf c t f y

-- The linear combination at one crossing keeps one crossing vertex in the
-- drawing. Linearity is used on the evaluation of its surrounding diagram.
private theorem linearLeftEval (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B)
    (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (y : ProjectionDot.Mixed s c t f) (z : Dot (r.comp t) (d.comp e)) :
    mergedEval a b c d e f (leftDrawing a b c d e f r s t xs [(1,y)] [(1,z)]) =
    weighted (fun x =>
      mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)])) xs := by
  let first := fun xs => atLeft (.compactProjection a b r s xs) (.up c)
  let middle := atRight (.up r) (.compactProjection s c t f [(1,y)])
  let last := atLeft (.parallelUp r t d e [(1,z)]) (.down f)
  let post := ev (before middle (before last (mergeTop d e f)))
  let frame := composeAround (ev (splitBottom a b c)) post
  change frame (ev (first xs)) = weighted (fun x => frame (ev (first [(1,x)]))) xs
  rw [weighted_atLeft _ _ xs (weighted_compact a b r s xs), map_weighted]

private theorem sumEval (terms : Parameter a b c d e f →
    LabelledDrawing Complex (bottom a b c) (top d e f)) (xs : List (Complex × Parameter a b c d e f)) :
    mergedEval a b c d e f
      (xs.foldr (fun term total => .add (.scale term.1 (terms term.2)) total)
        (.ordinary (.zero _ _))) =
    weighted (fun p => mergedEval a b c d e f (terms p)) xs := by
  let frame := composeAround (ev (splitBottom a b c)) (ev (mergeTop d e f))
  let fold := fun xs : List (Complex × Parameter a b c d e f) =>
    xs.foldr (fun term total => LabelledDrawing.add (.scale term.1 (terms term.2)) total)
        (.ordinary (.zero _ _))
  have h (xs : List (Complex × Parameter a b c d e f)) :
      ev (fold xs) = weighted (fun p => ev (terms p)) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change x.1 • ev (terms x.2) + ev (fold xs) =
        x.1 • ev (terms x.2) + weighted (fun p => ev (terms p)) xs
      rw [ih]
  change frame (ev (fold xs)) = weighted (fun p => frame (ev (terms p))) xs
  rw [h, map_weighted]

end
end CaseTwoLeftProjectionConstructionAux
