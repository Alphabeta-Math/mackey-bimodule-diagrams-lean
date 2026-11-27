namespace OutsideRegionsAux
open MackeyDiagrams

-- The registered Lemma 6.3 proves existence and uniqueness of the merged
-- projection parameter. Its internal coefficient computation also identifies
-- that parameter. Keep the coefficient calculation local so the bounds can
-- use the actual product of the three marked labels.
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

-- Lemma 6.3, left backward calculation. At each stage the linear coefficient
-- is evaluated at its unique backwards coordinate. The fixed strands act
-- freely at the balancing interfaces, so rebracketing retains the fiber sum.
private theorem pulls_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedPair a (b.comp c)
        (a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h)) := by
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
    (a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h))
  have hc : x' = a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h := by
    simp only [x', g', y', leftParameter, ConjEmbedding.comp_apply, map_mul, mul_assoc]
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
      (Generator.mixedPair a (b.comp c)
        (a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h)) := by
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
    (a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h))
  have hel := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at hel
  have hc : m' * ell.element⁻¹ =
      a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h := by
    simp only [m', n', rightParameter, ConjEmbedding.comp_apply, map_mul, mul_assoc, hel]
  rw [← hc]
  exact out

end
end OutsideRegionsAux
