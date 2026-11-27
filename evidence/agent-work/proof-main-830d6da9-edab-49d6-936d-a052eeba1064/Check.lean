import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import MackeyDiagrams
import Proofs.ParallelReidemeisterTwoInduction

set_option maxHeartbeats 2000000

namespace StandardSymmetricBraidProof

open MackeyDiagrams

noncomputable section

variable {U : Type*} [Group U] {G H J F : Subgroup U}
variable (a : ConjEmbedding H G) (b : ConjEmbedding J H) (c : ConjEmbedding F J)

private abbrev cross (d : Dot (a.comp b) (a.comp b)) :
    Diagram Complex ((Word.up a).tensor (.up b)) ((Word.up a).tensor (.up b)) :=
  (Diagram.mergeUp a b).vertical ((Diagram.upDot d).vertical (Diagram.splitUp a b))

private abbrev left (d : Dot (a.comp b) (a.comp b)) :=
  (cross a b d).horizontal (Diagram.id (.up c))

private abbrev right (e : Dot (b.comp c) (b.comp c)) :=
  (Diagram.associate (.up a) (.up b) (.up c)).vertical
    (((Diagram.id (.up a)).horizontal (cross b c e)).vertical
      (Diagram.unassociate (.up a) (.up b) (.up c)))

private abbrev triple (x : G) (y : H) (z : J) :
    (((Word.up a).tensor (.up b)).tensor (.up c)).basis.carrier :=
  ((Word.up a).basis.tensor (Word.up b).basis).pair (Word.up c).basis
    ((Word.up a).basis.pair (Word.up b).basis x y) z

private theorem pair_normal (x : G) (y : H) :
    (Word.up a).basis.pair (Word.up b).basis x y =
      (Word.up a).basis.pair (Word.up b).basis (x * a.toHom y) 1 := by
  symm
  simpa [Word.basis, Biset.induction] using
    (Word.up a).basis.pair_balance (Word.up b).basis y x 1

-- Balance the third coordinate into the second, then the second into
-- the first. This is the three-strand merge and split on representatives.
private theorem triple_normal (x : G) (y : H) (z : J) :
    triple a b c x y z = triple a b c (x * a.toHom (y * b.toHom z)) 1 1 := by
  have moveRight : triple a b c x (y * b.toHom z) 1 = triple a b c x y z := by
    simpa [Biset.act_pair, Word.basis, Biset.induction] using
      ((Word.up a).basis.tensor (Word.up b).basis).pair_balance (Word.up c).basis
        z ((Word.up a).basis.pair (Word.up b).basis x y) 1
  rw [← moveRight]
  exact congrArg (fun xy => ((Word.up a).basis.tensor (Word.up b).basis).pair
    (Word.up c).basis xy 1) (pair_normal a b x (y * b.toHom z))

-- The parallel-crossing composition supplier composes two crossings on
-- the same pair. Here the active pair alternates and the right crossing
-- changes parentheses. Compute each crossing using the checked merge,
-- dot, split and associator basis equations, then compose the resulting
-- right multiplications in stacking order.
private theorem cross_single (d : Dot (a.comp b) (a.comp b)) (x : G) (y : H)
    (r : Complex) :
    (cross a b d).eval.toLinearMap
      (Finsupp.single ((Word.up a).basis.pair (Word.up b).basis x y) r) =
    Finsupp.single ((Word.up a).basis.pair (Word.up b).basis
      (x * a.toHom y * d.element) 1) r := by
  unfold cross
  rw [Diagram.eval_vertical_apply, Diagram.eval_vertical_apply]
  rw [Diagram.eval_mergeUp_single a b x y r,
    Diagram.eval_upDot_single, Diagram.eval_splitUp_single]

private theorem left_single (d : Dot (a.comp b) (a.comp b)) (x : G) (r : Complex) :
    (left a b c d).eval.toLinearMap (Finsupp.single (triple a b c x 1 1) r) =
      Finsupp.single (triple a b c (x * d.element) 1 1) r := by
  rw [Diagram.eval_horizontal_single (cross a b d) (Diagram.id (.up c)),
    cross_single a b, Diagram.eval_id_apply, Biset.pairLinear_single]
  simp only [map_one, mul_one, Finsupp.smul_single, smul_eq_mul]

private theorem right_single (e : Dot (b.comp c) (b.comp c)) (x : G) (r : Complex) :
    (right a b c e).eval.toLinearMap (Finsupp.single (triple a b c x 1 1) r) =
      Finsupp.single (triple a b c (x * a.toHom e.element) 1 1) r := by
  unfold right
  rw [Diagram.eval_vertical_apply, Diagram.eval_vertical_apply]
  rw [Diagram.eval_associate_single (.up a) (.up b) (.up c),
    Diagram.eval_horizontal_single (Diagram.id (.up a)) (cross b c e),
    Diagram.eval_id_apply, cross_single b c, Biset.pairLinear_single]
  simp only [map_one, one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Diagram.eval_unassociate_single (.up a) (.up b) (.up c)]
  exact congrArg (fun xy => Finsupp.single
    (((Word.up a).basis.tensor (Word.up b).basis).pair (Word.up c).basis xy 1) r)
    (pair_normal a b x e.element)

private theorem braid (d : Dot (a.comp b) (a.comp b)) (e : Dot (b.comp c) (b.comp c))
    (h : a.toHom e.element * d.element * a.toHom e.element =
      d.element * a.toHom e.element * d.element) :
    ((right a b c e).vertical ((left a b c d).vertical (right a b c e))).eval =
      ((left a b c d).vertical ((right a b c e).vertical (left a b c d))).eval := by
  apply Diagram.eval_ext
  intro v r
  refine Quotient.inductionOn v (fun pair => ?_)
  rcases pair with ⟨xy, z⟩
  refine Quotient.inductionOn xy (fun pair => ?_)
  rcases pair with ⟨x, y⟩
  change
    (((right a b c e).vertical ((left a b c d).vertical (right a b c e))).eval.toLinearMap
      (Finsupp.single (triple a b c x y z) r)) =
    (((left a b c d).vertical ((right a b c e).vertical (left a b c d))).eval.toLinearMap
      (Finsupp.single (triple a b c x y z) r))
  rw [triple_normal a b c]
  rw [Diagram.eval_vertical_apply (right a b c e) ((left a b c d).vertical (right a b c e)),
    Diagram.eval_vertical_apply (left a b c d) (right a b c e),
    Diagram.eval_vertical_apply (left a b c d) ((right a b c e).vertical (left a b c d)),
    Diagram.eval_vertical_apply (right a b c e) (left a b c d),
    right_single, left_single, right_single, left_single, right_single, left_single]
  simpa only [mul_assoc] using congrArg
    (fun t => Finsupp.single (triple a b c ((x * a.toHom (y * b.toHom z)) * t) 1 1) r) h

end

end StandardSymmetricBraidProof

theorem StandardSymmetricGroupBraidRelation : (∀ n : Nat,
  let X := Fin (n + 3)
  let U := Equiv.Perm X
  let S := fun m : Nat => fixingSubgroup U {i : X | m ≤ i.val}
  let G : Subgroup U := ⊤
  let H := S (n + 2)
  let J := S (n + 1)
  let F := S n
  let nested : ∀ {m k : Nat}, m ≤ k → S m ≤ S k := fun h _ hp =>
    (mem_fixingSubgroup_iff U).mpr
      (fun i hi => (mem_fixingSubgroup_iff U).mp hp i (Nat.le_trans h hi))
  let inclusion : ∀ {A B : Subgroup U}, A ≤ B → MackeyDiagrams.ConjEmbedding A B :=
    fun h => ⟨Subgroup.inclusion h, ⟨1, fun _ => by simp⟩⟩
  let a : MackeyDiagrams.ConjEmbedding H G := inclusion le_top
  let b : MackeyDiagrams.ConjEmbedding J H := inclusion (nested (Nat.le_succ (n + 1)))
  let c : MackeyDiagrams.ConjEmbedding F J := inclusion (nested (Nat.le_succ n))
  let p := MackeyDiagrams.Word.up a
  let q := MackeyDiagrams.Word.up b
  let r := MackeyDiagrams.Word.up c
  let word := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.tensor p q) r
  let i : X := ⟨n, by omega⟩
  let j : X := ⟨n + 1, by omega⟩
  let k : X := ⟨n + 2, by omega⟩
  let leftSwap : U := Equiv.swap j k
  let rightSwap : U := Equiv.swap i j
  let ab := MackeyDiagrams.ConjEmbedding.comp a b
  let bc := MackeyDiagrams.ConjEmbedding.comp b c
  ∃ (leftDot : MackeyDiagrams.Dot ab ab) (rightDot : MackeyDiagrams.Dot bc bc),
    (MackeyDiagrams.Dot.element leftDot : U) = leftSwap ∧
    (MackeyDiagrams.Dot.element rightDot : U) = rightSwap ∧
    let cross := fun {A B C : Subgroup U}
        (upper : MackeyDiagrams.ConjEmbedding B C)
        (lower : MackeyDiagrams.ConjEmbedding A B)
        (dot : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp upper lower)
          (MackeyDiagrams.ConjEmbedding.comp upper lower)) =>
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.mergeUp (R := Complex) upper lower)
        (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.upDot dot)
          (MackeyDiagrams.Diagram.splitUp upper lower))
    let leftCrossing : MackeyDiagrams.Diagram Complex word word :=
      MackeyDiagrams.Diagram.horizontal (cross a b leftDot) (MackeyDiagrams.Diagram.id r)
    let rightCrossing : MackeyDiagrams.Diagram Complex word word :=
      MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.associate p q r)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id p) (cross b c rightDot))
          (MackeyDiagrams.Diagram.unassociate p q r))
    let rightLeftRight :=
      MackeyDiagrams.Diagram.vertical rightCrossing
        (MackeyDiagrams.Diagram.vertical leftCrossing rightCrossing)
    let leftRightLeft :=
      MackeyDiagrams.Diagram.vertical leftCrossing
        (MackeyDiagrams.Diagram.vertical rightCrossing leftCrossing)
    MackeyDiagrams.Diagram.eval rightLeftRight = MackeyDiagrams.Diagram.eval leftRightLeft) :=
(by
  -- Xiao §6.1 (archived p. 19, published 28 November revision p. 21)
  -- cites Khovanov, Proposition 7, equation (36), top-right identity
  -- (arXiv:1009.3295, p. 31). This endpoint has no matching numbered
  -- Alphabeta proof in the route. The adjacent-transposition argument
  -- applies over Complex and includes n = 0.
  intro n X U S G H J F nested inclusion a b c p q r word i j k leftSwap rightSwap ab bc
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change n = n + 1 at hv
    omega
  have hik : i ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    change n = n + 2 at hv
    omega
  have hjk : j ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    change n + 1 = n + 2 at hv
    omega
  -- Each swap has to be in its own target region and fix the source action
  -- by conjugation. The right swap fixes the last point of Fin (n+3).
  have rightMem : rightSwap ∈ H := by
    change Equiv.swap i j ∈ fixingSubgroup U {t : X | n + 2 ≤ t.val}
    apply (mem_fixingSubgroup_iff U).2
    intro t ht
    change n + 2 ≤ t.val at ht
    have hti : t ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      change t.val = n at hv
      omega
    have htj : t ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      change t.val = n + 1 at hv
      omega
    exact Equiv.swap_apply_of_ne_of_ne hti htj
  have fixes {m : Nat} (u : S m) (t : X) (ht : m ≤ t.val) : (u : U) t = t :=
    (mem_fixingSubgroup_iff U).mp u.property t ht
  -- Diagram.upDot uses the coefficient-one singleton case of the shared
  -- dot language. The two eligibility proofs use the endpoints fixed by
  -- each source subgroup and Mathlib's permutation transport of a swap.
  let d : MackeyDiagrams.Dot ab ab :=
    ⟨⟨leftSwap, Subgroup.mem_top _⟩, fun u => by
      apply Subtype.ext
      change (u : U) * Equiv.swap j k = Equiv.swap j k * (u : U)
      rw [Equiv.mul_swap_eq_swap_mul, fixes u j (by change n + 1 ≤ n + 1; omega),
        fixes u k (by change n + 1 ≤ n + 2; omega)]⟩
  let e : MackeyDiagrams.Dot bc bc :=
    ⟨⟨rightSwap, rightMem⟩, fun u => by
      apply Subtype.ext
      change (u : U) * Equiv.swap i j = Equiv.swap i j * (u : U)
      rw [Equiv.mul_swap_eq_swap_mul, fixes u i (by change n ≤ n; omega),
        fixes u j (by change n ≤ n + 1; omega)]⟩
  refine ⟨d, e, rfl, rfl, ?_⟩
  apply StandardSymmetricBraidProof.braid a b c d e
  apply Subtype.ext
  change Equiv.swap i j * Equiv.swap j k * Equiv.swap i j =
    Equiv.swap j k * Equiv.swap i j * Equiv.swap j k
  calc
    Equiv.swap i j * Equiv.swap j k * Equiv.swap i j =
        Equiv.swap j i * Equiv.swap k j * Equiv.swap j i := by
      rw [Equiv.swap_comm j i, Equiv.swap_comm k j]
    _ = Equiv.swap i k := Equiv.swap_mul_swap_mul_swap hjk.symm hik.symm
    _ = Equiv.swap k i := Equiv.swap_comm _ _
    _ = Equiv.swap j k * Equiv.swap i j * Equiv.swap j k :=
      (Equiv.swap_mul_swap_mul_swap hij hik).symm)

#print axioms StandardSymmetricGroupBraidRelation
