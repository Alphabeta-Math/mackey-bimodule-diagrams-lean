import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionBimoduleOrbitSumBasis

set_option maxHeartbeats 2000000

namespace FiniteOrbitSumDiagramSupport

open MackeyDiagrams Diagram
open scoped Classical Pointwise

noncomputable section

universe u

variable {U : Type u} [Group U] {H G : Subgroup U}

private def twist (a b : ConjEmbedding H G) (h : H) (g : G) : G :=
  a.toHom h * g * (b.toHom h)⁻¹

@[instance_reducible] private def twistAction (a b : ConjEmbedding H G) : MulAction H G where
  smul := twist a b
  one_smul g := by
    change twist a b 1 g = g
    simp [twist]
  mul_smul h k g := by
    change twist a b (h * k) g = twist a b h (twist a b k g)
    simp only [twist, map_mul, mul_inv_rev]
    group

private def twistStabilizer (a b : ConjEmbedding H G) (g : G) : Subgroup H :=
  letI := twistAction a b
  MulAction.stabilizer H g

private theorem coeff_orbitSum (s : Finset G) (z : G) [Decidable (z ∈ s)] :
    (∑ g ∈ s, MonoidAlgebra.single g (1 : Complex)).coeff z =
      if z ∈ s then 1 else 0 := by
  classical
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finset.sum_ite_eq']
  split <;> simp_all

private def trivialEmbedding (H : Subgroup U) : ConjEmbedding (⊥ : Subgroup U) H :=
  ConjEmbedding.ofConjugator 1 (fun h => by
    have hh : (h : U) = 1 := Subgroup.mem_bot.mp h.property
    simp [hh])

private theorem trivial_arg (h : (⊥ : Subgroup U)) : h = 1 :=
  Subtype.ext (Subgroup.mem_bot.mp h.property)

private def middleDot (a b : ConjEmbedding H G) (g : G) :
    Dot (a.comp (trivialEmbedding H)) (b.comp (trivialEmbedding H)) where
  element := g
  intertwines h := by rw [trivial_arg h, map_one, map_one, one_mul, mul_one]

-- Specialize the registered reverse-cup formula at 1, with all of H as the
-- transversal. Its pair (t⁻¹,t) uses the paper's parameter t directly.
private theorem cup_single [Fintype H] (finite : (trivialEmbedding H).toHom.range.FiniteIndex) :
    (reverseCup (R := Complex) (trivialEmbedding H) finite).eval.toLinearMap
      (Finsupp.single (1 : H) 1) =
      ∑ t : H, Finsupp.single ((Word.up (trivialEmbedding H)).basis.pair
        (Word.down (trivialEmbedding H)).basis t⁻¹ t) 1 := by
  let j := trivialEmbedding H
  have hmem (x : H) : x ∈ j.toHom.range ↔ x = 1 := by
    constructor
    · rintro ⟨s, rfl⟩
      rw [trivial_arg s, map_one]
    · rintro rfl
      exact ⟨1, map_one _⟩
  have htrans : ∀ x : H, ∃! t : {t : H // t ∈ (Finset.univ : Finset H)},
      x * t.val⁻¹ ∈ j.toHom.range := by
    intro x
    refine ⟨⟨x, Finset.mem_univ x⟩, (hmem _).2 (mul_inv_cancel x), ?_⟩
    intro t ht
    apply Subtype.ext
    simpa only [inv_inv] using inv_eq_of_mul_eq_one_left ((hmem _).1 ht)
  have adj := (FiniteIndexReverseAdjunction.{u, 0} (⊥ : Subgroup U) H 1 (by
    intro s
    simp [(Subgroup.mem_bot.mp s.property : (s : U) = 1)])).2.2.2.2 finite
  dsimp only at adj
  obtain ⟨_, _, _, hcup⟩ := adj
  have he := ((hcup Finset.univ htrans).1 (1 : H)).1
  rw [MonoidAlgebra.coeff_single] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro t _
  change Biset.pairLinear Complex (Word.up j).basis (Word.down j).basis
    (MonoidAlgebra.single ((1 : H) * t⁻¹) (1 : Complex)).coeff
    (MonoidAlgebra.single t (1 : Complex)).coeff =
    Finsupp.single ((Word.up j).basis.pair (Word.down j).basis t⁻¹ t) 1
  rw [one_mul, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
    Biset.pairLinear_single Complex (Word.up j).basis (Word.down j).basis t⁻¹ t, one_mul]

private def capPair (H : Subgroup U) (t : H) :
    (reverseCupWord (trivialEmbedding H)).basis.carrier :=
  (Word.up (trivialEmbedding H)).basis.pair (Word.down (trivialEmbedding H)).basis t⁻¹ t

private def openCup (a : ConjEmbedding H G)
    (finite : (trivialEmbedding H).toHom.range.FiniteIndex) :
    Diagram Complex (.up a) ((Word.up a).tensor (reverseCupWord (trivialEmbedding H))) :=
  (insertRightUnit (.up a)).vertical
    (.horizontal (.id (.up a)) (.reverseCup (trivialEmbedding H) finite))

private theorem openCup_single [Fintype H] (a : ConjEmbedding H G)
    (finite : (trivialEmbedding H).toHom.range.FiniteIndex) (x : G) :
    (openCup a finite).eval.toLinearMap (Finsupp.single x 1) =
      ∑ h : H, Finsupp.single
        ((Word.up a).basis.pair (reverseCupWord (trivialEmbedding H)).basis x (capPair H h)) 1 := by
  classical
  let p := Word.up a
  have he : (insertRightUnit (R := Complex) p).eval.toLinearMap (Finsupp.single x 1) =
      Finsupp.single (p.basis.pair (Biset.regular H) x 1) 1 := by
    change (Biset.insertRightUnit p.basis Complex).toLinearMap _ = _
    rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]
  unfold openCup
  rw [eval_vertical_apply, he, eval_horizontal_single, one_smul, eval_id_apply, cup_single, map_sum]
  apply Finset.sum_congr rfl
  intro h _
  change Biset.pairLinear Complex p.basis (reverseCupWord (trivialEmbedding H)).basis
    (Finsupp.single x 1) (Finsupp.single (capPair H h) 1) = _
  rw [Biset.pairLinear_single Complex p.basis (reverseCupWord (trivialEmbedding H)).basis x (capPair H h),
    one_mul]

private def orbitTail (a b : ConjEmbedding H G) (g : G) :
    Diagram Complex ((Word.up a).tensor (reverseCupWord (trivialEmbedding H))) (.up b) :=
  let t := trivialEmbedding H
  (unassociate (.up a) (.up t) (.down t)).vertical
    ((horizontal (mergeUp a t) (id (.down t))).vertical
      ((horizontal (upDot (middleDot a b g)) (id (.down t))).vertical
        ((horizontal (splitUp b t) (id (.down t))).vertical
          ((associate (.up b) (.up t) (.down t)).vertical
            ((horizontal (id (.up b)) (multiplicationCap t)).vertical
              (rightUnit (.up b)))))))

private theorem orbitTail_single (a b : ConjEmbedding H G) (g x : G) (h : H) :
    (orbitTail a b g).eval.toLinearMap (Finsupp.single
      ((Word.up a).basis.pair (reverseCupWord (trivialEmbedding H)).basis x (capPair H h)) 1) =
      Finsupp.single (x * twist a b h⁻¹ g) 1 := by
  let t := trivialEmbedding H
  let p := Word.up a
  let q := Word.up b
  let u := Word.up t
  let v := Word.down t
  let d := middleDot a b g
  let input := Finsupp.single (p.basis.pair (u.basis.tensor v.basis) x (u.basis.pair v.basis h⁻¹ h))
    (1 : Complex)
  change (rightUnit q).eval.toLinearMap
    ((horizontal (id q) (multiplicationCap t)).eval.toLinearMap
      ((associate q u v).eval.toLinearMap
        ((horizontal (splitUp b t) (id v)).eval.toLinearMap
          ((horizontal (upDot d) (id v)).eval.toLinearMap
            ((horizontal (mergeUp a t) (id v)).eval.toLinearMap
              ((unassociate p u v).eval.toLinearMap input)))))) = _
  dsimp only [input]
  rw [eval_unassociate_single p u v x h⁻¹ h 1]
  rw [eval_horizontal_single (mergeUp a t) (id v), one_smul, eval_id_apply,
    eval_mergeUp_single a t x h⁻¹ 1, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (upDot d) (id v), one_smul, eval_id_apply,
    eval_upDot_single d (x * a.toHom h⁻¹) 1, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (splitUp b t) (id v), one_smul, eval_id_apply,
    eval_splitUp_single b t, Biset.pairLinear_single, one_mul]
  rw [eval_associate_single q u v, eval_horizontal_single (id q) (multiplicationCap t),
    one_smul, eval_id_apply, eval_multiplicationCap_single t 1 h 1,
    Biset.pairLinear_single, one_mul, eval_rightUnit_single q]
  change Finsupp.single (1 * (x * a.toHom h⁻¹ * g) * (b.toHom (h⁻¹))⁻¹) (1 * 1 : Complex) = _
  simp [twist, mul_assoc]

-- Orbit-stabilizer identifies the fiber at z with the coset of a chosen
-- preimage. Translating that coset gives exactly the stabilizer of g.
private theorem fiberCard [Fintype H] (a b : ConjEmbedding H G) (g z : G)
    (hz : z ∈ Set.range (fun h : H => twist a b h g)) :
    (Finset.univ.filter (fun h : H => twist a b h g = z)).card =
      Nat.card (twistStabilizer a b g) := by
  classical
  let _ := twistAction a b
  obtain ⟨k, rfl⟩ := hz
  let S := MulAction.stabilizer H g
  let e := MulAction.orbitEquivQuotientStabilizer H g
  let T := Finset.univ.filter fun h : H => twist a b h g = twist a b k g
  have heq (h : H) : h ∈ T ↔ h ∈ k • (S : Set H) := by
    rw [mem_leftCoset_iff]
    change h ∈ T ↔ k⁻¹ * h ∈ S
    rw [← QuotientGroup.eq (s := S)]
    rw [← e.symm.injective.eq_iff, Subtype.ext_iff]
    change h ∈ T ↔ twist a b k g = twist a b h g
    simp [T, eq_comm]
  change T.card = Nat.card S
  rw [← Fintype.card_coe T, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ((Equiv.subtypeEquivRight heq).trans (S.leftCosetEquivSubgroup k))

private theorem sum_twist [Fintype H] (a b : ConjEmbedding H G) (g : G)
    (s : Finset G) (hs : (s : Set G) = Set.range (fun h : H => twist a b h g)) :
    (∑ h : H, MonoidAlgebra.single (twist a b h g) (1 : Complex)) =
      (Nat.card (twistStabilizer a b g) : Complex) •
        ∑ z ∈ s, MonoidAlgebra.single z (1 : Complex) := by
  classical
  let S := twistStabilizer a b g
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro z
  have hc :
      (∑ h : H, MonoidAlgebra.single (twist a b h g) (1 : Complex)).coeff z =
      ((Finset.univ.filter fun h : H => twist a b h g = z).card : Complex) := by
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hc]
  change _ = (Nat.card S : Complex) * (∑ w ∈ s, MonoidAlgebra.single w (1 : Complex)).coeff z
  rw [coeff_orbitSum]
  by_cases hz : z ∈ s
  · have hm : z ∈ Set.range (fun h : H => twist a b h g) :=
      hs ▸ (show z ∈ (s : Set G) from hz)
    rw [ite_eq_left hz, mul_one, fiberCard a b g z hm]
  · have he : (Finset.univ.filter (fun h : H => twist a b h g = z)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro h _ he
      exact hz (show z ∈ (s : Set G) from hs.symm ▸ ⟨h, he⟩)
    rw [he, Finset.card_empty, Nat.cast_zero, ite_eq_right hz, mul_zero]

private theorem sum_inv_twist [Fintype H] (a b : ConjEmbedding H G) (g : G)
    (s : Finset G) (hs : (s : Set G) = Set.range (fun h : H => twist a b h g)) :
    (∑ h : H, MonoidAlgebra.single (twist a b h⁻¹ g) (1 : Complex)) =
      (Nat.card {h : H // twist a b h g = g} : Complex) •
        ∑ z ∈ s, MonoidAlgebra.single z (1 : Complex) := by
  exact (Equiv.sum_comp (Equiv.inv H)
    (fun h : H => MonoidAlgebra.single (twist a b h g) (1 : Complex))).trans
    (sum_twist a b g s hs)

-- Alphabeta Math, Universal property of M ⊗[R] N, Steps 3.1 and 4.1
-- check balancing and descend to the quotient. Here the shared Biset
-- constructors supply the balance and descent proofs for each map.
-- Step 5.1 determines the descended map on elementary tensors. Here
-- MonoidAlgebra.induction_linear extends the singleton calculation using
-- linearity of the composite and of right multiplication by the fixed sum.
private theorem composite_eval [Fintype H] (a b : ConjEmbedding H G)
    (finite : (trivialEmbedding H).toHom.range.FiniteIndex) (g : G)
    (x : MonoidAlgebra Complex G) :
    ((openCup a finite).vertical (orbitTail a b g)).eval.toLinearMap x.coeff =
      (x * ∑ t : H, MonoidAlgebra.single (twist a b t⁻¹ g) (1 : Complex)).coeff := by
  let y := ∑ t : H, MonoidAlgebra.single (twist a b t⁻¹ g) (1 : Complex)
  change ((openCup a finite).vertical (orbitTail a b g)).eval.toLinearMap x.coeff = (x * y).coeff
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    simp only [MonoidAlgebra.coeff_add, map_add, add_mul, hx, hx']
  | single z r =>
    have hsingle := MonoidAlgebra.coeff_single (R := Complex) z r
    have hr : Finsupp.single z r = r • Finsupp.single z (1 : Complex) := by simp
    have hr' : MonoidAlgebra.single z r = r • MonoidAlgebra.single z (1 : Complex) := by simp
    rw [hsingle, hr, map_smul, hr', smul_mul_assoc, MonoidAlgebra.coeff_smul]
    congr 1
    rw [eval_vertical_apply, openCup_single, map_sum]
    dsimp only [y]
    rw [Finset.mul_sum, MonoidAlgebra.coeff_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [orbitTail_single, MonoidAlgebra.single_mul_single, one_mul]
    rfl

end
end FiniteOrbitSumDiagramSupport

theorem FiniteOrbitSumDiagram : (
∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
  (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
  (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom a)
  let ψ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom b)
  let action := fun (h : H) (g : G) =>
    MackeyDiagrams.ConjEmbedding.toHom a h * g * (MackeyDiagrams.ConjEmbedding.toHom b h)⁻¹
  let orbit := fun g : G => Set.range (fun h : H => action h g)
  let OrbitIndex := {s : Finset G // ∃ g : G, (s : Set G) = orbit g}
  let orbitSum := fun i : OrbitIndex =>
    Finset.sum (Subtype.val i) (fun g => MonoidAlgebra.single g (1 : Complex))
  let HomSpace : Submodule Complex (LinearMap (RingHom.id Complex) B B) :=
    { carrier := { f |
        (∀ s x : B, f (s * x) = s * f x) ∧
        (∀ (r : A) (x : B), f (x * φ r) = f x * ψ r) }
      zero_mem' := by
        simp
      add_mem' := by
        rintro f g ⟨hfL, hfR⟩ ⟨hgL, hgR⟩
        exact ⟨fun s x => by simp [hfL, hgL, mul_add],
          fun r x => by simp [hfR, hgR, add_mul]⟩
      smul_mem' := by
        rintro c f ⟨hfL, hfR⟩
        exact ⟨fun s x => by simp [hfL],
          fun r x => by simp [hfR]⟩ }
  ∃ basis : Module.Basis OrbitIndex Complex HomSpace,
    (∀ (i : OrbitIndex) (x : B), Subtype.val (basis i) x = x * orbitSum i) ∧
    (∀ g : G, (∃ d : MackeyDiagrams.Dot a b, MackeyDiagrams.Dot.element d = g) ↔ orbit g = {g}) ∧
    (∀ [Finite H],
      let T : Subgroup U := ⊥
      let j : MackeyDiagrams.ConjEmbedding T H :=
        MackeyDiagrams.ConjEmbedding.ofConjugator (1 : U) (by
          intro t
          have ht : (t : U) = 1 := Subgroup.mem_bot.mp t.property
          simp [ht])
      let finiteIndex : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom j)) :=
        Subgroup.finiteIndex_of_finite
      let p := MackeyDiagrams.Word.up a
      let q := MackeyDiagrams.Word.up b
      let up := MackeyDiagrams.Word.up j
      let down := MackeyDiagrams.Word.down j
      let groupElements : Finset H := @Finset.univ H (Fintype.ofFinite H)
      ∀ g : G,
        let finiteOrbit : Set.Finite (orbit g) := Set.finite_range (fun h : H => action h g)
        let i : OrbitIndex :=
          ⟨Set.Finite.toFinset finiteOrbit, ⟨g, Set.Finite.coe_toFinset finiteOrbit⟩⟩
        let order : Complex := (Nat.card {h : H // action h g = g} : Complex)
        let dot : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a j)
            (MackeyDiagrams.ConjEmbedding.comp b j) :=
          { element := g
            intertwines := by
              intro t
              have ht : t = 1 := Subtype.ext (Subgroup.mem_bot.mp t.property)
              rw [ht, map_one, map_one, one_mul, mul_one] }
        let cup := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.id p) (MackeyDiagrams.Diagram.reverseCup (R := Complex) j finiteIndex)
        let merge := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.mergeUp (R := Complex) a j) (MackeyDiagrams.Diagram.id down)
        let dotStep := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.upDot (R := Complex) dot) (MackeyDiagrams.Diagram.id down)
        let split := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.splitUp (R := Complex) b j) (MackeyDiagrams.Diagram.id down)
        let cap := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.id q) (MackeyDiagrams.Diagram.multiplicationCap (R := Complex) j)
        let d : MackeyDiagrams.Diagram Complex p q :=
          MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit p)
            (MackeyDiagrams.Diagram.vertical cup
              (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.unassociate p up down)
                (MackeyDiagrams.Diagram.vertical merge
                  (MackeyDiagrams.Diagram.vertical dotStep
                    (MackeyDiagrams.Diagram.vertical split
                      (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.associate q up down)
                        (MackeyDiagrams.Diagram.vertical cap (MackeyDiagrams.Diagram.rightUnit q))))))))
        let sumOverH : B := Finset.sum groupElements (fun t =>
          MonoidAlgebra.single
            (MackeyDiagrams.ConjEmbedding.toHom a t⁻¹ * g * MackeyDiagrams.ConjEmbedding.toHom b t)
            (1 : Complex))
        IsUnit order ∧
        (∀ x : B,
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval d)
              (MonoidAlgebra.coeff x) = MonoidAlgebra.coeff (x * sumOverH) ∧
          x * sumOverH = x * (order • orbitSum i)) ∧
        (∀ x : B,
          MackeyDiagrams.Biset.Hom.toLinearMap
              (MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.scale order⁻¹ d))
              (MonoidAlgebra.coeff x) = MonoidAlgebra.coeff (Subtype.val (basis i) x)))
) :=
(by
  open MackeyDiagrams FiniteOrbitSumDiagramSupport in
  intro U _ H G α β hα hβ A B a b φ ψ action orbit OrbitIndex orbitSum HomSpace
  classical
  -- Xiao, § 3.4, proof of Proposition 3.3. The endpoint is on archived p. 10
  -- (SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and current published p. 12 (SHA-256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- The registered orbit-basis theorem supplies the first paragraph, including
  -- the singleton criterion. Its existential realization does not specify the
  -- syntax, so the second paragraph computes this particular composite.
  obtain ⟨basis, basisApply, singletonDot, _⟩ := InductionBimoduleOrbitSumBasis H G α β hα hβ
  refine ⟨basis, basisApply, singletonDot, ?_⟩
  intro hfin T j finite p q up down groupElements g finiteOrbit i order dot cup merge dotStep split cap d sumOverH
  let _ : Fintype H := Fintype.ofFinite H
  have sumAsTwists : sumOverH =
      ∑ t : H, MonoidAlgebra.single (twist a b t⁻¹ g) (1 : Complex) := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [twist, map_inv, inv_inv]
  have heval (x : B) : d.eval.toLinearMap x.coeff = (x * sumOverH).coeff := by
    -- Both bracketings evaluate by the same sequence of maps. The inserted
    -- unitors and associators type the unchanged wiring.
    rw [sumAsTwists]
    calc
      _ = ((openCup a finite).vertical (orbitTail a b g)).eval.toLinearMap x.coeff := by
        change (Diagram.vertical (Diagram.insertRightUnit p)
          (Diagram.vertical cup (orbitTail a b g))).eval.toLinearMap x.coeff = _
        rfl
      _ = _ := composite_eval a b finite g x
  have hsum : sumOverH = order • orbitSum i :=
    sumAsTwists.trans (sum_inv_twist a b g i.val (Set.Finite.coe_toFinset finiteOrbit))
  have horder : order ≠ 0 := by
    let _ : Nonempty {h : H // action h g = g} := ⟨⟨1, by simp [action]⟩⟩
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨isUnit_iff_ne_zero.mpr horder, fun x => ⟨heval x, congrArg (x * ·) hsum⟩, ?_⟩
  intro x
  change order⁻¹ • d.eval.toLinearMap x.coeff = ((basis i).val x).coeff
  rw [heval, hsum, mul_smul_comm, basisApply]
  change order⁻¹ • (order • (x * orbitSum i).coeff) = (x * orbitSum i).coeff
  rw [smul_smul, inv_mul_cancel₀ horder, one_smul]
)

#print axioms FiniteOrbitSumDiagram
