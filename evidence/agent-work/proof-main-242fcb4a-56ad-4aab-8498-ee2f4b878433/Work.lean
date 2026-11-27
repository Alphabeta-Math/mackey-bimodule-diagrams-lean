import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.GroupElementDotCriterion

set_option maxHeartbeats 2000000
namespace OrbitSumBasisProof

open MackeyDiagrams

variable {U : Type*} [Group U] {H G : Subgroup U}

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

private theorem mem_twistOrbit (a b : ConjEmbedding H G) (g : G) :
    g ∈ Set.range (fun h : H => twist a b h g) :=
  ⟨1, (twistAction a b).one_smul g⟩

private theorem twistOrbit_eq (a b : ConjEmbedding H G) {g z : G}
    (hz : z ∈ Set.range (fun h : H => twist a b h g)) :
    Set.range (fun h : H => twist a b h z) = Set.range (fun h : H => twist a b h g) := by
  let _ := twistAction a b
  exact MulAction.orbit_eq_iff.mpr hz

private theorem coeff_intertwines (a b : ConjEmbedding H G) (y : MonoidAlgebra Complex G)
    (onA : ∀ (h : H) (c : Complex),
      MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom (MonoidAlgebra.single h c) =
        MonoidAlgebra.single (a.toHom h) c)
    (onB : ∀ (h : H) (c : Complex),
      MonoidAlgebra.mapDomainAlgHom Complex Complex b.toHom (MonoidAlgebra.single h c) =
        MonoidAlgebra.single (b.toHom h) c) :
    (∀ r : MonoidAlgebra Complex H,
      MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom r * y =
        y * MonoidAlgebra.mapDomainAlgHom Complex Complex b.toHom r) ↔
    (∀ (h : H) (g : G), (y.coeff) (twist a b h g) = (y.coeff) g) := by
  constructor
  · intro hy h g
    have he := hy (MonoidAlgebra.single h 1)
    rw [onA, onB] at he
    have hc := congrArg (fun x : MonoidAlgebra Complex G => x.coeff (a.toHom h * g)) he
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
      one_mul, mul_one, inv_mul_cancel_left] at hc
    exact hc.symm
  · intro hy r
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [map_add, add_mul, mul_add, hr, hs]
    | single h c =>
      apply MonoidAlgebra.ext
      apply Finsupp.ext
      intro z
      rw [onA, onB, MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply]
      have hev := hy h ((a.toHom h)⁻¹ * z)
      simp only [twist, mul_inv_cancel_left] at hev
      rw [hev, mul_comm]

private theorem coeff_orbitSum (s : Finset G) (z : G) [Decidable (z ∈ s)] :
    (∑ g ∈ s, MonoidAlgebra.single g (1 : Complex)).coeff z =
      if z ∈ s then 1 else 0 := by
  classical
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finset.sum_ite_eq']
  split <;> simp_all

end OrbitSumBasisProof

namespace OrbitSumBasisProof

open MackeyDiagrams Diagram
open scoped Classical Pointwise

noncomputable section

variable {U : Type*} [Group U] {H G : Subgroup U}

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

private def capPair (H : Subgroup U) (h : H) :
    (reverseCupWord (trivialEmbedding H)).basis.carrier :=
  (Word.up (trivialEmbedding H)).basis.pair (Word.down (trivialEmbedding H)).basis h h⁻¹

private theorem cup_single [Fintype H] (finite : (trivialEmbedding H).toHom.range.FiniteIndex) :
    (reverseCup (R := Complex) (trivialEmbedding H) finite).eval.toLinearMap
      (Finsupp.single (1 : H) 1) = ∑ h : H, Finsupp.single (capPair H h) 1 := by
  classical
  let t := trivialEmbedding H
  let fiber := Generator.multiplicationCap_finiteFiber t finite
  change (Generator.reverseCup Complex t finite).toLinearMap (Finsupp.single (1 : H) 1) = _
  unfold Generator.reverseCup
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]
  symm
  refine Finset.sum_bij (fun h _ => capPair H h) ?_ ?_ ?_ ?_
  · intro h _
    apply (fiber 1).mem_toFinset.mpr
    change h * h⁻¹ = 1
    exact mul_inv_cancel h
  · intro h _ k _ he
    have he' : (Biset.induction t).pair (Biset.restriction t) h h⁻¹ =
        (Biset.induction t).pair (Biset.restriction t) k k⁻¹ := he
    obtain ⟨z, hz, _⟩ := Quotient.exact he'
    change 1 * h * (t.toHom z)⁻¹ = k at hz
    simpa [trivial_arg z] using hz
  · intro w hw
    obtain ⟨⟨h,k⟩, hw'⟩ := Quotient.exists_rep w
    have hw'' : (Biset.induction t).pair (Biset.restriction t) h k = w := hw'
    have hmul := (fiber 1).mem_toFinset.mp hw
    change Generator.multiplicationCapBasis t w = 1 at hmul
    rw [← hw''] at hmul
    change h * k = 1 at hmul
    have hk : k = h⁻¹ := inv_eq_of_mul_eq_one_right hmul |>.symm
    refine ⟨h, Finset.mem_univ h, ?_⟩
    change (Biset.induction t).pair (Biset.restriction t) h h⁻¹ = w
    rw [← hk, hw'']
  · intros
    rfl

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
      Finsupp.single (x * twist a b h g) 1 := by
  let t := trivialEmbedding H
  let p := Word.up a
  let q := Word.up b
  let u := Word.up t
  let v := Word.down t
  let d := middleDot a b g
  let input := Finsupp.single (p.basis.pair (u.basis.tensor v.basis) x (u.basis.pair v.basis h h⁻¹))
    (1 : Complex)
  change (rightUnit q).eval.toLinearMap
    ((horizontal (id q) (multiplicationCap t)).eval.toLinearMap
      ((associate q u v).eval.toLinearMap
        ((horizontal (splitUp b t) (id v)).eval.toLinearMap
          ((horizontal (upDot d) (id v)).eval.toLinearMap
            ((horizontal (mergeUp a t) (id v)).eval.toLinearMap
              ((unassociate p u v).eval.toLinearMap input)))))) = _
  dsimp only [input]
  rw [eval_unassociate_single p u v x h h⁻¹ 1]
  rw [eval_horizontal_single (mergeUp a t) (id v), one_smul, eval_id_apply,
    eval_mergeUp_single a t x h 1, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (upDot d) (id v), one_smul, eval_id_apply,
    eval_upDot_single d (x * a.toHom h) 1, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (splitUp b t) (id v), one_smul, eval_id_apply,
    eval_splitUp_single b t, Biset.pairLinear_single, one_mul]
  rw [eval_associate_single q u v, eval_horizontal_single (id q) (multiplicationCap t),
    one_smul, eval_id_apply, eval_multiplicationCap_single t 1 h⁻¹ 1,
    Biset.pairLinear_single, one_mul, eval_rightUnit_single q]
  change Finsupp.single (1 * (x * a.toHom h * g) * (b.toHom (h⁻¹⁻¹))⁻¹) (1 * 1 : Complex) = _
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

-- Proposition 3.3's second paragraph inserts the right cup, merges, dots,
-- splits and caps. The first coordinate h of the cup pair is the inverse of
-- the paper's t. The inserted unitors and associators type the same wiring.
private theorem realize (a b : ConjEmbedding H G) (hfin : Finite H) (g : G)
    (s : Finset G) (hs : (s : Set G) = Set.range (fun h : H => twist a b h g)) :
    ∃ d : Diagram Complex (Word.up a) (Word.up b), ∀ x : MonoidAlgebra Complex G,
      d.eval.toLinearMap x.coeff =
        (x * ∑ z ∈ s, MonoidAlgebra.single z (1 : Complex)).coeff := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let S := twistStabilizer a b g
  let finite : (trivialEmbedding H).toHom.range.FiniteIndex := inferInstance
  let d := (openCup a finite).vertical (orbitTail a b g)
  let c : Complex := Nat.card S
  let y := ∑ z ∈ s, MonoidAlgebra.single z (1 : Complex)
  have c_ne : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : (∑ h : H, MonoidAlgebra.single (twist a b h g) (1 : Complex)) = c • y :=
    sum_twist a b g s hs
  have heval (x : G) : d.eval.toLinearMap (Finsupp.single x 1) =
      (MonoidAlgebra.single x 1 * (c • y)).coeff := by
    change (orbitTail a b g).eval.toLinearMap
      ((openCup a finite).eval.toLinearMap (Finsupp.single x 1)) = _
    rw [openCup_single, map_sum, ← hsum, Finset.mul_sum,
      MonoidAlgebra.coeff_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [orbitTail_single, MonoidAlgebra.single_mul_single, one_mul]
    rfl
  let normalized := Diagram.scale c⁻¹ d
  let E := MonoidAlgebra.coeffLinearEquiv Complex (M := G) (S := Complex)
  let rightMul : MonoidAlgebra Complex G →ₗ[Complex] MonoidAlgebra Complex G :=
    { toFun := fun x => x * y
      map_add' := fun x x' => add_mul x x' _
      map_smul' := fun k x => smul_mul_assoc k x _ }
  have normalEval : normalized.eval.toLinearMap =
      E.toLinearMap.comp (rightMul.comp E.symm.toLinearMap) := by
    apply Finsupp.lhom_ext
    intro x r
    have hr : Finsupp.single x r = r • Finsupp.single x (1 : Complex) := by simp
    rw [hr, map_smul, map_smul]
    congr 1
    change c⁻¹ • d.eval.toLinearMap (Finsupp.single x 1) = (MonoidAlgebra.single x 1 * y).coeff
    rw [heval, mul_smul_comm]
    change c⁻¹ • (c • (MonoidAlgebra.single x 1 * y).coeff) = _
    rw [smul_smul, inv_mul_cancel₀ c_ne, one_smul]
  refine ⟨normalized, fun x => ?_⟩
  rw [normalEval]
  change E (rightMul (E.symm (E x))) = _
  rw [E.symm_apply_apply]
  rfl

end

end OrbitSumBasisProof

theorem InductionBimoduleOrbitSumBasis : (∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
  (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
  (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom a)
  let ψ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom b)
  let orbit := fun g : G =>
    Set.range (fun h : H =>
      MackeyDiagrams.ConjEmbedding.toHom a h * g * (MackeyDiagrams.ConjEmbedding.toHom b h)⁻¹)
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
    (Finite H → ∀ i : OrbitIndex,
      ∃ d : MackeyDiagrams.Diagram Complex (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b),
        ∀ x : B,
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval d) (MonoidAlgebra.coeff x) =
            MonoidAlgebra.coeff (Subtype.val (basis i) x))) :=
(by
  classical
  intro U inst H G α β hα hβ A B a b φ ψ orbit OrbitIndex orbitSum HomSpace
  -- Xiao, Proposition 3.3, archived PDF p. 10 and revised published PDF p. 12.
  -- The project inventory records no Alphabeta Math numbered proof for this endpoint.
  -- The first paragraph evaluates a regular left-module map at 1. The finite orbit
  -- sets are indices. Representatives only read coefficients.
  have onA := ((InductionRestrictionBimoduleStrands.{_, 0, 0}).1 H G α hα).1
  have onB := ((InductionRestrictionBimoduleStrands.{_, 0, 0}).1 H G β hβ).1
  -- Whole intertwiners are compared in the group algebra by their coefficients.
  have intertwiner (y : B) := OrbitSumBasisProof.coeff_intertwines a b y onA onB
  have selfMem (g : G) : g ∈ orbit g := OrbitSumBasisProof.mem_twistOrbit a b g
  have orbitEq {g z : G} (hz : z ∈ orbit g) : orbit z = orbit g :=
    OrbitSumBasisProof.twistOrbit_eq a b hz
  let repr : OrbitIndex → G := fun i => i.property.choose
  have reprOrbit (i : OrbitIndex) : (i.val : Set G) = orbit (repr i) := i.property.choose_spec
  have memRepr (i : OrbitIndex) : repr i ∈ i.val :=
    show repr i ∈ (i.val : Set G) from (reprOrbit i).symm ▸ selfMem (repr i)
  have eqIndex {i j : OrbitIndex} {g : G} (hi : g ∈ i.val) (hj : g ∈ j.val) : i = j := by
    apply Subtype.ext
    apply Finset.coe_injective
    have hi' : g ∈ orbit (repr i) := reprOrbit i ▸ (show g ∈ (i.val : Set G) from hi)
    have hj' : g ∈ orbit (repr j) := reprOrbit j ▸ (show g ∈ (j.val : Set G) from hj)
    exact (reprOrbit i).trans ((orbitEq hi').symm.trans
      ((orbitEq hj').trans (reprOrbit j).symm))
  have reprInj : Function.Injective repr := by
    intro i j h
    exact eqIndex (memRepr i) (h.symm ▸ memRepr j)
  have orbitCoeff (i : OrbitIndex) (g : G) :
      (orbitSum i).coeff g = if g ∈ i.val then 1 else 0 :=
    OrbitSumBasisProof.coeff_orbitSum _ _
  have multiplier (f : HomSpace) (x : B) : f.val x = x * f.val 1 := by
    have hf := f.property.1 x 1
    rwa [mul_one] at hf
  have invariant (f : HomSpace) (h : H) (g : G) :
      (f.val 1).coeff (OrbitSumBasisProof.twist a b h g) = (f.val 1).coeff g := by
    apply (intertwiner (f.val 1)).mp
    intro r
    have hr := f.property.2 r 1
    rw [one_mul, multiplier] at hr
    exact hr
  have mulMem (i : OrbitIndex) :
      ∀ (h : H) (g : G), (orbitSum i).coeff (OrbitSumBasisProof.twist a b h g) =
        (orbitSum i).coeff g := by
    intro h g
    have heq := orbitEq (g := g) (z := OrbitSumBasisProof.twist a b h g) ⟨h, rfl⟩
    have hm (z : G) : z ∈ i.val ↔ orbit z = orbit (repr i) := by
      change z ∈ (i.val : Set G) ↔ _
      rw [reprOrbit]
      exact ⟨orbitEq, fun he => he ▸ selfMem z⟩
    simp only [orbitCoeff, hm, heq]
  let v (i : OrbitIndex) : HomSpace :=
    ⟨{ toFun := fun x => x * orbitSum i
       map_add' := fun x y => add_mul x y _
       map_smul' := fun c x => smul_mul_assoc c x _ },
      fun s x => mul_assoc s x _, fun r x => by
        change (x * φ r) * orbitSum i = (x * orbitSum i) * ψ r
        rw [mul_assoc, (intertwiner (orbitSum i)).mpr (mulMem i) r,
          ← mul_assoc]⟩
  let evalCoeff (g : G) : HomSpace →ₗ[Complex] Complex :=
    { toFun := fun f => (f.val 1).coeff g
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  have evV (g : G) (i : OrbitIndex) :
      evalCoeff g (v i) = if g ∈ i.val then 1 else 0 := by
    change ((1 : B) * orbitSum i).coeff g = _
    rw [one_mul, orbitCoeff]
  let assemble : (OrbitIndex →₀ Complex) →ₗ[Complex] HomSpace := MackeyDiagrams.freeLift Complex v
  have coefficient (g : G) (w : OrbitIndex →₀ Complex) :
      evalCoeff g (assemble w) = w.sum (fun i c => c * if g ∈ i.val then 1 else 0) := by
    have he : (evalCoeff g).comp assemble =
        MackeyDiagrams.freeLift Complex (fun i => if g ∈ i.val then 1 else 0) := by
      apply Finsupp.lhom_ext
      intro i c
      change evalCoeff g (MackeyDiagrams.freeLift Complex v (Finsupp.single i c)) = _
      simp only [MackeyDiagrams.freeLift_single, map_smul, evV]
    rw [← LinearMap.comp_apply, he]
    rfl
  have coeffInOrbit (i : OrbitIndex) (g : G) (hg : g ∈ i.val) (w : OrbitIndex →₀ Complex) :
      evalCoeff g (assemble w) = w i := by
    rw [coefficient]
    have he (j : OrbitIndex) (c : Complex) :
        c * (if g ∈ j.val then 1 else 0) = if j = i then c else 0 := by
      by_cases hj : g ∈ j.val
      · have heq := eqIndex hj hg
        subst j
        simp [hg]
      · have hne : j ≠ i := fun h => hj (h.symm ▸ hg)
        simp [hj, hne]
    simp only [he, Finsupp.sum_ite_eq']
    split
    · rfl
    · exact (Finsupp.notMem_support_iff.mp ‹i ∉ w.support›).symm
  have assembleInj : Function.Injective assemble := by
    intro w w' hw
    ext i
    rw [← coeffInOrbit i (repr i) (memRepr i) w, ← coeffInOrbit i (repr i) (memRepr i) w', hw]
  have assembleSurj : Function.Surjective assemble := by
    intro f
    have hfin : (Function.support (fun i : OrbitIndex => (f.val 1).coeff (repr i))).Finite :=
      by
        apply (((f.val 1).coeff.support.finite_toSet).preimage reprInj.injOn).subset
        intro i hi
        exact Finsupp.mem_support_iff.mpr hi
    let w : OrbitIndex →₀ Complex := Finsupp.ofSupportFinite _ hfin
    have coeffW (i : OrbitIndex) : w i = (f.val 1).coeff (repr i) := by
      rw [show (w : OrbitIndex → Complex) = _ from Finsupp.ofSupportFinite_coe]
    have horbit (g : G) (hg : (f.val 1).coeff g ≠ 0) :
        ∃ i : OrbitIndex, g ∈ i.val := by
      have hsub : orbit g ⊆ (f.val 1).coeff.support := by
        rintro _ ⟨h, rfl⟩
        exact Finsupp.mem_support_iff.mpr ((invariant f h g).symm ▸ hg)
      have hfinite : (orbit g).Finite := (f.val 1).coeff.support.finite_toSet.subset hsub
      exact ⟨⟨hfinite.toFinset, g, hfinite.coe_toFinset⟩, hfinite.mem_toFinset.mpr (selfMem g)⟩
    refine ⟨w, Subtype.ext (LinearMap.ext fun x => ?_)⟩
    rw [multiplier, multiplier f]
    congr 1
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    change evalCoeff g (assemble w) = (f.val 1).coeff g
    by_cases hg : ∃ i : OrbitIndex, g ∈ i.val
    · obtain ⟨i, hi⟩ := hg
      have hmem : g ∈ orbit (repr i) := reprOrbit i ▸ (show g ∈ (i.val : Set G) from hi)
      obtain ⟨h, rfl⟩ := hmem
      rw [coeffInOrbit _ _ hi, coeffW]
      exact (invariant f h (repr i)).symm
    · have hz : (f.val 1).coeff g = 0 := by
        by_contra hn
        exact hg (horbit g hn)
      rw [coefficient, hz]
      apply Finset.sum_eq_zero
      intro i _
      simp [show g ∉ i.val from fun hi => hg ⟨i, hi⟩]
  let basis := (Finsupp.basisSingleOne (R := Complex) (ι := OrbitIndex)).map
    (LinearEquiv.ofBijective assemble ⟨assembleInj, assembleSurj⟩)
  have basisApply (i : OrbitIndex) (x : B) : (basis i).val x = x * orbitSum i := by
    have he : basis i = v i := by
      change assemble ((Finsupp.basisSingleOne (R := Complex) (ι := OrbitIndex)) i) = v i
      rw [Finsupp.coe_basisSingleOne]
      change MackeyDiagrams.freeLift Complex v (Finsupp.single i 1) = v i
      rw [MackeyDiagrams.freeLift_single, one_smul]
    rw [he]
    rfl
  refine ⟨basis, basisApply, ?_, ?_⟩
  · intro g
    -- The registered group-element dot criterion identifies the fixed points.
    have hd := ((GroupElementDotCriterion H G α β hα hβ).2.1 g).2.2.2
    rw [← hd]
    constructor
    · intro h
      ext z
      constructor
      · rintro ⟨k, rfl⟩
        apply Set.mem_singleton_iff.mpr
        change OrbitSumBasisProof.twist a b k g = g
        unfold OrbitSumBasisProof.twist
        rw [h k, mul_inv_cancel_right]
      · intro hz
        exact (Set.mem_singleton_iff.mp hz).symm ▸ selfMem g
    · intro he h
      have hz : OrbitSumBasisProof.twist a b h g ∈ ({g} : Set G) := he ▸ ⟨h, rfl⟩
      have hz' := Set.mem_singleton_iff.mp hz
      unfold OrbitSumBasisProof.twist at hz'
      exact (mul_inv_eq_iff_eq_mul.mp hz')
  · intro hfin i
    obtain ⟨d, hd⟩ := OrbitSumBasisProof.realize a b hfin (repr i) i.val (reprOrbit i)
    exact ⟨d, fun x => (hd x).trans (congrArg MonoidAlgebra.coeff (basisApply i x)).symm⟩)

#print axioms InductionBimoduleOrbitSumBasis
