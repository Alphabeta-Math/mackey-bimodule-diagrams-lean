import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionAdjunction
import Proofs.SurvivingCosetRepresentative
import Proofs.MixedCrossingFiberMaps

set_option maxHeartbeats 2000000

namespace MackeyCrossingProof
open MackeyDiagrams

set_option maxHeartbeats 1000000

noncomputable section

universe u
variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

local notation "κγ" => Word.down a
local notation "γη" => Word.up b
local notation "κλ" => Word.up l
local notation "λη" => Word.down r
local notation "γλ" => Word.up (a.comp l)
local notation "ℳ" => Word.tensor κγ γη
local notation "ℳⱼ" => Word.tensor κλ λη
local notation "ψ" => Generator.mixedMultiplicationBasis a b l r d

theorem singleton_scope {p t : Word K H} (f : ScopedDiagram Complex p t) :
    (ScopedDiagram.linearCombination [(1, f)]).eval = f.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp

theorem compact_inclusion :
    (LabelledDrawing.mixedMultiplication a b l r [(1, d)]).interpret.eval =
      (Diagram.mixedMultiplication (R := Complex) a b l r d).eval :=
  singleton_scope (.ordinary (.mixedMultiplication a b l r d))

theorem compact_projection (hf : ∀ z, Set.Finite {w | ψ w = z}) :
    (LabelledDrawing.compactProjection a b l r [(1, ⟨d, hf⟩)]).interpret.eval =
      (Diagram.mixedProjection (R := Complex) a b l r d hf).eval :=
  singleton_scope (.ordinary (.mixedProjection a b l r d hf))

theorem dot_single {K G : Subgroup U} {a b : ConjEmbedding K G} (d : Dot a b) :
    (DotLabel.upDrawing (R := Complex) (Finsupp.single d 1)).interpret.eval =
      (Diagram.upDot (R := Complex) d).eval := by
  classical
  rw [DotLabel.eval_upDrawing]
  apply Diagram.eval_ext_on_generators
  intro x
  rw [Diagram.eval_linearUpDot_single, Diagram.eval_upDot_single]
  simp

theorem cup_junction_single (k : K) :
    ((BentVertex.ordinaryCup a l).expand (R := Complex)).eval.toLinearMap
      (Finsupp.single k 1) =
      Finsupp.single ((κγ).basis.pair (γλ).basis 1 (a.toHom k)) 1 := by
  let c : Diagram Complex _ _ := .ordinaryCup a
  let gk := Word.up a
  change (Diagram.horizontal (Diagram.id κγ) (Diagram.mergeUp a l)).eval.toLinearMap
    ((Diagram.associate κγ gk κλ).eval.toLinearMap
      ((Diagram.horizontal c (Diagram.id κλ)).eval.toLinearMap
        ((Diagram.insertLeftUnit κλ).eval.toLinearMap (Finsupp.single k 1)))) = _
  rw [Diagram.eval_insertLeftUnit_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, Diagram.eval_ordinaryCup_single, map_one, Biset.pairLinear_single,
    one_mul, Diagram.eval_associate_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, Diagram.eval_mergeUp_single, one_mul, Biset.pairLinear_single, one_mul]

theorem cap_junction_single (x : G) (h : H) :
    ((BentVertex.multiplicationCap b r).expand (R := Complex)).eval.toLinearMap
      (Finsupp.single ((Word.up (b.comp r)).basis.pair (λη).basis x h) 1) =
      Finsupp.single (x * b.toHom h) 1 := by
  let hr := Word.up r
  change (Diagram.rightUnit γη (R := Complex)).eval.toLinearMap
    ((Diagram.horizontal (Diagram.id γη) (Diagram.multiplicationCap r)).eval.toLinearMap
      ((Diagram.associate γη hr λη).eval.toLinearMap
        ((Diagram.horizontal (Diagram.splitUp b r) (Diagram.id λη)).eval.toLinearMap
          (Finsupp.single ((Word.up (b.comp r)).basis.pair (λη).basis x h) 1)))) = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply, Diagram.eval_splitUp_single,
    Biset.pairLinear_single, one_mul, Diagram.eval_associate_single, Diagram.eval_horizontal_single,
    one_smul, Diagram.eval_id_apply, Diagram.eval_multiplicationCap_single, one_mul,
    Biset.pairLinear_single, one_mul, Diagram.eval_rightUnit_single]
  change Finsupp.single (1 * x * (b.toHom h⁻¹)⁻¹) 1 = _
  simp only [one_mul, map_inv, inv_inv]

def inclusion_expansion : LabelledDrawing Complex ℳⱼ ℳ :=
  .vertical
    (.horizontal (.trivalent (.upToDownUp a l)) (.ordinary (.id λη)))
    (.vertical (.ordinary (.associate κγ γλ λη))
      (.vertical
        (.horizontal (.ordinary (.id κγ))
          (.horizontal (DotLabel.upDrawing (R := Complex) (Finsupp.single d 1))
            (.ordinary (.id λη))))
        (.horizontal (.ordinary (.id κγ)) (.trivalent (.upDownToUp b r)))))

/-
Diagram.eval_expandedMackeyInclusion has the same source, target and compact
map. Its left side is a different assembly of ordinary cup/cap primitives
in MackeyDiagrams.MackeyInclusionExpansion. The reviewed drawing uses the
shared trivalent vertices and a singleton linear label. The basis checks
cup_junction_single, dot_single and cap_junction_single evaluate precisely
those vertices, giving a direct comparison with the compact crossing.
-/
theorem eval_inclusion_expansion :
    (inclusion_expansion a b l r d).interpret.eval =
      (Diagram.mixedMultiplication (R := Complex) a b l r d).eval := by
  classical
  let cup : Diagram Complex _ _ := (BentVertex.ordinaryCup a l).expand
  let cap : Diagram Complex _ _ := (BentVertex.multiplicationCap b r).expand
  let body := Diagram.horizontal (Diagram.id κγ)
    (Diagram.horizontal (Diagram.upDot (R := Complex) d) (Diagram.id λη))
  have he : (inclusion_expansion a b l r d).interpret.eval =
      (Diagram.vertical (.horizontal cup (.id λη))
        (.vertical (.associate κγ γλ λη)
          (.vertical body (.horizontal (.id κγ) cap)))).eval := by
    simp only [inclusion_expansion, LabelledDrawing.interpret, ScopedDiagram.eval,
      TrivalentVertex.expand, Diagram.eval, body, cup, cap, dot_single]
  rw [he]
  apply Diagram.eval_ext_on_generators
  intro w
  refine Quotient.inductionOn w fun ⟨k, h⟩ => ?_
  change (Diagram.horizontal (Diagram.id κγ) cap).eval.toLinearMap
    (body.eval.toLinearMap
      ((Diagram.associate κγ γλ λη).eval.toLinearMap
        ((Diagram.horizontal cup (Diagram.id λη)).eval.toLinearMap
          (Finsupp.single ((κλ).basis.pair (λη).basis k h) 1)))) = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply]
  rw [show cup.eval.toLinearMap (Finsupp.single k 1) = _ from cup_junction_single a l k,
    Biset.pairLinear_single, one_mul, Diagram.eval_associate_single]
  dsimp only [body]
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
    Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply, Diagram.eval_upDot_single,
    Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul,
    Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply]
  rw [show cap.eval.toLinearMap (Finsupp.single _ 1) = _ from
      cap_junction_single b r (a.toHom k * d.element) h,
    Biset.pairLinear_single, one_mul]
  change _ = (Generator.mixedMultiplication a b l r d Complex).toLinearMap
    (Finsupp.single ((κλ).basis.pair (λη).basis k h) 1)
  rw [Generator.mixedMultiplication, Biset.Hom.ofFunction_single]
  apply congrArg (fun z => Finsupp.single z 1)
  have hw := Generator.mixedPair_mixedProduct a b
    ((κγ).basis.pair (γη).basis 1 (a.toHom k * d.element * b.toHom h))
  change Generator.mixedPair a b (1 * (a.toHom k * d.element * b.toHom h)) = _ at hw
  rw [one_mul] at hw
  exact hw.symm

theorem insert_right_single {A B : Subgroup U} (p : Word A B) (x : p.basis.carrier) :
    (Diagram.insertRightUnit (R := Complex) p).eval.toLinearMap (Finsupp.single x 1) =
      Finsupp.single (p.basis.pair (Biset.regular B) x 1) 1 := by
  change (Biset.insertRightUnit p.basis Complex).toLinearMap (Finsupp.single x 1) = _
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]

def finite_expansion (hi : Subgroup.FiniteIndex r.toHom.range) :
    LabelledDrawing Complex ℳ ℳⱼ :=
  .vertical
    (.horizontal (.ordinary (.id κγ)) (.trivalent (.upToUpDown b r hi)))
    (.vertical
      (.horizontal (.ordinary (.id κγ))
        (.horizontal (DotLabel.upDrawing (R := Complex) (Finsupp.single d.inverse 1))
          (.ordinary (.id λη))))
      (.vertical (.ordinary (.unassociate κγ γλ λη))
        (.horizontal (.trivalent (.downUpToUp a l)) (.ordinary (.id λη)))))

/-
RightCupTrace.eval_eq_reverseCup supplies the standalone cup at finite index.
Compare the explicit trivalent drawing and that scoped evaluation on each term
of the same cup fiber. The other projection clauses need only finite support
through the tail, supplied by injectivity and the trace calculations below.
-/
theorem eval_finite_expansion (hi : Subgroup.FiniteIndex r.toHom.range)
    (hf : ∀ z, Set.Finite {w | ψ w = z}) :
    (finite_expansion a b l r d hi).interpret.eval =
      (Diagram.mixedProjection (R := Complex) a b l r d hf).eval := by
  classical
  let hl := Word.up r
  let rightMid := Word.up (b.comp r)
  let cup := reverseCupWord r
  let reverse : Diagram Complex (.empty H) cup := .reverseCup r hi
  let merge : Diagram Complex ((γη).tensor hl) rightMid := .mergeUp b r
  let expand : Diagram Complex γη (rightMid.tensor λη) :=
    (BentVertex.reverseCup b r hi).expand
  let dot : Diagram Complex rightMid γλ := .upDot d.inverse
  let finish : Diagram Complex ((κγ).tensor (rightMid.tensor λη)) ℳⱼ :=
    .vertical (.horizontal (.id κγ) (.horizontal dot (.id λη)))
      (.vertical (.unassociate κγ γλ λη)
        (.horizontal (.traceCapOnLeft a l) (.id λη)))
  let tail := Diagram.mixedProjectionTail (R := Complex) a b l r d
  let scope := RightCupTrace.ofFiniteAfter tail
    (RightCupTrace.mixedProjectionTail_finiteAfter a b l r d hf)
  have hsyntax : (finite_expansion a b l r d hi).interpret.eval =
      (Diagram.vertical (.horizontal (.id κγ) expand) finish).eval := by
    simp only [finite_expansion, LabelledDrawing.interpret, ScopedDiagram.eval,
      TrivalentVertex.expand, finish, expand, dot, Diagram.eval, dot_single]
  have hscope : scope.eval = (Diagram.mixedProjection (R := Complex) a b l r d hf).eval :=
    ScopedDiagram.eval_expandedMixedProjection a b l r d hf
  rw [hsyntax, ← hscope, RightCupTrace.eval_eq_reverseCup scope hi]
  apply Diagram.eval_ext_on_generators
  intro w
  refine Quotient.inductionOn w fun ⟨x, y⟩ => ?_
  let fiber := Generator.multiplicationCap_finiteFiber r hi (1 : H)
  let openingTail : Diagram Complex ((γη).tensor cup) (rightMid.tensor λη) :=
    .vertical (.unassociate γη hl λη) (.horizontal merge (.id λη))
  have hcup : reverse.eval.toLinearMap (Finsupp.single (1 : H) 1) =
      ∑ z ∈ fiber.toFinset, Finsupp.single z (1 : Complex) := by
    change (Generator.reverseCup Complex r hi).toLinearMap (Finsupp.single (1 : H) 1) = _
    rw [Generator.reverseCup, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]
  have hexpand : expand.eval.toLinearMap (Finsupp.single y 1) =
      ∑ z ∈ fiber.toFinset, openingTail.eval.toLinearMap
        (Finsupp.single ((γη).basis.pair cup.basis y z) 1) := by
    change openingTail.eval.toLinearMap
      ((Diagram.horizontal (.id γη) reverse).eval.toLinearMap
        ((Diagram.insertRightUnit γη).eval.toLinearMap (Finsupp.single y 1))) = _
    rw [insert_right_single, Diagram.eval_horizontal_single, one_smul,
      Diagram.eval_id_apply, hcup, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [Biset.pairLinear_single, one_mul]
  change finish.eval.toLinearMap
    ((Diagram.horizontal (Diagram.id κγ) expand).eval.toLinearMap
      (Finsupp.single ((κγ).basis.pair (γη).basis x y) 1)) =
    tail.eval.toLinearMap
      ((Diagram.horizontal (Diagram.id ℳ) reverse).eval.toLinearMap
        ((Diagram.insertRightUnit ℳ).eval.toLinearMap
          (Finsupp.single ((κγ).basis.pair (γη).basis x y) 1)))
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply, hexpand, map_sum, map_sum,
    insert_right_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, hcup, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  refine Quotient.inductionOn z fun ⟨h₁, h₂⟩ => ?_
  change finish.eval.toLinearMap
    (Biset.pairLinear Complex (κγ).basis (rightMid.tensor λη).basis (Finsupp.single x 1)
      (openingTail.eval.toLinearMap
        (Finsupp.single ((γη).basis.pair cup.basis y (hl.basis.pair (λη).basis h₁ h₂)) 1))) =
    tail.eval.toLinearMap
      (Biset.pairLinear Complex (ℳ).basis cup.basis
        (Finsupp.single ((κγ).basis.pair (γη).basis x y) 1)
        (Finsupp.single (hl.basis.pair (λη).basis h₁ h₂) 1))
  rw [Biset.pairLinear_single, one_mul]
  have hopen : openingTail.eval.toLinearMap
      (Finsupp.single ((γη).basis.pair cup.basis y ((hl.basis).pair (λη).basis h₁ h₂)) 1) =
      Finsupp.single (rightMid.basis.pair (λη).basis (y * b.toHom h₁) h₂) 1 := by
    change (Diagram.horizontal merge (Diagram.id λη)).eval.toLinearMap
      ((Diagram.unassociate γη hl λη).eval.toLinearMap
        (Finsupp.single ((γη).basis.pair cup.basis y (hl.basis.pair (λη).basis h₁ h₂)) 1)) = _
    rw [Diagram.eval_unassociate_single, Diagram.eval_horizontal_single, one_smul,
      Diagram.eval_id_apply, Diagram.eval_mergeUp_single, Biset.pairLinear_single, one_mul]
  rw [hopen, Biset.pairLinear_single, one_mul, Diagram.eval_mixedProjectionTail_single]
  change (Diagram.horizontal (Diagram.traceCapOnLeft a l) (Diagram.id λη)).eval.toLinearMap
    ((Diagram.unassociate κγ γλ λη).eval.toLinearMap
      ((Diagram.horizontal (Diagram.id κγ) (Diagram.horizontal dot (Diagram.id λη))).eval.toLinearMap
        (Finsupp.single ((κγ).basis.pair (rightMid.tensor λη).basis x
          (rightMid.basis.pair (λη).basis (y * b.toHom h₁) h₂)) 1))) = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
    Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
    show dot.eval.toLinearMap (Finsupp.single (y * b.toHom h₁) 1) = _ from
      Diagram.eval_upDot_single d.inverse (y * b.toHom h₁) 1,
    Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul,
    Diagram.eval_unassociate_single]
  rfl

theorem trace_eq_iff (α β : U)
    (ha : ∀ k : K, (a.toHom k : U) = α * (k : U) * α⁻¹)
    (hb : ∀ h : H, (b.toHom h : U) = β * (h : U) * β⁻¹)
    (g : G) (h : H) (k : K) :
    a.toHom k = g * (b.toHom h⁻¹ * d.element⁻¹) ↔
      (k : U) = α⁻¹ * (g : U) * β * (h : U)⁻¹ * β⁻¹ * (d.element : U)⁻¹ * α := by
  constructor
  · intro he
    have e := congrArg Subtype.val he
    change (a.toHom k : U) = (g : U) * ((b.toHom h⁻¹ : U) * (d.element : U)⁻¹) at e
    rw [ha, hb] at e
    change α * (k : U) * α⁻¹ =
      (g : U) * ((β * (h : U)⁻¹ * β⁻¹) * (d.element : U)⁻¹) at e
    calc
      (k : U) = α⁻¹ * (α * (k : U) * α⁻¹) * α := by group
      _ = _ := by rw [e]; group
  · intro he
    apply Subtype.ext
    change (a.toHom k : U) = (g : U) * ((b.toHom h⁻¹ : U) * (d.element : U)⁻¹)
    rw [ha, hb]
    change α * (k : U) * α⁻¹ =
      (g : U) * ((β * (h : U)⁻¹ * β⁻¹) * (d.element : U)⁻¹)
    rw [he]
    group

/-
MixedCrossingFiberMaps, Proposition 5.1, uses a dot reconstructed from
products of conjugating elements and a transversal given as a subset of H.
For the actual supplied eligible dot and the indexed representatives of
(2.4), apply RightCupTrace.projectionTerm_image and projectionTerm_outside
directly. The preceding conjugation calculation gives exactly the test of
Lemma 2.3. LabelledDrawing.eval_expandProjection then compares the two
typed projection drawings with the same label and finite-fiber witness.
-/
theorem trace_support {ι : Type*} (rep : ι → H) (arg : G → ι → U)
    (harg : ∀ g i (k : K),
      a.toHom k = g * (b.toHom (rep i)⁻¹ * d.element⁻¹) ↔ (k : U) = arg g i)
    (z : (ℳ).basis.carrier) :
    Function.support (fun i => RightCupTrace.term
      (Diagram.mixedProjectionTail (R := Complex) a b l r d) z
      (RightCupTrace.unitPair r (rep i))) =
      {i | arg (Generator.mixedProduct a b z) i ∈ K} := by
  obtain ⟨g, rfl⟩ := (Generator.mixedEquiv a b).symm.surjective z
  ext i
  change RightCupTrace.term (Diagram.mixedProjectionTail (R := Complex) a b l r d)
      (Generator.mixedPair a b g) (RightCupTrace.unitPair r (rep i)) ≠ 0 ↔
      arg (Generator.mixedProduct a b (Generator.mixedPair a b g)) i ∈ K
  rw [Generator.mixedProduct_mixedPair]
  constructor
  · intro hn
    by_contra hout
    apply hn
    apply RightCupTrace.projectionTerm_outside
    rintro ⟨k, hk⟩
    exact hout ((harg g i k).mp hk ▸ k.property)
  · intro hin
    rw [RightCupTrace.projectionTerm_image a b l r d g (rep i) ⟨arg g i, hin⟩
      ((harg g i ⟨arg g i, hin⟩).mpr rfl)]
    simp

/-
Enumerate the transfer fiber by the supplied right coset representatives.
The coset lemma gives uniqueness on the index side and the full intersection
gives injectivity on the balanced-pair side.
-/
theorem projection_sum {ι : Type*} (rep : ι → H) (arg : G → ι → U)
    (harg : ∀ g i (k : K),
      a.toHom k = g * (b.toHom (rep i)⁻¹ * d.element⁻¹) ↔ (k : U) = arg g i)
    (hinj : Function.Injective ψ)
    (hf : ∀ z, Set.Finite {w | ψ w = z})
    (g : G) (hs : Set.Finite {i | arg g i ∈ K})
    (huniq : ∀ i j, arg g i ∈ K → arg g j ∈ K → i = j)
    (hcover : Generator.mixedPair a b g ∈ Set.range ψ → ∃ i, arg g i ∈ K) :
    (Diagram.mixedProjection (R := Complex) a b l r d hf).eval.toLinearMap
        (Finsupp.single (Generator.mixedPair a b g) 1) =
      ∑ i ∈ hs.toFinset.attach,
        Finsupp.single ((κλ).basis.pair (λη).basis
          ⟨arg g i.val, hs.mem_toFinset.mp i.property⟩ (rep i.val)) 1 := by
  classical
  let z := Generator.mixedPair a b g
  let liftRep : {i // i ∈ hs.toFinset} → (ℳⱼ).basis.carrier := fun i =>
    (κλ).basis.pair (λη).basis ⟨arg g i.val, hs.mem_toFinset.mp i.property⟩ (rep i.val)
  have hlift (i : {i // i ∈ hs.toFinset}) : ψ (liftRep i) = z := by
    change Generator.mixedPair a b
      (a.toHom ⟨arg g i.val, hs.mem_toFinset.mp i.property⟩ * d.element * b.toHom (rep i.val)) =
      Generator.mixedPair a b g
    apply congrArg (Generator.mixedPair a b)
    rw [(harg g i.val _).mpr rfl, map_inv]
    group
  change (Generator.mixedProjection a b l r d Complex hf).toLinearMap
    (Finsupp.single z 1) = ∑ i ∈ hs.toFinset.attach, Finsupp.single (liftRep i) 1
  rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]
  symm
  refine Finset.sum_bij (fun i _ => liftRep i) ?_ ?_ ?_ ?_
  · exact fun i _ => (hf z).mem_toFinset.mpr (hlift i)
  · intro i _ j _ _
    exact Subtype.ext (huniq _ _ (hs.mem_toFinset.mp i.property) (hs.mem_toFinset.mp j.property))
  · intro w hw
    have hw' : ψ w = z := (hf z).mem_toFinset.mp hw
    obtain ⟨i, hi⟩ := hcover ⟨w, hw'⟩
    let t : {i // i ∈ hs.toFinset} := ⟨i, hs.mem_toFinset.mpr hi⟩
    exact ⟨t, Finset.mem_attach _ _, hinj ((hlift t).trans hw'.symm)⟩
  · intros
    rfl

end
end MackeyCrossingProof

theorem MackeyInclusionAndProjectionCrossings : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U),
  let Kα := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K
  let Hβ := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj β)) H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun k => hK ⟨(k : U), k.property, rfl⟩)
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun h => hH ⟨(h : U), h.property, rfl⟩)
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let L := fun j : J =>
        Kα ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H
      let C := fun j : J =>
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (β⁻¹ * (σ j : U)⁻¹))) (L j)
      ∀ (I : J → Type v) (hRep : ∀ j : J, I j → H)
        (_ : ∀ (j : J) (h : H), ∃! i : I j, (h : U) * (hRep j i : U)⁻¹ ∈ C j)
        (j : J),
        let s := σ j
        let l := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹
          (by
            intro ℓ
            obtain ⟨k, hk, h⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at h
            change k ∈ K at hk
            rw [← h]
            convert hk using 1
            group)
        let r := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
          (β⁻¹ * (s : U)⁻¹)
          (by
            intro ℓ
            obtain ⟨h, hh, e⟩ := ℓ.property.2
            change (s : U) * β * h * ((s : U) * β)⁻¹ = (ℓ : U) at e
            change h ∈ H at hh
            rw [← e]
            convert hh using 1
            group)
        let d : MackeyDiagrams.Dot (a.comp l) (b.comp r) :=
          ⟨s, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (s : U) =
              (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
        let kg := MackeyDiagrams.Word.down a
        let gh := MackeyDiagrams.Word.up b
        let kl := MackeyDiagrams.Word.up l
        let lh := MackeyDiagrams.Word.down r
        let leftMiddle := MackeyDiagrams.Word.up (a.comp l)
        let M := MackeyDiagrams.Word.tensor kg gh
        let Mj := MackeyDiagrams.Word.tensor kl lh
        let traceArg := fun (g : G) (i : I j) =>
          α⁻¹ * (g : U) * β * (hRep j i : U)⁻¹ * β⁻¹ * (s : U)⁻¹ * α
        let surviving := fun g : G => {i : I j | traceArg g i ∈ K}
        let inclusionLabel : List (Complex × MackeyDiagrams.Dot (a.comp l) (b.comp r)) := [(1, d)]
        let ι : MackeyDiagrams.LabelledDrawing Complex Mj M :=
          MackeyDiagrams.LabelledDrawing.mixedMultiplication a b l r inclusionLabel
        let expandedInclusion : MackeyDiagrams.LabelledDrawing Complex Mj M :=
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal
              (MackeyDiagrams.LabelledDrawing.trivalent
                (MackeyDiagrams.TrivalentVertex.upToDownUp a l))
              (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id lh)))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.ordinary
                (MackeyDiagrams.Diagram.associate kg leftMiddle lh))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.horizontal
                  (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.DotLabel.upDrawing (R := Complex) (Finsupp.single d 1))
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id lh))))
                (MackeyDiagrams.LabelledDrawing.horizontal
                  (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                  (MackeyDiagrams.LabelledDrawing.trivalent
                    (MackeyDiagrams.TrivalentVertex.upDownToUp b r)))))
        let tracedTerm := fun (z : M.basis.carrier) (i : I j) =>
          MackeyDiagrams.RightCupTrace.term
            (MackeyDiagrams.Diagram.mixedProjectionTail (R := Complex) a b l r d)
            z (MackeyDiagrams.RightCupTrace.unitPair r (hRep j i))
        ∃ (hf : ∀ z, Set.Finite
            {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b l r d w = z})
          (hs : ∀ g, Set.Finite (surviving g)),
          let projectionLabel : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b l r) :=
            [(1, ⟨d, hf⟩)]
          let p : MackeyDiagrams.LabelledDrawing Complex M Mj :=
            MackeyDiagrams.LabelledDrawing.compactProjection a b l r projectionLabel
          let expandedProjection : MackeyDiagrams.LabelledDrawing Complex M Mj :=
            MackeyDiagrams.LabelledDrawing.expandedProjection a b l r projectionLabel
              MackeyDiagrams.ProjectionOpening.junction MackeyDiagrams.ProjectionClosing.junction
          let crossings : MackeyDiagrams.LabelledDrawing Complex M M :=
            MackeyDiagrams.LabelledDrawing.vertical p ι
          let expandedCrossings : MackeyDiagrams.LabelledDrawing Complex M M :=
            MackeyDiagrams.LabelledDrawing.vertical expandedProjection expandedInclusion
          (∀ z : M.basis.carrier, Function.support (tracedTerm z) =
            surviving (MackeyDiagrams.Generator.mixedProduct a b z)) ∧
          (∀ (k : K) (h : H),
            (MackeyDiagrams.ScopedDiagram.eval
              (MackeyDiagrams.LabelledDrawing.interpret ι)).toLinearMap
              (Finsupp.single (MackeyDiagrams.Biset.pair kl.basis lh.basis k h) 1) =
            Finsupp.single
              (MackeyDiagrams.Generator.mixedPair a b (a.toHom k * s * b.toHom h)) 1) ∧
          (∀ g : G, (hs g).toFinset.card ≤ 1 ∧
            (MackeyDiagrams.ScopedDiagram.eval
              (MackeyDiagrams.LabelledDrawing.interpret p)).toLinearMap
              (Finsupp.single (MackeyDiagrams.Generator.mixedPair a b g) 1) =
            Finset.sum (hs g).toFinset.attach (fun i =>
              Finsupp.single (MackeyDiagrams.Biset.pair kl.basis lh.basis
                ⟨traceArg g i.val, (Set.Finite.mem_toFinset (hs g)).mp i.property⟩
                (hRep j i.val)) 1)) ∧
          (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret ι) =
            MackeyDiagrams.ScopedDiagram.eval
              (MackeyDiagrams.LabelledDrawing.interpret expandedInclusion)) ∧
          (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret crossings) =
            MackeyDiagrams.ScopedDiagram.eval
              (MackeyDiagrams.LabelledDrawing.interpret expandedCrossings)) ∧
          (∀ hi : Subgroup.FiniteIndex r.toHom.range,
            let finiteProjection : MackeyDiagrams.LabelledDrawing Complex M Mj :=
              MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.horizontal
                  (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                  (MackeyDiagrams.LabelledDrawing.trivalent
                    (MackeyDiagrams.TrivalentVertex.upToUpDown b r hi)))
                (MackeyDiagrams.LabelledDrawing.vertical
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                    (MackeyDiagrams.LabelledDrawing.horizontal
                      (MackeyDiagrams.DotLabel.upDrawing (R := Complex)
                        (Finsupp.single (MackeyDiagrams.Dot.inverse d) 1))
                      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id lh))))
                  (MackeyDiagrams.LabelledDrawing.vertical
                    (MackeyDiagrams.LabelledDrawing.ordinary
                      (MackeyDiagrams.Diagram.unassociate kg leftMiddle lh))
                    (MackeyDiagrams.LabelledDrawing.horizontal
                      (MackeyDiagrams.LabelledDrawing.trivalent
                        (MackeyDiagrams.TrivalentVertex.downUpToUp a l))
                      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id lh)))))
            MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret crossings) =
              MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret
                (MackeyDiagrams.LabelledDrawing.vertical finiteProjection expandedInclusion)))
) :=
(by
  classical
  intro U _ K H G α β Kα Hβ hK hH a b A B J σ hσ L C I hRep hTrans j
    s l r d kg gh kl lh leftMiddle M Mj traceArg surviving inclusionLabel ι
    expandedInclusion tracedTerm
  /- Ian Xiao, § 2.2, Theorem 2.2 and Lemma 2.3. The archived
     source/mackey-bimodules.pdf has (2.1)–(2.2) on p. 5 and (2.4), the
     crossing formulas and the displayed composite on p. 6. The revised
     published PDF at https://getcurious.cc/downloads/mackey-bimodules.pdf
     has these on pp. 7 and 8 respectively. Both copies give the same
     hypotheses, formulas and wiring for this endpoint.
     Alphabeta Math's article, § 2.2, gives the argument in the prose of
     Lemma 2.3 and Theorem 2.2 with numbered equations and no numbered
     proof steps. Its diagram-05 stacks projection below inclusion;
     the inverse dot is on the lower branch. The finite complex label
     at each mark is a coefficient-one singleton.
     The proof uses the shared balanced basis and typed generators for
     the actions, intertwining, cup and cap. Those evaluated maps give
     the crossing formulas directly from the representations supplied
     by the endpoint. The functor-level strand and adjunction results
     and the abstract centralizer-coset classification are imported
     project dependencies for the setup. Here d carries the explicit
     intertwining proof at the supplied representative. -/
  let q := MackeyDiagrams.Generator.mixedMultiplicationBasis a b l r d
  have ha (k : K) : (a.toHom k : U) = α * (k : U) * α⁻¹ := rfl
  have hb (h : H) : (b.toHom h : U) = β * (h : U) * β⁻¹ := rfl
  have hd : d.element = s := rfl
  have hl (t : L j) : (l.toHom t : U) = α⁻¹ * (t : U) * (α⁻¹)⁻¹ := rfl
  -- Use the full intersection (2.2) to verify the injectivity supplier's hypothesis.
  have hintersection (k : K) (h : H)
      (e : a.toHom k = d.element * b.toHom h * d.element⁻¹) : k ∈ l.toHom.range := by
    have eU := congrArg Subtype.val e
    change (a.toHom k : U) = (d.element : U) * (b.toHom h : U) * (d.element : U)⁻¹ at eU
    rw [hd, ha, hb] at eU
    have hleft : (a.toHom k : U) ∈ Kα := ⟨(k : U), k.property, (ha k).symm⟩
    have hright : (a.toHom k : U) ∈ Subgroup.map
        (MulEquiv.toMonoidHom (MulAut.conj ((s : U) * β))) H := by
      refine ⟨(h : U), h.property, ?_⟩
      change (s : U) * β * (h : U) * ((s : U) * β)⁻¹ = (a.toHom k : U)
      rw [ha, eU]
      group
    let t : L j := ⟨(a.toHom k : U), hleft, hright⟩
    refine ⟨t, Subtype.ext ?_⟩
    change (l.toHom t : U) = (k : U)
    rw [hl]
    change α⁻¹ * (a.toHom k : U) * (α⁻¹)⁻¹ = (k : U)
    rw [ha]
    group
  have hinj : Function.Injective q :=
    MackeyDiagrams.Generator.injective_mixedMultiplicationBasis a b l r d hintersection
  have hf : ∀ z, Set.Finite {w | q w = z} :=
    MackeyDiagrams.Generator.finiteFiber_of_injective a b l r d hinj
  -- Lemma 2.3 is applied to the supplied right transversal (2.4).
  have hsurv (g : G) :
      (DoubleCoset.mk A B g = j → ∃! i : I j, i ∈ surviving g) ∧
      (DoubleCoset.mk A B g ≠ j → surviving g = ∅) :=
    SurvivingCosetRepresentative K H G α β hK hH σ hσ I hRep hTrans j g
  have hsub (g : G) : (surviving g).Subsingleton := by
    intro i hi i' hi'
    by_cases hclass : DoubleCoset.mk A B g = j
    · obtain ⟨t, _, ht⟩ := (hsurv g).1 hclass
      exact (ht i hi).trans (ht i' hi').symm
    · rw [(hsurv g).2 hclass] at hi
      exact hi.elim
  have hs (g : G) : Set.Finite (surviving g) := (hsub g).finite
  have harg (g : G) (i : I j) (k : K) :
      a.toHom k = g * (b.toHom (hRep j i)⁻¹ * d.element⁻¹) ↔
        (k : U) = traceArg g i :=
    MackeyCrossingProof.trace_eq_iff a b l r d α β ha hb g (hRep j i) k
  -- The range supplier gives the factorization in (2.1). The quotient
  -- equality puts it in the class of the actual representative σ j.
  have hcover (g : G) (hg : MackeyDiagrams.Generator.mixedPair a b g ∈ Set.range q) :
      ∃ i : I j, i ∈ surviving g := by
    obtain ⟨k, h, he⟩ := (MackeyDiagrams.Generator.mixedRange_eq_doubleCoset a b l r d g).mp hg
    have hka : a.toHom k ∈ A := ⟨(k : U), k.property, (ha k).symm⟩
    have hhb : b.toHom h ∈ B := ⟨(h : U), h.property, (hb h).symm⟩
    have hclass : DoubleCoset.mk A B (σ j) = DoubleCoset.mk A B g :=
      DoubleCoset.eq.mpr ⟨a.toHom k, hka, b.toHom h, hhb, he⟩
    obtain ⟨i, hi, _⟩ := (hsurv g).1 (hclass.symm.trans (hσ j))
    exact ⟨i, hi⟩
  refine ⟨hf, hs, ?_⟩
  intro projectionLabel p expandedProjection crossings expandedCrossings
  have hinc : ι.interpret.eval = (MackeyDiagrams.Diagram.mixedMultiplication
      (R := Complex) a b l r d).eval := MackeyCrossingProof.compact_inclusion a b l r d
  have hproj : p.interpret.eval = (MackeyDiagrams.Diagram.mixedProjection
      (R := Complex) a b l r d hf).eval := MackeyCrossingProof.compact_projection a b l r d hf
  have hei : ι.interpret.eval = expandedInclusion.interpret.eval :=
    hinc.trans (MackeyCrossingProof.eval_inclusion_expansion a b l r d).symm
  have hep : p.interpret.eval = expandedProjection.interpret.eval :=
    (MackeyDiagrams.LabelledDrawing.eval_expandProjection a b l r projectionLabel
      .junction .junction).symm
  refine ⟨?_, ?_, ?_, hei, ?_, ?_⟩
  · exact MackeyCrossingProof.trace_support a b l r d (hRep j) traceArg harg
  · intro k h
    rw [hinc]
    change (MackeyDiagrams.Generator.mixedMultiplication a b l r d Complex).toLinearMap
      (Finsupp.single (kl.basis.pair lh.basis k h) 1) = _
    rw [MackeyDiagrams.Generator.mixedMultiplication,
      MackeyDiagrams.Biset.Hom.ofFunction_single]
    rfl
  · intro g
    constructor
    · exact Finset.card_le_one.mpr (fun i hi i' hi' =>
        hsub g ((hs g).mem_toFinset.mp hi) ((hs g).mem_toFinset.mp hi'))
    · rw [hproj]
      exact MackeyCrossingProof.projection_sum a b l r d (hRep j) traceArg harg
        hinj hf g (hs g) (fun _ _ hi hi' => hsub g hi hi') (hcover g)
  · change p.interpret.eval.vertical ι.interpret.eval =
      expandedProjection.interpret.eval.vertical expandedInclusion.interpret.eval
    rw [hep, hei]
  · intro hi finiteProjection
    have hfinite : p.interpret.eval = finiteProjection.interpret.eval :=
      hproj.trans (MackeyCrossingProof.eval_finite_expansion a b l r d hi hf).symm
    change p.interpret.eval.vertical ι.interpret.eval =
      finiteProjection.interpret.eval.vertical expandedInclusion.interpret.eval
    rw [hfinite, hei])

#print axioms MackeyInclusionAndProjectionCrossings
