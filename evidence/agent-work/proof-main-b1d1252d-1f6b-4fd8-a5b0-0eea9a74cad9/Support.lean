import Mathlib.GroupTheory.DoubleCoset
import MackeyDiagrams
import MackeyDiagrams.MackeySummand
import Proofs.SurvivingCosetRepresentative

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
The coordinator's Diagram.eval_expandedMackeyInclusion evaluates an ordinary
cup/cap expansion. Its module is outside the configured imports, and the
endpoint uses explicit trivalent vertices carrying a singleton linear label.
Evaluate those vertices directly on balanced pairs using the shared basis rules.
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
The general article result MixedCrossingFiberMaps uses a reconstructed dot.
Here the supplied representative dot is already typed. Apply the underlying
projectionTerm_image and projectionTerm_outside lemmas at that dot, with the
conjugation calculation above giving exactly the test in Lemma 2.3.
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
