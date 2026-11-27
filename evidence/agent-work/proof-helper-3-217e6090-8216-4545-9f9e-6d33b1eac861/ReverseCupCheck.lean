import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import MackeyDiagrams.MixedIdentities
import MackeyDiagrams.DotLabels

set_option maxHeartbeats 2000000

namespace CupCapDotSlidesSupport

open MackeyDiagrams
open scoped BigOperators

universe u v

private theorem extOnBasis {ι : Type*} {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] {f g : (ι →₀ R) →ₗ[R] M}
    (h : ∀ i, f (Finsupp.single i 1) = g (Finsupp.single i 1)) : f = g := by
  apply Finsupp.lhom_ext
  intro i r
  have hr : Finsupp.single i r = r • Finsupp.single i (1 : R) := by
    simp [Finsupp.smul_single, smul_eq_mul]
  rw [hr, map_smul, map_smul, h]

section Reverse

variable {U : Type u} [Group U] {H G : Subgroup U}
variable {R : Type v} [CommSemiring R] {a b : ConjEmbedding H G}

private abbrev capCarrier (a : ConjEmbedding H G) :=
  ((Biset.induction a).tensor (Biset.restriction a)).carrier

private abbrev capPair (a : ConjEmbedding H G) (x y : G) : capCarrier a :=
  (Biset.induction a).pair (Biset.restriction a) x y

private def capShift (d : Dot a b) : capCarrier a → capCarrier b :=
  Quotient.map' (fun xy : G × G => (xy.1 * d.element, d.element⁻¹ * xy.2)) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    change 1 * x.1 * (a.toHom h)⁻¹ = y.1 at hx
    change a.toHom h * x.2 * (1 : G)⁻¹ = y.2 at hy
    have hd : b.toHom h * d.element⁻¹ = d.element⁻¹ * a.toHom h :=
      d.inverse.intertwines h
    have hi := d.intertwines h⁻¹
    rw [map_inv, map_inv] at hi
    refine ⟨h, ?_, ?_⟩
    · change 1 * (x.1 * d.element) * (b.toHom h)⁻¹ = y.1 * d.element
      rw [← hx]
      simp only [one_mul]
      rw [mul_assoc, mul_assoc, hi]
    · change b.toHom h * (d.element⁻¹ * x.2) * (1 : G)⁻¹ = d.element⁻¹ * y.2
      simp only [← hy, inv_one, mul_one, ← mul_assoc, hd])

private theorem capShift_inverse (d : Dot a b) (z : capCarrier a) :
    capShift d.inverse (capShift d z) = z := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change capPair a (xy.1 * d.element * d.element⁻¹) ((d.element⁻¹)⁻¹ * (d.element⁻¹ * xy.2)) =
    capPair a xy.1 xy.2
  simp [mul_assoc]

private theorem capShift_forward_inverse (d : Dot a b) (z : capCarrier b) :
    capShift d (capShift d.inverse z) = z := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change capPair b (xy.1 * d.element⁻¹ * d.element) (d.element⁻¹ * ((d.element⁻¹)⁻¹ * xy.2)) =
    capPair b xy.1 xy.2
  simp [mul_assoc]

private theorem capShift_product (d : Dot a b) (z : capCarrier a) :
    Generator.multiplicationCapBasis b (capShift d z) =
      Generator.multiplicationCapBasis a z := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change xy.1 * d.element * (d.element⁻¹ * xy.2) = xy.1 * xy.2
  group

private theorem reverseBasis (a : ConjEmbedding H G) (ha : a.toHom.range.FiniteIndex) (g : G) :
    (Diagram.reverseCup (R := R) a ha).eval.toLinearMap (Finsupp.single g 1) =
      ∑ z ∈ (Generator.multiplicationCap_finiteFiber a ha g).toFinset, Finsupp.single z 1 := by
  change (Generator.reverseCup R a ha).toLinearMap (Finsupp.single g 1) = _
  rw [Generator.reverseCup, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]

private theorem reverseTerm (d : Dot a b) (z : capCarrier a) :
    ((Diagram.upDot (R := R) d).horizontal (.id (.down a))).eval.toLinearMap
      (Finsupp.single z 1) =
    ((Diagram.id (R := R) (.up b)).horizontal (.downDot d.inverse)).eval.toLinearMap
      (Finsupp.single (capShift d z) 1) := by
  refine Quotient.inductionOn z (fun (xy : G × G) => ?_)
  change ((Diagram.upDot (R := R) d).horizontal (.id (.down a))).eval.toLinearMap
      (Finsupp.single (capPair a xy.1 xy.2) 1) =
    ((Diagram.id (R := R) (.up b)).horizontal (.downDot d.inverse)).eval.toLinearMap
      (Finsupp.single (capPair b (xy.1 * d.element) (d.element⁻¹ * xy.2)) 1)
  rw [Diagram.eval_horizontal_single (Diagram.upDot d) (Diagram.id (.down a)) xy.1 xy.2 1,
    Diagram.eval_horizontal_single (Diagram.id (.up b)) (Diagram.downDot d.inverse)
      (xy.1 * d.element) (d.element⁻¹ * xy.2) 1,
    Diagram.eval_id_apply, Diagram.eval_id_apply, Diagram.eval_upDot_single,
    Diagram.eval_downDot_single, Biset.pairLinear_single, Biset.pairLinear_single,
    one_mul, one_smul, one_smul]
  simp only [Dot.inverse, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

/- Proposition 3.1, equation (3.4). The draft reindexes chosen right coset
   representatives by t ↦ d⁻¹*t. The Lean reverse cup is a transfer, so we
   reindex the actual product fibers by [x,y] ↦ [x*d,d⁻¹*y]. This is the
   same change in the second representative and uses both supplied finiteness
   witnesses. Both terms at corresponding fiber elements give [x*d,y]. -/
private theorem reverse (d : Dot a b)
    (ha : a.toHom.range.FiniteIndex) (hb : b.toHom.range.FiniteIndex) :
    ((Diagram.reverseCup (R := R) a ha).vertical ((Diagram.upDot d).horizontal (.id (.down a)))).eval =
    ((Diagram.reverseCup (R := R) b hb).vertical ((Diagram.id (.up b)).horizontal (.downDot d.inverse))).eval := by
  classical
  apply Biset.Hom.ext
  apply extOnBasis
  intro g
  change G at g
  rw [Diagram.eval_vertical_apply, Diagram.eval_vertical_apply,
    reverseBasis a ha g, reverseBasis b hb g, map_sum, map_sum]
  let fa := Generator.multiplicationCap_finiteFiber a ha g
  let fb := Generator.multiplicationCap_finiteFiber b hb g
  change ∑ z ∈ fa.toFinset, ((Diagram.upDot (R := R) d).horizontal (.id (.down a))).eval.toLinearMap
      (Finsupp.single z 1) =
    ∑ z ∈ fb.toFinset, ((Diagram.id (R := R) (.up b)).horizontal (.downDot d.inverse)).eval.toLinearMap
      (Finsupp.single z 1)
  refine Finset.sum_bij' (fun z _ => capShift d z) (fun z _ => capShift d.inverse z) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    exact fb.mem_toFinset.mpr ((capShift_product d z).trans (fa.mem_toFinset.mp hz))
  · intro z hz
    exact fa.mem_toFinset.mpr ((capShift_product d.inverse z).trans (fb.mem_toFinset.mp hz))
  · intro z _
    exact capShift_inverse d z
  · intro z _
    exact capShift_forward_inverse d z
  · intro z _
    exact reverseTerm d z

end Reverse

section Linearity

variable {R : Type v} [CommSemiring R]

private theorem lift_map {ι : Type*} {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (L : M →ₗ[R] N) (f : ι → M) (z : ι →₀ R) :
    L (freeLift R f z) = freeLift R (fun d => L (f d)) z := by
  have h : L.comp (freeLift R f) = freeLift R (fun d => L (f d)) := by
    apply extOnBasis
    intro i
    simp only [LinearMap.comp_apply, freeLift_single, one_smul]
  exact LinearMap.congr_fun h z

private theorem lift_dual {ι κ : Type u} {M : Type*} [AddCommMonoid M] [Module R M]
    (rev : ι → κ) (f : κ → M) (z : ι →₀ R) :
    freeLift R f (Finsupp.mapDomain rev z) = freeLift R (fun d => f (rev d)) z := by
  have h : (freeLift R f).comp (Finsupp.lmapDomain R R rev) =
      freeLift R (fun d => f (rev d)) := by
    apply extOnBasis
    intro i
    simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      freeLift_single, one_smul]
  exact LinearMap.congr_fun h z

variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {X X' : Biset K H} {Y Y' : Biset H J}

private theorem lift_horizontal_left {ι : Type u}
    (z : ι →₀ R) (f : ι → Biset.Hom R X X') (F : Biset.Hom R X X')
    (hF : ∀ x, F.toLinearMap x = freeLift R (fun d => (f d).toLinearMap x) z)
    (g : Biset.Hom R Y Y') (w : (X.tensor Y).carrier →₀ R) :
    (F.horizontal g).toLinearMap w =
      freeLift R (fun d => ((f d).horizontal g).toLinearMap w) z := by
  let maps := fun d => ((f d).horizontal g).toLinearMap
  have h : (F.horizontal g).toLinearMap = freeLift R maps z := by
    apply extOnBasis
    intro t
    refine Quotient.inductionOn t (fun xy => ?_)
    obtain ⟨x,y⟩ := xy
    let w₀ := Finsupp.single (X.pair Y x y) (1 : R)
    change (F.horizontal g).toLinearMap w₀ = (freeLift R maps z) w₀
    have he := lift_map (LinearMap.applyₗ (R := R) w₀) maps z
    change (freeLift R maps z) w₀ = freeLift R (fun d => (maps d) w₀) z at he
    rw [he, Biset.Hom.horizontal_single F g x y 1, one_smul, hF]
    let L := (Biset.pairLinear R X' Y').flip (g.toLinearMap (Finsupp.single y 1))
    change L (freeLift R (fun d => (f d).toLinearMap (Finsupp.single x 1)) z) = _
    rw [lift_map]
    apply congrArg (fun basis => freeLift R basis z)
    funext d
    symm
    change ((f d).horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) 1) = _
    rw [Biset.Hom.horizontal_single (f d) g x y 1, one_smul]
    rfl
  calc
    (F.horizontal g).toLinearMap w = (freeLift R maps z) w := LinearMap.congr_fun h w
    _ = _ := lift_map (LinearMap.applyₗ (R := R) w) maps z

private theorem lift_horizontal_right {ι : Type u}
    (z : ι →₀ R) (g : Biset.Hom R X X') (f : ι → Biset.Hom R Y Y')
    (F : Biset.Hom R Y Y')
    (hF : ∀ y, F.toLinearMap y = freeLift R (fun d => (f d).toLinearMap y) z)
    (w : (X.tensor Y).carrier →₀ R) :
    (g.horizontal F).toLinearMap w =
      freeLift R (fun d => (g.horizontal (f d)).toLinearMap w) z := by
  let maps := fun d => (g.horizontal (f d)).toLinearMap
  have h : (g.horizontal F).toLinearMap = freeLift R maps z := by
    apply extOnBasis
    intro t
    refine Quotient.inductionOn t (fun xy => ?_)
    obtain ⟨x,y⟩ := xy
    let w₀ := Finsupp.single (X.pair Y x y) (1 : R)
    change (g.horizontal F).toLinearMap w₀ = (freeLift R maps z) w₀
    have he := lift_map (LinearMap.applyₗ (R := R) w₀) maps z
    change (freeLift R maps z) w₀ = freeLift R (fun d => (maps d) w₀) z at he
    rw [he, Biset.Hom.horizontal_single g F x y 1, one_smul, hF]
    let L := Biset.pairLinear R X' Y' (g.toLinearMap (Finsupp.single x 1))
    change L (freeLift R (fun d => (f d).toLinearMap (Finsupp.single y 1)) z) = _
    rw [lift_map]
    apply congrArg (fun basis => freeLift R basis z)
    funext d
    symm
    change (g.horizontal (f d)).toLinearMap (Finsupp.single (X.pair Y x y) 1) = _
    rw [Biset.Hom.horizontal_single g (f d) x y 1, one_smul]
  calc
    (g.horizontal F).toLinearMap w = (freeLift R maps z) w := LinearMap.congr_fun h w
    _ = _ := lift_map (LinearMap.applyₗ (R := R) w) maps z

end Linearity

section Drawing
variable {U : Type u} [Group U] {H G : Subgroup U}
variable {R : Type v} [CommSemiring R] {a b : ConjEmbedding H G}

private theorem up_eval (z : DotLabel R a b) (x : G →₀ R) :
    z.upDrawing.interpret.eval.toLinearMap x =
      freeLift R (fun (d : Dot a b) => (Diagram.upDot d).eval.toLinearMap x) z := by
  rw [DotLabel.eval_upDrawing, Diagram.eval_linearUpDot_apply]

private theorem down_eval (z : DotLabel R a b) (x : G →₀ R) :
    z.downDrawing.interpret.eval.toLinearMap x =
      freeLift R (fun (d : Dot a b) => (Diagram.downDot d).eval.toLinearMap x) z := by
  rw [DotLabel.eval_downDrawing, Diagram.eval_linearDownDot_apply]

private theorem down_dual (z : DotLabel R a b) (x : G →₀ R) :
    (DotLabel.downDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval.toLinearMap x =
      freeLift R (fun (d : Dot a b) => (Diagram.downDot d.inverse).eval.toLinearMap x) z := by
  rw [down_eval, lift_dual]

theorem reverse_label (z : DotLabel R a b) (ha : a.toHom.range.FiniteIndex)
    (hb : b.toHom.range.FiniteIndex) :
    (Diagram.reverseCup a ha).eval.vertical
      (z.upDrawing.interpret.eval.horizontal (Diagram.id (.down a)).eval) =
    (Diagram.reverseCup b hb).eval.vertical ((Diagram.id (.up b)).eval.horizontal
      (DotLabel.downDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro w
  simp only [Biset.Hom.vertical, LinearMap.comp_apply]
  rw [lift_horizontal_left z _ _ (up_eval z), lift_horizontal_right z _ _ _ (down_dual z)]
  apply congrArg (fun basis => freeLift R basis z)
  funext d
  exact congrArg (fun m => Biset.Hom.toLinearMap m w) (reverse (R := R) d ha hb)

end Drawing

end CupCapDotSlidesSupport

#print axioms CupCapDotSlidesSupport.reverse_label

theorem CupCapDotSlides_reverseConjunct : (
∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  ∀ z : MackeyDiagrams.DotLabel Complex a b,
    let zDual : MackeyDiagrams.DotLabel Complex b a :=
      Finsupp.mapDomain MackeyDiagrams.Dot.inverse z
    let rightZ := MackeyDiagrams.DotLabel.upDrawing z
    let leftZ := MackeyDiagrams.DotLabel.downDrawing zDual
    let idUpB := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up b))
    let idDownA := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down a))
    (∀ (finiteA : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)))
       (finiteB : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b))),
      let reverseLeft := MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.reverseCup a finiteA))
        (MackeyDiagrams.LabelledDrawing.horizontal rightZ idDownA)
      let reverseRight := MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.reverseCup b finiteB))
        (MackeyDiagrams.LabelledDrawing.horizontal idUpB leftZ)
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret reverseLeft) =
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret reverseRight))
) := by
  intro U inst H G α β hα hβ a b z
  exact fun ha hb => CupCapDotSlidesSupport.reverse_label z ha hb

#print axioms CupCapDotSlides_reverseConjunct
