import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction

set_option maxHeartbeats 2000000

universe u v

namespace ReverseTriangleIdentitiesSupport

open MackeyDiagrams
open MackeyDiagrams.Diagram

noncomputable section

variable {U : Type u} [Group U] {H G : Subgroup U} (a : ConjEmbedding H G)

local notation "A" => MonoidAlgebra Complex H
local notation "B" => MonoidAlgebra Complex G
local notation "S" => a.toHom.range
local notation "φ" => MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
local notation "bG" => fun g : G => MonoidAlgebra.single g (1 : Complex)

private abbrev Trace : B →ₗ[Complex] A :=
  LinearMap.comp (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap
    (LinearMap.comp (freeLift Complex (Generator.traceBasis Complex a))
      (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap)

private theorem trace_basis (g : G) :
    Trace a (bG g) = MonoidAlgebra.ofCoeff (Generator.traceBasis Complex a g) := by
  change MonoidAlgebra.ofCoeff (freeLift Complex (Generator.traceBasis Complex a)
    (Finsupp.single g 1)) = _
  rw [freeLift_single, one_smul]

private theorem trace_mapped_in (g : G) (hg : g ∈ S) :
    φ (Trace a (bG g)) = bG g := by
  obtain ⟨h, rfl⟩ := hg
  rw [trace_basis, Generator.traceBasis_image]
  change MonoidAlgebra.mapDomain a.toHom (MonoidAlgebra.single h (1 : Complex)) = _
  rw [MonoidAlgebra.mapDomain_single]

private theorem trace_mapped_out (g : G) (hg : g ∉ S) :
    φ (Trace a (bG g)) = 0 := by
  rw [trace_basis, Generator.traceBasis_outside _ _ _ hg]
  change φ 0 = 0
  rw [map_zero]

private abbrev IsTransversal (T : Finset G) :=
  ∀ g : G, ∃! t : {t : G // t ∈ T}, g * t.val⁻¹ ∈ S

-- Inverting the subgroup membership condition for g⁻¹ gives t * g ∈ (S).
private theorem inverse_transversal (T : Finset G) (hT : IsTransversal a T) (g : G) :
    ∃! t : {t : G // t ∈ T}, t.val * g ∈ S := by
  have h (t : G) : g⁻¹ * t⁻¹ ∈ S ↔ t * g ∈ S := by
    rw [← mul_inv_rev, Subgroup.inv_mem_iff]
  obtain ⟨t, ht, huniq⟩ := hT g⁻¹
  exact ⟨t, (h t).mp ht, fun r hr => huniq r ((h r).mpr hr)⟩

private theorem sum_survivor {M : Type*} [AddCommMonoid M] (T : Finset G)
    (p : G → Prop) (f : G → M) (b : M)
    (h : ∃! t : {t : G // t ∈ T}, p t.val)
    (hin : ∀ t, p t → f t = b) (hout : ∀ t, ¬ p t → f t = 0) :
    ∑ t ∈ T, f t = b := by
  classical
  obtain ⟨t, ht, huniq⟩ := h
  rw [Finset.sum_eq_single_of_mem t.val t.property, hin t ht]
  intro r hr hrt
  exact hout r fun hp => hrt (congrArg Subtype.val (huniq ⟨r, hr⟩ hp))

private theorem nonzero_survivor {M : Type*} [Zero M] (T : Finset G)
    (p : G → Prop) (f : G → M) (b : M) (hb : b ≠ 0)
    (h : ∃! t : {t : G // t ∈ T}, p t.val)
    (hin : ∀ t, p t → f t = b) (hout : ∀ t, ¬ p t → f t = 0) :
    ∃! t : {t : G // t ∈ T}, f t.val ≠ 0 := by
  classical
  obtain ⟨t, ht, huniq⟩ := h
  refine ⟨t, fun hz => hb ((hin t ht).symm.trans hz), fun r hr => huniq r ?_⟩
  by_contra hp
  exact hr (hout r hp)

private def leftTerm (t : G) (x : B) : B :=
  bG t⁻¹ * φ (Trace a (bG t * x))

private def rightTerm (t : G) (x : B) : B :=
  φ (Trace a (x * bG t⁻¹)) * bG t

private theorem left_in (t g : G) (h : t * g ∈ S) :
    leftTerm a t (bG g) = bG g := by
  simp only [leftTerm, MonoidAlgebra.single_mul_single, mul_one, trace_mapped_in a _ h,
    inv_mul_cancel_left]

private theorem left_out (t g : G) (h : t * g ∉ S) :
    leftTerm a t (bG g) = 0 := by
  simp only [leftTerm, MonoidAlgebra.single_mul_single, mul_one, trace_mapped_out a _ h,
    mul_zero]

private theorem right_in (t g : G) (h : g * t⁻¹ ∈ S) :
    rightTerm a t (bG g) = bG g := by
  simp only [rightTerm, MonoidAlgebra.single_mul_single, mul_one, trace_mapped_in a _ h,
    inv_mul_cancel_right]

private theorem right_out (t g : G) (h : g * t⁻¹ ∉ S) :
    rightTerm a t (bG g) = 0 := by
  simp only [rightTerm, MonoidAlgebra.single_mul_single, mul_one, trace_mapped_out a _ h,
    zero_mul]

private theorem dual_basis (T : Finset G) (hT : IsTransversal a T) :
    (∀ x : B, (∑ t ∈ T, leftTerm a t x) = x ∧ (∑ t ∈ T, rightTerm a t x) = x) ∧
      (∀ g : G, (∃! t : {t : G // t ∈ T}, leftTerm a t.val (bG g) ≠ 0) ∧
        (∃! t : {t : G // t ∈ T}, rightTerm a t.val (bG g) ≠ 0)) := by
  have leftSum (g : G) := sum_survivor T (fun t => t * g ∈ S)
    (fun t => leftTerm a t (bG g)) (bG g) (inverse_transversal a T hT g)
    (fun t => left_in a t g) (fun t => left_out a t g)
  have rightSum (g : G) := sum_survivor T (fun t => g * t⁻¹ ∈ S)
    (fun t => rightTerm a t (bG g)) (bG g) (hT g)
    (fun t => right_in a t g) (fun t => right_out a t g)
  constructor
  · intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => simpa only [MonoidAlgebra.of_apply] using And.intro (leftSum g) (rightSum g)
    | add x y hx hy =>
        simp only [leftTerm, rightTerm, mul_add, add_mul, map_add] at hx hy ⊢
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hx.1, hy.1, hx.2, hy.2]
        exact ⟨rfl, rfl⟩
    | smul c x hx =>
        simp only [leftTerm, rightTerm, mul_smul_comm, smul_mul_assoc, map_smul] at hx ⊢
        rw [← Finset.smul_sum, ← Finset.smul_sum, hx.1, hx.2]
        exact ⟨rfl, rfl⟩
  · intro g
    have hb : bG g ≠ 0 := by simp
    exact ⟨nonzero_survivor T (fun t => t * g ∈ S) _ _ hb
      (inverse_transversal a T hT g) (fun t => left_in a t g) (fun t => left_out a t g),
      nonzero_survivor T (fun t => g * t⁻¹ ∈ S) _ _ hb
        (hT g) (fun t => right_in a t g) (fun t => right_out a t g)⟩

local notation "D" => Word.down a
local notation "I" => Word.up a
local notation "idD" => Diagram.id (R := Complex) D
local notation "idI" => Diagram.id (R := Complex) I
local notation "cap" => traceCap (R := Complex) a

private abbrev CupFormula (finite : (S).FiniteIndex) (T : Finset G) :=
  (reverseCup (R := Complex) a finite).eval.toLinearMap (Finsupp.single (1 : G) 1) =
    ∑ t ∈ T, Finsupp.single ((I).basis.pair (D).basis t⁻¹ t) 1

private theorem insertRightUnit_single (g : G) :
    (insertRightUnit (R := Complex) D).eval.toLinearMap (Finsupp.single g 1) =
      Finsupp.single ((D).basis.pair (Biset.regular G) g 1) 1 := by
  change (Biset.insertRightUnit (D).basis Complex).toLinearMap _ = _
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]

private theorem triangle_down (finite : (S).FiniteIndex) (T : Finset G)
    (hT : IsTransversal a T) (hCup : CupFormula a finite T) :
    ((insertRightUnit D).vertical
      (((idD).horizontal (reverseCup (R := Complex) a finite)).vertical
        ((unassociate D I D).vertical
          (((cap).horizontal idD).vertical (leftUnit D))))).eval = (idD).eval := by
  apply eval_ext_on_generators
  intro g
  change G at g
  rw [eval_vertical_apply, eval_vertical_apply, eval_vertical_apply, eval_vertical_apply,
    insertRightUnit_single a g, eval_horizontal_single idD (reverseCup a finite) g 1 1,
    one_smul, eval_id_apply, hCup]
  simp only [map_sum]
  let f (t : G) :=
    (leftUnit (R := Complex) D).eval.toLinearMap
      (((cap).horizontal idD).eval.toLinearMap
        (Finsupp.single (((D).basis.tensor (I).basis).pair (D).basis
          ((D).basis.pair (I).basis g t⁻¹) t) 1))
  calc
    _ = ∑ t ∈ T, f t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Biset.pairLinear_single, mul_one, eval_unassociate_single D I D g t⁻¹ t]
    _ = Finsupp.single g (1 : Complex) := ?_
  have hContract (t : G) :
      f t = (leftUnit (R := Complex) D).eval.toLinearMap
        (Biset.pairLinear Complex (Biset.regular H) (D).basis
          (Generator.traceBasis Complex a (g * t⁻¹)) (Finsupp.single t 1)) := by
    dsimp only [f]
    rw [eval_horizontal_single cap idD ((D).basis.pair (I).basis g t⁻¹) t 1,
      one_smul, eval_id_apply, eval_traceCap_single a g t⁻¹ 1, one_smul]
  have hin (t : G) (ht : g * t⁻¹ ∈ S) : f t = Finsupp.single g 1 := by
    obtain ⟨h, hh⟩ := ht
    have he : (D).basis.act (h, 1) t = g := by
      change a.toHom h * t * (1 : G)⁻¹ = g
      rw [hh]
      simp
    rw [hContract, ← hh, Generator.traceBasis_image, Biset.pairLinear_single,
      mul_one, eval_leftUnit_single D h t 1, he]
  have hout (t : G) (ht : g * t⁻¹ ∉ S) : f t = 0 := by
    rw [hContract, Generator.traceBasis_outside Complex a _ ht]
    simp only [map_zero, LinearMap.zero_apply]
  exact sum_survivor T (fun t => g * t⁻¹ ∈ S) f _ (hT g) hin hout

private theorem triangle_up (finite : (S).FiniteIndex) (T : Finset G)
    (hT : IsTransversal a T) (hCup : CupFormula a finite T) :
    ((insertLeftUnit I).vertical
      (((reverseCup (R := Complex) a finite).horizontal idI).vertical
        ((associate I D I).vertical
          (((idI).horizontal cap).vertical (rightUnit I))))).eval = (idI).eval := by
  apply eval_ext_on_generators
  intro g
  change G at g
  rw [eval_vertical_apply, eval_vertical_apply, eval_vertical_apply, eval_vertical_apply,
    eval_insertLeftUnit_single I g, eval_horizontal_single (reverseCup a finite) idI 1 g 1,
    one_smul, eval_id_apply, hCup]
  let pair := (Biset.pairLinear Complex ((I).basis.tensor (D).basis) (I).basis).flip
    (Finsupp.single g 1)
  change (rightUnit (R := Complex) I).eval.toLinearMap
    (((idI).horizontal cap).eval.toLinearMap ((associate (R := Complex) I D I).eval.toLinearMap
      (pair (∑ t ∈ T, Finsupp.single ((I).basis.pair (D).basis t⁻¹ t) 1)))) = _
  simp only [map_sum, pair, LinearMap.flip_apply]
  let f (t : G) :=
    (rightUnit (R := Complex) I).eval.toLinearMap
      (((idI).horizontal cap).eval.toLinearMap
        (Finsupp.single ((I).basis.pair ((D).basis.tensor (I).basis) t⁻¹
          ((D).basis.pair (I).basis t g)) 1))
  calc
    _ = ∑ t ∈ T, f t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Biset.pairLinear_single, mul_one, eval_associate_single I D I t⁻¹ t g]
    _ = Finsupp.single g (1 : Complex) := ?_
  have hContract (t : G) :
      f t = (rightUnit (R := Complex) I).eval.toLinearMap
        (Biset.pairLinear Complex (I).basis (Biset.regular H)
          (Finsupp.single t⁻¹ 1) (Generator.traceBasis Complex a (t * g))) := by
    dsimp only [f]
    rw [eval_horizontal_single idI cap t⁻¹ ((D).basis.pair (I).basis t g) 1,
      one_smul, eval_id_apply, eval_traceCap_single a t g 1, one_smul]
  have hin (t : G) (ht : t * g ∈ S) : f t = Finsupp.single g 1 := by
    obtain ⟨h, hh⟩ := ht
    have he : (I).basis.act (1, h⁻¹) t⁻¹ = g := by
      change (1 : G) * t⁻¹ * (a.toHom h⁻¹)⁻¹ = g
      rw [map_inv, inv_inv, hh]
      simp
    rw [hContract, ← hh, Generator.traceBasis_image, Biset.pairLinear_single,
      mul_one, eval_rightUnit_single I t⁻¹ h 1, he]
  have hout (t : G) (ht : t * g ∉ S) : f t = 0 := by
    rw [hContract, Generator.traceBasis_outside Complex a _ ht]
    simp only [map_zero]
  exact sum_survivor T (fun t => t * g ∈ S) f _ (inverse_transversal a T hT g) hin hout

end
end ReverseTriangleIdentitiesSupport

theorem ReverseTriangleIdentities : (
∀ {U : Type u} [Group U] (H G : Subgroup U) (α : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom a)
  let up := MackeyDiagrams.Word.up a
  let down := MackeyDiagrams.Word.down a
  let traceCap := MackeyDiagrams.Diagram.traceCap (R := Complex) a
  let cap := MackeyDiagrams.Diagram.eval traceCap
  let pairDI := fun (x y : B) =>
    MackeyDiagrams.Biset.pairLinear Complex down.basis up.basis
      (MonoidAlgebra.coeff x) (MonoidAlgebra.coeff y)
  let pairID := fun (x y : B) =>
    MackeyDiagrams.Biset.pairLinear Complex up.basis down.basis
      (MonoidAlgebra.coeff x) (MonoidAlgebra.coeff y)
  let basisG := fun g : G => MonoidAlgebra.single g (1 : Complex)
  let E : LinearMap (RingHom.id Complex) B A :=
    LinearMap.comp (MonoidAlgebra.coeffLinearEquiv Complex).symm.toLinearMap
      (LinearMap.comp
        (MackeyDiagrams.freeLift Complex (MackeyDiagrams.Generator.traceBasis Complex a))
        (MonoidAlgebra.coeffLinearEquiv Complex).toLinearMap)
  (∀ g : G, g ∈ S →
    ∃ h : H, (h : U) = α⁻¹ * (g : U) * α ∧ E (basisG g) = MonoidAlgebra.single h 1) ∧
  (∀ g : G, g ∉ S → E (basisG g) = 0) ∧
  (∀ (r s : A) (x : B), E (φ r * x * φ s) = r * E x * s) ∧
  (∀ x y : B, cap.toLinearMap (pairDI x y) = MonoidAlgebra.coeff (E (x * y))) ∧
  (∀ finite : Subgroup.FiniteIndex S,
    let reverseCup := MackeyDiagrams.Diagram.reverseCup (R := Complex) a finite
    let cup := MackeyDiagrams.Diagram.eval reverseCup
    let IsTransversal := fun T : Finset G =>
      ∀ g : G, ∃! t : {t : G // t ∈ T}, g * t.val⁻¹ ∈ S
    let toRep : CategoryTheory.Functor (ModuleCat.{max u v} A) (Rep.{max u v} Complex H) :=
      Rep.ofModuleMonoidAlgebra
    let Ind : CategoryTheory.Functor (ModuleCat.{max u v} A) (ModuleCat.{max u v} B) :=
      CategoryTheory.Functor.comp
        (CategoryTheory.Functor.comp toRep (Rep.indFunctor Complex a.toHom))
        (Rep.toModuleMonoidAlgebra (k := Complex) (G := G))
    let Res : CategoryTheory.Functor (ModuleCat.{max u v} B) (ModuleCat.{max u v} A) :=
      ModuleCat.restrictScalars φ.toRingHom
    let pure := fun (X : ModuleCat.{max u v} A) (b : B) (x : X) =>
      let ρ := Rep.ρ (toRep.obj X)
      show Ind.obj X from
        (Representation.asModuleEquiv (Representation.ind a.toHom ρ)).symm
          (MackeyDiagrams.freeLift Complex
            (fun g : G => Representation.IndV.mk a.toHom ρ g⁻¹ x) (MonoidAlgebra.coeff b))
    (∃ T : Finset G, IsTransversal T) ∧
    (∀ (T : Finset G), IsTransversal T →
      let leftTerm := fun (t : G) (x : B) => basisG (t⁻¹) * φ (E (basisG t * x))
      let rightTerm := fun (t : G) (x : B) => φ (E (x * basisG (t⁻¹))) * basisG t
      (∀ x : B, Finset.sum T (fun t => leftTerm t x) = x ∧
        Finset.sum T (fun t => rightTerm t x) = x) ∧
      (∀ g : G,
        (∃! t : {t : G // t ∈ T}, leftTerm t.val (basisG g) ≠ 0) ∧
        (∃! t : {t : G // t ∈ T}, rightTerm t.val (basisG g) ≠ 0))) ∧
    (let idUp := MackeyDiagrams.Diagram.id (R := Complex) up
     let idDown := MackeyDiagrams.Diagram.id (R := Complex) down
     let triangleDown :=
       MackeyDiagrams.Diagram.vertical
         (MackeyDiagrams.Diagram.insertRightUnit down)
         (MackeyDiagrams.Diagram.vertical
           (MackeyDiagrams.Diagram.horizontal idDown reverseCup)
           (MackeyDiagrams.Diagram.vertical
             (MackeyDiagrams.Diagram.unassociate down up down)
             (MackeyDiagrams.Diagram.vertical
               (MackeyDiagrams.Diagram.horizontal traceCap idDown)
               (MackeyDiagrams.Diagram.leftUnit down))))
     let triangleUp :=
       MackeyDiagrams.Diagram.vertical
         (MackeyDiagrams.Diagram.insertLeftUnit up)
         (MackeyDiagrams.Diagram.vertical
           (MackeyDiagrams.Diagram.horizontal reverseCup idUp)
           (MackeyDiagrams.Diagram.vertical
             (MackeyDiagrams.Diagram.associate up down up)
             (MackeyDiagrams.Diagram.vertical
               (MackeyDiagrams.Diagram.horizontal idUp traceCap)
               (MackeyDiagrams.Diagram.rightUnit up))))
     MackeyDiagrams.Diagram.eval triangleDown = MackeyDiagrams.Diagram.eval idDown ∧
       MackeyDiagrams.Diagram.eval triangleUp = MackeyDiagrams.Diagram.eval idUp) ∧
    ∃ adj : CategoryTheory.Adjunction Res Ind,
      (∀ Y : ModuleCat.{max u v} B,
        CategoryTheory.CategoryStruct.comp (Res.map (adj.unit.app Y))
          (adj.counit.app (Res.obj Y)) = CategoryTheory.CategoryStruct.id (Res.obj Y)) ∧
      (∀ X : ModuleCat.{max u v} A,
        CategoryTheory.CategoryStruct.comp (adj.unit.app (Ind.obj X))
          (Ind.map (adj.counit.app X)) = CategoryTheory.CategoryStruct.id (Ind.obj X)) ∧
      (∀ (X : ModuleCat.{max u v} A) (x y : B) (z : X),
        ModuleCat.Hom.hom (adj.counit.app X) (show Res.obj (Ind.obj X) from pure X (x * y) z) =
          (MonoidAlgebra.ofCoeff (cap.toLinearMap (pairDI x y)) : A) • z) ∧
      (∀ (T : Finset G), IsTransversal T →
        (∀ g : G,
          cup.toLinearMap (MonoidAlgebra.coeff (basisG g)) =
            Finset.sum T (fun t => pairID (basisG (g * t⁻¹)) (basisG t)) ∧
          cup.toLinearMap (MonoidAlgebra.coeff (basisG g)) =
            Finset.sum T (fun t => pairID (basisG (t⁻¹)) (basisG (t * g)))) ∧
        (∀ (Y : ModuleCat.{max u v} B) (g : G) (z : Y),
          ModuleCat.Hom.hom (adj.unit.app Y) (basisG g • z) =
            Finset.sum T (fun t =>
              pure (Res.obj Y) (basisG (g * t⁻¹)) (basisG t • z)))))
) :=
(by
  open ReverseTriangleIdentitiesSupport in
  intro U _ H G α hα A B a S φ up down traceCap cap pairDI pairID basisG E
  -- Xiao, § 1.2, Cups and caps, p. 3 in the archived original and p. 4
  -- in the published 28 November revision (SHA-256 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
  -- The dual-basis formulas agree in both copies. The reverse cup starts
  -- at the empty G boundary and the trace cap ends at the empty H boundary.
  obtain ⟨hTraceIn, hTraceOut, hBimodule, hCap, hFinite⟩ :=
    FiniteIndexReverseAdjunction.{u, v} H G α hα
  refine ⟨hTraceIn, hTraceOut, hBimodule, hCap, ?_⟩
  intro finite reverseCup cup IsT toRep Ind Res pure
  obtain ⟨⟨T, hT⟩, adj, hCounit, hCupUnit⟩ := hFinite finite
  have hCup : CupFormula a finite T := by
    calc
      _ = _ := ((hCupUnit T hT).1 1).1
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        change MackeyDiagrams.Biset.pairLinear Complex up.basis down.basis
          (Finsupp.single ((1 : G) * t⁻¹) 1) (Finsupp.single t 1) = _
        rw [MackeyDiagrams.Biset.pairLinear_single, one_mul, mul_one]
  -- The right transversal selects the term for the down strand. Applying
  -- it to g⁻¹ selects the term for the up strand by subgroup inversion.
  -- Alphabeta Math's module tensor universal property, Steps 3.1 and 4.1,
  -- motivates balance and checking on elementary tensors. The shared
  -- balanced biset supplies descent, and linearity extends the basis checks.
  -- The categorical triangle laws apply to the supplied module adjunction.
  -- The diagram triangles are evaluated separately on the strand bases,
  -- with the supplied cup expansion and the trace-basis formula.
  exact ⟨⟨T, hT⟩, fun T' hT' => dual_basis a T' hT',
    ⟨triangle_down a finite T hT hCup, triangle_up a finite T hT hCup⟩,
    adj, adj.left_triangle_components, adj.right_triangle_components, hCounit, hCupUnit⟩)
