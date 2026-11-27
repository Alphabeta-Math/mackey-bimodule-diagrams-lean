import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.DoubleCoset
import MackeyDiagrams
import Proofs.MackeyInclusionAndProjectionCrossings

set_option maxHeartbeats 2000000

universe u

theorem MackeyIdentityDiagram : (
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
      let l := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹
          (by
            intro ℓ
            obtain ⟨k, hk, h⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at h
            change k ∈ K at hk
            rw [← h]
            convert hk using 1
            group)
      let r := fun j : J =>
        let s := σ j
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
          (β⁻¹ * (s : U)⁻¹)
          (by
            intro ℓ
            obtain ⟨h, hh, e⟩ := ℓ.property.2
            change (s : U) * β * h * ((s : U) * β)⁻¹ = (ℓ : U) at e
            change h ∈ H at hh
            rw [← e]
            convert hh using 1
            group)
      let d := fun j : J =>
        let s := σ j
        show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (l j))
          (MackeyDiagrams.ConjEmbedding.comp b (r j)) from
          ⟨s, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (s : U) =
              (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
      let down := MackeyDiagrams.Word.down a
      let up := MackeyDiagrams.Word.up b
      let M := MackeyDiagrams.Word.tensor down up
      let Mj := fun j : J =>
        MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (l j)) (MackeyDiagrams.Word.down (r j))
      ∃ hf : ∀ (j : J) (z : (MackeyDiagrams.Word.basis M).carrier),
          Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b (l j) (r j) (d j) w = z},
        let inclusion : ∀ j : J, MackeyDiagrams.Diagram Complex (Mj j) M := fun j =>
          MackeyDiagrams.Diagram.mixedMultiplication a b (l j) (r j) (d j)
        let projection : ∀ j : J, MackeyDiagrams.Diagram Complex M (Mj j) := fun j =>
          MackeyDiagrams.Diagram.mixedProjection a b (l j) (r j) (d j) (hf j)
        let straight : MackeyDiagrams.Diagram Complex M M :=
          MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id down) (MackeyDiagrams.Diagram.id up)
        let crossed : J → MackeyDiagrams.Diagram Complex M M := fun j =>
          MackeyDiagrams.Diagram.vertical (projection j) (inclusion j)
        let term := fun (x : (MackeyDiagrams.Word.basis M).carrier →₀ Complex) (j : J) =>
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval (crossed j)) x
        (∃ finite : ∀ x, Set.Finite (Function.support (term x)),
          let sum : MackeyDiagrams.PointwiseIndexedDrawing Complex M M J :=
            ⟨fun j => MackeyDiagrams.LabelledDrawing.ordinary (crossed j), finite⟩
          ∀ x, MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval straight) x =
            sum.evalAt x) ∧
        (∀ j : J,
          MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical (inclusion j) (projection j)) =
            MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id (Mj j))) ∧
        (∀ (i j : J), i ≠ j →
          MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical (inclusion i) (projection j)) =
            MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.zero (Mj i) (Mj j)))
) :=
((by
  intro U inst K H G α β Kα Hβ hK hH a b A B J σ reps L l r d down up M Mj
  let crossing (j : J) := MackeyDiagrams.Generator.mixedMultiplicationBasis a b (l j) (r j) (d j)
  have injective (j : J) : Function.Injective (crossing j) := by
    apply MackeyDiagrams.Generator.injective_mixedMultiplicationBasis
    intro k h he
    let ell := α * (k : U) * α⁻¹
    have hleft : ell ∈ Kα := ⟨k,k.property,rfl⟩
    have hright : ell ∈ Subgroup.map
        (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H := by
      refine ⟨h,h.property,?_⟩
      have hh := congrArg Subtype.val he
      change α * (k : U) * α⁻¹ =
        (σ j : U) * (β * (h : U) * β⁻¹) * (σ j : U)⁻¹ at hh
      change ((σ j : U) * β) * (h : U) * ((σ j : U) * β)⁻¹ = ell
      change ((σ j : U) * β) * (h : U) * ((σ j : U) * β)⁻¹ =
        α * (k : U) * α⁻¹
      rw [hh]
      group
    refine ⟨⟨ell, hleft, hright⟩, ?_⟩
    apply Subtype.ext
    change α⁻¹ * (α * (k : U) * α⁻¹) * (α⁻¹)⁻¹ = (k : U)
    group
  have hf (j : J) (z : M.basis.carrier) : Set.Finite {w | crossing j w = z} :=
    MackeyDiagrams.Generator.finiteFiber_of_injective a b (l j) (r j) (d j) (injective j) z
  have equivariant (j : J) :=
    MackeyDiagrams.Generator.mixedMultiplication_equivariant a b (l j) (r j) (d j)
  have rangeCriterion (j : J) (z : M.basis.carrier) :
      z ∈ Set.range (crossing j) ↔ DoubleCoset.mk A B (MackeyDiagrams.Generator.mixedProduct a b z) = j := by
    let g := MackeyDiagrams.Generator.mixedProduct a b z
    have hz := MackeyDiagrams.Generator.mixedPair_mixedProduct a b z
    change z ∈ Set.range (crossing j) ↔ DoubleCoset.mk A B g = j
    rw [← hz]
    change MackeyDiagrams.Generator.mixedPair a b g ∈ Set.range (crossing j) ↔ DoubleCoset.mk A B g = j
    rw [MackeyDiagrams.Generator.mixedRange_eq_doubleCoset a b (l j) (r j) (d j)]
    constructor
    · rintro ⟨k,h,hg⟩
      have hc : DoubleCoset.mk A B (σ j) = DoubleCoset.mk A B g := by
        apply DoubleCoset.eq.mpr
        refine ⟨a.toHom k, ⟨k,k.property,rfl⟩, b.toHom h, ⟨h,h.property,rfl⟩, ?_⟩
        exact hg
      exact hc.symm.trans (reps j)
    · intro hg
      have hc : DoubleCoset.mk A B (σ j) = DoubleCoset.mk A B g :=
        (reps j).trans hg.symm
      obtain ⟨x,hx,y,hy,hg⟩ := DoubleCoset.eq.mp hc
      change (x : U) ∈ Kα at hx
      change (y : U) ∈ Hβ at hy
      obtain ⟨k,hk,hx⟩ := hx
      obtain ⟨h,hh,hy⟩ := hy
      have hx' : a.toHom ⟨k,hk⟩ = x := Subtype.ext hx
      have hy' : b.toHom ⟨h,hh⟩ = y := Subtype.ext hy
      exact ⟨⟨k,hk⟩, ⟨h,hh⟩, by rw [hx', hy']; exact hg⟩
  have partition (z : M.basis.carrier) : ∃! j : J, z ∈ Set.range (crossing j) := by
    let j := DoubleCoset.mk A B (MackeyDiagrams.Generator.mixedProduct a b z)
    exact ⟨j, (rangeCriterion j z).mpr rfl,
      fun i hi => ((rangeCriterion i z).mp hi).symm⟩
  refine ⟨hf, ?_⟩
  intro inclusion projection straight crossed term
  refine ⟨?_, ?_, ?_⟩
  · classical
    have pointwise (x : M.basis.carrier →₀ Complex) :
        ∃ finite : Set.Finite (Function.support (term x)), x = ∑ j ∈ finite.toFinset, term x j :=
      MackeyDiagrams.Biset.Hom.sum_partition_projections
        (R := Complex) (fun j => (Mj j).basis) crossing equivariant hf injective partition x
    choose finite hsum using pointwise
    refine ⟨finite, fun x => ?_⟩
    have hs : straight.eval = MackeyDiagrams.Biset.Hom.id M.basis :=
      MackeyDiagrams.Biset.Hom.horizontal_id down.basis up.basis
    rw [hs]
    exact hsum x
  · intro j
    exact MackeyDiagrams.Biset.Hom.inclusion_projection (crossing j)
      (equivariant j) (hf j) (injective j)
  · intro i j hij
    have disj : Disjoint (Set.range (crossing j)) (Set.range (crossing i)) := by
      apply Set.disjoint_left.mpr
      intro y hyj hyi
      exact hij (((rangeCriterion i y).mp hyi).symm.trans ((rangeCriterion j y).mp hyj))
    exact MackeyDiagrams.Biset.Hom.projection_between_disjoint (crossing j)
      (equivariant j) (hf j) (crossing i) (equivariant i) disj))
