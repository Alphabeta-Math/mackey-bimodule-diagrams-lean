import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.PointwiseIndexedDrawing
import Mathlib.GroupTheory.DoubleCoset

universe u

def checkedMackeyIdentityEndpoint : Prop :=
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
