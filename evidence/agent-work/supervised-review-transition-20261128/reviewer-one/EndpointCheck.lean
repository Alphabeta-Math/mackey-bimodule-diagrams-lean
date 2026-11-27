import MackeyDiagrams.PointwiseIndexedDrawing
import MackeyDiagrams.IndexedDrawing
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 1000000

def commonMackeyIntersectionSumEndpoint : Prop :=
  ∀ {U : Type*} [Group U] (K H G : Subgroup U) (α β : U),
    let conjugate := fun (c : U) (S : Subgroup U) =>
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
    ∀ (hα : conjugate α K ≤ G) (hβ : conjugate β H ≤ G),
      let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
        (fun k => hα ⟨(k : U), k.property, rfl⟩)
      let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
        (fun h => hβ ⟨(h : U), h.property, rfl⟩)
      let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
      let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b)
      let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
      ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
        let Lj := fun j : J => conjugate α K ⊓ conjugate ((σ j : U) * β) H
        let left := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
          MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := K) α⁻¹ (by
            intro ℓ
            obtain ⟨k, hk, heq⟩ := (hS ℓ.property).1
            change α * k * α⁻¹ = (ℓ : U) at heq
            rw [← heq]
            change k ∈ K at hk
            convert hk using 1
            group)
        let right := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
          MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := H) (β⁻¹ * (σ j : U)⁻¹) (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := (hS ℓ.property).2
            change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
            rw [← heq]
            change h ∈ H at hh
            convert hh using 1
            group)
        let dot := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
          show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (left j S hS))
            (MackeyDiagrams.ConjEmbedding.comp b (right j S hS)) from
            ⟨σ j, by
              intro ℓ
              apply Subtype.ext
              change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (σ j : U) =
                (σ j : U) * (β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
                  (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹)
              group⟩
        let kg := MackeyDiagrams.Word.down a
        let gk := MackeyDiagrams.Word.up a
        let gh := MackeyDiagrams.Word.up b
        let M := MackeyDiagrams.Word.tensor kg gh
        let inner := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
          MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (left j S hS)) (MackeyDiagrams.Word.down (right j S hS))
        let finiteFibers := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
          ∀ z : (MackeyDiagrams.Word.basis M).carrier,
            Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b
              (left j S hS) (right j S hS) (dot j S hS) w = z}
        let inclusion := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
          show MackeyDiagrams.Diagram Complex (inner j S hS) M from
            MackeyDiagrams.Diagram.mixedMultiplication a b (left j S hS) (right j S hS) (dot j S hS)
        let projection := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
            (hf : finiteFibers j S hS) =>
          show MackeyDiagrams.Diagram Complex M (inner j S hS) from
            MackeyDiagrams.Diagram.mixedProjection a b (left j S hS) (right j S hS) (dot j S hS) hf
        let outer := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
            (hf : finiteFibers j S hS) =>
          MackeyDiagrams.Diagram.vertical (projection j S hS hf) (inclusion j S hS)
        let full := fun j : J => le_refl (Lj j)
        let cupProjection := fun {S : Subgroup U} (l : MackeyDiagrams.ConjEmbedding S K)
            (r : MackeyDiagrams.ConjEmbedding S H)
            (d : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a l) (MackeyDiagrams.ConjEmbedding.comp b r))
            (hc : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom r))) =>
          let kl := MackeyDiagrams.Word.up l
          let hl := MackeyDiagrams.Word.up r
          let lh := MackeyDiagrams.Word.down r
          let target := MackeyDiagrams.Word.tensor kl lh
          let insertCup := MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg) (MackeyDiagrams.Diagram.insertRightUnit gh))
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg)
              (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id gh) (MackeyDiagrams.Diagram.reverseCup r hc)))
          let rebracket := MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg)
            (MackeyDiagrams.Diagram.unassociate gh hl lh)
          let insertDot := MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg)
            (MackeyDiagrams.Diagram.horizontal
              (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.mergeUp b r)
                (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.upDot (MackeyDiagrams.Dot.inverse d))
                  (MackeyDiagrams.Diagram.splitUp a l)))
              (MackeyDiagrams.Diagram.id lh))
          let prepareTrace := MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg) (MackeyDiagrams.Diagram.associate gk kl lh))
            (MackeyDiagrams.Diagram.unassociate kg gk target)
          let trace := MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.traceCap a) (MackeyDiagrams.Diagram.id target))
            (MackeyDiagrams.Diagram.leftUnit target)
          show MackeyDiagrams.Diagram Complex M target from
            MackeyDiagrams.Diagram.vertical insertCup (MackeyDiagrams.Diagram.vertical rebracket
              (MackeyDiagrams.Diagram.vertical insertDot (MackeyDiagrams.Diagram.vertical prepareTrace trace)))
        (∀ (j : J) (S : Subgroup U) (hS : S ≤ Lj j), Subgroup.IsFiniteRelIndex S (Lj j) →
          ∃ (hf : finiteFibers j S hS) (hfJ : finiteFibers j (Lj j) (full j)),
            MackeyDiagrams.Diagram.eval (outer j S hS hf) =
              MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.scale (Subgroup.relIndex S (Lj j) : Complex)
                (outer j (Lj j) (full j) hfJ))) ∧
        (∀ (J₀ : Set J), Set.Nonempty J₀ →
          let I := {j : J // j ∈ J₀}
          let L := ⨅ j : I, Lj j.val
          let hL := fun j : I => iInf_le (fun i : I => Lj i.val) j
          (∀ i j : I, right i.val L (hL i) = right j.val L (hL j) ↔
            (σ i.val : U) * (σ j.val : U)⁻¹ ∈ Subgroup.centralizer (L : Set U)) ∧
          ((∀ j : I, Subgroup.IsFiniteRelIndex L (Lj j.val)) →
            ∃ (hfL : ∀ j : I, finiteFibers j.val L (hL j))
              (hfJ : ∀ j : I, finiteFibers j.val (Lj j.val) (full j.val)),
              let n := fun j : I => (Subgroup.relIndex L (Lj j.val) : Complex)
              let restricted := fun j : I => outer j.val L (hL j) (hfL j)
              let usual := fun j : I => outer j.val (Lj j.val) (full j.val) (hfJ j)
              let normalized := fun j : I => MackeyDiagrams.Diagram.scale (n j)⁻¹ (restricted j)
              let V := (MackeyDiagrams.Word.basis M).carrier →₀ Complex
              let term := fun (diagrams : I → MackeyDiagrams.Diagram Complex M M) (x : V) (j : I) =>
                MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval (diagrams j)) x
              (∀ j : I, MackeyDiagrams.Diagram.eval (normalized j) = MackeyDiagrams.Diagram.eval (usual j)) ∧
              (∀ (i j : I), i ≠ j →
                MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical
                  (inclusion i.val L (hL i)) (projection j.val L (hL j) (hfL j))) =
                MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.zero (inner i.val L (hL i)) (inner j.val L (hL j)))) ∧
              (∀ z : (MackeyDiagrams.Word.basis M).carrier,
                let basis := Finsupp.single z (1 : Complex)
                let coset := DoubleCoset.mk A B (MackeyDiagrams.Generator.mixedProduct a b z)
                let selected := {j : I | j.val = coset}
                Function.support (term normalized basis) = selected ∧
                Function.support (term usual basis) = selected) ∧
              (∃ (finiteL : ∀ x : V, Set.Finite (Function.support (term normalized x)))
                (finiteJ : ∀ x : V, Set.Finite (Function.support (term usual x))),
                let sumL : MackeyDiagrams.PointwiseIndexedDrawing Complex M M I :=
                  ⟨fun j => MackeyDiagrams.LabelledDrawing.ordinary (normalized j), finiteL⟩
                let sumJ : MackeyDiagrams.PointwiseIndexedDrawing Complex M M I :=
                  ⟨fun j => MackeyDiagrams.LabelledDrawing.ordinary (usual j), finiteJ⟩
                (∀ x : V, sumL.evalAt x = sumJ.evalAt x)) ∧
              (∀ (hJ₀ : Set.Finite J₀)
                  (cupsL : ∀ j : I, Subgroup.FiniteIndex
                    (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (right j.val L (hL j)))))
                  (cupsJ : ∀ j : I, Subgroup.FiniteIndex
                    (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (right j.val (Lj j.val) (full j.val))))),
                let indices :=
                  letI : Fintype I := Set.Finite.fintype hJ₀
                  (Finset.univ : Finset I)
                let withCupL := fun j : I =>
                  MackeyDiagrams.Diagram.scale (n j)⁻¹
                    (MackeyDiagrams.Diagram.vertical
                      (cupProjection (left j.val L (hL j)) (right j.val L (hL j))
                        (dot j.val L (hL j)) (cupsL j))
                      (inclusion j.val L (hL j)))
                let withCupJ := fun j : I =>
                  let S := Lj j.val
                  let hS := full j.val
                  MackeyDiagrams.Diagram.vertical
                    (cupProjection (left j.val S hS) (right j.val S hS) (dot j.val S hS) (cupsJ j))
                    (inclusion j.val S hS)
                let sumL : MackeyDiagrams.IndexedDrawing Complex M M I :=
                  ⟨indices, fun j => MackeyDiagrams.LabelledDrawing.ordinary (withCupL j)⟩
                let sumJ : MackeyDiagrams.IndexedDrawing Complex M M I :=
                  ⟨indices, fun j => MackeyDiagrams.LabelledDrawing.ordinary (withCupJ j)⟩
                sumL.eval = sumJ.eval ∧
                (∀ j : I, MackeyDiagrams.Diagram.eval (withCupL j) = MackeyDiagrams.Diagram.eval (normalized j) ∧
                  MackeyDiagrams.Diagram.eval (withCupJ j) = MackeyDiagrams.Diagram.eval (usual j)))))
