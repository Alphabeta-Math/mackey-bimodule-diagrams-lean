import Mathlib.RepresentationTheory.FiniteIndex
import MackeyDiagrams
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.InductionRestrictionAdjunction

universe u v
set_option maxHeartbeats 1500000
#check (
∀ {U : Type u} [Group U] (H G : Subgroup U) (α : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := a.toHom.range
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
  let up := MackeyDiagrams.Word.up a
  let down := MackeyDiagrams.Word.down a
  let cap := MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.traceCap (R := Complex) a)
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
  (∀ finite : S.FiniteIndex,
    let cup := MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.reverseCup (R := Complex) a finite)
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
    ∃ adj : CategoryTheory.Adjunction Res Ind,
      (∀ (X : ModuleCat.{max u v} A) (x y : B) (z : X),
        ModuleCat.Hom.hom (adj.counit.app X) (show Res.obj (Ind.obj X) from pure X (x * y) z) =
          (MonoidAlgebra.ofCoeff (cap.toLinearMap (pairDI x y)) : A) • z) ∧
      (∀ (T : Finset G), IsTransversal T →
        (∀ g : G,
          cup.toLinearMap (MonoidAlgebra.coeff (basisG g)) =
            Finset.sum T (fun t => pairID (basisG (g * t⁻¹)) (basisG t)) ∧
          cup.toLinearMap (MonoidAlgebra.coeff (basisG g)) =
            Finset.sum T (fun t => pairID (basisG t⁻¹) (basisG (t * g)))) ∧
        (∀ (Y : ModuleCat.{max u v} B) (g : G) (z : Y),
          ModuleCat.Hom.hom (adj.unit.app Y) (basisG g • z) =
            Finset.sum T (fun t =>
              pure (Res.obj Y) (basisG (g * t⁻¹)) (basisG t • z))))))
