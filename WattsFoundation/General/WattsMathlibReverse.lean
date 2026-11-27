import WattsFoundation.General.WattsMathlibBridge
import WattsFoundation.General.ConcreteTensorPreservation
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Connect explicit cokernel and coproduct preservation to Mathlib's
preservation typeclasses. -/

set_option backward.isDefEq.respectTransparency false

namespace WattsFoundation.General

universe u v
open CategoryTheory CategoryTheory.Limits

variable {A B : Type u} [Ring A] [Ring B]
variable (F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B) [F.Additive]

/-- Explicit universal-property preservation implies Mathlib preservation of
all coproducts of a given index type. -/
theorem mathlibCoproducts_of_watts (h : WattsPreservesCoproducts F) (I : Type (max u v)) :
    PreservesColimitsOfShape (Discrete I) F := by
  classical
  constructor
  intro K
  let D : I → ModuleCat.{max u v} A := fun i => K.obj ⟨i⟩
  let c : Cofan D := Cofan.mk (∐ D) (Sigma.ι D)
  have hc : IsColimit c := coproductIsCoproduct D
  have source (Q : ModuleCat.{max u v} A) (legs : ∀ i, D i ⟶ Q) :
      ∃! d : ∐ D ⟶ Q, ∀ i, Sigma.ι D i ≫ d = legs i := by
    refine ⟨Cofan.IsColimit.desc hc legs, ?_, ?_⟩
    · intro i
      exact Cofan.IsColimit.fac hc legs i
    · intro d hd
      apply Cofan.IsColimit.hom_ext hc
      intro i
      change Sigma.ι D i ≫ d = Sigma.ι D i ≫ Cofan.IsColimit.desc hc legs
      exact (hd i).trans (Cofan.IsColimit.fac hc legs i).symm
  have target := h I D (∐ D) (Sigma.ι D) source
  let c' : Cofan (fun i => F.obj (D i)) := Cofan.mk (F.obj (∐ D)) (fun i => F.map (Sigma.ι D i))
  have hc' : IsColimit c' := Cofan.IsColimit.mk c'
    (fun s => Classical.choose (target s.pt s.inj))
    (fun s i => (Classical.choose_spec (target s.pt s.inj)).1 i)
    (fun s d hd => (Classical.choose_spec (target s.pt s.inj)).2 d hd)
  have hmap : IsColimit (F.mapCocone c) :=
    (isColimitMapCoconeCofanMkEquiv F D (Sigma.ι D)).symm hc'
  letI : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk)) F := by
    change PreservesColimit (Discrete.functor D) F
    exact preservesColimit_of_preserves_colimit_cocone hc hmap
  exact preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := K)).symm

/-- Explicit cokernel preservation implies Mathlib's finite-colimit
preservation for additive functors between module categories. -/
theorem mathlibFiniteColimits_of_watts (h : WattsPreservesCokernels F) :
    PreservesFiniteColimits F := by
  classical
  letI : ∀ {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F := by
    intro X Y f
    let c : CokernelCofork f := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)
    have hc : IsColimit c := cokernelIsCokernel f
    have source (Z : ModuleCat.{max u v} A) (g : Y ⟶ Z) (hg : f ≫ g = ModuleCat.ofHom 0) :
        ∃! d : cokernel f ⟶ Z, cokernel.π f ≫ d = g := by
      let d := Cofork.IsColimit.desc hc g (by simpa using hg)
      refine ⟨d, ?_, ?_⟩
      · simpa [d, c] using Cofork.IsColimit.π_desc' hc g (by simpa using hg)
      · intro e he
        apply Cofork.IsColimit.hom_ext hc
        change cokernel.π f ≫ e = cokernel.π f ≫ d
        rw [he]
        symm
        simpa [d, c] using Cofork.IsColimit.π_desc' hc g (by simpa using hg)
    have target := h X Y (cokernel f) f (cokernel.π f) (cokernel.condition f) source
    let c' : CokernelCofork (F.map f) := CokernelCofork.ofπ (F.map (cokernel.π f)) target.1
    have hc' : IsColimit c' := Cofork.IsColimit.mk c'
      (fun s => Classical.choose (target.2 s.pt s.π (CokernelCofork.condition s)))
      (fun s => (Classical.choose_spec (target.2 s.pt s.π (CokernelCofork.condition s))).1)
      (fun s d hd => (Classical.choose_spec (target.2 s.pt s.π (CokernelCofork.condition s))).2 d hd)
    have hmap : IsColimit (F.mapCocone c) :=
      (isColimitMapCoconeCoforkEquiv' F (cokernel.condition f)).symm hc'
    exact preservesColimit_of_preserves_colimit_cocone hc hmap
  exact Functor.preservesFiniteColimits_of_preservesCokernels F

#print axioms mathlibCoproducts_of_watts
#print axioms mathlibFiniteColimits_of_watts

end WattsFoundation.General
