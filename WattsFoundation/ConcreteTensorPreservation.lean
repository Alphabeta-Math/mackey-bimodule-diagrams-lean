import WattsFoundation.ConcreteTensorFunctor
import WattsFoundation.WattsNaturalIso

/-! Categorical preservation properties for tensoring with an arbitrary
bimodule over arbitrary rings. -/

set_option backward.isDefEq.respectTransparency false

namespace WattsFoundation

universe u
open CategoryTheory

variable {R S : Type u} [Ring R] [Ring S]
variable (M : Type u) [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [SMulCommClass (MulOpposite R) S M]

local instance ConcreteTensorPreservation_local1 {X : Type u} [AddCommGroup X] [Module R X] :
    AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup _
local instance ConcreteTensorPreservation_local2 {X : Type u} [AddCommGroup X] [Module R X] :
    Module S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.outerModule _ right_commute

/-- The concrete tensor functor preserves categorical cokernels. -/
theorem concreteTensorFunctor_preservesCokernels :
    WattsPreservesCokernels (concreteTensorFunctor (R := R) (S := S) M) := by
  intro L P X f q hzero hcok
  have zero : ∀ l, q.hom (f.hom l) = 0 := fun l =>
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hzero) l
  have factor (Z : Type u) [AddCommGroup Z] [Module R Z] (g : P →ₗ[R] Z)
      (hg : ∀ l, g (f.hom l) = 0) :
      ∃! d : X →ₗ[R] Z, ∀ p, d (q.hom p) = g p := by
    have hz : f ≫ ModuleCat.ofHom g = ModuleCat.ofHom 0 := by
      apply ModuleCat.hom_ext
      ext l
      exact hg l
    obtain ⟨d, hd, unique⟩ := hcok (ModuleCat.of R Z) (ModuleCat.ofHom g) hz
    refine ⟨d.hom, ?_, ?_⟩
    · intro p
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd) p
    · intro e he
      have hm : ModuleCat.ofHom e = d := by
        apply unique
        apply ModuleCat.hom_ext
        ext p
        exact he p
      exact congrArg ModuleCat.Hom.hom hm
  have qsurj := cokernel_factorization_surjective f.hom q.hom zero factor
  have qexact := cokernel_universal_exact f.hom q.hom (fun Z _ _ g hg => (factor Z g hg).exists)
  have tf := concrete_tensor_preserves_cokernel (M := M) (S := S) f.hom q.hom qsurj qexact zero
  constructor
  · apply ModuleCat.hom_ext
    ext z
    exact tf.1 z
  · intro Z g hg
    have hg' : ∀ z, g.hom (concreteTensorMap (M := M) (S := S) f.hom z) = 0 := fun z =>
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hg) z
    obtain ⟨d, hd, unique⟩ := tf.2 Z g.hom hg'
    refine ⟨ModuleCat.ofHom d, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      ext z
      exact hd z
    · intro e he
      apply ModuleCat.hom_ext
      apply unique
      intro z
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) z

/-- The concrete tensor functor preserves arbitrary categorical coproducts. -/
theorem concreteTensorFunctor_preservesCoproducts :
    WattsPreservesCoproducts (concreteTensorFunctor (R := R) (S := S) M) := by
  intro I D P ι hP Q legs
  let T := concreteTensorFunctor (R := R) (S := S) M
  let J (i : I) : D i ⟶ ChoiceFreeWatts.sumObj D :=
    @ModuleCat.ofHom R _ (D i) (ChoiceFreeWatts.sumObj D) _ _ _ _ (ChoiceFreeWatts.sumIncl D i)
  obtain ⟨u, hu, _⟩ := hP (ChoiceFreeWatts.sumObj D) J
  let v : ChoiceFreeWatts.sumObj D ⟶ P :=
    @ModuleCat.ofHom R _ (ChoiceFreeWatts.sumObj D) P _ _ _ _ (ChoiceFreeWatts.sumLift D (fun i => (ι i).hom))
  have hv (i : I) : J i ≫ v = ι i := by
    apply ModuleCat.hom_ext
    ext x
    change ChoiceFreeWatts.sumLift D (fun i => (ι i).hom) (ChoiceFreeWatts.summand D i x) = (ι i).hom x
    exact ChoiceFreeWatts.sumLift_summand D (fun i => (ι i).hom) i x
  have huv : u ≫ v = 𝟙 P := by
    obtain ⟨a, ha, unique⟩ := hP P ι
    have huv' : ∀ i, ι i ≫ (u ≫ v) = ι i := by
      intro i
      rw [← Category.assoc, hu, hv]
    have hid : ∀ i, ι i ≫ 𝟙 P = ι i := by intro i; exact Category.comp_id _
    exact (unique _ huv').trans (unique _ hid).symm
  obtain ⟨k, hk, kunique⟩ := concrete_tensor_preserves_coproduct (M := M) (S := S) D Q
    (fun i => (legs i).hom)
  have hkcat (i : I) : T.map (J i) ≫ ModuleCat.ofHom k = legs i := by
    apply ModuleCat.hom_ext
    ext t
    change k (concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i) t) = (legs i).hom t
    exact hk i t
  let h : T.obj P ⟶ Q := T.map u ≫ ModuleCat.ofHom k
  refine ⟨h, ?_, ?_⟩
  · intro i
    change T.map (ι i) ≫ (T.map u ≫ ModuleCat.ofHom k) = legs i
    rw [← Category.assoc, ← T.map_comp, hu, hkcat]
  · intro e he
    have heq : T.map v ≫ e = ModuleCat.ofHom k := by
      apply ModuleCat.hom_ext
      apply kunique
      intro i t
      have ht : T.map (J i) ≫ (T.map v ≫ e) = legs i := by
        rw [← Category.assoc, ← T.map_comp, hv, he]
      have ht' := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ht) t
      change (ModuleCat.Hom.hom (T.map v ≫ e))
        (concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i) t) = _ at ht'
      exact ht'
    calc
      e = T.map (𝟙 P) ≫ e := by simp
      _ = (T.map u ≫ T.map v) ≫ e := by rw [← T.map_comp, huv]
      _ = h := by rw [Category.assoc, heq]

#print axioms concreteTensorFunctor_preservesCoproducts
#print axioms concreteTensorFunctor_preservesCokernels

end WattsFoundation
