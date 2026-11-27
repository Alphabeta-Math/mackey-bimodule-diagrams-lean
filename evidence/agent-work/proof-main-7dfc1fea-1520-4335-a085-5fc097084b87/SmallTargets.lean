import MackeyDiagrams
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Module.Submodule.Range

open CategoryTheory

namespace ChoiceFreeWatts

universe v w j

def explicitRange {B S T : Type*} [Ring B] [AddCommGroup S] [Module B S]
    [AddCommGroup T] [Module B T] (f : S →ₗ[B] T) : Submodule B T where
  carrier := { t | ∃ s, f s = t }
  zero_mem' := ⟨0, map_zero f⟩
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, map_add f s t⟩
  smul_mem' := by
    rintro b _ ⟨s, rfl⟩
    exact ⟨b • s, f.map_smul b s⟩

section

variable {B : Type v} [Ring B]
variable {I : Type j} {D : I → ModuleCat.{w} B} {P : ModuleCat.{w} B}

/-- Step 2.1 with the target universe from the reviewed hypothesis. Applying
its uniqueness to the image detects joint surjectivity, without using an
inverse or resizing the full tensor carrier into the target universe. -/
theorem surjectiveOfPreservedCoproduct (ι : ∀ i, D i ⟶ P)
    (coprod : ∀ (Q : ModuleCat.{w} B) (legs : ∀ i, D i ⟶ Q),
      ∃! d : P ⟶ Q, ∀ i, ι i ≫ d = legs i)
    {T : Type*} [AddCommGroup T] [Module B T] (τ : T →ₗ[B] P)
    (legs : ∀ i, D i →ₗ[B] T) (hlegs : ∀ i, τ.comp (legs i) = (ι i).hom) :
    Function.Surjective τ := by
  let Q := ModuleCat.of B (explicitRange τ)
  let inc : Q ⟶ P := ModuleCat.ofHom (explicitRange τ).subtype
  let lifts (i : I) : D i ⟶ Q :=
    ModuleCat.ofHom ((ι i).hom.codRestrict (explicitRange τ) fun d =>
      ⟨legs i d, DFunLike.congr_fun (hlegs i) d⟩)
  have lifts_inc (i : I) : lifts i ≫ inc = ι i := by
    apply ModuleCat.hom_ext
    rfl
  obtain ⟨k, hk, _⟩ := coprod Q lifts
  obtain ⟨l, _, hl⟩ := coprod P ι
  have equal : k ≫ inc = 𝟙 P := by
    apply (hl (k ≫ inc) ?_).trans (hl (𝟙 P) ?_).symm
    · intro i
      rw [← Category.assoc, hk i, lifts_inc]
    · intro i
      exact Category.comp_id (ι i)
  intro p
  have hp : ((k.hom p : Q) : P) = p := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom equal) p
  exact hp ▸ (k.hom p).property

end

section

variable {B : Type v} [Ring B]
variable {L P X : ModuleCat.{w} B}

/-- The range of the preserved cokernel map lies in the tested target
universe. Cokernel uniqueness in Step 2.2 implies surjectivity by
factorization through this range. -/
theorem cokernelSurjective (f : L ⟶ P) (q : P ⟶ X)
    (zero : f ≫ q = ModuleCat.ofHom 0)
    (cokern : ∀ (Z : ModuleCat.{w} B) (g : P ⟶ Z),
      f ≫ g = ModuleCat.ofHom 0 → ∃! d : X ⟶ Z, q ≫ d = g) :
    Function.Surjective q.hom := by
  let Q := ModuleCat.of B (explicitRange q.hom)
  let inc : Q ⟶ X := ModuleCat.ofHom (explicitRange q.hom).subtype
  let π : P ⟶ Q := ModuleCat.ofHom (q.hom.codRestrict (explicitRange q.hom) fun x => ⟨x, rfl⟩)
  have hinc : π ≫ inc = q := by
    apply ModuleCat.hom_ext
    rfl
  have hπ : f ≫ π = ModuleCat.ofHom 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom zero) p
  obtain ⟨back, hback, _⟩ := cokern Q π hπ
  obtain ⟨d, _, hd⟩ := cokern X q zero
  have hinv : back ≫ inc = 𝟙 X := by
    apply (hd (back ≫ inc) ?_).trans (hd (𝟙 X) (Category.comp_id q)).symm
    rw [← Category.assoc, hback, hinc]
  intro x
  have hx : ((back.hom x : Q) : X) = x :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hinv) x
  exact hx ▸ (back.hom x).property

end
end ChoiceFreeWatts

#print axioms ChoiceFreeWatts.surjectiveOfPreservedCoproduct
#print axioms ChoiceFreeWatts.cokernelSurjective
