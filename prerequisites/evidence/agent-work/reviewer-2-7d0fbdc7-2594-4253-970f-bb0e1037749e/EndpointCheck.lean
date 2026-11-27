import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Isomorphisms

open CategoryTheory CategoryTheory.Limits

universe u v

axiom TranslatedEndpoint :
  ∀ (R : Type _) [Ring R] {M N : ModuleCat.{_} R} (f : Quiver.Hom M N),
    let g := ModuleCat.Hom.hom f
    let ker := LinearMap.ker g
    let im := LinearMap.range g
    (∀ m : M, m ∈ ker ↔ g m = 0) ∧
    (∀ n : N, n ∈ im ↔ ∃ m : M, g m = n) ∧
    (∃ h : CategoryTheory.CategoryStruct.comp
        (ModuleCat.ofHom (Submodule.subtype ker)) f = 0,
      Nonempty (CategoryTheory.Limits.IsLimit
        (CategoryTheory.Limits.KernelFork.ofι (ModuleCat.ofHom (Submodule.subtype ker)) h))) ∧
    (∃ h : CategoryTheory.CategoryStruct.comp f (ModuleCat.ofHom (Submodule.mkQ im)) = 0,
      Nonempty (CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.CokernelCofork.ofπ (ModuleCat.ofHom (Submodule.mkQ im)) h))) ∧
    (∃ e : LinearEquiv (RingHom.id R) (HasQuotient.Quotient M ker) ↥im,
      ∀ m : M, (e (Submodule.mkQ ker m) : N) = g m) ∧
    (CategoryTheory.Mono f ↔ Function.Injective ⇑g) ∧
    (CategoryTheory.Epi f ↔ Function.Surjective ⇑g)

def SourceEndpoint : Prop :=
  ∀ (R : Type u) [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N),
  let map : M →ₗ[R] N := f.hom
  let kernel := LinearMap.ker map
  let image := LinearMap.range map
  let inclusion : ModuleCat.of R kernel ⟶ M := ModuleCat.ofHom kernel.subtype
  let projection : N ⟶ ModuleCat.of R (N ⧸ image) := ModuleCat.ofHom image.mkQ
  (∀ m : M, m ∈ kernel ↔ map m = 0) ∧
  (∀ n : N, n ∈ image ↔ ∃ m : M, map m = n) ∧
  (∃ condition : inclusion ≫ f = 0,
    Nonempty (IsLimit (KernelFork.ofι inclusion condition))) ∧
  (∃ condition : f ≫ projection = 0,
    Nonempty (IsColimit (CokernelCofork.ofπ projection condition))) ∧
  (∃ canonical : (M ⧸ kernel) ≃ₗ[R] image,
    ∀ m : M, (canonical (kernel.mkQ m) : N) = map m) ∧
  (Mono f ↔ Function.Injective map) ∧
  (Epi f ↔ Function.Surjective map)

set_option pp.universes true in
#check @TranslatedEndpoint

example : SourceEndpoint.{u, v} := TranslatedEndpoint.{u, v}
