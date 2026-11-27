import WattsFoundation.General.OriginalBimoduleRepack

set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace WattsFoundation.General
universe u v
variable (R S : Type u) [Ring R] [Ring S]
variable (M : OriginalBimodule.{u,v} R S) (N : ModuleCat.{max u v} S) (e : M.1 ≅ N)

theorem repackRight_inv (n : N) (r : R) :
    e.inv (originalRight R S (repackBimodule R S M N e) n r) =
      originalRight R S M (e.inv n) r := by
  calc
    _ = e.inv (originalRight R S (repackBimodule R S M N e) (e.hom (e.inv n)) r) := by simp
    _ = e.inv (e.hom (originalRight R S M (e.inv n) r)) := by rw [repackRight_hom]
    _ = _ := by simp

noncomputable def repackIso : M ≅ repackBimodule R S M N e where
  hom := ⟨e.hom.hom, fun m r => (repackRight_hom R S M N e m r).symm⟩
  inv := ⟨e.inv.hom, fun n r => repackRight_inv R S M N e n r⟩
  hom_inv_id := by
    apply Subtype.ext
    ext m
    exact e.toLinearEquiv.left_inv m
  inv_hom_id := by
    apply Subtype.ext
    ext n
    exact e.toLinearEquiv.right_inv n

end WattsFoundation.General
