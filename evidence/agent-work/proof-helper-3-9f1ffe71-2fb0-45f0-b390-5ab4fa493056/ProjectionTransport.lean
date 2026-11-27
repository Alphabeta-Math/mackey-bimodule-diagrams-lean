import Mathlib.GroupTheory.GroupAction.Basic

universe u
namespace OrbitAlgebra

variable {G F U : Type u} [Group G] [Group F] [Group U]
variable {Z : Type*} [MulAction (G × F) Z]

theorem projected_left_smul (proj : F →* U) (g : G) (z : Z) :
    (MulAction.stabilizer (G × F) ((g, (1 : F)) • z)).map
      (proj.comp (MonoidHom.snd G F)) =
      (MulAction.stabilizer (G × F) z).map (proj.comp (MonoidHom.snd G F)) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map]
  congr 1
  ext q
  simp [MulAut.conj_apply]

end OrbitAlgebra

#print axioms OrbitAlgebra.projected_left_smul
