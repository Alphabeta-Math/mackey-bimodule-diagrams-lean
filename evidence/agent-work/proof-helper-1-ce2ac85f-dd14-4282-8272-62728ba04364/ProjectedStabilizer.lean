import Proofs.ParabolicRightOrbitMultiplicity
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Basic

namespace SpanAudit

theorem projectedStabilizer_normalize {U G F X : Type*}
    [Group U] [Group G] [Group F] [MulAction (G × F) X]
    (ι : F →* U) (g : G) (x : X) :
    (MulAction.stabilizer (G × F) ((g, (1 : F)) • x)).map
        (ι.comp (MonoidHom.snd G F)) =
      (MulAction.stabilizer (G × F) x).map (ι.comp (MonoidHom.snd G F)) := by
  let f := ι.comp (MonoidHom.snd G F)
  have hf : f.comp (MulAut.conj (g, (1 : F))).toMonoidHom = f := by
    ext q
    change ι (1 * q.2 * 1⁻¹) = ι q.2
    simp
  change (MulAction.stabilizer (G × F) ((g, (1 : F)) • x)).map f = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, hf]

theorem indexTower {U : Type*} [Group U] {K L P : Subgroup U}
    [Finite P] (hKL : K ≤ L) (hLP : L ≤ P) :
    0 < L.relIndex P ∧ L.relIndex P ∣ K.relIndex P ∧ L.relIndex P ≤ K.relIndex P := by
  haveI : (L.subgroupOf P).FiniteIndex := inferInstance
  haveI : L.IsFiniteRelIndex P := ⟨Subgroup.index_ne_zero⟩
  have hpos : 0 < L.relIndex P := Subgroup.relIndex_pos
  have hdvd : L.relIndex P ∣ K.relIndex P :=
    ⟨K.relIndex L, (Subgroup.relIndex_mul_relIndex K L P hKL hLP).symm.trans (Nat.mul_comm _ _)⟩
  haveI : (K.subgroupOf P).FiniteIndex := inferInstance
  haveI : K.IsFiniteRelIndex P := ⟨Subgroup.index_ne_zero⟩
  exact ⟨hpos, hdvd, Nat.le_of_dvd Subgroup.relIndex_pos hdvd⟩

theorem indexOne {U : Type*} [Group U] {L P : Subgroup U} {parabolic : Subgroup U → Prop}
    (h : IsGreatest {K : Subgroup U | K ≤ P ∧ parabolic K} L) :
    L.relIndex P = 1 ↔ parabolic P := by
  rw [Subgroup.relIndex_eq_one]
  exact ⟨fun hh => le_antisymm h.1.1 hh ▸ h.1.2, fun hP => h.2 ⟨le_rfl, hP⟩⟩

end SpanAudit

#print axioms ParabolicRightOrbitMultiplicity
#print axioms ExtremalParabolicsOfFiniteGroup
#print axioms FiniteParabolicClosure
#print axioms RightOrbitDiagramFromProjectedStabilizer
#print axioms SpanAudit.projectedStabilizer_normalize
#print axioms SpanAudit.indexTower

section IntegralMultiplicity
theorem nat_eq_of_ulift_int_cast_eq (n m : Nat) (h : (n : ULift Int) = (m : ULift Int)) : n = m := by
  have hd := congrArg ULift.down h
  change (n : Int) = (m : Int) at hd
  exact Nat.cast_injective hd
end IntegralMultiplicity

#print axioms nat_eq_of_ulift_int_cast_eq
