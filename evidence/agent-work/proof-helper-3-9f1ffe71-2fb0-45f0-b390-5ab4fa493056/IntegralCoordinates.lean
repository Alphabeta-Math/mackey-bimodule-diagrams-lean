import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Span

noncomputable section
namespace OrbitAlgebra

variable {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module (ULift ℤ) M]

def reduce (b : Module.Basis ι (ULift ℤ) M) (n : ι → Nat) :
    M →+ ∀ i, ZMod (n i) where
  toFun m i := ((b.repr m i).down : ZMod (n i))
  map_zero' := by ext i; simp
  map_add' m m' := by ext i; simp

theorem reduce_surjective (b : Module.Basis ι (ULift ℤ) M) (n : ι → Nat) :
    Function.Surjective (reduce b n) := by
  intro t
  choose a ha using fun i => ZMod.intCast_surjective (n := n i) (t i)
  refine ⟨b.equivFun.symm (fun i => ULift.up (a i)), ?_⟩
  funext i
  have h := congrFun (b.equivFun.apply_symm_apply (fun i => ULift.up (a i))) i
  change b.repr (b.equivFun.symm (fun i => ULift.up (a i))) i = ULift.up (a i) at h
  exact (congrArg (fun x : ULift ℤ => (x.down : ZMod (n i))) h).trans (ha i)

theorem reduce_mem_ker (b : Module.Basis ι (ULift ℤ) M) (n : ι → Nat) (m : M) :
    m ∈ (reduce b n).ker ↔
      ∀ i, b.repr m i ∈ Ideal.span ({(n i : ULift ℤ)} : Set (ULift ℤ)) := by
  change (fun i => ((b.repr m i).down : ZMod (n i))) = 0 ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro i
  change ((b.repr m i).down : ZMod (n i)) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨ULift.up k, ULift.ext hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k.down, congrArg ULift.down hk⟩

def quotientCoordinates (b : Module.Basis ι (ULift ℤ) M) (n : ι → Nat) :
    M ⧸ (reduce b n).ker ≃+ DirectSum ι (fun i => ZMod (n i)) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (reduce b n) (reduce_surjective b n)).trans
    (DirectSum.addEquivProd (fun i => ZMod (n i))).symm

omit [Fintype ι] in
theorem span_uliftInt_eq_closure (S : Set M) :
    (Submodule.span (ULift ℤ) S).toAddSubgroup = AddSubgroup.closure S := by
  apply Eq.symm
  refine AddSubgroup.closure_eq_of_le _ Submodule.subset_span ?_
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact AddSubgroup.subset_closure hx
  | zero => exact AddSubgroup.zero_mem _
  | add x y hx hy ihx ihy => exact AddSubgroup.add_mem _ ihx ihy
  | smul r x hx ih =>
      have hr : (r.down : ULift ℤ) = r := ULift.ext rfl
      rw [← hr, Int.cast_smul_eq_zsmul]
      exact AddSubgroup.zsmul_mem _ ih r.down

end OrbitAlgebra

#print axioms OrbitAlgebra.reduce_mem_ker
#print axioms OrbitAlgebra.quotientCoordinates
#print axioms OrbitAlgebra.span_uliftInt_eq_closure
