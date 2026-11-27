import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Opposite

/-! Balanced maps out of a coproduct assemble from their components. -/

namespace NotesProofs

universe u v

variable {R S : Type u} [Ring R] [Ring S]
variable {M C D : Type v} [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [AddCommGroup C] [Module R C] [AddCommGroup D] [Module S D]
variable {I : Type v} (X : I → Type v) [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]

/-- Balanced, outer-linear maps on the summands assemble uniquely into a
balanced, outer-linear map on their coproduct. The coproduct is expressed in
the underlying additive groups, as is true for a module direct sum. -/
theorem balanced_coproduct_assembly
    (inj : ∀ i, X i →ₗ[R] C)
    (coprod : ∀ (E : Type v) [AddCommGroup E] (legs : ∀ i, X i →+ E),
      ∃! d : C →+ E, ∀ i x, d (inj i x) = legs i x)
    (b : ∀ i, M →+ (X i →+ D))
    (balance : ∀ (i : I) (r : R) (m : M) (x : X i),
      b i (MulOpposite.op r • m) x = b i m (r • x))
    (outer : ∀ (i : I) (s : S) (m : M) (x : X i),
      b i (s • m) x = s • b i m x) :
    ∃! c : M →+ (C →+ D),
      (∀ i m x, c m (inj i x) = b i m x) ∧
      (∀ (r : R) (m : M) (x : C),
        c (MulOpposite.op r • m) x = c m (r • x)) ∧
      (∀ (s : S) (m : M) (x : C), c (s • m) x = s • c m x) := by
  classical
  have ext_coprod (g h : C →+ D) (eq : ∀ i x, g (inj i x) = h (inj i x)) : g = h := by
    obtain ⟨d, hd, unique⟩ := coprod D (fun i => g.comp (inj i).toAddMonoidHom)
    have hg : ∀ i x, g (inj i x) = (g.comp (inj i).toAddMonoidHom) x := by intros; rfl
    have hh : ∀ i x, h (inj i x) = (g.comp (inj i).toAddMonoidHom) x := by
      intro i x
      exact (eq i x).symm
    exact (unique g hg).trans (unique h hh).symm
  let d (m : M) : C →+ D := Classical.choose (coprod D (fun i => b i m))
  have d_spec (m : M) (i : I) (x : X i) : d m (inj i x) = b i m x :=
    (Classical.choose_spec (coprod D (fun i => b i m))).1 i x
  let c : M →+ (C →+ D) := AddMonoidHom.mk' d (by
    intro m n
    apply ext_coprod
    intro i x
    change d (m + n) (inj i x) = d m (inj i x) + d n (inj i x)
    rw [d_spec, d_spec, d_spec, map_add]
    rfl)
  have c_inj (i : I) (m : M) (x : X i) : c m (inj i x) = b i m x := d_spec m i x
  refine ⟨c, ⟨c_inj, ?_, ?_⟩, ?_⟩
  · intro r m
    have eq : c (MulOpposite.op r • m) =
        (c m).comp (DistribSMul.toAddMonoidHom C r) := by
      apply ext_coprod
      intro i x
      change c (MulOpposite.op r • m) (inj i x) = c m (r • inj i x)
      rw [← (inj i).map_smul, c_inj, c_inj, balance]
    exact fun x => DFunLike.congr_fun eq x
  · intro s m
    have eq : c (s • m) = (DistribSMul.toAddMonoidHom D s).comp (c m) := by
      apply ext_coprod
      intro i x
      change c (s • m) (inj i x) = s • c m (inj i x)
      rw [c_inj, c_inj, outer]
    exact fun x => DFunLike.congr_fun eq x
  · intro c' hc'
    ext m x
    have eq : c' m = c m := by
      apply ext_coprod
      intro i y
      rw [hc'.1, c_inj]
    exact DFunLike.congr_fun eq x

#print axioms balanced_coproduct_assembly

end NotesProofs
