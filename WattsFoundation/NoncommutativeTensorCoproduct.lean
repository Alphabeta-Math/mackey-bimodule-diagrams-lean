import WattsFoundation.BalancedCoproductAssembly
import WattsFoundation.NoncommutativeTensorCokernel

/-! Universal-property proof of coproduct preservation by balanced tensors. -/

namespace WattsFoundation

universe u v

variable {R S : Type u} [Ring R] [Ring S]
variable {M C TC : Type v} [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [AddCommGroup C] [Module R C] [AddCommGroup TC] [Module S TC]
variable {I : Type v} (X T : I → Type v)
variable [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]
variable [∀ i, AddCommGroup (T i)] [∀ i, Module S (T i)]

/-- Tensoring carries an additive coproduct to an S-module coproduct, provided
the supplied objects have the balanced-map universal property. -/
theorem balanced_tensor_preserves_coproduct
    (inj : ∀ i, X i →ₗ[R] C)
    (coprod : ∀ (D : Type v) [AddCommGroup D] (legs : ∀ i, X i →+ D),
      ∃! d : C →+ D, ∀ i x, d (inj i x) = legs i x)
    (p : ∀ i, M →+ (X i →+ T i)) (pc : M →+ (C →+ TC))
    (tensor : ∀ i, IsBalancedTensor (R := R) (S := S) (p i))
    (tensorC : IsBalancedTensor (R := R) (S := S) pc)
    (tinj : ∀ i, T i →ₗ[S] TC)
    (tinj_pure : ∀ i m x, tinj i (p i m x) = pc m (inj i x)) :
    ∀ (D : Type v) [AddCommGroup D] [Module S D] (legs : ∀ i, T i →ₗ[S] D),
      ∃! h : TC →ₗ[S] D, ∀ i t, h (tinj i t) = legs i t := by
  intro D _ _ legs
  let b (i : I) : M →+ (X i →+ D) :=
    { toFun := fun m => (legs i).toAddMonoidHom.comp (p i m)
      map_zero' := by ext x; simp
      map_add' := by intro m n; ext x; simp }
  have b_balance : ∀ (i : I) (r : R) (m : M) (x : X i),
      b i (MulOpposite.op r • m) x = b i m (r • x) := by
    intro i r m x
    change legs i (p i (MulOpposite.op r • m) x) = legs i (p i m (r • x))
    rw [(tensor i).1]
  have b_outer : ∀ (i : I) (s : S) (m : M) (x : X i),
      b i (s • m) x = s • b i m x := by
    intro i s m x
    change legs i (p i (s • m) x) = s • legs i (p i m x)
    rw [(tensor i).2.1, map_smul]
  obtain ⟨c, ⟨c_inj, c_balance, c_outer⟩, _⟩ :=
    balanced_coproduct_assembly X inj coprod b b_balance b_outer
  obtain ⟨h, h_pure, h_unique⟩ := tensorC.2.2 D c c_balance c_outer
  refine ⟨h, ?_, ?_⟩
  · intro i t
    have factor_pure : ∀ m x, (h.comp (tinj i)) (p i m x) = b i m x := by
      intro m x
      change h (tinj i (p i m x)) = b i m x
      rw [tinj_pure, h_pure, c_inj]
    have legs_pure : ∀ m x, legs i (p i m x) = b i m x := by intro m x; rfl
    obtain ⟨g, hg, unique⟩ := (tensor i).2.2 D (b i) (b_balance i) (b_outer i)
    have eqmaps : h.comp (tinj i) = legs i :=
      (unique _ factor_pure).trans (unique _ legs_pure).symm
    exact DFunLike.congr_fun eqmaps t
  · intro k hk
    apply h_unique
    intro m x
    let kmap : C →+ D := k.toAddMonoidHom.comp (pc m)
    obtain ⟨g, hg, unique⟩ := coprod D (fun i => b i m)
    have hkmap : ∀ i y, kmap (inj i y) = b i m y := by
      intro i y
      change k (pc m (inj i y)) = legs i (p i m y)
      rw [← tinj_pure, hk]
    have hcmap : ∀ i y, c m (inj i y) = b i m y := by intro i y; exact c_inj i m y
    have eqmaps : kmap = c m := (unique _ hkmap).trans (unique _ hcmap).symm
    exact DFunLike.congr_fun eqmaps x

#print axioms balanced_tensor_preserves_coproduct

end WattsFoundation
