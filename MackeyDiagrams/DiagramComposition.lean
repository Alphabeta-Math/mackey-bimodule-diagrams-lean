import MackeyDiagrams.DiagramVectorSpace

namespace MackeyDiagrams.DiagramVectorSpace
universe u v
variable {U : Type u} [Group U] {K H : Subgroup U}
variable (R : Type v) [CommRing R] (p q t : Word K H)

noncomputable def rawStack (x : Expressions R p q) (y : Expressions R q t) : Expressions R p t := by
  classical
  exact x.sum fun d c => y.sum fun e b => (c * b) • Finsupp.single (.vertical d e) 1

theorem expand_eval (x : Expressions R p q) :
    evaluate R p q x = ∑ d ∈ x.support, x d • d.interpret.eval.toLinearMap := by
  rw [evaluate, freeLift, Finsupp.lsum_apply]
  rfl

theorem rawStack_eval (x : Expressions R p q) (y : Expressions R q t) :
    evaluate R p t (rawStack R p q t x y) =
      (evaluate R q t y).comp (evaluate R p q x) := by
  classical
  rw [expand_eval R p q x, expand_eval R q t y]
  apply LinearMap.ext
  intro z
  simp only [rawStack, Finsupp.sum, map_sum, map_smul, singleton_eval, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.sum_apply, map_sum, map_smul]
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  change (x d * y e) • e.interpret.eval.toLinearMap (d.interpret.eval.toLinearMap z) =
    (x d * y e) • e.interpret.eval.toLinearMap (d.interpret.eval.toLinearMap z)
  rfl

noncomputable def representative (x : MapClasses R p q) : Expressions R p q :=
  Classical.choose ((Submodule.Quotient.mk_surjective (evaluate R p q).ker) x)

@[simp] theorem representative_mk (x : MapClasses R p q) :
    (Submodule.Quotient.mk (representative R p q x) : MapClasses R p q) = x :=
  Classical.choose_spec ((Submodule.Quotient.mk_surjective (evaluate R p q).ker) x)

noncomputable def classEval (x : MapClasses R p q) :
    (p.basis.carrier →₀ R) →ₗ[R] (q.basis.carrier →₀ R) :=
  evaluate R p q (representative R p q x)

@[simp] theorem classEval_mk (x : Expressions R p q) :
    classEval R p q (Submodule.Quotient.mk x) = evaluate R p q x := by
  apply (quotient_eq_iff R p q _ _).1
  exact representative_mk R p q (Submodule.Quotient.mk x)

theorem classEval_injective : Function.Injective (classEval R p q) := by
  intro x y h
  have same := (quotient_eq_iff R p q (representative R p q x) (representative R p q y)).2 h
  simpa only [representative_mk] using same

theorem classEval_add (x y : MapClasses R p q) :
    classEval R p q (x + y) = classEval R p q x + classEval R p q y := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      change classEval R p q (Submodule.Quotient.mk (a + b)) = _
      simp only [classEval_mk, map_add]

theorem classEval_smul (c : R) (x : MapClasses R p q) :
    classEval R p q (c • x) = c • classEval R p q x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    change classEval R p q (Submodule.Quotient.mk (c • a)) = _
    simp only [classEval_mk, map_smul]

noncomputable def stack (x : MapClasses R p q) (y : MapClasses R q t) : MapClasses R p t :=
  Submodule.Quotient.mk (rawStack R p q t (representative R p q x) (representative R q t y))

@[simp] theorem classEval_stack (x : MapClasses R p q) (y : MapClasses R q t) :
    classEval R p t (stack R p q t x y) = (classEval R q t y).comp (classEval R p q x) := by
  rw [stack, classEval_mk, rawStack_eval]
  change _ = (evaluate R q t (representative R q t y)).comp (evaluate R p q (representative R p q x))
  rfl

noncomputable def identityClass : MapClasses R p p :=
  Submodule.Quotient.mk (Finsupp.single (.ordinary (.id p)) 1)

@[simp] theorem classEval_identity : classEval R p p (identityClass R p) = LinearMap.id := by
  rw [identityClass, classEval_mk, singleton_eval]
  rfl

@[simp] theorem stack_singletons (d : LabelledDrawing R p q) (e : LabelledDrawing R q t) :
    stack R p q t (Submodule.Quotient.mk (Finsupp.single d 1))
      (Submodule.Quotient.mk (Finsupp.single e 1)) =
        Submodule.Quotient.mk (Finsupp.single (.vertical d e) 1) := by
  apply classEval_injective R p t
  simp only [classEval_stack, classEval_mk, singleton_eval]
  rfl

theorem stack_add_left (x x' : MapClasses R p q) (y : MapClasses R q t) :
    stack R p q t (x + x') y = stack R p q t x y + stack R p q t x' y := by
  apply classEval_injective R p t
  simp only [classEval_stack, classEval_add, LinearMap.comp_add]

theorem stack_add_right (x : MapClasses R p q) (y y' : MapClasses R q t) :
    stack R p q t x (y + y') = stack R p q t x y + stack R p q t x y' := by
  apply classEval_injective R p t
  simp only [classEval_stack, classEval_add, LinearMap.add_comp]

theorem stack_smul_left (c : R) (x : MapClasses R p q) (y : MapClasses R q t) :
    stack R p q t (c • x) y = c • stack R p q t x y := by
  apply classEval_injective R p t
  simp only [classEval_stack, classEval_smul, LinearMap.comp_smul]

theorem stack_smul_right (c : R) (x : MapClasses R p q) (y : MapClasses R q t) :
    stack R p q t x (c • y) = c • stack R p q t x y := by
  apply classEval_injective R p t
  simp only [classEval_stack, classEval_smul, LinearMap.smul_comp]

theorem stack_assoc (s : Word K H) (x : MapClasses R p q)
    (y : MapClasses R q t) (z : MapClasses R t s) :
    stack R p t s (stack R p q t x y) z = stack R p q s x (stack R q t s y z) := by
  apply classEval_injective R p s
  simp only [classEval_stack, LinearMap.comp_assoc]

theorem identity_stack (x : MapClasses R p q) :
    stack R p p q (identityClass R p) x = x := by
  apply classEval_injective R p q
  simp only [classEval_stack, classEval_identity, LinearMap.comp_id]

theorem stack_identity (x : MapClasses R p q) :
    stack R p q q x (identityClass R q) = x := by
  apply classEval_injective R p q
  simp only [classEval_stack, classEval_identity, LinearMap.id_comp]

end MackeyDiagrams.DiagramVectorSpace
