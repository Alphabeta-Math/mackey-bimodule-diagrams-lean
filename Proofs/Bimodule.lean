import Mathlib.Algebra.Module.Opposite
import MackeyDiagrams

set_option maxHeartbeats 2000000

universe u v w

noncomputable def Bimodule : (Prod
  (∀ (S : Type u) (R : Type v) (N : Type w) [Ring S] [Ring R] [AddCommGroup N],
    Type (max u v w))
  (Prod
    (∀ (R : Type v) [Ring R],
      Subtype (fun B : Sigma (fun left : Module R R =>
        Subtype (fun right : Module (MulOpposite R) R =>
          letI : SMul R R := left.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          letI : SMul (MulOpposite R) R := right.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          SMulCommClass (MulOpposite R) R R)) =>
        letI : SMul R R := B.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        letI : SMul (MulOpposite R) R := B.2.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        (∀ s n : R, s • n = s * n) ∧
        (∀ n r : R, MulOpposite.op r • n = n * r)))
    (∀ (R : Type v) (N : Type w) [CommRing R] [AddCommGroup N] [left : Module R N],
      Subtype (fun B : Sigma (fun l : Module R N =>
        Subtype (fun right : Module (MulOpposite R) N =>
          letI : SMul R N := l.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          letI : SMul (MulOpposite R) N := right.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          SMulCommClass (MulOpposite R) R N)) =>
        B.1 = left ∧
        (letI : SMul (MulOpposite R) N := B.2.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
         ∀ (r : R) (n : N), MulOpposite.op r • n = r • n))))) :=
(⟨(fun S R N _ _ _ =>
    Sigma (fun left : Module S N =>
      Subtype (fun right : Module (MulOpposite R) N =>
        letI : SMul S N := left.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        letI : SMul (MulOpposite R) N := right.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        SMulCommClass (MulOpposite R) S N))),
  ⟨(fun R _ =>
      let left : Module R R := Semiring.toModule
      let right : Module (MulOpposite R) R := Semiring.toOppositeModule
      letI : SMul R R := left.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      letI : SMul (MulOpposite R) R := right.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      ⟨⟨left, ⟨right,
          show SMulCommClass (MulOpposite R) R R from Semigroup.opposite_smulCommClass⟩⟩,
        ⟨(fun _ _ => rfl), (fun _ _ => rfl)⟩⟩),
    (fun R N _ _ left =>
      letI : Module R N := left
      let right : Module (MulOpposite R) N :=
        Module.compHom N (RingHom.fromOpposite (RingHom.id R) (fun a b => mul_comm a b))
      letI : SMul R N := left.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      letI : SMul (MulOpposite R) N := right.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      ⟨⟨left, ⟨right, show SMulCommClass (MulOpposite R) R N from
          ⟨fun r s n => show MulOpposite.unop r • (s • n) = s • (MulOpposite.unop r • n) from
            by
              simpa only [← mul_smul] using
                congrArg (fun a : R => a • n) (mul_comm (MulOpposite.unop r) s)⟩⟩⟩,
        ⟨rfl, (fun _ _ => rfl)⟩⟩)⟩⟩)
