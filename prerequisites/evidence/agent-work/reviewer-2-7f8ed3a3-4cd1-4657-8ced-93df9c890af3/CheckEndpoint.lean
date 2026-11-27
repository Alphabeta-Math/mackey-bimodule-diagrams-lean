import NotesProofs.WattsSupport

universe u v w s

def checkedRegularModuleTensorUnits : Prop :=
  ∀ (R : Type u) [Ring R],
    let regularRight := fun (r x : R) => x * r
    let LeftTensor := fun (M : ModuleCat.{v} R) => ChoiceFreeWatts.Tensor regularRight M
    letI _leftAdd (M : ModuleCat.{v} R) : AddCommGroup (LeftTensor M) :=
      ChoiceFreeWatts.tensorAddCommGroup (X := M) regularRight
    letI _leftModule (M : ModuleCat.{v} R) : Module R (LeftTensor M) :=
      ChoiceFreeWatts.outerModule (X := M) regularRight (fun (r a x : R) => mul_assoc a x r)
    let leftPure := fun (M : ModuleCat.{v} R) (r : R) (m : M) =>
      (ChoiceFreeWatts.pure regularRight r m : LeftTensor M)
    let RightMod := ModuleCat.{w} (MulOpposite R)
    let right := fun (B : RightMod) (r : R) (b : B) => MulOpposite.op r • b
    let RightTensor := fun (B : RightMod) => ChoiceFreeWatts.Tensor (right B) R
    letI _rightAdd (B : RightMod) : AddCommGroup (RightTensor B) :=
      ChoiceFreeWatts.tensorAddCommGroup (X := R) (right B)
    let rightPure := fun (B : RightMod) (b : B) (r : R) =>
      (ChoiceFreeWatts.pure (right B) b r : RightTensor B)
    (∃ leftUnit : ∀ M : ModuleCat.{v} R, LinearEquiv (RingHom.id R) (LeftTensor M) M,
      (∀ (M : ModuleCat.{v} R) (r : R) (m : M),
        leftUnit M (leftPure M r m) = r • m) ∧
      (∀ {M N : ModuleCat.{v} R} (f : Quiver.Hom M N),
        ∃ tf : LinearMap (RingHom.id R) (LeftTensor M) (LeftTensor N),
          (∀ (r : R) (m : M), tf (leftPure M r m) = leftPure N r (f m)) ∧
          (∀ z : LeftTensor M, leftUnit N (tf z) = f (leftUnit M z)))) ∧
    (∃ rightModule : ∀ B : RightMod, Module (MulOpposite R) (RightTensor B),
      letI _rightModuleInstance (B : RightMod) : Module (MulOpposite R) (RightTensor B) :=
        rightModule B
      ∃ rightUnit : ∀ B : RightMod, LinearEquiv (RingHom.id (MulOpposite R)) (RightTensor B) B,
        (∀ (B : RightMod) (b : B) (r : R), rightUnit B (rightPure B b r) = right B r b) ∧
        (∀ (B : RightMod) (a r : R) (b : B),
          MulOpposite.op a • rightPure B b r = rightPure B b (r * a)) ∧
        (∀ {B C : RightMod} (g : Quiver.Hom B C),
          ∃ tg : LinearMap (RingHom.id (MulOpposite R)) (RightTensor B) (RightTensor C),
            (∀ (b : B) (r : R), tg (rightPure B b r) = rightPure C (g b) r) ∧
            (∀ z : RightTensor B, rightUnit C (tg z) = g (rightUnit B z))) ∧
        (∀ (S : Type s) [Ring S] (B : RightMod) [Module S B]
            [SMulCommClass (MulOpposite R) S B],
          letI : Module S (RightTensor B) :=
            ChoiceFreeWatts.outerModule (X := R) (right B)
              (fun (r : R) (a : S) (b : B) => smul_comm (MulOpposite.op r) a b)
          SMulCommClass (MulOpposite R) S (RightTensor B) ∧
          (∀ (a : S) (z : RightTensor B), rightUnit B (a • z) = a • rightUnit B z)))
