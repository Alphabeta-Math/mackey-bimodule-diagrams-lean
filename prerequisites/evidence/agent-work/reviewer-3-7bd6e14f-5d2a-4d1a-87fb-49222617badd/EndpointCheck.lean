import Mathlib.Algebra.Module.Opposite
import NotesProofs.ConcreteTensorFunctor

universe u

def checkedEndpoint : Prop :=
  ∀ (R : Type u) [Ring R],
    (let F := NotesProofs.concreteTensorFunctor (R := R) (S := R) R
     ∃ unit : CategoryTheory.Iso F (CategoryTheory.Functor.id (ModuleCat.{u} R)),
       ∀ (M : ModuleCat.{u} R) (r : R) (m : M),
         (unit.hom.app M) (NotesProofs.concretePure (R := R) (M := R) r m) = r • m) ∧
    (∀ (S T : Type u) [Ring S] [Ring T]
        (B C : Type u) [AddCommGroup B] [AddCommGroup C]
        [Module S B] [Module (MulOpposite R) B] [SMulCommClass (MulOpposite R) S B]
        [Module T C] [Module (MulOpposite S) C] [SMulCommClass (MulOpposite S) T C],
      let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
      let TC := NotesProofs.concreteTensorFunctor (R := S) (S := T) C
      let CB := TC.obj (ModuleCat.of S B)
      let pureCB := fun (c : C) (b : B) =>
        (NotesProofs.concretePure (R := S) (M := C) c b : CB)
      (∀ (t : T) (c : C) (b : B), (ModuleCat.isModule CB).smul t (pureCB c b) = pureCB (t • c) b) ∧
      (∃ rightCB : Module (MulOpposite R) CB,
        letI := rightCB
        (∀ (r : R) (c : C) (b : B),
          rightCB.smul (MulOpposite.op r) (pureCB c b) = pureCB c (MulOpposite.op r • b)) ∧
        (∃ commute : SMulCommClass (MulOpposite R) T CB,
          letI := commute
          let TCB := NotesProofs.concreteTensorFunctor (R := R) (S := T) (CB : Type u)
          ∃ assoc : CategoryTheory.Iso (CategoryTheory.Functor.comp TB TC) TCB,
            ∀ (M : ModuleCat.{u} R) (c : C) (b : B) (m : M),
              (assoc.hom.app M) (NotesProofs.concretePure (R := S) (M := C) c
                (NotesProofs.concretePure (R := R) (M := B) b m)) =
                NotesProofs.concretePure (R := R) (M := (CB : Type u)) (pureCB c b) m)))

#print axioms checkedEndpoint

example (R : Type u) [Ring R] (r x : R) :
    NotesProofs.rightAction (R := R) r x = x * r := rfl
