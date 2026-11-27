import Mathlib.CategoryTheory.Functor.Category
import NotesProofs.ConcreteTensorBimoduleMap

universe u

def CheckedEndpoint : Prop :=
  ∀ (R S T : Type u) [Ring R] [Ring S] [Ring T]
      (B B' C C' : Type u)
      [AddCommGroup B] [Module S B] [Module (MulOpposite R) B]
      [SMulCommClass (MulOpposite R) S B]
      [AddCommGroup B'] [Module S B'] [Module (MulOpposite R) B']
      [SMulCommClass (MulOpposite R) S B']
      [AddCommGroup C] [Module T C] [Module (MulOpposite S) C]
      [SMulCommClass (MulOpposite S) T C]
      [AddCommGroup C'] [Module T C'] [Module (MulOpposite S) C']
      [SMulCommClass (MulOpposite S) T C'],
    let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    let TB' := NotesProofs.concreteTensorFunctor (R := R) (S := S) B'
    let TC := NotesProofs.concreteTensorFunctor (R := S) (S := T) C
    let TC' := NotesProofs.concreteTensorFunctor (R := S) (S := T) C'
    let CB := CategoryTheory.Functor.obj TC (ModuleCat.of S B)
    let CB' := CategoryTheory.Functor.obj TC' (ModuleCat.of S B')
    let pureCB := fun (c : C) (b : B) =>
      (NotesProofs.concretePure (R := S) (M := C) c b : ModuleCat.carrier CB)
    let pureCB' := fun (c' : C') (b' : B') =>
      (NotesProofs.concretePure (R := S) (M := C') c' b' : ModuleCat.carrier CB')
    ∃ (rightCB : Module (MulOpposite R) (ModuleCat.carrier CB))
      (rightCB' : Module (MulOpposite R) (ModuleCat.carrier CB')),
      letI : Module (MulOpposite R) (ModuleCat.carrier CB) := rightCB
      letI : Module (MulOpposite R) (ModuleCat.carrier CB') := rightCB'
      (∀ (r : R) (c : C) (b : B),
        rightCB.smul (MulOpposite.op r) (pureCB c b) = pureCB c (MulOpposite.op r • b)) ∧
      (∀ (r : R) (c' : C') (b' : B'),
        rightCB'.smul (MulOpposite.op r) (pureCB' c' b') = pureCB' c' (MulOpposite.op r • b')) ∧
      (∃ (commuteCB : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB))
        (commuteCB' : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB')),
        letI : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB) := commuteCB
        letI : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB') := commuteCB'
        let TCB := NotesProofs.concreteTensorFunctor (R := R) (S := T) (ModuleCat.carrier CB)
        let TCB' := NotesProofs.concreteTensorFunctor (R := R) (S := T) (ModuleCat.carrier CB')
        ∃ (assoc : CategoryTheory.Iso (CategoryTheory.Functor.comp TB TC) TCB)
          (assoc' : CategoryTheory.Iso (CategoryTheory.Functor.comp TB' TC') TCB'),
          (∀ (M : ModuleCat.{u} R) (c : C) (b : B) (m : M),
            (CategoryTheory.NatTrans.app assoc.hom M)
              (NotesProofs.concretePure (R := S) (M := C) c
                (NotesProofs.concretePure (R := R) (M := B) b m)) =
              NotesProofs.concretePure (R := R) (M := ModuleCat.carrier CB) (pureCB c b) m) ∧
          (∀ (M : ModuleCat.{u} R) (c' : C') (b' : B') (m : M),
            (CategoryTheory.NatTrans.app assoc'.hom M)
              (NotesProofs.concretePure (R := S) (M := C') c'
                (NotesProofs.concretePure (R := R) (M := B') b' m)) =
              NotesProofs.concretePure (R := R) (M := ModuleCat.carrier CB') (pureCB' c' b') m) ∧
          (∀ (β : NotesProofs.BimoduleMap (R := R) (S := S) (M := B) (N := B'))
             (γ : NotesProofs.BimoduleMap (R := S) (S := T) (M := C) (N := C')),
            ∃ δ : NotesProofs.BimoduleMap (R := R) (S := T)
                (M := ModuleCat.carrier CB) (N := ModuleCat.carrier CB'),
              (∀ (c : C) (b : B),
                (Subtype.val δ) (pureCB c b) = pureCB' ((Subtype.val γ) c) ((Subtype.val β) b)) ∧
              CategoryTheory.CategoryStruct.comp
                  (CategoryTheory.NatTrans.hcomp
                    (NotesProofs.tensorBimoduleMapNatTrans β)
                    (NotesProofs.tensorBimoduleMapNatTrans γ)) assoc'.hom =
                CategoryTheory.CategoryStruct.comp assoc.hom
                  (NotesProofs.tensorBimoduleMapNatTrans δ)))

#print axioms CheckedEndpoint
