
namespace DiagramFunctorProof
open CategoryTheory
universe u v
variable {U : Type u} [Group U]

private noncomputable abbrev wordVec := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    Finsupp (MackeyDiagrams.Word.basis p).carrier Complex

private noncomputable abbrev lower := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    (ULift.moduleEquiv : LinearEquiv (RingHom.id Complex) (ULift.{v} (wordVec p)) (wordVec p))

private noncomputable abbrev wordBimod := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    (Rep.of
      ({ toFun := fun g => (lower p).symm.toLinearMap.comp
            ((MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) g).comp
              (lower p).toLinearMap)
         map_one' := by
           ext x
           simp
         map_mul' := by
           intro g h
           have actMul :
               MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) (g * h) =
                 (MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) g).comp
                 (MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) h) := by
             apply Finsupp.lhom_ext
             intro i z
             simp [MackeyDiagrams.Biset.mul_act]
           ext x
           simp [actMul] } :
        Representation Complex (Prod K H) (ULift.{v} (wordVec p))) : BM.{u,v} K H)

private noncomputable abbrev T {K H : Subgroup U} (p : Word K H) :=
  tensor (wordBimod p)

end DiagramFunctorProof
