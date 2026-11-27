import Algebra

set_option maxHeartbeats 200000

universe u

namespace RightUpCurlSupport

open MackeyDiagrams

variable {U : Type u} [Group U] {K H G : Subgroup U}
  (a : ConjEmbedding H G) (d : ConjEmbedding K H)

local notation "UP" => Biset.induction a
local notation "LOOPUP" => Biset.induction d
local notation "LOOPDOWN" => Biset.restriction d
local notation "STRAIGHT" => Biset.Hom.id (R := Complex) UP
local notation "INSERT" => Biset.insertRightUnit UP Complex
local notation "REMOVE" => Biset.rightUnit UP Complex
local notation "REASSOC" => Biset.unassociate UP LOOPUP LOOPDOWN Complex
local notation "ASSOC" => Biset.associate UP LOOPUP LOOPDOWN Complex
local notation "MERGE" => Biset.Hom.horizontal (Generator.mergeUp Complex a d) (Biset.Hom.id LOOPDOWN)
local notation "SPLIT" => Biset.Hom.horizontal (Generator.splitUp Complex a d) (Biset.Hom.id LOOPDOWN)
local notation "CUP[" f "]" => Biset.Hom.horizontal STRAIGHT (Generator.reverseCup Complex d f)
local notation "CAP" => Biset.Hom.horizontal STRAIGHT (Generator.multiplicationCap Complex d)
local notation "SCALAR" => (d.toHom.range.index : Complex)

private theorem middle :
    ((REASSOC).vertical MERGE).vertical ((SPLIT).vertical ASSOC) =
      Biset.Hom.id ((UP).tensor ((LOOPUP).tensor LOOPDOWN)) := by
  have h :
      (Generator.mergeUp Complex a d).vertical (Generator.splitUp Complex a d) =
        Biset.Hom.id ((UP).tensor LOOPUP) :=
    Diagram.mergeUp_splitUp (R := Complex) a d
  exact Biset.Hom.cancel_middle REASSOC MERGE SPLIT ASSOC
    (rightUpCurl_tensorInverse _ _ LOOPDOWN h)
    (Biset.unassociate_associate (R := Complex))

private theorem loop (finite : d.toHom.range.FiniteIndex) :
    (CUP[finite]).vertical CAP = (Biset.Hom.id ((UP).tensor (Biset.regular H))).scale SCALAR := by
  have h : (Generator.reverseCup Complex d finite).vertical (Generator.multiplicationCap Complex d) =
      (Biset.Hom.id (Biset.regular H)).scale SCALAR :=
    Diagram.reverseCup_multiplicationCap (R := Complex) d finite
  exact rightUpCurl_tensorScalar UP _ _ SCALAR h

theorem calculation (finite : d.toHom.range.FiniteIndex) :
    ((INSERT).vertical ((CUP[finite]).vertical ((REASSOC).vertical MERGE))).vertical
        ((SPLIT).vertical ((ASSOC).vertical ((CAP).vertical REMOVE))) = (STRAIGHT).scale SCALAR :=
  rightUpCurl_assemble INSERT (CUP[finite]) REASSOC MERGE SPLIT ASSOC CAP REMOVE SCALAR
    (middle a d) (loop a d finite) (Biset.insertRightUnit_rightUnit (R := Complex))

end RightUpCurlSupport
