import MackeyDiagrams
import Proofs.RegularModuleRightAction
import Proofs.CanonicalWattsComparison
import Proofs.ModuleTensorUniversalProperty
import MackeyDiagrams.External.StacksEilenbergWatts
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.GroupTheory.Congruence.Hom

open CategoryTheory

#check AddCon.addGroup
#check AddCon.eq
#check AddCon.lift
#check AddCon.lift_coe
#check AddCon.mk'
#check AddCon.mk'_apply
#check AddCon.toQuotient
#check AddCon.ker_rel
#check AddCon.addConGen_le
#check addConGen_le
#check AddCon.ext
#check AddCon.induction_on
#check FreeAddGroup.ext
#check FreeAddGroup.induction_on
#check AddCon.ker
#check (Functor.map_add)
#check ModuleCat.hom_comp
#check ModuleCat.hom_id
#check ModuleCat.hom_ofHom
#check ModuleCat.hom_ext
#check LinearMap.smulRight_apply
#check ModuleCat.uliftFunctor
#print RegularModuleRightAction
#print axioms RegularModuleRightAction
#print axioms CanonicalWattsComparison
#print axioms ModuleTensorUniversalProperty
#print axioms CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan
#print axioms Stacks.EilenbergWatts.iso
