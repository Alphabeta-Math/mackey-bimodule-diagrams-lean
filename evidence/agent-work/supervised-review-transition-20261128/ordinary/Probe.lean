import MackeyDiagrams
import Proofs.GeneralizedMackeyDecomposition

#check «_private».Proofs.GeneralizedMackeyDecomposition.«0».GeneralizedMackeySupport.repCofanIsColimit
#check «_private».Proofs.GeneralizedMackeyDecomposition.«0».GeneralizedMackeySupport.pure
set_option pp.universes true
#check GeneralizedMackeySupport.pure
#check GeneralizedMackeySupport.repCofanIsColimit
#check GeneralizedMackeySupport.inclusionAt_pure
#check Rep.mkIso
#check Rep.hom_comm_apply
#check Rep.res
#check Rep.resFunctor
#check ModuleCat.restrictScalars
#check CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_inv
#check CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
#check CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv
#check MonoidAlgebra.liftNCAlgHom
#check MonoidAlgebra.liftLinearMap
#check MonoidAlgebra.lift
#check MonoidAlgebra.induction_on
#check LinearEquiv.toModuleIso
#check ModuleCat.isoOfLinearEquiv
#check MonoidAlgebra.mapDomainAlgHom_of
#check Representation.ofModule
#check ModuleCat.ofHom
