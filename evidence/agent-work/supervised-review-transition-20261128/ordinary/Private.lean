import MackeyDiagrams
import Proofs.GeneralizedMackeyDecomposition
open Lean
local macro "mackey_impl%" id:ident : term => do
  let n := (Name.num `_private.Proofs.GeneralizedMackeyDecomposition 0) ++
    `GeneralizedMackeySupport ++ id.getId
  return mkIdent n
#check mackey_impl% pure
#check mackey_impl% repCofanIsColimit
#check mackey_impl% inclusionAt_pure
#check mackey_impl% toGroup
#check mackey_impl% repCofan
#check mackey_impl% liftPure
#check mackey_impl% pure_ext
