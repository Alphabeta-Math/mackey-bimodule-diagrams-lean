namespace BimoduleTensorFunctorialityAux

open CategoryTheory

universe r s v

variable {R : Type r} [Ring R] {S : Type s} [Ring S]

local notation "★" => SingleObj.star (MulOpposite R)

example (B : Bimod.{r,s,v} R S) (b : carrier B) : action B 1 b = b :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (B.obj.map_id ★)) b

example (B : Bimod.{r,s,v} R S) (a a' : R) (b : carrier B) :
    action B (a * a') b = action B a' (action B a b) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (B.obj.map_comp (show ★ ⟶ ★ from MulOpposite.op a)
      (show ★ ⟶ ★ from MulOpposite.op a'))) b

example (B : Bimod.{r,s,v} R S) (a a' : R) (b : carrier B) :
    action B (a + a') b = action B a b + action B a' b :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (B.obj.map_add (f := (show ★ ⟶ ★ from MulOpposite.op a))
      (g := (show ★ ⟶ ★ from MulOpposite.op a')))) b

end BimoduleTensorFunctorialityAux

#check BalancedTensorUniversalProperty
#print axioms BalancedTensorUniversalProperty
#print axioms ChoiceFreeWatts.outerModule
#print axioms ChoiceFreeWatts.scale_pure
#print axioms ChoiceFreeWatts.pureBalanced
#print axioms ChoiceFreeWatts.tensorLift
#print axioms ChoiceFreeWatts.tensorLift_pure
#print axioms ChoiceFreeWatts.tensorLinearLift
#print axioms ChoiceFreeWatts.tensorLinearLift_pure
#print axioms ChoiceFreeWatts.tensorExt
