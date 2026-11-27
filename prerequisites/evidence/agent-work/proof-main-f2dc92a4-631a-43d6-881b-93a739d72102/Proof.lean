by
  intro R _ S _ Bimod star carrier right Balanced
  exact ⟨BimoduleTensorFunctorialityAux.tensorFunctor.{r,s,v,w,t},
    BimoduleTensorFunctorialityAux.pure.{r,s,v,w,t},
    fun B M => ⟨BimoduleTensorFunctorialityAux.pure_balanced.{r,s,v,w,t} B M,
      BimoduleTensorFunctorialityAux.unique_lift.{r,s,v,w,t} B M,
      BimoduleTensorFunctorialityAux.smul_pure.{r,s,v,w,t} B M⟩,
    fun u f b m => BimoduleTensorFunctorialityAux.map_pure.{r,s,v,w,t} u f b m,
    BimoduleTensorFunctorialityAux.sectL_additive.{r,s,v,w,t},
    BimoduleTensorFunctorialityAux.sectR_additive.{r,s,v,w,t}⟩