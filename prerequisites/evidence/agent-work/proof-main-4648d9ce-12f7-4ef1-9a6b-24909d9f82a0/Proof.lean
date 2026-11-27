by
  intro T S R _ _ _ TS SR starS starR carrierC carrierB rightC rightB
    CB BM CBType BMType Left Right
  -- Evaluate both additive functors at their unique object. Their functor
  -- and additivity laws supply the right-module laws, and their maps are
  -- linear for the original left actions. The quotient identifications
  -- below are definitional, including the classes of the generators.
  let leftCB (C : TS) (B : SR) : Module T (CBType C B) := by
    let _ := NotesBalancedAssoc.rightAction C
    let _ := NotesBalancedAssoc.rightAction_comm C
    let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
    exact NotesBalancedAssoc.leftModule (K := T) (R := S)
      (X := carrierC C) (Y := carrierB B)
  let rightCB (C : TS) (B : SR) : Module (MulOpposite R) (CBType C B) := by
    let _ := NotesBalancedAssoc.rightAction C
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm B
    exact NotesBalancedAssoc.rightModule (K := MulOpposite R) (R := S)
      (X := carrierC C) (Y := carrierB B)
  let leftBM (B : SR) (M : ModuleCat R) : Module S (BMType B M) := by
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm B
    let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
    exact NotesBalancedAssoc.leftModule (K := S) (R := R) (X := carrierB B) (Y := M)
  refine ⟨leftCB, rightCB, leftBM, ?_, ?_, ?_⟩
  · intro C B
    let _ := NotesBalancedAssoc.rightAction C
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm C
    let _ := NotesBalancedAssoc.rightAction_comm B
    let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
    exact ⟨NotesBalancedAssoc.commute (R := S) (K := T) (J := MulOpposite R)
        (X := carrierC C) (Y := carrierB B),
      fun t c b => NotesBalancedAssoc.left_pure (R := S) t c b,
      fun r c b => NotesBalancedAssoc.right_pure (R := S) (MulOpposite.op r) c b⟩
  · intro B M s b m
    let _ := NotesBalancedAssoc.rightAction B
    let _ := NotesBalancedAssoc.rightAction_comm B
    let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
    exact NotesBalancedAssoc.left_pure (R := R) s b m
  · intro L U pureL pureU
    let actL (C : TS) (B : SR) (M : ModuleCat R) : Module T (L C B M) := by
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      exact NotesBalancedAssoc.actL (T := T) (S := S) (R := R)
        (X := carrierC C) (Y := carrierB B) (Z := M)
    let actU (C : TS) (B : SR) (M : ModuleCat R) : Module T (U C B M) := by
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      exact NotesBalancedAssoc.actU (T := T) (S := S) (R := R)
        (X := carrierC C) (Y := carrierB B) (Z := M)
    let α (C : TS) (B : SR) (M : ModuleCat R) :
        letI := actL C B M
        letI := actU C B M
        LinearEquiv (RingHom.id T) (L C B M) (U C B M) := by
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      exact NotesBalancedAssoc.assoc (T := T) (S := S) (R := R)
        (X := carrierC C) (Y := carrierB B) (Z := M)
    refine ⟨actL, actU, α, ?_, ?_⟩
    · intro C B M c b m
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      exact ⟨NotesBalancedAssoc.assoc_pure (T := T) (S := S) (R := R) c b m,
        fun t => ⟨NotesBalancedAssoc.actL_pure (S := S) (R := R) t c b m,
          NotesBalancedAssoc.actU_pure (S := S) (R := R) t c b m⟩⟩
    · intro C C' B B' M M' f g h
      let _ := NotesBalancedAssoc.rightAction C
      let _ := NotesBalancedAssoc.rightAction C'
      let _ := NotesBalancedAssoc.rightAction B
      let _ := NotesBalancedAssoc.rightAction B'
      let _ := NotesBalancedAssoc.rightAction_comm C
      let _ := NotesBalancedAssoc.rightAction_comm C'
      let _ := NotesBalancedAssoc.rightAction_comm B
      let _ := NotesBalancedAssoc.rightAction_comm B'
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C)
      let _ := SMulCommClass.symm (MulOpposite S) T (carrierC C')
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B)
      let _ := SMulCommClass.symm (MulOpposite R) S (carrierB B')
      exact NotesBalancedAssoc.natural (NotesBalancedAssoc.evalRight f)
        (g.hom.app starR).hom h.hom (fun t c => map_smul (f.hom.app starS).hom t c)
        (fun r b => map_smul (NotesBalancedAssoc.evalRight g) r b)
