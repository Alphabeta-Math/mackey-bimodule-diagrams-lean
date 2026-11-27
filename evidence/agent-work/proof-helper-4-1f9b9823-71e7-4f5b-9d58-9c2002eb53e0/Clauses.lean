private noncomputable abbrev paired {K L H : Subgroup U} (p : Word K L) (q : Word L H)
    (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) : wordBimod.{u,v} (Word.tensor p q) :=
  (lower.{u,v} (Word.tensor p q)).symm
    (Biset.pairLinear Complex p.basis q.basis (lower.{u,v} p b) (lower.{u,v} q c))

private theorem paired_generators_ext {K L H : Subgroup U} (p : Word K L) (q : Word L H)
    {W : Type*} [AddCommGroup W] [Module Complex W]
    {f g : wordBimod.{u,v} (Word.tensor p q) →ₗ[Complex] W}
    (h : ∀ i j,
      f (paired p q ((lower.{u,v} p).symm (Finsupp.single i 1))
        ((lower.{u,v} q).symm (Finsupp.single j 1))) =
      g (paired p q ((lower.{u,v} p).symm (Finsupp.single i 1))
        ((lower.{u,v} q).symm (Finsupp.single j 1)))) : f = g := by
  let l := lower.{u,v} (Word.tensor p q)
  have eq : f.comp l.symm.toLinearMap = g.comp l.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro z a
    change Quotient (Biset.balance p.basis q.basis) at z
    refine Quotient.inductionOn z ?_
    rintro ⟨i, j⟩
    have h₁ := h i j
    simp only [paired, LinearEquiv.apply_symm_apply, Biset.pairLinear_single, one_mul] at h₁
    have ha : Finsupp.single (Biset.pair p.basis q.basis i j) a =
        a • Finsupp.single (Biset.pair p.basis q.basis i j) (1 : Complex) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    change f (l.symm (Finsupp.single (Biset.pair p.basis q.basis i j) a)) =
      g (l.symm (Finsupp.single (Biset.pair p.basis q.basis i j) a))
    rw [ha, map_smul, map_smul, map_smul, h₁]
  apply LinearMap.ext
  intro b
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using DFunLike.congr_fun eq (l b)

private noncomputable abbrev drawingEval {K H : Subgroup U} {p q : Word K H}
    (d : LabelledDrawing Complex p q) : wordHom p q :=
  ScopedDiagram.eval (LabelledDrawing.interpret d)

private noncomputable abbrev diagramMap {K H : Subgroup U} {p q : Word K H}
    (d : LabelledDrawing Complex p q) :=
  liftMap.{u,v} (drawingEval d)

private theorem evaluated_horizontal_pair {K L H : Subgroup U}
    (p p' : Word K L) (q q' : Word L H) (d : LabelledDrawing Complex p p')
    (e : LabelledDrawing Complex q q') (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) :
    (wordMap.{u,v} (drawingEval (LabelledDrawing.horizontal d e))).hom (paired p q b c) =
      paired p' q' ((wordMap.{u,v} (drawingEval d)).hom b)
        ((wordMap.{u,v} (drawingEval e)).hom c) := by
  have hp := (InductionRestrictionBimoduleStrands.{u, 0, 0} (U := U)).2.2.1
    K L H p p' q q' d e (lower.{u,v} p b) (lower.{u,v} q c)
  change (lower.{u,v} (Word.tensor p' q')).symm
      ((drawingEval (LabelledDrawing.horizontal d e)).toLinearMap
        (lower.{u,v} (Word.tensor p q) ((lower.{u,v} (Word.tensor p q)).symm
          (Biset.pairLinear Complex p.basis q.basis (lower.{u,v} p b) (lower.{u,v} q c))))) =
    (lower.{u,v} (Word.tensor p' q')).symm
      (Biset.pairLinear Complex p'.basis q'.basis
        (lower.{u,v} p' ((lower.{u,v} p').symm ((drawingEval d).toLinearMap (lower.{u,v} p b))))
        (lower.{u,v} q' ((lower.{u,v} q').symm ((drawingEval e).toLinearMap (lower.{u,v} q c)))))
  simpa only [LinearEquiv.apply_symm_apply] using
    congrArg (lower.{u,v} (Word.tensor p' q')).symm hp

private theorem hcomp_pure {K L H : Subgroup U} {p p' : Word K L} {q q' : Word L H}
    (d : LabelledDrawing Complex p p') (e : LabelledDrawing Complex q q')
    (X : Mod.{u,v} H) (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) (x : X) :
    (((diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d)).app X).hom
        (rawPure (wordBimod.{u,v} p) ((T.{u,v} q).obj X) b (rawPure (wordBimod.{u,v} q) X c x)) =
      rawPure (wordBimod.{u,v} p') ((T.{u,v} q').obj X)
        ((wordMap.{u,v} (drawingEval d)).hom b)
        (rawPure (wordBimod.{u,v} q') X ((wordMap.{u,v} (drawingEval e)).hom c) x) := by
  rw [NatTrans.hcomp_app]
  change ((T.{u,v} p').map ((diagramMap.{u,v} e).app X)).hom
      (((diagramMap.{u,v} d).app ((T.{u,v} q).obj X)).hom
        (rawPure (wordBimod.{u,v} p) ((T.{u,v} q).obj X) b (rawPure (wordBimod.{u,v} q) X c x))) = _
  rw [rawMapBimod, rawMapInput, rawMapBimod]

-- Alphabeta Math, balanced tensor associativity, Steps 3.1 and 3.2.
-- Compare the two maps on generators using the already specified associator formula.
private theorem horizontal_comp_of_pure {K L H : Subgroup U}
    (compIso : ∀ (p : Word K L) (q : Word L H),
      T.{u,v} (Word.tensor p q) ≅ T.{u,v} q ⋙ T.{u,v} p)
    (compPure : ∀ (p : Word K L) (q : Word L H) (X : Mod.{u,v} H)
      (b : wordBimod.{u,v} p) (c : wordBimod.{u,v} q) (x : V X),
      VMap ((compIso p q).hom.app X)
        (pure (wordBimod.{u,v} (Word.tensor p q)) X (paired p q b c) x) =
      pure (wordBimod.{u,v} p) ((T.{u,v} q).obj X) b
        (pure (wordBimod.{u,v} q) X c x))
    (p p' : Word K L) (q q' : Word L H) (d : LabelledDrawing Complex p p')
    (e : LabelledDrawing Complex q q') :
    diagramMap.{u,v} (LabelledDrawing.horizontal d e) ≫ (compIso p' q').hom =
      (compIso p q).hom ≫ (diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d) := by
  apply NatTrans.ext
  funext X
  apply hom_ext_pure (wordBimod.{u,v} (Word.tensor p q)) X
  intro z x
  let left := (diagramMap.{u,v} (LabelledDrawing.horizontal d e) ≫ (compIso p' q').hom).app X
  let right := ((compIso p q).hom ≫ (diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d)).app X
  let test := (pure (wordBimod.{u,v} (Word.tensor p q)) X).flip x
  change (VMap left).comp test z = (VMap right).comp test z
  apply DFunLike.congr_fun (paired_generators_ext p q ?_) z
  intro i j
  let b := (lower.{u,v} p).symm (Finsupp.single i 1)
  let c := (lower.{u,v} q).symm (Finsupp.single j 1)
  change ((compIso p' q').hom.app X).hom
      (((diagramMap.{u,v} (LabelledDrawing.horizontal d e)).app X).hom
        (rawPure (wordBimod.{u,v} (Word.tensor p q)) X (paired p q b c) x)) =
    (((diagramMap.{u,v} e).hcomp (diagramMap.{u,v} d)).app X).hom
      (((compIso p q).hom.app X).hom
        (rawPure (wordBimod.{u,v} (Word.tensor p q)) X (paired p q b c) x))
  have pure_eq (r : Word K L) (s : Word L H) (b' : wordBimod.{u,v} r)
      (c' : wordBimod.{u,v} s) :
      ((compIso r s).hom.app X).hom
        (rawPure (wordBimod.{u,v} (Word.tensor r s)) X (paired r s b' c') x) =
      rawPure (wordBimod.{u,v} r) ((T.{u,v} s).obj X) b'
        (rawPure (wordBimod.{u,v} s) X c' x) :=
    compPure r s X b' c' x
  rw [rawMapBimod, evaluated_horizontal_pair, pure_eq, pure_eq]
  exact (hcomp_pure d e X b c x).symm
