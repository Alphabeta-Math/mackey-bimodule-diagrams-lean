open CategoryTheory CategoryTheory.Limits
private theorem abelianEquivalenceSmallness
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] (e : C ≌ D) [e.functor.Additive]
    {I : Type w} [DecidableEq I] [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (P : C) (Y : I → D)
    (h : Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => P ⟶ e.inverse.obj (Y i))
        (fun i => Preadditive.rightComp P (Sigma.ι (fun j => e.inverse.obj (Y j)) i)))) :
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => e.functor.obj P ⟶ Y i)
        (fun i => Preadditive.rightComp (e.functor.obj P) (Sigma.ι Y i))) := by
  -- Alphabeta Math's progenerator corollary, steps 1.1 and 2.2, uses the
  -- adjoint-equivalence transposition and coproduct preservation by the inverse.
  -- https://alphabetamath.cc/item/lem-equivalences-preserve-progenerators
  let : PreservesColimitsOfShape (Discrete I) e.inverse :=
    (Adjunction.isEquivalence_preservesColimits e.inverse).preservesColimitsOfShape
  let X := fun i => e.inverse.obj (Y i)
  let compareC := DirectSum.toAddMonoid (β := fun i => P ⟶ X i)
    (fun i => Preadditive.rightComp P (Sigma.ι X i))
  let compareD := DirectSum.toAddMonoid (β := fun i => e.functor.obj P ⟶ Y i)
    (fun i => Preadditive.rightComp (e.functor.obj P) (Sigma.ι Y i))
  let mapSummand := fun i => e.toAdjunction.homAddEquiv P (Y i)
  let mapSum : DirectSum I (fun i => e.functor.obj P ⟶ Y i) ≃+
      DirectSum I (fun i => P ⟶ X i) :=
    DFinsupp.mapRange.addEquiv mapSummand
  let coproductIso := (asIso (sigmaComparison e.inverse Y)).symm
  let postcompose : (P ⟶ e.inverse.obj (∐ Y)) ≃+ (P ⟶ ∐ X) :=
    { coproductIso.homToEquiv with
      map_add' := fun f g => Preadditive.add_comp _ _ _ f g coproductIso.hom }
  let mapCoproduct := (e.toAdjunction.homAddEquiv P (∐ Y)).trans postcompose

  -- Identify the actual comparison in Lemma 10.3 by checking the inclusions.
  have hSquare : mapCoproduct.toAddMonoidHom.comp compareD =
      compareC.comp mapSum.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    have hSummand :
        mapSum (DirectSum.of (fun j => e.functor.obj P ⟶ Y j) i f) =
          DirectSum.of (fun j => P ⟶ X j) i (mapSummand i f) := by
      change DFinsupp.mapRange.addEquiv mapSummand (DFinsupp.single i f) =
        DFinsupp.single i (mapSummand i f)
      rw [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_single]
    change mapCoproduct (compareD (DirectSum.of (fun j => e.functor.obj P ⟶ Y j) i f)) =
      compareC (mapSum (DirectSum.of (fun j => e.functor.obj P ⟶ Y j) i f))
    simp only [hSummand, compareC, compareD, DirectSum.toAddMonoid_of]
    change e.toAdjunction.homEquiv P (∐ Y) (f ≫ Sigma.ι Y i) ≫ coproductIso.hom =
      e.toAdjunction.homEquiv P (Y i) f ≫ Sigma.ι X i
    rw [e.toAdjunction.homEquiv_naturality_right, Category.assoc]
    congr 1
    exact map_ι_comp_inv_sigmaComparison e.inverse Y i
  apply (mapCoproduct.bijective.of_comp_iff' compareD).mp
  change Function.Bijective (⇑(mapCoproduct.toAddMonoidHom.comp compareD))
  rw [hSquare]
  exact h.comp mapSum.bijective
