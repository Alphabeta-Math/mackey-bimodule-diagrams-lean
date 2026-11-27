
section Modules

private abbrev Mod (G : Type u) [Group G] := ModuleCat.{max u v} (MonoidAlgebra Complex G)
private abbrev ofMod (G : Type u) [Group G] : Mod.{u,v} G ⥤ Rep.{max u v} Complex G :=
  Rep.ofModuleMonoidAlgebra
private abbrev toMod (G : Type u) [Group G] : Rep.{max u v} Complex G ⥤ Mod.{u,v} G :=
  Rep.toModuleMonoidAlgebra
private abbrev indMod (f : H →* G) : Mod.{u,v} H ⥤ Mod.{u,v} G :=
  (ofMod H ⋙ Rep.indFunctor Complex f) ⋙ toMod G
private abbrev resMod (f : H →* G) : Mod.{u,v} G ⥤ Mod.{u,v} H :=
  ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex f).toRingHom
private abbrev repEquiv (G : Type u) [Group G] : Rep.{max u v} Complex G ≌ Mod.{u,v} G :=
  Rep.equivalenceModuleMonoidAlgebra

private def adjointRestriction (f : H →* G) (adj : indMod.{u,v} f ⊣ resMod.{u,v} f) :
    (ofMod G ⋙ Rep.resFunctor f ⋙ toMod H) ≅ resMod.{u,v} f :=
  Adjunction.rightAdjointUniq
    (((repEquiv.{u,v} H).symm.toAdjunction.comp (Rep.indResAdjunction Complex f)).comp
      (repEquiv.{u,v} G).toAdjunction) adj

private theorem existsModuleAdjunction {U : Type u} [Group U] {S T : Subgroup U}
    (f : MackeyDiagrams.ConjEmbedding S T) :
    Nonempty (indMod.{u,v} f.toHom ⊣ resMod.{u,v} f.toHom) := by
  obtain ⟨a, ha⟩ := f.hasRepresentative
  have hm (x : S) : a * (x : U) * a⁻¹ ∈ T := ha x ▸ (f.toHom x).property
  have hf : f = MackeyDiagrams.ConjEmbedding.ofConjugator a hm := by
    apply MackeyDiagrams.ConjEmbedding.ext
    exact MonoidHom.ext (fun x => Subtype.ext (ha x))
  rw [hf]
  obtain ⟨_, _, _, _, _, adj, _, _⟩ := InductionRestrictionAdjunction.{u,v} S T a hm
  exact ⟨adj⟩

private def insertModuleEquiv (P : Mod.{u,v} H ⥤ Rep.{max u v} Complex G)
    (Q : Rep.{max u v} Complex G ⥤ Mod.{u,v} K) :
    (P ⋙ Q) ≅ (P ⋙ toMod G) ⋙ (ofMod G ⋙ Q) :=
  isoWhiskerLeft P ((Functor.leftUnitor Q).symm ≪≫
    isoWhiskerRight (repEquiv.{u,v} G).unitIso Q)

private def moduleMackey {J : Type u} {S : J → Type u} [∀ j, Group (S j)]
    (a : K →* G) (b : H →* G) (l : ∀ j, S j →* K) (r : ∀ j, S j →* H)
    (s : J → G) (intertwines : ∀ j t, a (l j t) * s j = s j * b (r j t))
    (bijective : Function.Bijective (toGroup a b l r s intertwines))
    (adjA : indMod.{u,v} a ⊣ resMod.{u,v} a)
    (adjR : ∀ j, indMod.{u,v} (r j) ⊣ resMod.{u,v} (r j)) :
    (indMod.{u,v} b ⋙ resMod.{u,v} a) ≅
      sigmaObj (fun j => resMod.{u,v} (r j) ⋙ indMod.{u,v} (l j)) := by
  let P := (Functor.whiskeringLeft _ _ (Rep.{max u v} Complex K)).obj (ofMod.{u,v} H)
  let Q := (Functor.whiskeringRight (Mod.{u,v} H) _ _).obj (toMod.{u,v} K)
  let c := repCofan.{u,v} a b l r s intertwines
  let F := Discrete.functor (summandRep.{u,v} l r)
  have hc : IsColimit c := repCofanIsColimit a b l r s intertwines bijective
  have hm : IsColimit ((P ⋙ Q).mapCocone c) := by
    letI : (toMod.{u,v} K).IsEquivalence := (repEquiv.{u,v} K).functor.isEquivalence
    exact isColimitOfPreserves (P ⋙ Q) hc
  let diagram := Discrete.functor (fun j => resMod.{u,v} (r j) ⋙ indMod.{u,v} (l j))
  have hmain : (P ⋙ Q).obj c.pt ≅ indMod.{u,v} b ⋙ resMod.{u,v} a := by
    exact (insertModuleEquiv (ofMod H ⋙ Rep.indFunctor Complex b)
      (Rep.resFunctor a ⋙ toMod K)) ≪≫
      isoWhiskerLeft (indMod b) (adjointRestriction a adjA)
  have hsummand : F ⋙ (P ⋙ Q) ≅ diagram := by
    apply Discrete.natIso
    intro j
    exact (insertModuleEquiv (ofMod H ⋙ Rep.resFunctor (r j.as))
      (Rep.indFunctor Complex (l j.as) ⋙ toMod K)) ≪≫
      isoWhiskerRight (adjointRestriction (r j.as) (adjR j.as)) (indMod (l j.as))
  exact hmain.symm ≪≫ hm.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    HasColimit.isoOfNatIso hsummand

end Modules
