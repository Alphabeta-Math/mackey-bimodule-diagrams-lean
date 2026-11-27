(open NotesCategoricalDictionary in
by
  intro A D _ _ _ _ _ _ _ _ P Q _ _ hP hQ hSmallP hSmallQ
  dsimp only
  let R := MulOpposite (End P)
  let S := MulOpposite (End Q)
  let HA : A ⥤ ModuleCat.{v} R := preadditiveCoyonedaObj P
  let HD : D ⥤ ModuleCat.{v} S := preadditiveCoyonedaObj Q
  -- Alphabeta Math, module-category reconstruction, steps 1.1, 2.1,
  -- 3.1 and 4.1. The registered Chapter 8 result supplies the inverse
  -- functors and both natural comparisons from the separators, projectivity,
  -- and precisely the two coproduct comparisons above.
  -- The lecture notes' §8.1 permits the choice used by that construction.
  have reconA := ReconstructionFromSmallProjectiveGenerator A P hP hSmallP
  have reconD := ReconstructionFromSmallProjectiveGenerator D Q hQ hSmallQ

  -- Use Corollary 9.6 at the carrier universe v. Its registered result
  -- supplies the actual tensor functor and regular-evaluation object
  -- formula on the same ConcreteBimodule category as this endpoint.
  obtain ⟨_, _, _, T, hTensor, hEval, _, _, _⟩ :=
    BimoduleFunctorHomEquivalence.{v,0} R S
  let liftDictionary (LA : ModuleCat.{v} R ⥤ A) (LD : ModuleCat.{v} S ⥤ D)
      (cA : LA ⋙ HA ≅ 𝟭 (ModuleCat.{v} R)) (uA : HA ⋙ LA ≅ 𝟭 A)
      (cD : LD ⋙ HD ≅ 𝟭 (ModuleCat.{v} S)) (uD : HD ⋙ LD ≅ 𝟭 D) :=
    (transport (CategoryTheory.Equivalence.mk HA LA uA.symm cA)
      (CategoryTheory.Equivalence.mk HD LD uD.symm cD)).trans T.symm

  refine ⟨?_, ?_⟩
  · obtain ⟨LA, ⟨cA⟩, ⟨uA⟩⟩ := reconA
    obtain ⟨LD, ⟨cD⟩, ⟨uD⟩⟩ := reconD
    exact ⟨liftDictionary LA LD cA uA cD uD⟩
  · rintro LA LD ⟨cA⟩ ⟨uA⟩ ⟨cD⟩ ⟨uD⟩
    let eA := CategoryTheory.Equivalence.mk HA LA uA.symm cA
    let eD := CategoryTheory.Equivalence.mk HD LD uD.symm cD
    let WU := transport eA eD
    refine ⟨liftDictionary LA LD cA uA cD uD, ?_, ?_⟩
    · intro F
      let W := LA ⋙ F.obj ⋙ HD
      let G := WU.functor.obj F
      let : W.Additive := G.property.1
      let evaluated := NotesProofs.General.ConcreteBimodule.wattsBimodule.{v,0} R S W
      have hB : T.inverse.obj G = evaluated := hEval G
      change ModuleCat.of S (T.inverse.obj G).carrier = W.obj (ChoiceFreeWatts.regular.{v,0} R) ∧
        ∀ r : R, HEq (fun m : (T.inverse.obj G).carrier => MulOpposite.op r • m)
          (fun x => ChoiceFreeWatts.right W r x)
      rw [hB]
      refine ⟨rfl, ?_⟩
      intro r
      exact heq_of_eq (funext (NotesProofs.wattsRight_apply W r))
    · intro B
      change (WU.inverse.obj (T.functor.obj B)).obj =
        HA ⋙ NotesProofs.General.concreteTensorFunctor.{v,0} (R := R) (S := S) B.carrier ⋙ LD
      rw [hTensor]
      rfl)
