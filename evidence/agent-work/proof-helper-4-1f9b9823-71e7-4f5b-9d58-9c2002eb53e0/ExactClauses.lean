private abbrev endpointAllowedOrdinary := fun {K H : Subgroup U} {p q : Word K H}
      (d : MackeyDiagrams.Diagram Complex p q) =>
    MackeyDiagrams.Diagram.rec (motive := fun _ _ _ => Prop)
      (fun _ => True)
      (fun _ => False) (fun _ => False)
      (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ => True) (fun _ => True) (fun _ _ => True) (fun _ => True)
      (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False)
      (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)
      (fun _ _ => True) (fun _ _ a b => a ∧ b) (fun _ _ a => a) d
private abbrev endpointDrawing := fun {K H : Subgroup U} (p q : Word K H) =>
    MackeyDiagrams.LabelledDrawing Complex p q
private abbrev endpointAllowed := fun {K H : Subgroup U} {p q : Word K H} (d : endpointDrawing p q) =>
    MackeyDiagrams.LabelledDrawing.rec (motive := fun _ _ _ => Prop)
      (fun d => endpointAllowedOrdinary d)
      (fun _ => True) (fun _ => True)
      (fun vertex => match MackeyDiagrams.TrivalentVertex.kind vertex with
        | MackeyDiagrams.TrivalentKind.mergeUp | MackeyDiagrams.TrivalentKind.splitUp
        | MackeyDiagrams.TrivalentKind.mergeDown | MackeyDiagrams.TrivalentKind.splitDown => True
        | _ => False)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ => False)
      (fun _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ _ => False)
      (fun _ _ a b => a ∧ b) (fun _ _ a => a)
      (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) d

private abbrev endpointGen {K H : Subgroup U} {p q : Word K H} :=
  {d : endpointDrawing p q // endpointAllowed d}

private noncomputable abbrev endpointSetoid {K H : Subgroup U} (p q : Word K H) :=
  Setoid.ker (fun d : @endpointGen U _ K H p q => drawingEval d.val)

private noncomputable abbrev endpointGenHom {K H : Subgroup U} (p q : Word K H) :=
  Quotient (endpointSetoid p q)

private noncomputable abbrev endpointInDiagram {K H : Subgroup U} {p q : Word K H}
    (η : T.{u,v} p ⟶ T.{u,v} q) :=
  ∃ d : @endpointGen U _ K H p q, onRegular.{u,v} η = conjugateMap.{u,v} (drawingEval d.val)

private theorem endpointInDiagram_iff {K H : Subgroup U} {p q : Word K H}
    (η : T.{u,v} p ⟶ T.{u,v} q) :
    endpointInDiagram.{u,v} η ↔
      ∃ d : @endpointGen U _ K H p q, η = diagramMap.{u,v} d.val := by
  obtain ⟨f, rfl⟩ := liftMap_bijective.2 η
  constructor
  · rintro ⟨d, hd⟩
    rw [onRegular_lift] at hd
    exact ⟨d, congrArg liftMap.{u,v} (conjugateMap_injective hd)⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, (congrArg onRegular.{u,v} hd).trans (onRegular_lift (drawingEval d.val))⟩

private theorem endpointQuotient :
  (∀ (K H : Subgroup U) (p q : Word K H),
    Function.Bijective (@liftMap.{u,v} U _ K H p q) ∧
    (∀ f : wordHom p q, onRegular.{u,v} (liftMap.{u,v} f) = conjugateMap.{u,v} f) ∧
    ∃ e : Equiv (endpointGenHom p q) {η : CategoryTheory.NatTrans (T.{u,v} p) (T.{u,v} q) // endpointInDiagram.{u,v} η},
      ∀ d : @endpointGen U _ K H p q,
        (e (Quotient.mk (endpointSetoid p q) d)).val = diagramMap.{u,v} d.val) := by
  intro K H p q
  exact ⟨liftMap_bijective, onRegular_lift,
    diagramQuotientEquiv (fun d : @endpointGen U _ K H p q => drawingEval d.val),
    fun _ => rfl⟩

private theorem endpointMatrices :
  (∀ K H : Subgroup U,
    letI : CategoryTheory.Limits.HasFiniteBiproducts (BM.{u,v} K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    letI : CategoryTheory.Limits.HasFiniteBiproducts (Func.{u,v} K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    let bimodSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => wordBimod.{u,v} (p i))
    let funSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => T.{u,v} (p i))
    ∃ sumIso : ∀ {n : Nat} (p : Fin n → Word K H),
        CategoryTheory.Iso (tensor.{u,v} (bimodSum p)) (funSum p),
      ∀ {m n : Nat} (p : Fin m → Word K H) (q : Fin n → Word K H),
        (∀ f : ∀ i j, wordHom (p i) (q j),
          CategoryTheory.CategoryStruct.comp
            ((trans.{u,v} K H).map (CategoryTheory.Limits.biproduct.matrix
              (fun i j => wordMap.{u,v} (f i j)))) (sumIso q).hom =
          CategoryTheory.CategoryStruct.comp (sumIso p).hom
            (CategoryTheory.Limits.biproduct.matrix (fun i j => liftMap.{u,v} (f i j)))) ∧
        (∀ η : CategoryTheory.NatTrans (funSum p) (funSum q),
          (∀ i j, endpointInDiagram.{u,v} (CategoryTheory.Limits.biproduct.components
            (f := fun i => T.{u,v} (p i)) (g := fun j => T.{u,v} (q j)) η i j)) ↔
          ∃ d : ∀ i j, @endpointGen U _ K H (p i) (q j),
            η = CategoryTheory.Limits.biproduct.matrix (fun i j => diagramMap.{u,v} (d i j).val))) := by
  intro K H
  letI : HasFiniteBiproducts (BM.{u,v} K H) := HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts (Func.{u,v} K H) := HasFiniteBiproducts.of_hasFiniteProducts
  letI : (trans.{u,v} K H).Additive := transAdditive
  refine ⟨fun p => (trans.{u,v} K H).mapBiproduct (fun i => wordBimod.{u,v} (p i)), ?_⟩
  intro m n p q
  refine ⟨fun f => biproduct_matrix_transport (trans.{u,v} K H)
    (fun i => wordBimod.{u,v} (p i)) (fun j => wordBimod.{u,v} (q j))
    (fun i j => wordMap.{u,v} (f i j)), ?_⟩
  intro η
  refine Iff.trans ?_ (matrix_predicate
    (fun i j => @endpointGen U _ K H (p i) (q j))
    (fun _ _ d => diagramMap.{u,v} d.val) η)
  exact forall_congr' (fun _ => forall_congr' (fun _ => endpointInDiagram_iff _))
