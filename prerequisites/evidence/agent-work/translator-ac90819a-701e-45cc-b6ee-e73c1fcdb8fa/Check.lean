import Proofs.BimoduleTensorBicategoryCoherence

universe u

def Endpoint : Prop :=
  let regular := fun (A : RingCat.{u}) =>
    (⟨AddCommGrpCat.of A, (Bimodule.{u,u,u}.2.1 A).val⟩ : MoritaCoherence.Bimod A A)
  let isoHom := fun {B A : RingCat.{u}} {M N : MoritaCoherence.Bimod B A}
      (e : MoritaCoherence.Iso M N) =>
    (⟨e.val.toAddMonoidHom, e.property⟩ : MoritaCoherence.Hom M N)
  let idMap := fun {B A : RingCat.{u}} (M : MoritaCoherence.Bimod B A) =>
    (⟨AddMonoidHom.id M.1, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩ : MoritaCoherence.Hom M M)
  let comp := fun {B A : RingCat.{u}} {M N P : MoritaCoherence.Bimod B A}
      (g : MoritaCoherence.Hom N P) (f : MoritaCoherence.Hom M N) =>
    (⟨g.val.comp f.val,
      ⟨fun b m => (congrArg g.val (f.property.1 b m)).trans (g.property.1 b (f.val m)),
       fun a m => (congrArg g.val (f.property.2 a m)).trans (g.property.2 a (f.val m))⟩⟩ :
      MoritaCoherence.Hom M P)
  let balanced := fun {C B A : RingCat.{u}}
      (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A)
      (X : AddCommGrpCat.{u}) (p : G.1 → F.1 → X) =>
    (∀ (g g' : G.1) (f : F.1), p (g + g') f = p g f + p g' f) ∧
    (∀ (g : G.1) (f f' : F.1), p g (f + f') = p g f + p g f') ∧
    (∀ (b : B) (g : G.1) (f : F.1),
      p (MoritaCoherence.right G b g) f = p g (MoritaCoherence.left F b f))
  ∃ (tensor : ∀ {C B A : RingCat.{u}},
        MoritaCoherence.Bimod C B → MoritaCoherence.Bimod B A → MoritaCoherence.Bimod C A)
    (pure : ∀ {C B A : RingCat.{u}}
        (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A),
        G.1 → F.1 → (tensor G F).1),
    (∀ {C B A : RingCat.{u}} (G : MoritaCoherence.Bimod C B)
        (F : MoritaCoherence.Bimod B A),
      balanced G F (tensor G F).1 (pure G F) ∧
      ∀ (X : AddCommGrpCat.{u}) (p : G.1 → F.1 → X), balanced G F X p →
        ∃! lift : AddMonoidHom (tensor G F).1 X, ∀ g f, lift (pure G F g f) = p g f) ∧
    (∀ {C B A : RingCat.{u}} (G : MoritaCoherence.Bimod C B)
        (F : MoritaCoherence.Bimod B A) (g : G.1) (f : F.1),
      (∀ c : C, MoritaCoherence.left (tensor G F) c (pure G F g f) =
        pure G F (MoritaCoherence.left G c g) f) ∧
      (∀ a : A, MoritaCoherence.right (tensor G F) a (pure G F g f) =
        pure G F g (MoritaCoherence.right F a f))) ∧
    ∃ (tensorMap : ∀ {C B A : RingCat.{u}} {G G' : MoritaCoherence.Bimod C B}
          {F F' : MoritaCoherence.Bimod B A},
          MoritaCoherence.Hom G G' → MoritaCoherence.Hom F F' →
            MoritaCoherence.Hom (tensor G F) (tensor G' F'))
      (assoc : ∀ {D C B A : RingCat.{u}} (H : MoritaCoherence.Bimod D C)
          (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A),
          MoritaCoherence.Iso (tensor (tensor H G) F) (tensor H (tensor G F)))
      (leftUnitor : ∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A),
          MoritaCoherence.Iso (tensor (regular B) F) F)
      (rightUnitor : ∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A),
          MoritaCoherence.Iso (tensor F (regular A)) F),
      (∀ {C B A : RingCat.{u}} {G G' : MoritaCoherence.Bimod C B}
          {F F' : MoritaCoherence.Bimod B A}
          (g : MoritaCoherence.Hom G G') (f : MoritaCoherence.Hom F F')
          (y : G.1) (x : F.1),
        (tensorMap g f).val (pure G F y x) = pure G' F' (g.val y) (f.val x)) ∧
      (∀ {D C B A : RingCat.{u}} (H : MoritaCoherence.Bimod D C)
          (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A)
          (h : H.1) (g : G.1) (f : F.1),
        (assoc H G F).val (pure (tensor H G) F (pure H G h g) f) =
          pure H (tensor G F) h (pure G F g f)) ∧
      (∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A) (b : B) (f : F.1),
        (leftUnitor F).val (pure (regular B) F b f) = MoritaCoherence.left F b f) ∧
      (∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A) (a : A) (f : F.1),
        (rightUnitor F).val (pure F (regular A) f a) = MoritaCoherence.right F a f) ∧
      (∀ {E D C B A : RingCat.{u}}
          (K : MoritaCoherence.Bimod E D) (H : MoritaCoherence.Bimod D C)
          (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A),
        comp (isoHom (assoc K H (tensor G F))) (isoHom (assoc (tensor K H) G F)) =
          comp (tensorMap (idMap K) (isoHom (assoc H G F)))
            (comp (isoHom (assoc K (tensor H G) F))
              (tensorMap (isoHom (assoc K H G)) (idMap F)))) ∧
      (∀ {C B A : RingCat.{u}} (G : MoritaCoherence.Bimod C B)
          (F : MoritaCoherence.Bimod B A),
        comp (tensorMap (idMap G) (isoHom (leftUnitor F))) (isoHom (assoc G (regular B) F)) =
          tensorMap (isoHom (rightUnitor G)) (idMap F))

set_option maxHeartbeats 2000000 in
theorem TensorPentagonAndTriangle : Endpoint.{u} := by
  unfold Endpoint
  dsimp only
  obtain ⟨actions, hBalanced, hActions, tensorMap, assoc, leftUnitor, rightUnitor,
    _, hTensorMap, _, _, hAssoc, hUnitor, _, _, hPentagon, hTriangle⟩ :=
    BimoduleTensorBicategoryCoherence.{u}
  refine ⟨_, _, hBalanced, hActions, tensorMap, assoc, leftUnitor, rightUnitor,
    hTensorMap, hAssoc, ?_, ?_, hPentagon, hTriangle⟩
  · intro B A F b f
    exact (hUnitor F b (0 : A) f).1
  · intro B A F a f
    exact (hUnitor F (0 : B) a f).2

#print axioms TensorPentagonAndTriangle
