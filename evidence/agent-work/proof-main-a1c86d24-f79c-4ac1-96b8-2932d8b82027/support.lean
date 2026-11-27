open scoped ModuleCat.Algebra

section
open CategoryTheory

private def complexWattsBalanced {S R : RingCat.{u}}
    (B : ModuleCat.{max u v} S) [Module Rᵐᵒᵖ B]
    (X : ModuleCat.{max u v} R) (Y : ModuleCat.{max u v} S) (p : B → X → Y) : Prop :=
  (∀ b b' x, p (b + b') x = p b x + p b' x) ∧
  (∀ b x x', p b (x + x') = p b x + p b x') ∧
  (∀ (s : S) b x, p (s • b) x = s • p b x) ∧
  (∀ (r : R) b x, p (MulOpposite.op r • b) x = p b (r • x))

private theorem complexWatts_hom_ext {S R : RingCat.{u}}
    {B : ModuleCat.{max u v} S} [Module Rᵐᵒᵖ B]
    {X : ModuleCat.{max u v} R} {Y : ModuleCat.{max u v} S} {p : B → X → Y}
    (hp : complexWattsBalanced B X Y p)
    (universal : ∀ (Z : ModuleCat.{max u v} S) (q : B → X → Z),
      complexWattsBalanced B X Z q → ∃! f : Y →ₗ[S] Z, ∀ b x, f (p b x) = q b x)
    (f g : Y ⟶ Y) (h : ∀ b x, f.hom (p b x) = g.hom (p b x)) : f = g := by
  let q : B → X → Y := fun b x => f.hom (p b x)
  have hq : complexWattsBalanced B X Y q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b b' x
      simp only [q, hp.1, map_add]
    · intro b x x'
      simp only [q, hp.2.1, map_add]
    · intro s b x
      simp only [q, hp.2.2.1, LinearMap.map_smul]
    · intro r b x
      simp only [q, hp.2.2.2]
  obtain ⟨k, _, unique⟩ := universal Y q hq
  exact ModuleCat.hom_injective ((unique f.hom (fun _ _ => rfl)).trans
    (unique g.hom (fun b x => (h b x).symm)).symm)

-- Alphabeta Math, thm-eilenberg-watts-for-arbitrary-unital-rings, step 2.1.
-- For the scalar comparison we need the regular tensor unit at the chosen
-- carrier universe. Construct its contraction from the registered universal
-- property on the lifted regular module.
private theorem complexWatts_regular_retraction {S R : RingCat.{u}}
    {B Y : ModuleCat.{max u v} S} [Module Rᵐᵒᵖ B] [SMulCommClass Rᵐᵒᵖ S B]
    (p : B → ModuleCat.of R (ULift.{v} R) → Y)
    (universal : ∀ (Z : ModuleCat.{max u v} S)
      (q : B → ModuleCat.of R (ULift.{v} R) → Z),
      complexWattsBalanced B (ModuleCat.of R (ULift.{v} R)) Z q →
      ∃! f : Y →ₗ[S] Z, ∀ b x, f (p b x) = q b x) :
    ∃ f : Y →ₗ[S] B, ∀ b, f (p b (ULift.up 1)) = b := by
  let q : B → ModuleCat.of R (ULift.{v} R) → B := fun b x => MulOpposite.op x.down • b
  have hq : complexWattsBalanced B (ModuleCat.of R (ULift.{v} R)) B q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b b' x
      exact smul_add _ _ _
    · intro b x x'
      exact add_smul (MulOpposite.op x.down) (MulOpposite.op x'.down) b
    · intro s b x
      exact smul_comm (MulOpposite.op x.down) s b
    · intro r b x
      exact (mul_smul (MulOpposite.op x.down) (MulOpposite.op r) b).symm
  obtain ⟨f, hf, _⟩ := universal B q hq
  exact ⟨f, fun b => (hf b (ULift.up 1)).trans (one_smul Rᵐᵒᵖ b)⟩

private theorem complexWatts_linear_iff {S R : RingCat.{u}}
    [Algebra Complex S] [Algebra Complex R]
    (B : ModuleCat.{max u v} S) [Module Rᵐᵒᵖ B] [SMulCommClass Rᵐᵒᵖ S B]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} S)
    (p : ∀ X : ModuleCat.{max u v} R, B → X → F.obj X)
    (universal : ∀ X : ModuleCat.{max u v} R, complexWattsBalanced B X (F.obj X) (p X) ∧
      ∀ (Y : ModuleCat.{max u v} S) (q : B → X → Y), complexWattsBalanced B X Y q →
        ∃! f : F.obj X →ₗ[S] Y, ∀ b x, f (p X b x) = q b x)
    (map_pure : ∀ (X Y : ModuleCat.{max u v} R) (f : X ⟶ Y) (b : B) (x : X),
      (F.map f).hom (p X b x) = p Y b (f.hom x)) :
    (∀ (z : Complex) (b : B),
      algebraMap Complex S z • b = MulOpposite.op (algebraMap Complex R z) • b) ↔
      F.Linear Complex := by
  -- The scalar refinement adds a balanced-tensor calculation to the tensor
  -- functor in Alphabeta Math, cor-eilenberg-watts-is-an-equivalence-of-hom-categories,
  -- step 1.1. Scaled identity maps suffice by Mathlib's linearity criterion.
  rw [Functor.linear_iff]
  constructor
  · intro equalScalars X z
    obtain ⟨hp, hu⟩ := universal X
    apply complexWatts_hom_ext hp hu
    intro b x
    calc
      (F.map (z • 𝟙 X)).hom (p X b x) =
          p X b (algebraMap Complex R z • x) := map_pure X X (z • 𝟙 X) b x
      _ = p X (MulOpposite.op (algebraMap Complex R z) • b) x := (hp.2.2.2 _ _ _).symm
      _ = p X (algebraMap Complex S z • b) x := by rw [equalScalars]
      _ = (z • 𝟙 (F.obj X)).hom (p X b x) := hp.2.2.1 _ _ _
  · intro linear z b
    -- At 1 in the lifted regular module the scaled identity sends 1 to
    -- the scalar times 1. Balancing only needs this value of the endomorphism.
    -- The contraction recovers equality in B from the elementary tensors.
    let X : ModuleCat.{max u v} R := ModuleCat.of R (ULift.{v} R)
    let one : X := ULift.up 1
    obtain ⟨hp, hu⟩ := universal X
    obtain ⟨f, hf⟩ := complexWatts_regular_retraction (p X) hu
    -- Form the scaled identity with a symbolic module, using the same
    -- hom scalar action as the linearity criterion.
    let scaledId (M : ModuleCat.{max u v} R) : M ⟶ M := z • 𝟙 M
    have compare : (z • 𝟙 (F.obj X)).hom (p X b one) =
        (F.map (scaledId X)).hom (p X b one) :=
      congrArg (fun g : F.obj X ⟶ F.obj X => g.hom (p X b one)) (linear X z).symm
    have h : p X (algebraMap Complex S z • b) one =
        p X (MulOpposite.op (algebraMap Complex R z) • b) one := calc
      _ = algebraMap Complex S z • p X b one := hp.2.2.1 _ _ _
      _ = (z • 𝟙 (F.obj X)).hom (p X b one) := rfl
      _ = (F.map (scaledId X)).hom (p X b one) := compare
      _ = p X b (algebraMap Complex R z • one) := map_pure X X (scaledId X) b one
      _ = _ := (hp.2.2.2 _ _ _).symm
    exact (hf _).symm.trans ((congrArg (fun y => f y) h).trans (hf _))

private theorem complexWatts_restrict {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (hPQ : ∀ X, P X ↔ Q (e.functor.obj X))
    (hQ : ∀ {X Y : D}, (X ≅ Y) → Q X → Q Y) :
    ∃ restricted : P.FullSubcategory ≌ Q.FullSubcategory,
      restricted.functor ⋙ Q.ι = P.ι ⋙ e.functor := by
  -- Alphabeta Math, cor-eilenberg-watts-is-an-equivalence-of-hom-categories,
  -- steps 1.2–1.3 and 2.1. Full faithfulness passes through the two full
  -- subcategories. The existing counit supplies preimages in the restricted
  -- category after transporting the property backwards along it.
  let lift := Q.lift (P.ι ⋙ e.functor) (fun X => (hPQ X.obj).mp X.property)
  have : lift.EssSurj := ⟨fun Y => by
    let X := e.inverse.obj Y.obj
    let i : e.functor.obj X ≅ Y.obj := e.counitIso.app Y.obj
    let X' : P.FullSubcategory := ⟨X, (hPQ X).mpr (hQ i.symm Y.property)⟩
    exact ⟨X', ⟨Q.isoMk i⟩⟩⟩
  have : lift.IsEquivalence := { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact ⟨lift.asEquivalence, rfl⟩

end
