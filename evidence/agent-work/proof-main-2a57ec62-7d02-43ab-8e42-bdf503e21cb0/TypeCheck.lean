import MackeyDiagrams
import Proofs.ComplexEilenbergWatts
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionAdjunction
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.ModuleTensorUniversalProperty
import Proofs.BalancedTensorAssociativity
set_option maxHeartbeats 4000000
universe u v
#check (
∀ {U : Type u} [Group U],
  let Alg := fun H : Subgroup U => MonoidAlgebra Complex H
  let Mod := fun H : Subgroup U => ModuleCat.{max u v} (Alg H)
  let Fun := fun K H : Subgroup U => CategoryTheory.Functor (Mod H) (Mod K)
  let Bimod := fun K H : Subgroup U => Rep.{max u v} Complex (Prod K H)
  let V := fun {H : Subgroup U} (X : Mod H) =>
    (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).obj X
  let VMap := fun {H : Subgroup U} {X Y : Mod H} (f : ModuleCat.Hom X Y) =>
    (Rep.Hom.hom ((Rep.ofModuleMonoidAlgebra (k := Complex) (G := H)).map f)).toLinearMap
  let regular := fun H : Subgroup U => ModuleCat.of (Alg H) (ULift.{v} (Alg H))
  let left := fun {K H : Subgroup U} (B : Bimod K H) (k : K) => B.ρ (k, 1)
  let right := fun {K H : Subgroup U} (B : Bimod K H) (h : H) => B.ρ (1, h⁻¹)
  let leftAlg := fun {K H : Subgroup U} (B : Bimod K H) (a : Alg K) (b : B) =>
    MackeyDiagrams.freeLift Complex (fun k : K => left B k b) (MonoidAlgebra.coeff a)
  let rightAlg := fun {K H : Subgroup U} (B : Bimod K H) (b : B) (a : Alg H) =>
    MackeyDiagrams.freeLift Complex (fun h : H => right B h b) (MonoidAlgebra.coeff a)
  let Word := fun K H : Subgroup U => MackeyDiagrams.Word K H
  let wordVec := fun {K H : Subgroup U} (p : Word K H) =>
    Finsupp (MackeyDiagrams.Word.basis p).carrier Complex
  let lower := fun {K H : Subgroup U} (p : Word K H) =>
    (ULift.moduleEquiv : LinearEquiv (RingHom.id Complex) (ULift.{v} (wordVec p)) (wordVec p))
  let wordBimod := fun {K H : Subgroup U} (p : Word K H) =>
    (Rep.of
      ({ toFun := fun g => (lower p).symm.toLinearMap.comp
            ((MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) g).comp
              (lower p).toLinearMap)
         map_one' := by
           ext x
           simp
         map_mul' := by
           intro g h
           have actMul :
               MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) (g * h) =
                 (MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) g).comp
                 (MackeyDiagrams.Biset.actLinear Complex (MackeyDiagrams.Word.basis p) h) := by
             apply Finsupp.lhom_ext
             intro i z
             simp [MackeyDiagrams.Biset.mul_act]
           ext x
           simp [actMul] } :
        Representation Complex (Prod K H) (ULift.{v} (wordVec p))) : Bimod K H)
  let wordHom := fun {K H : Subgroup U} (p q : Word K H) =>
    MackeyDiagrams.Biset.Hom Complex (MackeyDiagrams.Word.basis p) (MackeyDiagrams.Word.basis q)
  let allowedOrdinary := fun {K H : Subgroup U} {p q : Word K H}
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
  let drawing := fun {K H : Subgroup U} (p q : Word K H) =>
    MackeyDiagrams.LabelledDrawing Complex p q
  let allowed := fun {K H : Subgroup U} {p q : Word K H} (d : drawing p q) =>
    MackeyDiagrams.LabelledDrawing.rec (motive := fun _ _ _ => Prop)
      (fun d => allowedOrdinary d)
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
  let drawingEval := fun {K H : Subgroup U} {p q : Word K H} (d : drawing p q) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d)
  let good := fun (K H : Subgroup U) (F : Fun K H) =>
    CategoryTheory.Functor.Linear Complex F ∧
    CategoryTheory.Limits.PreservesFiniteColimits F ∧
    ∀ I : Type (max u v),
      CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F
  let goodFun := fun K H => CategoryTheory.ObjectProperty.FullSubcategory (good K H)
  let Ind := fun {H G : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H G) =>
    (CategoryTheory.Functor.comp
      (CategoryTheory.Functor.comp (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H))
        (Rep.indFunctor Complex a.toHom))
      (Rep.toModuleMonoidAlgebra (k := Complex) (G := G)) : Fun G H)
  let Res := fun {H G : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H G) =>
    (ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom).toRingHom :
      Fun H G)
  let conjugateMap := fun {K H : Subgroup U} {p q : Word K H} (f : wordHom p q) =>
    (lower q).symm.toLinearMap.comp (f.toLinearMap.comp (lower p).toLinearMap)
  let wordMap := fun {K H : Subgroup U} {p q : Word K H} (f : wordHom p q) =>
    (Rep.ofHom
      { toLinearMap := conjugateMap f
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          simpa [wordBimod, conjugateMap] using
            congrArg (fun y => (lower q).symm y)
              (MackeyDiagrams.Biset.Hom.commutes f g (lower p x)) } :
      Quiver.Hom (wordBimod p) (wordBimod q))
  let Balanced := fun {K H : Subgroup U} (B : Bimod K H) (X : Mod H) (Y : Mod K)
      (t : LinearMap (RingHom.id Complex) B
        (LinearMap (RingHom.id Complex) (V X) (V Y))) =>
    (∀ (a : Alg K) (b : B) (x : V X),
      let y : Y := t b x
      t (leftAlg B a b) x = a • y) ∧
    (∀ (a : Alg H) (b : B) (x : V X),
      let x' : X := x
      t (rightAlg B b a) x = t b (a • x'))
  let gen := fun {K H : Subgroup U} {p q : Word K H} =>
    {d : drawing p q // allowed d}
  let evalSetoid := fun {K H : Subgroup U} (p q : Word K H) =>
    Setoid.ker (fun d : @gen K H p q => drawingEval d.val)
  let genHom := fun {K H : Subgroup U} (p q : Word K H) => Quotient (evalSetoid p q)
  (∀ (H G : Subgroup U) (a : MackeyDiagrams.ConjEmbedding H G),
    letI : Module (MulOpposite (Alg H)) (Alg G) :=
      Module.compHom (Alg G) (RingHom.op
        (MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom).toRingHom)
    Module.Free (MulOpposite (Alg H)) (Alg G)) ∧
  ∃ E : ∀ K H : Subgroup U, CategoryTheory.Equivalence (Bimod K H) (goodFun K H),
  let transport := fun K H : Subgroup U =>
    CategoryTheory.Functor.comp (E K H).functor (CategoryTheory.ObjectProperty.ι (good K H))
  let tensor := fun {K H : Subgroup U} (B : Bimod K H) => (transport K H).obj B
  let T := fun {K H : Subgroup U} (p : Word K H) => tensor (wordBimod p)
  let liftMap := fun {K H : Subgroup U} {p q : Word K H} (f : wordHom p q) =>
    (transport K H).map (wordMap f)
  let diagramMap := fun {K H : Subgroup U} {p q : Word K H} (d : drawing p q) =>
    liftMap (drawingEval d)
  ∃ (pure : ∀ {K H : Subgroup U} (B : Bimod K H) (X : Mod H),
        LinearMap (RingHom.id Complex) B (LinearMap (RingHom.id Complex) (V X) (V ((tensor B).obj X))))
    (unit : ∀ {K H : Subgroup U} (B : Bimod K H),
        LinearEquiv (RingHom.id Complex) (V ((tensor B).obj (regular H))) B)
    (compIso : ∀ {K L H : Subgroup U} (p : Word K L) (q : Word L H),
        CategoryTheory.Iso (T (MackeyDiagrams.Word.tensor p q)) (CategoryTheory.Functor.comp (T q) (T p)))
    (emptyIso : ∀ H : Subgroup U,
        CategoryTheory.Iso (T (MackeyDiagrams.Word.empty H)) (CategoryTheory.Functor.id (Mod H))),
  let onRegular := fun {K H : Subgroup U} {p q : Word K H}
      (η : CategoryTheory.NatTrans (T p) (T q)) =>
    (unit (wordBimod q)).toLinearMap.comp
      ((VMap (η.app (regular H))).comp (unit (wordBimod p)).symm.toLinearMap)
  let inDiagram := fun {K H : Subgroup U} {p q : Word K H}
      (η : CategoryTheory.NatTrans (T p) (T q)) =>
    ∃ d : @gen K H p q, onRegular η = conjugateMap (drawingEval d.val)
  let pair := fun {K L H : Subgroup U} (p : Word K L) (q : Word L H)
      (b : wordBimod p) (c : wordBimod q) =>
    (lower (MackeyDiagrams.Word.tensor p q)).symm
      (MackeyDiagrams.Biset.pairLinear Complex
        (MackeyDiagrams.Word.basis p) (MackeyDiagrams.Word.basis q) (lower p b) (lower q c))
  (∀ (K H : Subgroup U) (B : Bimod K H) (z : Complex) (b : B),
    leftAlg B (algebraMap Complex (Alg K) z) b = z • b ∧
    rightAlg B b (algebraMap Complex (Alg H) z) = z • b) ∧
  (∀ K H : Subgroup U, CategoryTheory.Functor.Linear Complex (transport K H)) ∧
  (∀ (K H : Subgroup U) (I : Type (max u v)),
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) (transport K H)) ∧
  (∀ (K H : Subgroup U) (B : Bimod K H) (X : Mod H),
    Balanced B X ((tensor B).obj X) (pure B X) ∧
    ∀ (Y : Mod K) (t : LinearMap (RingHom.id Complex) B
        (LinearMap (RingHom.id Complex) (V X) (V Y))),
      Balanced B X Y t →
      ∃! f : ModuleCat.Hom ((tensor B).obj X) Y,
        ∀ (b : B) (x : V X), VMap f (pure B X b x) = t b x) ∧
  (∀ (K H : Subgroup U) (B : Bimod K H) (X Y : Mod H)
      (f : ModuleCat.Hom X Y) (b : B) (x : V X),
    VMap ((tensor B).map f) (pure B X b x) = pure B Y b (VMap f x)) ∧
  (∀ (K H : Subgroup U) (B C : Bimod K H) (f : Quiver.Hom B C)
      (X : Mod H) (b : B) (x : V X),
    VMap (((transport K H).map f).app X) (pure B X b x) =
      pure C X ((Rep.Hom.hom f).toLinearMap b) x) ∧
  (∀ (K H : Subgroup U) (B : Bimod K H) (b : B) (x : V (regular H)),
    unit B (pure B (regular H) b x) = rightAlg B b (ULift.down x)) ∧
  (∀ (H : Subgroup U) (X : Mod H) (b : wordBimod (MackeyDiagrams.Word.empty H)) (x : V X),
    let p := MackeyDiagrams.Word.empty H
    let x' : X := x
    VMap ((emptyIso H).hom.app X) (pure (wordBimod p) X b x) =
      (MonoidAlgebra.ofCoeff (lower p b) : Alg H) • x') ∧
  (∀ (H G : Subgroup U) (a : MackeyDiagrams.ConjEmbedding H G),
    Nonempty (CategoryTheory.Iso (T (MackeyDiagrams.Word.up a)) (Ind a)) ∧
    Nonempty (CategoryTheory.Iso (T (MackeyDiagrams.Word.down a)) (Res a))) ∧
  (∀ (K L H : Subgroup U) (p : Word K L) (q : Word L H) (X : Mod H)
      (b : wordBimod p) (c : wordBimod q) (x : V X),
    VMap ((compIso p q).hom.app X)
        (pure (wordBimod (MackeyDiagrams.Word.tensor p q)) X (pair p q b c) x) =
      pure (wordBimod p) ((T q).obj X) b (pure (wordBimod q) X c x)) ∧
  (∀ (K H : Subgroup U) (p : Word K H), CategoryTheory.Limits.PreservesFiniteLimits (T p)) ∧
  (∀ (K H : Subgroup U) (p q : Word K H),
    Function.Bijective (@liftMap K H p q) ∧
    (∀ f : wordHom p q, onRegular (liftMap f) = conjugateMap f) ∧
    ∃ e : Equiv (genHom p q) {η : CategoryTheory.NatTrans (T p) (T q) // inDiagram η},
      ∀ d : @gen K H p q,
        (e (Quotient.mk (evalSetoid p q) d)).val = diagramMap d.val) ∧
  (∀ (K H : Subgroup U) (p : Word K H),
    diagramMap (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id p)) = CategoryTheory.CategoryStruct.id (T p)) ∧
  (∀ (K H : Subgroup U) (p q r : Word K H)
      (d : drawing p q) (e : drawing q r),
    diagramMap (MackeyDiagrams.LabelledDrawing.vertical d e) =
      CategoryTheory.CategoryStruct.comp (diagramMap d) (diagramMap e)) ∧
  (∀ (K H : Subgroup U) (p q : Word K H) (d e : drawing p q) (z : Complex),
    diagramMap (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero p q)) = 0 ∧
    diagramMap (MackeyDiagrams.LabelledDrawing.add d e) = diagramMap d + diagramMap e ∧
    diagramMap (MackeyDiagrams.LabelledDrawing.scale z d) = z • diagramMap d) ∧
  (∀ (K L H : Subgroup U) (p p' : Word K L) (q q' : Word L H)
      (d : drawing p p') (e : drawing q q'),
    CategoryTheory.CategoryStruct.comp
        (diagramMap (MackeyDiagrams.LabelledDrawing.horizontal d e)) (compIso p' q').hom =
      CategoryTheory.CategoryStruct.comp (compIso p q).hom
        (CategoryTheory.NatTrans.hcomp (diagramMap e) (diagramMap d))) ∧
  (∀ K H : Subgroup U,
    letI : CategoryTheory.Limits.HasFiniteBiproducts (Bimod K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    letI : CategoryTheory.Limits.HasFiniteBiproducts (Fun K H) :=
      CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
    let bimodSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => wordBimod (p i))
    let funSum := fun {n : Nat} (p : Fin n → Word K H) =>
      CategoryTheory.Limits.biproduct (fun i => T (p i))
    ∃ sumIso : ∀ {n : Nat} (p : Fin n → Word K H),
        CategoryTheory.Iso (tensor (bimodSum p)) (funSum p),
      ∀ {m n : Nat} (p : Fin m → Word K H) (q : Fin n → Word K H),
        (∀ f : ∀ i j, wordHom (p i) (q j),
          CategoryTheory.CategoryStruct.comp
            ((transport K H).map (CategoryTheory.Limits.biproduct.matrix
              (fun i j => wordMap (f i j)))) (sumIso q).hom =
          CategoryTheory.CategoryStruct.comp (sumIso p).hom
            (CategoryTheory.Limits.biproduct.matrix (fun i j => liftMap (f i j)))) ∧
        (∀ η : CategoryTheory.NatTrans (funSum p) (funSum q),
          (∀ i j, inDiagram (CategoryTheory.Limits.biproduct.components
            (f := fun i => T (p i)) (g := fun j => T (q j)) η i j)) ↔
          ∃ d : ∀ i j, @gen K H (p i) (q j),
            η = CategoryTheory.Limits.biproduct.matrix (fun i j => diagramMap (d i j).val)))
)
