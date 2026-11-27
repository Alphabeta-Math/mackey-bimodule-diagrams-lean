import MackeyDiagrams
import Proofs.FiniteParabolicBicategoryComposition
import Proofs.BimoduleTensorBicategoryCoherence

set_option maxHeartbeats 2000000

theorem FiniteParabolicBimoduleBicategory : (
let P := Equiv.Perm Nat
let Finitary := Subgroup.closure {s : P | Equiv.Perm.IsSwap s}
let blockSym := fun (D : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ D))
let blockProduct := fun {m : Nat} (D : Fin m → Finset Nat) =>
  iSup (fun i => blockSym (D i))
let Parabolic := fun (S : Subgroup P) =>
  ∃ (m : Nat) (D : Fin m → Finset Nat),
    (∀ i, Finset.Nonempty (D i)) ∧ Pairwise (fun i j => Disjoint (D i) (D j)) ∧
    S = blockProduct D
let conjugate := fun (s : P) (S : Subgroup P) =>
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) S
let embed := fun {S T : Subgroup P} (s : P) (h : conjugate s S ≤ T) =>
  MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := T) s
    (fun x => h ⟨(x : P), x.property, rfl⟩)
let Span := fun (K H : Subgroup P) =>
  Σ L : {S : Subgroup P // Parabolic S},
    {α : ↥Finitary // conjugate (α : P) L.val ≤ K} ×
    {β : ↥Finitary // conjugate (β : P) L.val ≤ H}
let pairWord := fun {K H L : Subgroup P}
    (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H) =>
  MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.down b)
let spanBasis := fun {K H : Subgroup P} (S : Span K H) =>
  MackeyDiagrams.Word.basis
    (pairWord (embed (S.2.1.val : P) S.2.1.property) (embed (S.2.2.val : P) S.2.2.property))
let sumBasis := fun {K H : Subgroup P} {ι : Type} (Z : ι → MackeyDiagrams.Biset K H) =>
  ({ carrier := Sigma (fun i => (Z i).carrier)
     act := fun g z => ⟨z.1, (Z z.1).act g z.2⟩
     one_act := fun z => Sigma.ext rfl (heq_of_eq ((Z z.1).one_act z.2))
     mul_act := fun g h z => Sigma.ext rfl (heq_of_eq ((Z z.1).mul_act g h z.2)) } :
    MackeyDiagrams.Biset K H)
let Object := {H : Subgroup P // Parabolic H}
let linearize := fun {K H : Subgroup P} (X : MackeyDiagrams.Biset K H) =>
  letI : MulAction (K × H) (ULift.{u} X.carrier) :=
    { smul := fun g x => ⟨X.act g x.down⟩
      one_smul := fun x => congrArg ULift.up (X.one_act x.down)
      mul_smul := fun g h x => congrArg ULift.up (X.mul_act g h x.down) }
  Rep.ofMulAction Complex (K × H) (ULift.{u} X.carrier)
let regular := fun (H : Object) => linearize (MackeyDiagrams.Biset.regular H.val)
let Admissible := fun (K H : Object) (X : Rep.{u} Complex (K.val × H.val)) =>
  ∃ (m : Nat) (S : Fin m → Span K.val H.val),
    Nonempty (CategoryTheory.Iso X (linearize (sumBasis (fun i => spanBasis (S i)))))
let Mor := fun (K H : Object) => {X : Rep.{u} Complex (K.val × H.val) // Admissible K H X}
let Hom := fun {K H : Object} (X Y : Mor K H) => Rep.Hom X.val Y.val
let Iso := fun {K H : Object} (X Y : Mor K H) => CategoryTheory.Iso X.val Y.val
let idMap := fun {K H : Object} (X : Mor K H) =>
  (CategoryTheory.CategoryStruct.id X.val : Hom X X)
let comp := fun {K H : Object} {X Y Z : Mor K H} (f : Hom X Y) (g : Hom Y Z) =>
  (CategoryTheory.CategoryStruct.comp (X := X.val) (Y := Y.val) (Z := Z.val) f g : Hom X Z)
let leftAct := fun {K H : Object} (X : Mor K H)
    (a : MonoidAlgebra Complex K.val) (x : X.val.V) =>
  Finsupp.sum a.coeff (fun k c => c • X.val.ρ (k, 1) x)
let rightAct := fun {K H : Object} (X : Mor K H)
    (a : MonoidAlgebra Complex H.val) (x : X.val.V) =>
  Finsupp.sum a.coeff (fun h c => c • X.val.ρ (1, h⁻¹) x)
let IsBalanced := fun {K H J : Object} (X : Mor K H) (Y : Mor H J)
    (V : Type u) [AddCommGroup V] [Module Complex V]
    (b : LinearMap (RingHom.id Complex) X.val.V
      (LinearMap (RingHom.id Complex) Y.val.V V)) =>
  ∀ (a : MonoidAlgebra Complex H.val) x y, b (rightAct X a x) y = b x (leftAct Y a y)
(∀ H : Object, H.val ≤ Finitary) ∧
∃ (unitAdmissible : ∀ H : Object, Admissible H H (regular H)),
  let unit := fun (H : Object) => (⟨regular H, unitAdmissible H⟩ : Mor H H)
  ∃ (tensor : ∀ {K H J : Object}, Mor K H → Mor H J → Mor K J)
    (tmul : ∀ {K H J : Object} (X : Mor K H) (Y : Mor H J),
      LinearMap (RingHom.id Complex) X.val.V
        (LinearMap (RingHom.id Complex) Y.val.V (tensor X Y).val.V))
    (tensorMap : ∀ {K H J : Object} {X X' : Mor K H} {Y Y' : Mor H J},
      Hom X X' → Hom Y Y' → Hom (tensor X Y) (tensor X' Y'))
    (assoc : ∀ {K H J F : Object} (X : Mor K H) (Y : Mor H J) (Z : Mor J F),
      Iso (tensor (tensor X Y) Z) (tensor X (tensor Y Z)))
    (leftUnit : ∀ {K H : Object} (X : Mor K H), Iso (tensor (unit K) X) X)
    (rightUnit : ∀ {K H : Object} (X : Mor K H), Iso (tensor X (unit H)) X),
    (∀ {K H J : Object} (X : Mor K H) (Y : Mor H J),
      IsBalanced X Y (tensor X Y).val.V (tmul X Y) ∧
      (∀ (a : MonoidAlgebra Complex K.val) (c : MonoidAlgebra Complex J.val) x y,
        tmul X Y (leftAct X a x) (rightAct Y c y) =
          leftAct (tensor X Y) a (rightAct (tensor X Y) c (tmul X Y x y))) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module Complex V]
        (b : LinearMap (RingHom.id Complex) X.val.V
          (LinearMap (RingHom.id Complex) Y.val.V V)),
        IsBalanced X Y V b →
        ∃! lift : LinearMap (RingHom.id Complex) (tensor X Y).val.V V,
          ∀ x y, lift (tmul X Y x y) = b x y) ∧
    (∀ {K H J : Object} {X X' : Mor K H} {Y Y' : Mor H J}
        (f : Hom X X') (g : Hom Y Y') x y,
      (Rep.Hom.hom (tensorMap f g)) (tmul X Y x y) =
        tmul X' Y' ((Rep.Hom.hom f) x) ((Rep.Hom.hom g) y)) ∧
    (∀ {K H J : Object} (X : Mor K H) (Y : Mor H J),
      tensorMap (idMap X) (idMap Y) = idMap (tensor X Y)) ∧
    (∀ {K H J : Object} {X X' X'' : Mor K H} {Y Y' Y'' : Mor H J}
        (f : Hom X X') (f' : Hom X' X'') (g : Hom Y Y') (g' : Hom Y' Y''),
      tensorMap (comp f f') (comp g g') = comp (tensorMap f g) (tensorMap f' g')) ∧
    (∀ {K H J F : Object} (X : Mor K H) (Y : Mor H J) (Z : Mor J F) x y z,
      (Rep.Hom.hom (CategoryTheory.Iso.hom (assoc X Y Z)))
        (tmul (tensor X Y) Z (tmul X Y x y) z) =
        tmul X (tensor Y Z) x (tmul Y Z y z)) ∧
    (∀ {K H : Object} (X : Mor K H)
        (a : MonoidAlgebra Complex K.val) (b : MonoidAlgebra Complex H.val) x,
      (Rep.Hom.hom (CategoryTheory.Iso.hom (leftUnit X)))
        (tmul (unit K) X (MonoidAlgebra.mapDomain ULift.up a) x) = leftAct X a x ∧
      (Rep.Hom.hom (CategoryTheory.Iso.hom (rightUnit X)))
        (tmul X (unit H) x (MonoidAlgebra.mapDomain ULift.up b)) = rightAct X b x) ∧
    (∀ {K H J F : Object} {X X' : Mor K H} {Y Y' : Mor H J} {Z Z' : Mor J F}
        (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z'),
      comp (tensorMap (tensorMap f g) h) (CategoryTheory.Iso.hom (assoc X' Y' Z')) =
        comp (CategoryTheory.Iso.hom (assoc X Y Z)) (tensorMap f (tensorMap g h))) ∧
    (∀ {K H : Object} {X X' : Mor K H} (f : Hom X X'),
      comp (tensorMap (idMap (unit K)) f) (CategoryTheory.Iso.hom (leftUnit X')) =
        comp (CategoryTheory.Iso.hom (leftUnit X)) f ∧
      comp (tensorMap f (idMap (unit H))) (CategoryTheory.Iso.hom (rightUnit X')) =
        comp (CategoryTheory.Iso.hom (rightUnit X)) f) ∧
    (∀ {K H J F E : Object} (W : Mor K H) (X : Mor H J) (Y : Mor J F) (Z : Mor F E),
      comp (CategoryTheory.Iso.hom (assoc (tensor W X) Y Z))
          (CategoryTheory.Iso.hom (assoc W X (tensor Y Z))) =
        comp (tensorMap (CategoryTheory.Iso.hom (assoc W X Y)) (idMap Z))
          (comp (CategoryTheory.Iso.hom (assoc W (tensor X Y) Z))
            (tensorMap (idMap W) (CategoryTheory.Iso.hom (assoc X Y Z))))) ∧
    (∀ {K H J : Object} (X : Mor K H) (Y : Mor H J),
      comp (CategoryTheory.Iso.hom (assoc X (unit H) Y))
          (tensorMap (idMap X) (CategoryTheory.Iso.hom (leftUnit Y))) =
        tensorMap (CategoryTheory.Iso.hom (rightUnit X)) (idMap Y))
) :=
(by
  -- Xiao, Corollary 7.5 and § 7.5, p. 32 in the archived original and
  -- p. 34 in the published 28 November revision.
  -- Alphabeta Math, Morita bicategory coherence, steps 1.1–1.3, 2.1–2.2
  -- and 3.1. The composition supplier checks the canonical maps and laws
  -- on pure tensors for these complex representations. Its balance and
  -- lift laws apply to the same tensor witnesses, with the inverse right
  -- action on the second group factor. The general Morita theorem uses
  -- a different quotient model, so this proof takes the laws directly
  -- from the composition supplier along with its admissibility proofs.
  -- The identity-span isomorphism and the explicit double-coset formula
  -- are the two additional clauses of that supplier.
  obtain ⟨hFinitary, _, hUnitAdmissible, tensor, tmul, tensorMap, assoc,
    leftUnit, rightUnit, hTensor, hTensorMap, hId, hComp, hAssoc,
    hUnits, hAssocNatural, hUnitsNatural, hPentagon, hTriangle, _⟩ :=
    FiniteParabolicBicategoryComposition.{u}
  exact ⟨hFinitary, hUnitAdmissible, tensor, tmul, tensorMap, assoc,
    leftUnit, rightUnit, hTensor, hTensorMap, hId, hComp, hAssoc,
    hUnits, hAssocNatural, hUnitsNatural, hPentagon, hTriangle⟩)

#print axioms FiniteParabolicBimoduleBicategory
