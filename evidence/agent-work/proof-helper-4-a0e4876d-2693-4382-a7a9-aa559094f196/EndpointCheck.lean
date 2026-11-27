import Final
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.GroupTheory.Perm.ClosureSwap

universe u
set_option maxHeartbeats 2000000 in
example : (
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
let inverseEmbed := fun {S T : Subgroup P} (s : P) (h : T ≤ conjugate s S) =>
  MackeyDiagrams.ConjEmbedding.ofConjugator (H := T) (G := S) s⁻¹ (by
    intro x
    obtain ⟨y, hy, he⟩ := h x.property
    change s * y * s⁻¹ = (x : P) at he
    rw [← he]
    have cancel : s⁻¹ * (s * y * s⁻¹) * (s⁻¹)⁻¹ = y := by group
    rw [cancel]
    exact hy)
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
let inside := fun (H A : Subgroup P) => Subgroup.comap (Subgroup.subtype H) A
let Cosets := fun (H A B : Subgroup P) =>
  DoubleCoset.Quotient (inside H A : Set H) (inside H B : Set H)
let classOf := fun (H A B : Subgroup P) (r : H) => DoubleCoset.mk (inside H A) (inside H B) r
let OrderedSection := fun (H A B : Subgroup P) (r : Cosets H A B → H) =>
  ∃ (X : Finset Nat) (m p q : Nat)
    (D : Fin m → Finset Nat) (U : Fin p → Finset Nat) (V : Fin q → Finset Nat),
    (∀ i, Finset.Nonempty (D i)) ∧
    (∀ a, Finset.Nonempty (U a)) ∧
    (∀ b, Finset.Nonempty (V b)) ∧
    Pairwise (fun i j => Disjoint (D i) (D j)) ∧
    Pairwise (fun a a' => Disjoint (U a) (U a')) ∧
    Pairwise (fun b b' => Disjoint (V b) (V b')) ∧
    (∀ n : Nat, n ∈ X ↔ ∃ i, n ∈ D i) ∧
    (∀ n : Nat, n ∈ X ↔ ∃ a, n ∈ U a) ∧
    (∀ n : Nat, n ∈ X ↔ ∃ b, n ∈ V b) ∧
    H = blockProduct D ∧ A = blockProduct U ∧ B = blockProduct V ∧
    (∀ a, ∃ i, U a ⊆ D i) ∧
    (∀ b, ∃ i, V b ⊆ D i) ∧
    let rows := fun i : Fin m => Finset.filter (fun a : Fin p => U a ⊆ D i) Finset.univ
    let cols := fun i : Fin m => Finset.filter (fun b : Fin q => V b ⊆ D i) Finset.univ
    let row := fun (i : Fin m) (a : Fin (Finset.card (rows i))) =>
      U (Finset.orderIsoOfFin (rows i) rfl a).val
    let col := fun (i : Fin m) (b : Fin (Finset.card (cols i))) =>
      V (Finset.orderIsoOfFin (cols i) rfl b).val
    let Mat := fun i : Fin m =>
      {R : Fin (Finset.card (rows i)) → Fin (Finset.card (cols i)) → Nat //
        (∀ a, Finset.sum Finset.univ (R a) = Finset.card (row i a)) ∧
        (∀ b, Finset.sum Finset.univ (fun a => R a b) = Finset.card (col i b))}
    let rank := fun (S : Finset Nat) (x : ↥S) =>
      ((Finset.orderIsoOfFin S rfl).symm x).val
    ∃ classify : Cosets H A B ≃ (∀ i : Fin m, Mat i),
      (∀ (s : H) (i : Fin m) a b,
        (classify (classOf H A B s) i).val a b =
          Finset.card (row i a ∩ Finset.map (Equiv.toEmbedding (s : P)) (col i b))) ∧
      (∀ j : Cosets H A B, classOf H A B (r j) = j) ∧
      ∀ (j : Cosets H A B) (i : Fin m) a b (x : ↥(row i a)) (y : ↥(col i b)),
        (r j : P) y.val = x.val ↔
          ∃ k : Fin ((classify j i).val a b),
            rank (row i a) x =
              Finset.sum (Finset.Iio b) (fun b' => (classify j i).val a b') + k.val ∧
            rank (col i b) y =
              Finset.sum (Finset.Iio a) (fun a' => (classify j i).val a' b) + k.val
let sumBasis := fun {K H : Subgroup P} {ι : Type} (Z : ι → MackeyDiagrams.Biset K H) =>
  ({ carrier := Sigma (fun i => (Z i).carrier)
     act := fun g z => ⟨z.1, (Z z.1).act g z.2⟩
     one_act := fun z => Sigma.ext rfl (heq_of_eq ((Z z.1).one_act z.2))
     mul_act := fun g h z => Sigma.ext rfl (heq_of_eq ((Z z.1).mul_act g h z.2)) } :
    MackeyDiagrams.Biset K H)
let vectors := fun {K H : Subgroup P} (X : MackeyDiagrams.Biset K H) =>
  Finsupp X.carrier Complex
let Equivariant := fun {K H : Subgroup P} {X Y : MackeyDiagrams.Biset K H}
    (e : LinearEquiv (RingHom.id Complex) (vectors X) (vectors Y)) =>
  ∀ g x, e (MackeyDiagrams.Biset.actLinear Complex X g x) =
    MackeyDiagrams.Biset.actLinear Complex Y g (e x)
let Distributes := fun {K H J : Subgroup P} {ι κ : Type}
    (X : ι → MackeyDiagrams.Biset K H) (Y : κ → MackeyDiagrams.Biset H J) =>
  let source := MackeyDiagrams.Biset.tensor (sumBasis X) (sumBasis Y)
  let target := sumBasis (fun ij : ι × κ => MackeyDiagrams.Biset.tensor (X ij.1) (Y ij.2))
  ∃ e : LinearEquiv (RingHom.id Complex) (vectors source) (vectors target),
    Equivariant e ∧
    ∀ (i : ι) (j : κ) (x : (X i).carrier) (y : (Y j).carrier),
      e (MackeyDiagrams.Biset.pairLinear Complex (sumBasis X) (sumBasis Y)
          (Finsupp.single ⟨i, x⟩ 1) (Finsupp.single ⟨j, y⟩ 1)) =
        Finsupp.single ⟨(i, j), MackeyDiagrams.Biset.pair (X i) (Y j) x y⟩ 1
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
(∀ H : Object, Nonempty (CategoryTheory.Iso (regular H)
  (linearize (MackeyDiagrams.Word.basis
    (pairWord (MackeyDiagrams.ConjEmbedding.id H.val)
      (MackeyDiagrams.ConjEmbedding.id H.val)))))) ∧
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
        tensorMap (CategoryTheory.Iso.hom (rightUnit X)) (idMap Y)) ∧
    (∀ (K H J : Object) (m n : Nat) (S : Fin m → Span K.val H.val)
        (T : Fin n → Span H.val J.val),
      let A := fun i => conjugate ((S i).2.2.val : P) (S i).1.val
      let B := fun j => conjugate ((T j).2.1.val : P) (T j).1.val
      let Q := fun (i : Fin m) (j : Fin n) => Cosets H.val (A i) (B j)
      (∀ i j, Finite (Q i j)) ∧
      (∀ i j, ∃ r : Q i j → H.val, OrderedSection H.val (A i) (B j) r) ∧
      ∀ (r : ∀ i j, Q i j → H.val)
        (_ : ∀ i j k, classOf H.val (A i) (B j) (r i j k) = k),
        let L := fun i j k => A i ⊓ conjugate (r i j k : P) (B j)
        let left := fun i j k =>
          MackeyDiagrams.ConjEmbedding.comp
            (embed ((S i).2.1.val : P) (S i).2.1.property)
            (inverseEmbed ((S i).2.2.val : P) (show L i j k ≤ A i from inf_le_left))
        let right := fun i j k =>
          MackeyDiagrams.ConjEmbedding.comp
            (embed ((T j).2.2.val : P) (T j).2.2.property)
            (MackeyDiagrams.ConjEmbedding.comp
              (inverseEmbed ((T j).2.1.val : P) (show B j ≤ B j from le_rfl))
              (inverseEmbed (r i j k : P)
                (show L i j k ≤ conjugate (r i j k : P) (B j) from inf_le_right)))
        (∀ i j k, Parabolic (L i j k)) ∧
        (∀ i j k,
          ∃ R : Span K.val J.val,
            R.1.val = L i j k ∧
            (R.2.1.val : P) = ((S i).2.1.val : P) * ((S i).2.2.val : P)⁻¹ ∧
            (R.2.2.val : P) =
              ((T j).2.2.val : P) * ((T j).2.1.val : P)⁻¹ * (r i j k : P)⁻¹) ∧
        let result := fun (w : Σ i : Fin m, Σ j : Fin n, Q i j) =>
          MackeyDiagrams.Word.basis (pairWord (left w.1 w.2.1 w.2.2) (right w.1 w.2.1 w.2.2))
        let X := fun i => spanBasis (S i)
        let Y := fun j => spanBasis (T j)
        Distributes X Y ∧
        ∀ (M : Mor K H) (N : Mor H J),
          Nonempty (CategoryTheory.Iso M.val (linearize (sumBasis X))) →
          Nonempty (CategoryTheory.Iso N.val (linearize (sumBasis Y))) →
          Nonempty (CategoryTheory.Iso (tensor M N).val (linearize (sumBasis result))))
) := FiniteParabolicBicategoryComposition

#print axioms FiniteParabolicBicategoryComposition
#check Representation.Coinvariants.lift
#check Representation.Coinvariants.hom_ext
#check mem_closure_isSwap'

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants do
    if ["unitAdmissible", "tensorAdmissible", "familyTensorIso", "assoc_natural",
        "leftUnit_natural", "rightUnit_natural", "pentagon", "triangle", "flattenSum",
        "reindexSum", "sumIso", "resultBasis", "quotientFamily"].any
          (fun leaf => name.toString.endsWith ("." ++ leaf)) &&
        name.toString.startsWith "_private.Final." then
      logInfo (toString name)
