import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import MackeyDiagrams.DotLabels

set_option maxHeartbeats 400000 in
def reviewedEndpoint : Prop :=
∀ {U : Type*} [Group U] (G A D F C E : Subgroup U)
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let ga := up a
  let ad := down b
  let df := up d
  let gc := up c
  let ce := down e
  let ef := up f
  let bottom := tensor ga (tensor ad df)
  let top := tensor gc (tensor ce ef)
  let X := MackeyDiagrams.Word.basis bottom
  let Y := MackeyDiagrams.Word.basis top
  let Pair := X.carrier × Y.carrier
  let input := fun (g : G) (x : D) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let orbit : Pair → Set Pair := MulAction.orbit (G × F)
  let stabilizer : Pair → Subgroup (G × F) := MulAction.stabilizer (G × F)
  let projected := fun z : Pair =>
    Subgroup.map (MonoidHom.comp (Subgroup.subtype F) (MonoidHom.snd G F)) (stabilizer z)
  let coefficient := fun (M : MackeyDiagrams.Biset.Hom Complex X Y) (z : Pair) =>
    MackeyDiagrams.Biset.Hom.toLinearMap M (Finsupp.single z.1 (1 : Complex)) z.2
  let LowerLabel := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F) =>
    MackeyDiagrams.Dot (comp b i) (comp d j)
  let MiddleLabel := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (k : MackeyDiagrams.ConjEmbedding P C) =>
    MackeyDiagrams.Dot (comp a i) (comp c k)
  let UpperLabel := fun (P : Subgroup U)
      (j : MackeyDiagrams.ConjEmbedding P F) (k : MackeyDiagrams.ConjEmbedding P C) =>
    MackeyDiagrams.Dot (comp e k) (comp f j)
  let Fiber := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F) =>
    (MackeyDiagrams.Word.basis (tensor (up i) (down j))).carrier
  let lowerMap := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
      (r : LowerLabel P i j) (w : Fiber P i j) =>
    MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r w
  let finiteFibers := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
      (r : LowerLabel P i j) =>
    ∀ z : (MackeyDiagrams.Word.basis (tensor ad df)).carrier,
      Set.Finite {w | lowerMap P i j r w = z}
  let ProjectionTerm := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F) =>
    MackeyDiagrams.ProjectionDot.Mixed b d i j
  let projectionTerm := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
      (r : LowerLabel P i j) (finite : finiteFibers P i j r) =>
    (⟨r, finite⟩ : ProjectionTerm P i j)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let rightDrawing := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
      (k : MackeyDiagrams.ConjEmbedding P C)
      (lower : List (Complex × ProjectionTerm P i j))
      (middle : List (Complex × MiddleLabel P i k))
      (upper : List (Complex × UpperLabel P j k)) =>
    let ai := up i
    let fj := down j
    let ck := up k
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId ga)
        (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.parallelUp a i c k middle) (drawId fj))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId gc)
              (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j upper))))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let singletonDrawing := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
      (k : MackeyDiagrams.ConjEmbedding P C)
      (r : LowerLabel P i j) (t : MiddleLabel P i k) (s : UpperLabel P j k)
      (finite : finiteFibers P i j r) =>
    rightDrawing P i j k [(1, projectionTerm P i j r finite)] [(1, t)] [(1, s)]
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let IsRightTerm := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    ∃ (P : Subgroup U) (i : MackeyDiagrams.ConjEmbedding P A)
      (j : MackeyDiagrams.ConjEmbedding P F) (k : MackeyDiagrams.ConjEmbedding P C)
      (lower : List (Complex × ProjectionTerm P i j))
      (middle : List (Complex × MiddleLabel P i k))
      (upper : List (Complex × UpperLabel P j k)),
      drawing = rightDrawing P i j k lower middle upper
  (∀ (M : MackeyDiagrams.Biset.Hom Complex X Y) (z z' : Pair),
    z' ∈ orbit z → coefficient M z' = coefficient M z) ∧
  (∀ z : Pair, ∃ (r : D) (t : G) (s : E), z ∈ orbit (input 1 r, output t s)) ∧
  (∀ (r : D) (t : G) (s : E),
    let z₀ : Pair := (input 1 r, output t s)
    let P := projected z₀
    let O := orbit z₀
    (∀ h : F, (h : U) ∈ P ↔
      ∃ (α : A) (κ : C),
        r * MackeyDiagrams.ConjEmbedding.toHom d h * r⁻¹ =
          MackeyDiagrams.ConjEmbedding.toHom b α ∧
        s * MackeyDiagrams.ConjEmbedding.toHom f h * s⁻¹ =
          MackeyDiagrams.ConjEmbedding.toHom e κ ∧
        MackeyDiagrams.ConjEmbedding.toHom a α =
          t * MackeyDiagrams.ConjEmbedding.toHom c κ * t⁻¹) ∧
    O = Set.range (fun q : G × F =>
      (input q.1 (r * MackeyDiagrams.ConjEmbedding.toHom d q.2),
       output (q.1 * t) (s * MackeyDiagrams.ConjEmbedding.toHom f q.2))) ∧
    (∀ (g g' : G) (x : D) (h : F),
      input g' (r * MackeyDiagrams.ConjEmbedding.toHom d h) = input g x ↔
        ∃ α : A, g' = g * MackeyDiagrams.ConjEmbedding.toHom a α ∧
          x = MackeyDiagrams.ConjEmbedding.toHom b α * r * MackeyDiagrams.ConjEmbedding.toHom d h) ∧
    ∃ (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
        (k : MackeyDiagrams.ConjEmbedding P C)
        (rDot : LowerLabel P i j) (tDot : MiddleLabel P i k) (sDot : UpperLabel P j k),
      (∀ h : P, (MackeyDiagrams.ConjEmbedding.toHom j h : U) = (h : U)) ∧
      MackeyDiagrams.Dot.element rDot = r ∧ MackeyDiagrams.Dot.element tDot = t ∧
      MackeyDiagrams.Dot.element sDot = s ∧
      (∀ q : G × F, q ∈ stabilizer z₀ ↔ ∃ h : P,
        q = (MackeyDiagrams.ConjEmbedding.toHom a (MackeyDiagrams.ConjEmbedding.toHom i h),
             MackeyDiagrams.ConjEmbedding.toHom j h)) ∧
      (∀ (g : G) (x : D),
        Set.BijOn
          (fun w : Fiber P i j =>
            let v : A × F := Quotient.out w
            output (g * MackeyDiagrams.ConjEmbedding.toHom a v.1 * t)
              (s * MackeyDiagrams.ConjEmbedding.toHom f v.2))
          {w | lowerMap P i j rDot w = MackeyDiagrams.Generator.mixedPair b d x}
          {y | (input g x, y) ∈ O}) ∧
      (∀ M : MackeyDiagrams.Biset.Hom Complex X Y, coefficient M z₀ ≠ 0 →
        (∀ p : X.carrier, Set.Finite {y | (p, y) ∈ O}) ∧
        ∃ finite : finiteFibers P i j rDot,
          ∀ z : Pair,
            coefficient (eval (singletonDrawing P i j k rDot tDot sDot finite)) z =
              @ite Complex (z ∈ O) (Classical.propDecidable (z ∈ O)) 1 0)) ∧
  (∀ (P : Subgroup U) (i : MackeyDiagrams.ConjEmbedding P A)
      (j : MackeyDiagrams.ConjEmbedding P F) (k : MackeyDiagrams.ConjEmbedding P C)
      (r : LowerLabel P i j) (t : MiddleLabel P i k) (s : UpperLabel P j k)
      (finite : finiteFibers P i j r) (z : Pair),
    coefficient (eval (singletonDrawing P i j k r t s finite)) z ≠ 0 →
      z ∈ orbit (input 1 (MackeyDiagrams.Dot.element r),
        output (MackeyDiagrams.Dot.element t) (MackeyDiagrams.Dot.element s))) ∧
  (∀ terms : List (Complex × MackeyDiagrams.LabelledDrawing Complex bottom top),
    (∀ term ∈ terms, IsRightTerm term.2) →
    let drawing := List.foldr
      (fun term rest => MackeyDiagrams.LabelledDrawing.add
        (MackeyDiagrams.LabelledDrawing.scale term.1 term.2) rest)
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.zero (R := Complex) bottom top)) terms
    Set.Finite {O : Set Pair | ∃ z : Pair,
      O = orbit z ∧ coefficient (eval drawing) z ≠ 0}) ∧
  (∀ (M : MackeyDiagrams.Biset.Hom Complex X Y) (p : X.carrier),
    Set.Finite {O : Set Pair | ∃ y : Y.carrier, coefficient M (p, y) ≠ 0 ∧ O = orbit (p, y)})
