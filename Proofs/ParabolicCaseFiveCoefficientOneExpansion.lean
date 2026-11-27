import MackeyDiagrams
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.SupportedLeftOrbitProjectedStabilizer
import Proofs.ParabolicRightOrbitMultiplicity

set_option maxHeartbeats 2000000

theorem ParabolicCaseFiveCoefficientOneExpansion : (
let Sinf : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ | Equiv.Perm.IsSwap σ}
let U := ↥Sinf
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun X => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
let parabolic : Subgroup U → Prop :=
  fun H => ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, Finset.Nonempty (blocks l)) ∧
    Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    Subgroup.map (Subgroup.subtype Sinf) H = iSup (fun l => blockSym (blocks l))
∀ (G A D F C E : Subgroup U),
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  ∀ (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
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
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis ga)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis gc)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  let pair := fun (r : D) (t : G) (s : E) => (input 1 r, output t s)
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
  let swaps := fun P : Subgroup U =>
    Subgroup.closure {σ : U | σ ∈ P ∧ Equiv.Perm.IsSwap (σ : Equiv.Perm Nat)}
  let coefficient := fun (M : MackeyDiagrams.Biset.Hom Complex X Y) (z : Pair) =>
    MackeyDiagrams.Biset.Hom.toLinearMap M (Finsupp.single z.1 (1 : Complex)) z.2
  let matrix := fun (O : Set Pair) (n : Nat) (z : Pair) =>
    @ite Complex (z ∈ O) (Classical.propDecidable (z ∈ O)) (n : Complex) 0
  let RightData := fun B' : Subgroup U =>
    Σ (i : MackeyDiagrams.ConjEmbedding B' A)
      (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C),
      MackeyDiagrams.Dot (comp b i) (comp d j) ×
      MackeyDiagrams.Dot (comp a i) (comp c k) ×
      MackeyDiagrams.Dot (comp e k) (comp f j)
  let labels : {B' : Subgroup U} → RightData B' → D × G × E :=
    fun ⟨_, _, _, r, t, s⟩ =>
      (MackeyDiagrams.Dot.element r, MackeyDiagrams.Dot.element t, MackeyDiagrams.Dot.element s)
  let representative := fun {B'} (data : RightData B') =>
    let (r, t, s) := labels data
    pair r t s
  let toF : {B' : Subgroup U} → RightData B' → (B' →* F) :=
    fun ⟨_, j, _, _, _, _⟩ => MackeyDiagrams.ConjEmbedding.toHom j
  let isInclusion := fun {B'} (data : RightData B') =>
    ∀ h : B', (toF data h : U) = (h : U)
  let Fiber : {B' : Subgroup U} → RightData B' → Type :=
    fun ⟨i, j, _, _, _, _⟩ => (MackeyDiagrams.Word.basis (tensor (up i) (down j))).carrier
  let lowerMap : {B' : Subgroup U} → (data : RightData B') → Fiber data →
      (MackeyDiagrams.Word.basis (tensor ad df)).carrier :=
    fun ⟨i, j, _, r, _, _⟩ => MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r
  let finiteFibers := fun {B'} (data : RightData B') =>
    ∀ z, Set.Finite {w : Fiber data | lowerMap data w = z}
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let rightDiagram : {B' : Subgroup U} → (data : RightData B') → finiteFibers data →
      MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨i, j, k, r, t, s⟩ finite =>
      let ai := up i
      let fj := down j
      let ck := up k
      let lower := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex) b d i j [(1, ⟨r, finite⟩)]
      let middle := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex) a i c k [(1, t)]
      let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex) e f k j [(1, s)]
      MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId ga) lower)
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal middle (drawId fj))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
              (MackeyDiagrams.LabelledDrawing.horizontal (drawId gc) upper))))
  let realizes := fun {B'} (data : RightData B') (O : Set Pair) (n : Nat) =>
    orbit (representative data) = O ∧
      ∃ finite : finiteFibers data, ∀ z : Pair,
        coefficient (eval (rightDiagram data finite)) z = matrix O n z
  let LeftUpperFiber := fun {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (w : MackeyDiagrams.ConjEmbedding E B)
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) =>
    ∀ z, Set.Finite {p | MackeyDiagrams.Generator.mixedMultiplicationBasis u w c e s p = z}
  let leftDiagram := fun {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (r : MackeyDiagrams.Dot (comp u a) (comp v b))
      (t : MackeyDiagrams.Dot (comp v d) (comp w f))
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) (finite : LeftUpperFiber u w s) =>
    let lower := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex) u v a b [(1, r)]
    let middle := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex) v d w f [(1, t)]
    let upper := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex) u w c e [(1, ⟨s, finite⟩)]
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal lower (drawId df))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate (down u) (up v) df))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down u)) middle)
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate (down u) (up w) ef))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.horizontal upper (drawId ef))
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ce ef)))))))
  (∀ (B : Subgroup U), parabolic B →
    ∀ (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (r : MackeyDiagrams.Dot (comp u a) (comp v b))
      (t : MackeyDiagrams.Dot (comp v d) (comp w f))
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) (finite : LeftUpperFiber u w s),
    let M := eval (leftDiagram u v w r t s finite)
    let S : Set (Set Pair) := {O | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0}
    ∃ expansion : MackeyDiagrams.IndexedDrawing Complex bottom top ↥S,
      (∀ O : ↥S, O ∈ MackeyDiagrams.IndexedDrawing.indices expansion) ∧
      (∀ O : ↥S,
        ∃ (r₀ : D) (t₀ : G) (s₀ : E),
          let z := pair r₀ t₀ s₀
          let P := projected z
          O.val = orbit z ∧ parabolic P ∧
          ∃ (data : RightData P) (fiberProof : finiteFibers data),
            labels data = (r₀, t₀, s₀) ∧ isInclusion data ∧
            MackeyDiagrams.IndexedDrawing.summand expansion O = rightDiagram data fiberProof ∧
            ∀ z' : Pair,
              coefficient (eval (MackeyDiagrams.IndexedDrawing.summand expansion O)) z' =
                matrix O.val 1 z') ∧
      MackeyDiagrams.Biset.Hom.toLinearMap M = MackeyDiagrams.IndexedDrawing.eval expansion) ∧
  (∀ z : Pair,
    let P := projected z
    let n := Subgroup.relIndex (swaps P) P
    IsLeast {m : Nat | ∃ (B' : Subgroup U) (term : RightData B'),
      parabolic B' ∧ realizes term (orbit z) m} n ∧
    (n = 1 ↔ parabolic P))
) :=
(by
  intro Sinf U blockSym parabolic G A D F C E hG hA hD hF hC hE a b d c e f
  -- Xiao, Proposition 8.7: archived source PDF pp. 39–40 and revised
  -- published PDF pp. 41–42. The proof at the portal is in paragraphs.
  -- The step numbers below follow the registered multiplicity proof.
  have multiplicity := ParabolicRightOrbitMultiplicity G A D F C E hG hA hD hF hC hE a b d c e f
  -- Steps 1–3 and 6: the registered expansion already uses
  -- SupportedLeftOrbitProjectedStabilizer for parabolicity and unit left
  -- coefficients, and RightOrbitDiagramFromProjectedStabilizer for the full
  -- projected group and its coefficient-one right drawing. Reuse its finite
  -- typed sum directly. Its singleton labels and compact projection fibers
  -- agree definitionally with those in the endpoint.
  refine ⟨multiplicity.2.2.2.2.2, ?_⟩
  -- Steps 4–5: the checked minimum uses the coset count and the largest
  -- parabolic subgroup. The endpoint takes just the least multiplicity and
  -- the index-one criterion from that result for each pair.
  intro z
  obtain ⟨minimum, indexOne, _⟩ := multiplicity.2.2.2.2.1 z
  exact ⟨minimum, indexOne⟩)
