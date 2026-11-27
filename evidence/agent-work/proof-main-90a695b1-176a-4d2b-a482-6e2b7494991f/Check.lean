import MackeyDiagrams
import Proofs.ParabolicCaseSixStrictStabilizerObstruction
import Proofs.ParabolicCaseSixReplacementThroughJoin

theorem ParabolicCaseSixObstructionAndReplacementFamily :
(
  let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
  let U := ↥finitary
  let blockSym := fun (S : Finset Nat) =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
  let parabolic := fun (H : Subgroup U) =>
    ∃ (n : Nat) (blocks : Fin n → Finset Nat),
      (∀ i, Finset.Nonempty (blocks i)) ∧
      Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
      Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
  ∀ {G A D F C E : Subgroup U},
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
    letI : MulAction (G × F) X.carrier :=
      { smul := MackeyDiagrams.Biset.act X
        one_smul := MackeyDiagrams.Biset.one_act X
        mul_smul := MackeyDiagrams.Biset.mul_act X }
    letI : MulAction (G × F) Y.carrier :=
      { smul := MackeyDiagrams.Biset.act Y
        one_smul := MackeyDiagrams.Biset.one_act Y
        mul_smul := MackeyDiagrams.Biset.mul_act Y }
    letI : MulAction (G × F) Pair :=
      { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
        one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
          (MackeyDiagrams.Biset.one_act Y z.2)
        mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
          (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
    let project := Subgroup.map (MonoidHom.snd G F)
    let projectedPair := fun z : Pair => project (MulAction.stabilizer (G × F) z)
    let projectedSource := fun x : X.carrier => project (MulAction.stabilizer (G × F) x)
    let projectedTarget := fun y : Y.carrier => project (MulAction.stabilizer (G × F) y)
    let MatrixMap := (X.carrier →₀ Complex) →ₗ[Complex] (Y.carrier →₀ Complex)
    let coefficient := fun (M : MatrixMap) (z : Pair) =>
      M (Finsupp.single z.1 (1 : Complex)) z.2
    let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
      MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
    let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
    let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
    let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
    let ProjectionLabel := fun {K L M H : Subgroup U}
        (α : MackeyDiagrams.ConjEmbedding K M) (β : MackeyDiagrams.ConjEmbedding L M)
        (η : MackeyDiagrams.ConjEmbedding H K) (θ : MackeyDiagrams.ConjEmbedding H L) =>
      List (Complex × MackeyDiagrams.ProjectionDot.Mixed α β η θ)
    let LeftData :=
      Σ (B : Subgroup U) (u : MackeyDiagrams.ConjEmbedding G B)
        (v : MackeyDiagrams.ConjEmbedding D B) (w : MackeyDiagrams.ConjEmbedding E B),
        MackeyDiagrams.DotLabel Complex (comp u a) (comp v b) ×
        MackeyDiagrams.DotLabel Complex (comp v d) (comp w f) ×
        ProjectionLabel u w c e
    let leftDrawing : LeftData → MackeyDiagrams.LabelledDrawing Complex bottom top :=
      fun ⟨_, u, v, w, r, t, s⟩ =>
        let du := down u
        let uv := up v
        let uw := up w
        let lower := MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b
          (MackeyDiagrams.DotLabel.terms r)
        let middle := MackeyDiagrams.LabelledDrawing.parallelUp v d w f
          (MackeyDiagrams.DotLabel.terms t)
        let upper := MackeyDiagrams.LabelledDrawing.compactProjection u w c e s
        stack (ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
          (stack (juxtapose lower (ordinary (MackeyDiagrams.Diagram.id df)))
            (stack (ordinary (MackeyDiagrams.Diagram.associate du uv df))
              (stack (juxtapose (ordinary (MackeyDiagrams.Diagram.id du)) middle)
                (stack (ordinary (MackeyDiagrams.Diagram.unassociate du uw ef))
                  (stack (juxtapose upper (ordinary (MackeyDiagrams.Diagram.id ef)))
                    (ordinary (MackeyDiagrams.Diagram.associate gc ce ef)))))))
    let rightDrawing := fun {B' : Subgroup U}
        (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
        (k : MackeyDiagrams.ConjEmbedding B' C) (r : ProjectionLabel b d i j)
        (t : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
        (s : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j)) =>
      let ai := up i
      let fj := down j
      let ck := up k
      let lower := MackeyDiagrams.LabelledDrawing.compactProjection b d i j r
      let middle := MackeyDiagrams.LabelledDrawing.parallelUp a i c k
        (MackeyDiagrams.DotLabel.terms t)
      let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j
        (MackeyDiagrams.DotLabel.terms s)
      stack (juxtapose (ordinary (MackeyDiagrams.Diagram.id ga)) lower)
        (stack (ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
          (stack (juxtapose middle (ordinary (MackeyDiagrams.Diagram.id fj)))
            (stack (ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
              (juxtapose (ordinary (MackeyDiagrams.Diagram.id gc)) upper))))
    ∀ {B₀ : Subgroup U}, parabolic B₀ →
    ∀ (i₀ : MackeyDiagrams.ConjEmbedding B₀ A) (j₀ : MackeyDiagrams.ConjEmbedding B₀ F)
      (k₀ : MackeyDiagrams.ConjEmbedding B₀ C) (r₀ : MackeyDiagrams.ProjectionDot.Mixed b d i₀ j₀)
      (t₀ : MackeyDiagrams.Dot (comp a i₀) (comp c k₀))
      (s₀ : MackeyDiagrams.Dot (comp e k₀) (comp f j₀)),
    let z : Pair := (input 1 (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot r₀)),
      output (MackeyDiagrams.Dot.element t₀) (MackeyDiagrams.Dot.element s₀))
    let orbit := MulAction.orbit (G × F) z
    let orbitCoefficient := fun p : Pair =>
      @ite Complex (p ∈ orbit) (Classical.propDecidable (p ∈ orbit)) 1 0
    projectedPair z < projectedSource z.1 ⊓ projectedTarget z.2 →
    ∀ (N : Nat) (terms : Fin N → LeftData) (weights : Fin N → Complex),
      (∀ ν, parabolic (terms ν).1) →
      let leftSum : MackeyDiagrams.IndexedDrawing Complex bottom top (Fin N) :=
        ⟨Finset.univ, fun ν => MackeyDiagrams.LabelledDrawing.scale (weights ν) (leftDrawing (terms ν))⟩
      (¬ ∀ p : Pair, coefficient (MackeyDiagrams.IndexedDrawing.eval leftSum) p = orbitCoefficient p) ∧
      (∀ {B' : Subgroup U}, parabolic B' →
        ∀ (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
          (k : MackeyDiagrams.ConjEmbedding B' C) (r : ProjectionLabel b d i j)
          (t : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
          (s : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j)),
        let rightMap := evaluate (rightDrawing i j k r t s)
        coefficient rightMap z ≠ 0 →
        rightMap ≠ MackeyDiagrams.IndexedDrawing.eval leftSum)
)
∧
(
  let P := Equiv.Perm Nat
  let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
  let U := ↥finitary
  let F : Subgroup U := ⊥
  let parabolic := fun (H : Subgroup U) =>
    ∃ (n : Nat) (blocks : Fin n → Finset Nat),
      (∀ i, Finset.Nonempty (blocks i)) ∧
      Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
      Subgroup.map (Subgroup.subtype finitary) H =
        iSup (fun i => MonoidHom.range
          (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ blocks i)))
  ∀ {G A D C E : Subgroup U},
    parabolic G → parabolic A → parabolic D → parabolic C → parabolic E →
    ∀ (GE : Subgroup U),
      (GE : Set U) = Set.image2 (fun g e : U => g * e) (G : Set U) (E : Set U) →
      ∀ (hA : D ⊓ GE = A) (hC : G ⊓ E = C) (hAG : A ≤ G),
    let B := (G ⊔ D) ⊔ E
    let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
      (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
    let a := incl hAG
    let b := incl (show A ≤ D by rw [← hA]; exact inf_le_left)
    let d := incl (show F ≤ D from bot_le)
    let c := incl (show C ≤ G by rw [← hC]; exact inf_le_left)
    let e := incl (show C ≤ E by rw [← hC]; exact inf_le_right)
    let f := incl (show F ≤ E from bot_le)
    let u := incl (show G ≤ B from le_trans le_sup_left le_sup_left)
    let v := incl (show D ≤ B from le_trans le_sup_right le_sup_left)
    let w := incl (show E ≤ B from le_sup_right)
    let i := incl (show F ≤ A from bot_le)
    let j := MackeyDiagrams.ConjEmbedding.id F
    let k := incl (show F ≤ C from bot_le)
    let up := @MackeyDiagrams.Word.up U _
    let down := @MackeyDiagrams.Word.down U _
    let tensor := @MackeyDiagrams.Word.tensor U _
    let comp := @MackeyDiagrams.ConjEmbedding.comp U _
    let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
    let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
    let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
    let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
      ordinary (MackeyDiagrams.Diagram.id p)
    let bottom := tensor (up a) (tensor (down b) (up d))
    let top := tensor (up c) (tensor (down e) (up f))
    let atLeft := fun {K J J' L M : Subgroup U}
        {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
        {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
        (tail : MackeyDiagrams.Word L M)
        (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
      stack (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
        (stack (juxtapose crossing (drawId tail))
          (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
    let finiteFibers := fun {H K L M : Subgroup U}
        (α : MackeyDiagrams.ConjEmbedding K M) (β : MackeyDiagrams.ConjEmbedding L M)
        (γ : MackeyDiagrams.ConjEmbedding H K) (δ : MackeyDiagrams.ConjEmbedding H L)
        (dot : MackeyDiagrams.Dot (comp α γ) (comp β δ)) =>
      ∀ z, Set.Finite {y | MackeyDiagrams.Generator.mixedMultiplicationBasis α β γ δ dot y = z}
    let lowerOne : MackeyDiagrams.Dot (comp u a) (comp v b) :=
      ⟨1, fun x => by simpa only [mul_one, one_mul] using
        (show MackeyDiagrams.ConjEmbedding.toHom (comp u a) x =
          MackeyDiagrams.ConjEmbedding.toHom (comp v b) x from rfl)⟩
    let upperOne : MackeyDiagrams.Dot (comp u c) (comp w e) :=
      ⟨1, fun x => by simpa only [mul_one, one_mul] using
        (show MackeyDiagrams.ConjEmbedding.toHom (comp u c) x =
          MackeyDiagrams.ConjEmbedding.toHom (comp w e) x from rfl)⟩
    let RightLower := MackeyDiagrams.Dot (comp b i) (comp d j)
    let RightMiddle := MackeyDiagrams.Dot (comp a i) (comp c k)
    let RightUpper := MackeyDiagrams.Dot (comp e k) (comp f j)
    let LeftMiddle := MackeyDiagrams.Dot (comp v d) (comp w f)
    let middleDot := fun (r : RightLower) (t : RightMiddle) (s : RightUpper) =>
      let z := (MackeyDiagrams.ConjEmbedding.toHom v (MackeyDiagrams.Dot.element r))⁻¹ *
        MackeyDiagrams.ConjEmbedding.toHom u (MackeyDiagrams.Dot.element t) *
        MackeyDiagrams.ConjEmbedding.toHom w (MackeyDiagrams.Dot.element s)
      (⟨z, fun x => by
        have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.property)
        simp [hx]⟩ : LeftMiddle)
    ∃ (hLeft : finiteFibers u w c e upperOne)
      (hRight : ∀ r : RightLower, finiteFibers b d i j r),
    let leftDrawing := fun (middle : List (Complex × LeftMiddle)) =>
      (stack
        (atLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b [(1, lowerOne)]))
        (stack (juxtapose (drawId (down u)) (MackeyDiagrams.LabelledDrawing.parallelUp v d w f middle))
          (atLeft (up f) (MackeyDiagrams.LabelledDrawing.compactProjection u w c e
            [(1, ⟨upperOne, hLeft⟩)]))) :
        MackeyDiagrams.LabelledDrawing Complex bottom top)
    let rightDrawing := fun
        (lower : List (Complex × MackeyDiagrams.ProjectionDot.Mixed b d i j))
        (middle : List (Complex × RightMiddle)) (upper : List (Complex × RightUpper)) =>
      (stack
        (juxtapose (drawId (up a)) (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
        (stack (atLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i c k middle))
          (juxtapose (drawId (up c)) (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j upper))) :
        MackeyDiagrams.LabelledDrawing Complex bottom top)
    let rightProjectionTerm := fun (r : RightLower) =>
      (⟨r, hRight r⟩ : MackeyDiagrams.ProjectionDot.Mixed b d i j)
    let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
    parabolic B ∧
      (∀ (r : RightLower) (t : RightMiddle) (s : RightUpper),
        evaluate (leftDrawing [(1, middleDot r t s)]) =
          evaluate (rightDrawing [(1, rightProjectionTerm r)] [(1, t)] [(1, s)])) ∧
      (∀ (rs : MackeyDiagrams.DotLabel Complex (comp b i) (comp d j))
          (ts : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
          (ss : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j)),
        let middleLabel : MackeyDiagrams.DotLabel Complex (comp v d) (comp w f) :=
          Finsupp.sum rs (fun r cr =>
            Finsupp.sum ts (fun t ct =>
              Finsupp.sum ss (fun s cs => Finsupp.single (middleDot r t s) (cr * ct * cs))))
        let lowerTerms := List.map (fun (term : Complex × RightLower) =>
          (Prod.fst term, rightProjectionTerm (Prod.snd term))) (MackeyDiagrams.DotLabel.terms rs)
        evaluate (leftDrawing (MackeyDiagrams.DotLabel.terms middleLabel)) =
          evaluate (rightDrawing lowerTerms (MackeyDiagrams.DotLabel.terms ts)
            (MackeyDiagrams.DotLabel.terms ss)))
)
:=
(by
  -- Xiao, Proposition 8.8, archived original p. 41 and published
  -- 28 November revision p. 43 (SHA-256
  -- e7712567f611d36713fb4dbf45f8b1aeefea022ea2e403462529850ebe290cc8).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=43
  constructor
  · -- The first proof paragraph uses Proposition 8.7 to force each left
    -- term's coefficient to vanish on the chosen orbit. The registered
    -- supplier already proves both matrix comparisons, including the
    -- nonzero-coefficient hypothesis for a right drawing with linear labels.
    exact ParabolicCaseSixStrictStabilizerObstruction
  · -- The second paragraph uses F = 1 and inclusion embeddings. The
    -- registered supplier uses D ∩ GE = A for existence of the output
    -- and G ∩ E = C for uniqueness, and combines the weighted r⁻¹ts
    -- terms at the middle mark of one left drawing through the join.
    -- The supplier compares evaluations at the fixed typed boundary.
    exact ParabolicCaseSixReplacementThroughJoin)

#print axioms ParabolicCaseSixObstructionAndReplacementFamily
