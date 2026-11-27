import MackeyDiagrams
import Proofs.CaseFiveLeftShapeEvaluation
import Proofs.CaseSixRightShapeEvaluation

universe u

theorem EvaluationWithOneProjection : (
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E),
  (∀ {B : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding G B) (β : MackeyDiagrams.ConjEmbedding D B)
      (γ : MackeyDiagrams.ConjEmbedding E B),
    let up := @MackeyDiagrams.Word.up U _
    let down := @MackeyDiagrams.Word.down U _
    let tensor := @MackeyDiagrams.Word.tensor U _
    let comp := @MackeyDiagrams.ConjEmbedding.comp U _
    let sourcePair := tensor (up a) (down b)
    let targetPair := tensor (up c) (down e)
    let targetBasis := MackeyDiagrams.Word.basis targetPair
    let bottom := tensor sourcePair (up d)
    let top := tensor targetPair (up f)
    let RDot := MackeyDiagrams.Dot (comp α a) (comp β b)
    let TDot := MackeyDiagrams.Dot (comp β d) (comp γ f)
    let SDot := MackeyDiagrams.Dot (comp α c) (comp γ e)
    let q := fun (s : SDot) (p : targetBasis.carrier) =>
      MackeyDiagrams.Generator.mixedProduct α γ
        (MackeyDiagrams.Generator.mixedMultiplicationBasis α γ c e s p)
    let finiteFibers := fun (s : SDot) => ∀ z : B, Set.Finite {p | q s p = z}
    let projectionDot := fun (s : SDot) (hs : finiteFibers s) =>
      (⟨s, fun z => Set.Finite.subset (hs (MackeyDiagrams.Generator.mixedProduct α γ z))
        (fun _ hz => congrArg (MackeyDiagrams.Generator.mixedProduct α γ) hz)⟩ :
          MackeyDiagrams.ProjectionDot.Mixed α γ c e)
    let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
    let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
    let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
    let drawing := fun (rs : List (Complex × RDot)) (ts : List (Complex × TDot))
        (ss : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)) =>
      (stack
        (juxtapose (MackeyDiagrams.LabelledDrawing.mixedMultiplication α β a b rs)
          (ordinary (MackeyDiagrams.Diagram.id (up d))))
        (stack
          (ordinary (MackeyDiagrams.Diagram.associate (down α) (up β) (up d)))
          (stack
            (juxtapose (ordinary (MackeyDiagrams.Diagram.id (down α)))
              (MackeyDiagrams.LabelledDrawing.parallelUp β d γ f ts))
            (stack
              (ordinary (MackeyDiagrams.Diagram.unassociate (down α) (up γ) (up f)))
              (juxtapose (MackeyDiagrams.LabelledDrawing.compactProjection α γ c e ss)
                (ordinary (MackeyDiagrams.Diagram.id (up f))))))) :
        MackeyDiagrams.LabelledDrawing Complex bottom top)
    let input := fun (g : G) (x : D) =>
      MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis sourcePair)
        (MackeyDiagrams.Biset.induction d)
        (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
          (MackeyDiagrams.Biset.restriction b) g x) 1
    let output := fun (p : targetBasis.carrier) =>
      MackeyDiagrams.Biset.pair targetBasis (MackeyDiagrams.Biset.induction f) p 1
    let evaluates := fun (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top)
        (g : G) (x : D) =>
      MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret diagram))
        (Finsupp.single (input g x) 1)
    let fiberSum := fun (r : RDot) (t : TDot) (s : SDot) (hs : finiteFibers s) (g : G) (x : D) =>
      Finset.sum (Set.Finite.toFinset (hs
        (MackeyDiagrams.ConjEmbedding.toHom α g * MackeyDiagrams.Dot.element r *
          MackeyDiagrams.ConjEmbedding.toHom β x * MackeyDiagrams.Dot.element t)))
        (fun p => Finsupp.single (output p) (1 : Complex))
    (∀ (r : RDot) (t : TDot) (s : SDot) (hs : finiteFibers s) (g : G) (x : D),
      evaluates (drawing [(1, r)] [(1, t)] [(1, projectionDot s hs)]) g x =
        fiberSum r t s hs g x) ∧
    (∀ (rs : MackeyDiagrams.DotLabel Complex (comp α a) (comp β b))
        (ts : MackeyDiagrams.DotLabel Complex (comp β d) (comp γ f))
        (ss : MackeyDiagrams.DotLabel Complex (comp α c) (comp γ e))
        (hs : ∀ s ∈ Finsupp.support ss, finiteFibers s) (g : G) (x : D),
      let supported := Finset.attach (Finsupp.support ss)
      let terms := List.map (fun s =>
        (ss (Subtype.val s), projectionDot (Subtype.val s) (hs (Subtype.val s) (Subtype.property s))))
        (Finset.toList supported)
      evaluates (drawing (MackeyDiagrams.DotLabel.terms rs) (MackeyDiagrams.DotLabel.terms ts) terms) g x =
        Finsupp.sum rs (fun r cr =>
          Finsupp.sum ts (fun t ct =>
            Finset.sum supported (fun s =>
              (cr * ct * ss (Subtype.val s)) •
                fiberSum r t (Subtype.val s) (hs (Subtype.val s) (Subtype.property s)) g x))))) ∧
  (∀ (B' : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C),
    let up := @MackeyDiagrams.Word.up U _
    let down := @MackeyDiagrams.Word.down U _
    let tensor := @MackeyDiagrams.Word.tensor U _
    let comp := @MackeyDiagrams.ConjEmbedding.comp U _
    let ga := up a
    let ad := down b
    let df := up d
    let ai := up i
    let fj := down j
    let gc := up c
    let ck := up k
    let ce := down e
    let ef := up f
    let bottom := tensor ga (tensor ad df)
    let top := tensor gc (tensor ce ef)
    let LowerDot := MackeyDiagrams.Dot (comp b i) (comp d j)
    let MiddleDot := MackeyDiagrams.Dot (comp a i) (comp c k)
    let UpperDot := MackeyDiagrams.Dot (comp e k) (comp f j)
    let FiberWord := tensor ai fj
    let q := fun (r : LowerDot) (w : (MackeyDiagrams.Word.basis FiberWord).carrier) =>
      MackeyDiagrams.Generator.mixedProduct b d
        (MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r w)
    let finiteFibers := fun (r : LowerDot) => ∀ x : D, Set.Finite {w | q r w = x}
    let projectionTerm := fun (r : LowerDot) (hr : finiteFibers r) =>
      (⟨r, fun z => Set.Finite.subset (hr (MackeyDiagrams.Generator.mixedProduct b d z))
        (fun _ hw => congrArg (MackeyDiagrams.Generator.mixedProduct b d) hw)⟩ :
          MackeyDiagrams.ProjectionDot.Mixed b d i j)
    let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
      MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
    let rightDrawing := fun
        (lower : List (Complex × MackeyDiagrams.ProjectionDot.Mixed b d i j))
        (middle : List (Complex × MiddleDot)) (upper : List (Complex × UpperDot)) =>
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
    let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top)
        (g : G) (x : D) =>
      MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
        (Finsupp.single
          (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
            (MackeyDiagrams.Word.basis (tensor ad df)) g
            (MackeyDiagrams.Generator.mixedPair b d x)) 1)
    let formula := fun (r : LowerDot) (hr : finiteFibers r)
        (t : MiddleDot) (s : UpperDot) (g : G) (x : D) =>
      Finset.sum (Set.Finite.toFinset (hr x)) (fun w =>
        let representative : A × F := Quotient.out w
        Finsupp.single
          (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
            (MackeyDiagrams.Word.basis (tensor ce ef))
            (g * MackeyDiagrams.ConjEmbedding.toHom a representative.1 *
              MackeyDiagrams.Dot.element t)
            (MackeyDiagrams.Generator.mixedPair e f
              (MackeyDiagrams.Dot.element s *
                MackeyDiagrams.ConjEmbedding.toHom f representative.2))) (1 : Complex))
    (∀ (r : LowerDot) (hr : finiteFibers r) (t : MiddleDot) (s : UpperDot) (g : G) (x : D),
      evaluate (rightDrawing [(1, projectionTerm r hr)] [(1, t)] [(1, s)]) g x =
        formula r hr t s g x) ∧
    (∀ (R : MackeyDiagrams.DotLabel Complex (comp b i) (comp d j))
        (T : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
        (S : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j))
        (hR : ∀ r ∈ Finsupp.support R, finiteFibers r) (g : G) (x : D),
      let lowerSupport := Finset.attach (Finsupp.support R)
      let lowerTerms := List.map (fun r : {r // r ∈ Finsupp.support R} =>
        (R r.val, projectionTerm r.val (hR r.val r.property))) (Finset.toList lowerSupport)
      evaluate (rightDrawing lowerTerms (MackeyDiagrams.DotLabel.terms T)
        (MackeyDiagrams.DotLabel.terms S)) g x =
        Finset.sum lowerSupport (fun r =>
          Finset.sum (Finsupp.support T) (fun t =>
            Finset.sum (Finsupp.support S) (fun s =>
              (R r.val * T t * S s) • formula r.val (hR r.val r.property) t s g x)))))
) := by
  -- Xiao, Lemma 6.6, archived PDF p. 25 and revised published PDF p. 27.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The numbered steps below follow the article's calculations.
  -- Pair the compiled evaluations at their native tensor bracketings.
  intro U _ G A D F C E a b d c e f
  constructor
  · intro B α β γ
    -- Equation (6.3), Case 5. Steps 1–3 multiply the lower pair,
    -- act by the middle dot, and take the upper finite fiber.
    -- Step 4 sums the weighted evaluations over the three supports.
    exact CaseFiveLeftShapeEvaluation a b d c e f α β γ
  · intro B' i j k
    -- Equation (6.4), Case 6. Steps 1–3 take the lower finite fiber,
    -- act on the first coordinate, and multiply the upper pair.
    -- Step 4 sums over the supports with a finiteness witness for
    -- each supported lower projection term.
    exact CaseSixRightShapeEvaluation G A D F C E B' a b d c e f i j k

#print axioms EvaluationWithOneProjection
