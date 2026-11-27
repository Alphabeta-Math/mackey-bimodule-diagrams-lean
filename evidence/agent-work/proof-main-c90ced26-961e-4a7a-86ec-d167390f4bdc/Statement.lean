import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention

#check (∀ {U : Type*} [Group U] (G A D F C E B' : Subgroup U)
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E)
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
