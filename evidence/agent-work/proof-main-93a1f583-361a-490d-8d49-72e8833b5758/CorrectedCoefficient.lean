import MackeyDiagrams
import Proofs.MixedCrossingFiberMaps
universe u
set_option pp.explicit true
set_option pp.deepTerms true
#check (∀ {U : Type u} [Group U],
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  (∀ {K H G L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K G) (β : MackeyDiagrams.ConjEmbedding H G)
      (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H)
      (d : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp α a)
        (MackeyDiagrams.ConjEmbedding.comp β b)),
    let inner := tensor (up a) (down b)
    let q := fun (w : (MackeyDiagrams.Word.basis inner).carrier) =>
      MackeyDiagrams.Generator.mixedProduct α β
        (MackeyDiagrams.Generator.mixedMultiplicationBasis α β a b d w)
    let traceDot := MackeyDiagrams.Dot.inverse d
    let traceInput := fun (z : G) (t : H) =>
      z * (MackeyDiagrams.ConjEmbedding.toHom β t)⁻¹ * MackeyDiagrams.Dot.element traceDot
    let traceSurvivors := fun (T : Set H) (z : G) =>
      {t : H | t ∈ T ∧ traceInput z t ∈ MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom α)}
    (∀ (k : K) (h : H),
      q (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
          (MackeyDiagrams.Biset.restriction b) k h) =
        MackeyDiagrams.ConjEmbedding.toHom α k * MackeyDiagrams.Dot.element d *
          MackeyDiagrams.ConjEmbedding.toHom β h) ∧
    (∀ w : (MackeyDiagrams.Word.basis inner).carrier,
      MackeyDiagrams.Biset.Hom.toLinearMap
          (MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.mixedMultiplication (R := Complex) α β a b d))
          (Finsupp.single w 1) =
        Finsupp.single (MackeyDiagrams.Generator.mixedPair α β (q w)) 1) ∧
    MackeyDiagrams.Dot.element traceDot = (MackeyDiagrams.Dot.element d)⁻¹ ∧
    (∀ hf : ∀ z : G, Set.Finite {w | q w = z},
      let diagram := MackeyDiagrams.Diagram.mixedProjection (R := Complex) α β a b d
        (fun z => Set.Finite.subset (hf (MackeyDiagrams.Generator.mixedProduct α β z))
          (fun _ hw => congrArg (MackeyDiagrams.Generator.mixedProduct α β) hw))
      let valueAt := fun z : G => MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.Diagram.eval diagram)
        (Finsupp.single (MackeyDiagrams.Generator.mixedPair α β z) 1)
      (∀ z : G, valueAt z = Finset.sum (Set.Finite.toFinset (hf z))
        (fun w => Finsupp.single w 1)) ∧
      (∀ (T : Set H)
          (_ : ∀ h : H, ∃! t : H, t ∈ T ∧
            h * t⁻¹ ∈ MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b))
          (z : G),
        ∃ hs : Set.Finite (traceSurvivors T z),
          valueAt z = Finset.sum (Set.Finite.toFinset hs) (fun t =>
            MackeyDiagrams.Biset.pairLinear Complex (MackeyDiagrams.Biset.induction a)
              (MackeyDiagrams.Biset.restriction b)
              (MackeyDiagrams.Generator.traceBasis Complex α (traceInput z t))
              (Finsupp.single t 1))))))
