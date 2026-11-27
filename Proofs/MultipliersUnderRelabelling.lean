import MackeyDiagrams
import Proofs.ThreeInductionCrossingMultipliers

set_option maxHeartbeats 2000000

open MackeyDiagrams

namespace MultipliersUnderRelabellingProof

variable {U : Type*} [Group U] {H K : Subgroup U}

private noncomputable abbrev dotValue {a b : ConjEmbedding H K} (label : DotLabel Complex a b) :
    MonoidAlgebra Complex K :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element label)

private theorem dotValue_identity (a : ConjEmbedding H K) :
    dotValue (DotLabel.identity (R := Complex) a) = 1 := by
  simp only [dotValue, DotLabel.identity, Finsupp.mapDomain_single]
  rfl

private theorem dotElement_injective {a b : ConjEmbedding H K} :
    Function.Injective (Dot.element (a := a) (b := b)) :=
  fun _ _ h => Dot.ext h

private noncomputable def liftMultiplier {a b : ConjEmbedding H K}
    (m : MonoidAlgebra Complex K) : DotLabel Complex a b :=
  Finsupp.comapDomain Dot.element m.coeff dotElement_injective.injOn

private theorem liftMultiplier_value {a b : ConjEmbedding H K}
    (m : MonoidAlgebra Complex K)
    (eligible : ∀ p ∈ m.coeff.support, ∀ f : H,
      a.toHom f * p = p * b.toHom f) :
    dotValue (liftMultiplier (a := a) (b := b) m) = m := by
  have inRange : (↑m.coeff.support : Set K) ⊆ Set.range (Dot.element (a := a) (b := b)) := by
    intro p hp
    exact ⟨⟨p, eligible p hp⟩, rfl⟩
  exact congrArg MonoidAlgebra.ofCoeff
    (Finsupp.mapDomain_comapDomain Dot.element dotElement_injective m.coeff inRange)

private theorem eligibleOfCentralizer {a b : ConjEmbedding H K} {u v : U}
    (ha : ∀ f : H, (a.toHom f : U) = u * (f : U) * u⁻¹)
    (hb : ∀ f : H, (b.toHom f : U) = v * (f : U) * v⁻¹)
    (p : K)
    (he : ∀ f : H, (u * (f : U) * u⁻¹) * (p : U) =
      (p : U) * (v * (f : U) * v⁻¹)) :
    ∀ f : H, a.toHom f * p = p * b.toHom f := by
  intro f
  apply Subtype.ext
  change (a.toHom f : U) * (p : U) = (p : U) * (b.toHom f : U)
  rw [ha f, hb f]
  exact he f

section Relabel

variable {G A D F C E : Subgroup U}
variable (ga : ConjEmbedding A G) (ad : ConjEmbedding D A) (df : ConjEmbedding F D)
variable (gc : ConjEmbedding C G) (ce : ConjEmbedding E C) (ef : ConjEmbedding F E)

private abbrev LeftLabels :=
  Σ (B : Subgroup U) (gb : ConjEmbedding B G)
    (bd : ConjEmbedding D B) (be : ConjEmbedding E B),
    DotLabel Complex (ga.comp ad) (gb.comp bd) × DotLabel Complex (bd.comp df) (be.comp ef) ×
    DotLabel Complex (gb.comp be) (gc.comp ce)

private abbrev RightLabels :=
  Σ (B' : Subgroup U) (ab' : ConjEmbedding B' A) (cb' : ConjEmbedding B' C)
    (b'f : ConjEmbedding F B'),
    DotLabel Complex (ad.comp df) (ab'.comp b'f) × DotLabel Complex (ga.comp ab') (gc.comp cb') ×
    DotLabel Complex (cb'.comp b'f) (ce.comp ef)

private noncomputable abbrev along (a : ConjEmbedding H K) :=
  MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom

private theorem relabel
    (leftMultiplier : LeftLabels ga ad df gc ce ef → MonoidAlgebra Complex G)
    (rightMultiplier : RightLabels ga ad df gc ce ef → MonoidAlgebra Complex G)
    (allowed : G → Prop)
    (intertwines : ∀ p : G, allowed p → ∀ f : F,
      ((ga.comp ad).comp df).toHom f * p = p * ((gc.comp ce).comp ef).toHom f)
    (hLeft : ∀ (B : Subgroup U) (gb : ConjEmbedding B G)
      (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
      (x₁ : DotLabel Complex (ga.comp ad) (gb.comp bd))
      (x₂ : DotLabel Complex (bd.comp df) (be.comp ef))
      (x₃ : DotLabel Complex (gb.comp be) (gc.comp ce)),
      let m := leftMultiplier ⟨B, gb, bd, be, x₁, x₂, x₃⟩
      m = dotValue x₁ * along gb (dotValue x₂) * dotValue x₃ ∧
        ∀ p ∈ m.coeff.support, allowed p)
    (hRight : ∀ (B' : Subgroup U) (ab' : ConjEmbedding B' A) (cb' : ConjEmbedding B' C)
      (b'f : ConjEmbedding F B')
      (y₁ : DotLabel Complex (ad.comp df) (ab'.comp b'f))
      (y₂ : DotLabel Complex (ga.comp ab') (gc.comp cb'))
      (y₃ : DotLabel Complex (cb'.comp b'f) (ce.comp ef)),
      let m := rightMultiplier ⟨B', ab', cb', b'f, y₁, y₂, y₃⟩
      m = along ga (dotValue y₁) * dotValue y₂ * along gc (dotValue y₃) ∧
        ∀ p ∈ m.coeff.support, allowed p) :
    ∃ (φ : LeftLabels ga ad df gc ce ef → RightLabels ga ad df gc ce ef)
      (ψ : RightLabels ga ad df gc ce ef → LeftLabels ga ad df gc ce ef),
      (∀ d, rightMultiplier (φ d) = leftMultiplier d) ∧
      (∀ d, leftMultiplier (ψ d) = rightMultiplier d) ∧
      (∀ d, leftMultiplier (ψ (φ d)) = leftMultiplier d) ∧
      (∀ d, rightMultiplier (φ (ψ d)) = rightMultiplier d) := by
  classical
  let bottomPair := ga.comp ad
  let topPair := gc.comp ce
  let middle := fun m =>
    liftMultiplier (a := bottomPair.comp df) (b := topPair.comp ef) m
  -- Constructions of φ and ψ in Lemma 6.1. The article uses representatives
  -- pv and v for each p in the support. Use the equivalent pointwise
  -- intertwining law to form Dot and pull back coefficients along Dot.element.
  -- Composing the homomorphisms gives definitional equality of the differently
  -- bracketed middle embeddings and of the outer embeddings at identity dots.
  let ab' := ad.comp df
  let cb' := ce.comp ef
  let b'f := ConjEmbedding.id F
  let gb := ConjEmbedding.id G
  let y₁ := DotLabel.identity (R := Complex) ab'
  let y₃ := DotLabel.identity (R := Complex) cb'
  let x₁ := DotLabel.identity (R := Complex) bottomPair
  let x₃ := DotLabel.identity (R := Complex) topPair
  let makeRight : MonoidAlgebra Complex G → RightLabels ga ad df gc ce ef :=
    fun m => ⟨F, ab', cb', b'f, y₁, middle m, y₃⟩
  let makeLeft : MonoidAlgebra Complex G → LeftLabels ga ad df gc ce ef :=
    fun m => ⟨G, gb, bottomPair, topPair, x₁, middle m, x₃⟩
  have rightValue (m : MonoidAlgebra Complex G) (hm : ∀ p ∈ m.coeff.support, allowed p) :
      rightMultiplier (makeRight m) = m := by
    have middleValue : dotValue (middle m) = m :=
      liftMultiplier_value m fun p hp => intertwines p (hm p hp)
    calc
      _ = along ga (dotValue y₁) * dotValue (middle m) * along gc (dotValue y₃) :=
        (hRight F ab' cb' b'f y₁ (middle m) y₃).1
      _ = m := by
        rw [dotValue_identity ab', dotValue_identity cb', map_one, map_one,
          one_mul, mul_one, middleValue]
  have leftValue (m : MonoidAlgebra Complex G) (hm : ∀ p ∈ m.coeff.support, allowed p) :
      leftMultiplier (makeLeft m) = m := by
    have middleValue : dotValue (middle m) = m :=
      liftMultiplier_value m fun p hp => intertwines p (hm p hp)
    calc
      _ = dotValue x₁ * along gb (dotValue (middle m)) * dotValue x₃ :=
        (hLeft G gb bottomPair topPair x₁ (middle m) x₃).1
      _ = m := by
        rw [dotValue_identity bottomPair, dotValue_identity topPair, one_mul, mul_one, middleValue]
        change MonoidAlgebra.mapDomainAlgHom Complex Complex (MonoidHom.id G) m = m
        simp only [MonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_apply]
  have hφ (d : LeftLabels ga ad df gc ce ef) : rightMultiplier (makeRight (leftMultiplier d)) =
      leftMultiplier d := by
    rcases d with ⟨B, g, bd, be, x, y, z⟩
    exact rightValue _ (hLeft B g bd be x y z).2
  have hψ (d : RightLabels ga ad df gc ce ef) : leftMultiplier (makeLeft (rightMultiplier d)) =
      rightMultiplier d := by
    rcases d with ⟨B', ab, cb, bf, x, y, z⟩
    exact leftValue _ (hRight B' ab cb bf x y z).2
  -- Round-trip calculations in Lemma 6.1 follow by composing preservation.
  exact ⟨fun d => makeRight (leftMultiplier d), fun d => makeLeft (rightMultiplier d),
    hφ, hψ, fun d => (hψ _).trans (hφ d), fun d => (hφ _).trans (hψ d)⟩

end Relabel
end MultipliersUnderRelabellingProof

open MultipliersUnderRelabellingProof

theorem MultipliersUnderRelabelling : (
∀ {U : Type*} [Group U] (G A D F C E : Subgroup U)
    (repGA repAD repDF repGC repCE repEF : U)
    (hGA : ∀ a : A, repGA * (a : U) * repGA⁻¹ ∈ G)
    (hAD : ∀ d : D, repAD * (d : U) * repAD⁻¹ ∈ A)
    (hDF : ∀ f : F, repDF * (f : U) * repDF⁻¹ ∈ D)
    (hGC : ∀ c : C, repGC * (c : U) * repGC⁻¹ ∈ G)
    (hCE : ∀ e : E, repCE * (e : U) * repCE⁻¹ ∈ C)
    (hEF : ∀ f : F, repEF * (f : U) * repEF⁻¹ ∈ E),
  let ga := MackeyDiagrams.ConjEmbedding.ofConjugator repGA hGA
  let ad := MackeyDiagrams.ConjEmbedding.ofConjugator repAD hAD
  let df := MackeyDiagrams.ConjEmbedding.ofConjugator repDF hDF
  let gc := MackeyDiagrams.ConjEmbedding.ofConjugator repGC hGC
  let ce := MackeyDiagrams.ConjEmbedding.ofConjugator repCE hCE
  let ef := MackeyDiagrams.ConjEmbedding.ofConjugator repEF hEF
  let bottomPair := MackeyDiagrams.ConjEmbedding.comp ga ad
  let topPair := MackeyDiagrams.ConjEmbedding.comp gc ce
  let word := fun {P Q S T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (c : MackeyDiagrams.ConjEmbedding T S) =>
    MackeyDiagrams.Word.tensor
      (MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b))
      (MackeyDiagrams.Word.up c)
  let bottom := word ga ad df
  let top := word gc ce ef
  let straight := fun {P Q : Subgroup U} (a : MackeyDiagrams.ConjEmbedding Q P) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
  let merge := fun {P Q S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.mergeUp a b)
  let split := fun {P Q S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.splitUp a b)
  let splitBottom :=
    MackeyDiagrams.LabelledDrawing.vertical (split bottomPair df)
      (MackeyDiagrams.LabelledDrawing.horizontal (split ga ad) (straight df))
  let mergeTop :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (merge gc ce) (straight ef))
      (merge topPair ef)
  let mergedEvaluation := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top)
      (z : MonoidAlgebra Complex G) =>
    MonoidAlgebra.ofCoeff
      (MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.interpret
            (MackeyDiagrams.LabelledDrawing.vertical splitBottom
              (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
        (MonoidAlgebra.coeff z))
  let multiplier := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    mergedEvaluation drawing 1
  let crossing := fun {P Q Q' S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
        (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
    MackeyDiagrams.LabelledDrawing.vertical (merge a b)
      (MackeyDiagrams.LabelledDrawing.vertical (MackeyDiagrams.DotLabel.upDrawing weights)
        (split a' b'))
  let crossLeft := fun {P Q Q' S T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
      (c : MackeyDiagrams.ConjEmbedding T S)
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
        (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
    MackeyDiagrams.LabelledDrawing.horizontal (crossing a b a' b' weights)
      (straight c)
  let crossRight := fun {P Q S S' T : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P)
      (b : MackeyDiagrams.ConjEmbedding S Q) (c : MackeyDiagrams.ConjEmbedding T S)
      (b' : MackeyDiagrams.ConjEmbedding S' Q) (c' : MackeyDiagrams.ConjEmbedding T S')
      (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp b c)
        (MackeyDiagrams.ConjEmbedding.comp b' c')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.associate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b)
          (MackeyDiagrams.Word.up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (straight a)
          (crossing b c b' c' weights))
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.unassociate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b')
            (MackeyDiagrams.Word.up c'))))
  let LeftLabels :=
    Σ (B : Subgroup U) (gb : MackeyDiagrams.ConjEmbedding B G)
      (bd : MackeyDiagrams.ConjEmbedding D B) (be : MackeyDiagrams.ConjEmbedding E B),
      MackeyDiagrams.DotLabel Complex bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd) ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp bd df) (MackeyDiagrams.ConjEmbedding.comp be ef) ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp gb be) topPair
  let RightLabels :=
    Σ (B' : Subgroup U) (ab' : MackeyDiagrams.ConjEmbedding B' A)
      (cb' : MackeyDiagrams.ConjEmbedding B' C) (b'f : MackeyDiagrams.ConjEmbedding F B'),
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ad df) (MackeyDiagrams.ConjEmbedding.comp ab' b'f) ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ga ab') (MackeyDiagrams.ConjEmbedding.comp gc cb') ×
      MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp cb' b'f) (MackeyDiagrams.ConjEmbedding.comp ce ef)
  let leftDiagram : LeftLabels → MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨_, gb, bd, be, x₁, x₂, x₃⟩ =>
      MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ad gb bd df x₁)
        (MackeyDiagrams.LabelledDrawing.vertical (crossRight gb bd df be ef x₂)
          (crossLeft gb be gc ce ef x₃))
  let rightDiagram : RightLabels → MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨_, ab', cb', b'f, y₁, y₂, y₃⟩ =>
      MackeyDiagrams.LabelledDrawing.vertical (crossRight ga ad df ab' b'f y₁)
        (MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ab' gc cb' b'f y₂)
          (crossRight gc cb' b'f ce ef y₃))
  let leftMultiplier := fun d : LeftLabels => multiplier (leftDiagram d)
  let rightMultiplier := fun d : RightLabels => multiplier (rightDiagram d)
  ∃ (φ : LeftLabels → RightLabels) (ψ : RightLabels → LeftLabels),
    (∀ d : LeftLabels, rightMultiplier (φ d) = leftMultiplier d) ∧
    (∀ d : RightLabels, leftMultiplier (ψ d) = rightMultiplier d) ∧
    (∀ d : LeftLabels, leftMultiplier (ψ (φ d)) = leftMultiplier d) ∧
    (∀ d : RightLabels, rightMultiplier (φ (ψ d)) = rightMultiplier d)
) :=
(by
  intro U inst G A D F C E repGA repAD repDF repGC repCE repEF
    hGA hAD hDF hGC hCE hEF ga ad df gc ce ef bottomPair topPair
    word bottom top straight merge split splitBottom mergeTop mergedEvaluation multiplier
    crossing crossLeft crossRight LeftLabels RightLabels leftDiagram rightDiagram
    leftMultiplier rightMultiplier
  -- Lemma 6.1, archived PDF pp. 19–20 and revised published PDF pp. 21–22.
  -- The source locator uses the archived pagination. The PDFs have different
  -- checksums. The online proof has named sections, with no numbered
  -- Alphabeta proof steps supplied for this endpoint.
  -- The registered supplier gives both ordered multiplier formulas and their
  -- termwise support condition on exactly the merge-dot-split drawings above.
  have supplier :=
    ThreeInductionCrossingMultipliers G A D F C E repGA repAD repDF repGC repCE repEF
      hGA hAD hDF hGC hCE hEF
  let allowed := fun p : G =>
    (repGA * repAD * repDF)⁻¹ * (p : U) * (repGC * repCE * repEF) ∈ Subgroup.centralizer (F : Set U)
  refine relabel ga ad df gc ce ef leftMultiplier rightMultiplier allowed ?_ ?_ ?_
  · intro p hp
    exact eligibleOfCentralizer (fun f => (supplier.1 f).1) (fun f => (supplier.1 f).2)
      p ((supplier.2.2.2.2.1 p).2.mpr hp)
  · exact supplier.2.2.2.2.2.1
  · exact supplier.2.2.2.2.2.2)
