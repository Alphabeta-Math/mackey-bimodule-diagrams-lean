import MackeyDiagrams
import Proofs.ThreeInductionCrossingMultipliers
import Proofs.ThreeInductionReidemeisterThree

set_option maxHeartbeats 2000000

namespace AlternativeThreeInductionProof

open MackeyDiagrams

variable {U : Type*} [Group U] {H K L : Subgroup U}

private abbrev Represents (a : ConjEmbedding H K) (s : U) : Prop :=
  ∀ h : H, (a.toHom h : U) = s * (h : U) * s⁻¹

private theorem repEq {a b : ConjEmbedding H K} {s : U}
    (ha : Represents a s) (hb : Represents b s) : a = b :=
  ConjEmbedding.ext (MonoidHom.ext fun h => Subtype.ext ((ha h).trans (hb h).symm))

private theorem repComp {a : ConjEmbedding K L} {b : ConjEmbedding H K} {s t : U}
    (ha : Represents a s) (hb : Represents b t) : Represents (a.comp b) (s * t) := by
  intro h
  rw [ConjEmbedding.comp_apply, ha, hb]
  group

private theorem asConjugator (a : ConjEmbedding H K) :
    ∃ s : U, ∃ hs : ∀ h : H, s * (h : U) * s⁻¹ ∈ K,
      a = ConjEmbedding.ofConjugator s hs := by
  obtain ⟨s, hs⟩ := a.hasRepresentative
  exact ⟨s, fun h => hs h ▸ (a.toHom h).property,
    repEq hs (fun _ => rfl)⟩

private theorem repDotLeft {a b : ConjEmbedding H K} (d : Dot a b) {s : U}
    (hb : Represents b s) : Represents a ((d.element : U) * s) := by
  intro h
  have he := congrArg (fun k : K => (k : U)) (d.intertwines h)
  simp only [Subgroup.coe_mul, hb h] at he
  calc
    (a.toHom h : U) = ((a.toHom h : U) * (d.element : U)) * (d.element : U)⁻¹ := by group
    _ = ((d.element : U) * s) * (h : U) * ((d.element : U) * s)⁻¹ := by rw [he]; group

private theorem repDotRight {a b : ConjEmbedding H K} (d : Dot a b) {s : U}
    (ha : Represents a s) : Represents b ((d.element : U)⁻¹ * s) :=
  repDotLeft d.inverse ha

private theorem repFactorRight {a : ConjEmbedding K L} {b : ConjEmbedding H K} {s t : U}
    (ha : Represents a s) (hab : Represents (a.comp b) t) :
    Represents b (s⁻¹ * t) := by
  intro h
  have he := hab h
  rw [ConjEmbedding.comp_apply, ha] at he
  calc
    (b.toHom h : U) = s⁻¹ * (s * (b.toHom h : U) * s⁻¹) * s := by group
    _ = (s⁻¹ * t) * (h : U) * (s⁻¹ * t)⁻¹ := by rw [he]; group

private def restrictTarget (a : ConjEmbedding H K) (L : Subgroup U)
    (ha : ∀ h : H, (a.toHom h : U) ∈ L) : ConjEmbedding H L where
  toHom :=
    { toFun := fun h => ⟨a.toHom h, ha h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' x y := Subtype.ext (by simp) }
  hasRepresentative := a.hasRepresentative

private theorem idDotOfEq {a b : ConjEmbedding H K} (h : a = b) :
    ∃ d : Dot a b, d.element = 1 := by
  subst b
  exact ⟨Dot.id a, rfl⟩

private theorem liftSupported {B G F : Subgroup U} (hBG : B ≤ G)
    {a b : ConjEmbedding F B} (m : MonoidAlgebra Complex G)
    (hB : ∀ p ∈ m.coeff.support, (p : U) ∈ B)
    (hDot : ∀ p ∈ m.coeff.support, ∀ f : F,
      (a.toHom f : U) * (p : U) = (p : U) * (b.toHom f : U)) :
    ∃ x : DotLabel Complex a b,
      MonoidAlgebra.mapDomainAlgHom Complex Complex (Subgroup.inclusion hBG)
        (MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element x)) = m := by
  classical
  let inc := Subgroup.inclusion hBG
  let key : Dot a b → G := fun d => inc d.element
  have injective : Function.Injective key :=
    fun _ _ heq => Dot.ext (Subtype.ext (congrArg (fun g : G => (g : U)) heq))
  have hRange : ↑m.coeff.support ⊆ Set.range key := by
    intro p hp
    let bp : B := ⟨p, hB p hp⟩
    let d : Dot a b := ⟨bp, fun f => Subtype.ext (hDot p hp f)⟩
    exact ⟨d, Subtype.ext rfl⟩
  refine ⟨Finsupp.comapDomain key m.coeff injective.injOn, ?_⟩
  apply MonoidAlgebra.coeff_injective
  change Finsupp.mapDomain inc (Finsupp.mapDomain Dot.element _) = _
  rw [← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_comapDomain key injective m.coeff hRange

private theorem singletonValue {a b : ConjEmbedding H K} (d : Dot a b) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (Finsupp.single d (1 : Complex))) =
      MonoidAlgebra.single d.element 1 := by
  rw [Finsupp.mapDomain_single]
  rfl

private abbrev conjugate (s : U) (H : Subgroup U) : Subgroup U :=
  H.map (MulAut.conj s).toMonoidHom

private theorem mem_conjugate {s z : U} :
    z ∈ conjugate s H ↔ s⁻¹ * z * s ∈ H := by
  change (∃ x ∈ H, s * x * s⁻¹ = z) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hz
    exact ⟨_, hz, by group⟩

end AlternativeThreeInductionProof

open MackeyDiagrams AlternativeThreeInductionProof

theorem AlternativeThreeInductionInternalGroups : (
∀ {U : Type*} [Group U] (G A D F C E : Subgroup U)
    (ga : MackeyDiagrams.ConjEmbedding A G) (ad : MackeyDiagrams.ConjEmbedding D A)
    (df : MackeyDiagrams.ConjEmbedding F D) (gc : MackeyDiagrams.ConjEmbedding C G)
    (ce : MackeyDiagrams.ConjEmbedding E C) (ef : MackeyDiagrams.ConjEmbedding F E),
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
  let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
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
  let DotWeights := fun {H K : Subgroup U} (a b : MackeyDiagrams.ConjEmbedding H K) =>
    MackeyDiagrams.DotLabel Complex a b
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
      DotWeights bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd) ×
      DotWeights (MackeyDiagrams.ConjEmbedding.comp bd df) (MackeyDiagrams.ConjEmbedding.comp be ef) ×
      DotWeights (MackeyDiagrams.ConjEmbedding.comp gb be) topPair
  let RightLabels :=
    Σ (B' : Subgroup U) (ab' : MackeyDiagrams.ConjEmbedding B' A)
      (cb' : MackeyDiagrams.ConjEmbedding B' C) (b'f : MackeyDiagrams.ConjEmbedding F B'),
      DotWeights (MackeyDiagrams.ConjEmbedding.comp ad df) (MackeyDiagrams.ConjEmbedding.comp ab' b'f) ×
      DotWeights (MackeyDiagrams.ConjEmbedding.comp ga ab') (MackeyDiagrams.ConjEmbedding.comp gc cb') ×
      DotWeights (MackeyDiagrams.ConjEmbedding.comp cb' b'f) (MackeyDiagrams.ConjEmbedding.comp ce ef)
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
  let represents := fun {H K : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H K) (s : U) =>
    ∀ h : H, (MackeyDiagrams.ConjEmbedding.toHom a h : U) = s * (h : U) * s⁻¹
  let conjugate := fun (s : U) (H : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) H
  let singleDot := fun {H K : Subgroup U} {a b : MackeyDiagrams.ConjEmbedding H K}
      (d : MackeyDiagrams.Dot a b) => Finsupp.single d (1 : Complex)
  let sameEvaluation := fun (left : LeftLabels) (right : RightLabels) =>
    evaluate (leftDiagram left) = evaluate (rightDiagram right)
  (∀ (right : RightLabels) (B : Subgroup U) (hBG : B ≤ G),
    let m := rightMultiplier right
    (∀ a : A, (MackeyDiagrams.ConjEmbedding.toHom ga a : U) ∈ B) →
    (∀ c : C, (MackeyDiagrams.ConjEmbedding.toHom gc c : U) ∈ B) →
    (∀ p ∈ Finsupp.support (MonoidAlgebra.coeff m), (p : U) ∈ B) →
    ∃ (gb : MackeyDiagrams.ConjEmbedding B G)
      (bd : MackeyDiagrams.ConjEmbedding D B) (be : MackeyDiagrams.ConjEmbedding E B)
      (x₁ : MackeyDiagrams.Dot bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd))
      (x₂ : DotWeights (MackeyDiagrams.ConjEmbedding.comp bd df)
        (MackeyDiagrams.ConjEmbedding.comp be ef))
      (x₃ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp gb be) topPair),
      let left : LeftLabels := ⟨B, gb, bd, be, singleDot x₁, x₂, singleDot x₃⟩
      represents gb 1 ∧
      MackeyDiagrams.ConjEmbedding.comp gb bd = bottomPair ∧
      MackeyDiagrams.ConjEmbedding.comp gb be = topPair ∧
      MackeyDiagrams.Dot.element x₁ = 1 ∧ MackeyDiagrams.Dot.element x₃ = 1 ∧
      MonoidAlgebra.mapDomainAlgHom Complex Complex (Subgroup.inclusion hBG)
        (MonoidAlgebra.ofCoeff (Finsupp.mapDomain MackeyDiagrams.Dot.element x₂)) = m ∧
      leftMultiplier left = m ∧ sameEvaluation left right) ∧
  (∀ (B : Subgroup U) (gb : MackeyDiagrams.ConjEmbedding B G)
      (bd : MackeyDiagrams.ConjEmbedding D B) (be : MackeyDiagrams.ConjEmbedding E B)
      (x₁ : MackeyDiagrams.Dot bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd))
      (x₂ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp bd df)
        (MackeyDiagrams.ConjEmbedding.comp be ef))
      (x₃ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp gb be) topPair),
    let left : LeftLabels := ⟨B, gb, bd, be, singleDot x₁, singleDot x₂, singleDot x₃⟩
    let p := MackeyDiagrams.Dot.element x₁ *
      MackeyDiagrams.ConjEmbedding.toHom gb (MackeyDiagrams.Dot.element x₂) *
      MackeyDiagrams.Dot.element x₃
    ∃ repGA repAD repDF repGC repCE repEF repGB repBD repBE repGB' repBD' repBE' : U,
      represents ga repGA ∧ represents ad repAD ∧ represents df repDF ∧
      represents gc repGC ∧ represents ce repCE ∧ represents ef repEF ∧
      represents gb repGB ∧ represents bd repBD ∧ represents be repBE ∧
      represents gb repGB' ∧ represents bd repBD' ∧ represents be repBE' ∧
      (MackeyDiagrams.Dot.element x₁ : U) = repGA * repAD * repBD⁻¹ * repGB⁻¹ ∧
      (MackeyDiagrams.Dot.element x₂ : U) = repBD' * repDF * repEF⁻¹ * repBE⁻¹ ∧
      (MackeyDiagrams.Dot.element x₃ : U) = repGB' * repBE' * repCE⁻¹ * repGC⁻¹ ∧
      ∀ τ : U,
        let B'' := conjugate repDF⁻¹ D ⊓ conjugate repEF⁻¹ E
        let B' := conjugate τ B''
        ∃ (ab' : MackeyDiagrams.ConjEmbedding B' A) (cb' : MackeyDiagrams.ConjEmbedding B' C)
          (b'f : MackeyDiagrams.ConjEmbedding F B')
          (y₁ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp ad df)
            (MackeyDiagrams.ConjEmbedding.comp ab' b'f))
          (y₂ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp ga ab')
            (MackeyDiagrams.ConjEmbedding.comp gc cb'))
          (y₃ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp cb' b'f)
            (MackeyDiagrams.ConjEmbedding.comp ce ef)),
          let right : RightLabels := ⟨B', ab', cb', b'f, singleDot y₁, singleDot y₂, singleDot y₃⟩
          represents ab' (repAD * repDF * τ⁻¹) ∧ represents cb' (repCE * repEF * τ⁻¹) ∧
          represents b'f τ ∧
          MackeyDiagrams.Dot.element y₁ = 1 ∧ MackeyDiagrams.Dot.element y₂ = p ∧
          MackeyDiagrams.Dot.element y₃ = 1 ∧
          rightMultiplier right = leftMultiplier left ∧ sameEvaluation left right)
) :=
(by
  classical
  intro U inst G A D F C E ga ad df gc ce ef
  obtain ⟨sGA, hsGA, rfl⟩ := asConjugator ga
  obtain ⟨sAD, hsAD, rfl⟩ := asConjugator ad
  obtain ⟨sDF, hsDF, rfl⟩ := asConjugator df
  obtain ⟨sGC, hsGC, rfl⟩ := asConjugator gc
  obtain ⟨sCE, hsCE, rfl⟩ := asConjugator ce
  obtain ⟨sEF, hsEF, rfl⟩ := asConjugator ef
  let ga : ConjEmbedding A G := ConjEmbedding.ofConjugator sGA hsGA
  let ad : ConjEmbedding D A := ConjEmbedding.ofConjugator sAD hsAD
  let df : ConjEmbedding F D := ConjEmbedding.ofConjugator sDF hsDF
  let gc : ConjEmbedding C G := ConjEmbedding.ofConjugator sGC hsGC
  let ce : ConjEmbedding E C := ConjEmbedding.ofConjugator sCE hsCE
  let ef : ConjEmbedding F E := ConjEmbedding.ofConjugator sEF hsEF
  intro bottomPair topPair word bottom top straight merge split splitBottom mergeTop
    evaluate mergedEvaluation multiplier DotWeights crossing crossLeft crossRight
    LeftLabels RightLabels leftDiagram rightDiagram leftMultiplier rightMultiplier
    represents conjugate singleDot sameEvaluation
  -- Ian Xiao, § 6.1, “Other choices of internal group,” archived PDF p. 21
  -- and 28 November published revision p. 23.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- Numbering below follows the
  -- arguments in this unnumbered paragraph, which has no Alphabeta Math proof entry.
  -- Lemma 6.1 is the registered supplier for support, the two multiplier formulas,
  -- and equality of evaluations, so the crossing basis computations are
  -- available in assembled form. Theorem 6.2 supplies an equivalence of
  -- evaluation classes. The witnesses for these specified internal groups
  -- are constructed below.
  have laws := ThreeInductionCrossingMultipliers G A D F C E sGA sAD sDF sGC sCE sEF
    hsGA hsAD hsDF hsGC hsCE hsEF
  have compare (d e : LabelledDrawing Complex bottom top) :
      evaluate d = evaluate e ↔ multiplier d = multiplier e :=
    laws.2.2.2.1 d e
  have leftRule := laws.2.2.2.2.2.1
  have rightRule := laws.2.2.2.2.2.2
  have boundary := laws.1
  constructor
  · -- Step 1 (ψ). Restrict the two composite embeddings to the chosen B.
    -- Lift the coefficients along the injection from eligible middle dots to G.
    intro right B hBG m hA hC hmB
    let gb : ConjEmbedding B G :=
      ⟨Subgroup.inclusion hBG, ⟨1, by intro h; simp⟩⟩
    let bd : ConjEmbedding D B := restrictTarget bottomPair B (fun d => hA (ad.toHom d))
    let be : ConjEmbedding E B := restrictTarget topPair B (fun e => hC (ce.toHom e))
    have hbd : gb.comp bd = bottomPair :=
      ConjEmbedding.ext (MonoidHom.ext fun d => Subtype.ext rfl)
    have hbe : gb.comp be = topPair :=
      ConjEmbedding.ext (MonoidHom.ext fun e => Subtype.ext rfl)
    obtain ⟨x₁, hx₁⟩ := idDotOfEq hbd.symm
    obtain ⟨x₃, hx₃⟩ := idDotOfEq hbe
    have support : ∀ p ∈ m.coeff.support,
        (sGA * sAD * sDF)⁻¹ * (p : U) * (sGC * sCE * sEF) ∈
          Subgroup.centralizer (F : Set U) := by
      rcases right with ⟨B', ab', cb', b'f, y₁, y₂, y₃⟩
      exact (rightRule B' ab' cb' b'f y₁ y₂ y₃).2
    have middle (p : G) (hp : p ∈ m.coeff.support) (f : F) :
        ((bd.comp df).toHom f : U) * (p : U) =
          (p : U) * ((be.comp ef).toHom f : U) := by
      let u := sGA * sAD * sDF
      let v := sGC * sCE * sEF
      change (bottomPair.toHom (df.toHom f) : U) * (p : U) =
        (p : U) * (topPair.toHom (ef.toHom f) : U)
      rcases boundary f with ⟨hu, hv⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp (support p hp) (f : U) f.property
      change (f : U) * (u⁻¹ * (p : U) * v) = (u⁻¹ * (p : U) * v) * (f : U) at hcomm
      change (bottomPair.toHom (df.toHom f) : U) = u * (f : U) * u⁻¹ at hu
      change (topPair.toHom (ef.toHom f) : U) = v * (f : U) * v⁻¹ at hv
      rw [hu, hv]
      calc
        (u * (f : U) * u⁻¹) * (p : U) =
            u * ((f : U) * (u⁻¹ * (p : U) * v)) * v⁻¹ := by group
        _ = u * ((u⁻¹ * (p : U) * v) * (f : U)) * v⁻¹ := by rw [hcomm]
        _ = (p : U) * (v * (f : U) * v⁻¹) := by group
    obtain ⟨x₂, hx₂⟩ := liftSupported hBG m hmB middle
    let left : LeftLabels := ⟨B, gb, bd, be, singleDot x₁, x₂, singleDot x₃⟩
    have leftValue : leftMultiplier left = m := by
      have formula := (leftRule B gb bd be (singleDot x₁) x₂ (singleDot x₃)).1
      change leftMultiplier left =
        MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot x₁)) *
        MonoidAlgebra.mapDomainAlgHom Complex Complex (Subgroup.inclusion hBG)
          (MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element x₂)) *
        MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot x₃)) at formula
      rw [formula]
      dsimp only [singleDot]
      simp only [singletonValue, hx₁, hx₂, hx₃, ← MonoidAlgebra.one_def, one_mul, mul_one]
    exact ⟨gb, bd, be, x₁, x₂, x₃, (fun h => by change (h : U) = _; simp),
      hbd, hbe, hx₁, hx₃, hx₂, leftValue,
      (compare (leftDiagram left) (rightDiagram right)).2 leftValue⟩
  · -- Step 2 (φ). Each outer strand occurs at just one crossing.
    -- Fix the internal representatives and absorb the three dot elements into
    -- AD, DF and CE. The primed representatives can then equal the unprimed ones.
    intro B gb bd be x₁ x₂ x₃ left p
    obtain ⟨rg, hg⟩ := gb.hasRepresentative
    obtain ⟨rd, hd⟩ := bd.hasRepresentative
    obtain ⟨re, he⟩ := be.hasRepresentative
    let rAD := sGA⁻¹ * ((x₁.element : U) * (rg * rd))
    let rDF := rd⁻¹ * ((x₂.element : U) * (re * sEF))
    let rCE := sGC⁻¹ * ((x₃.element : U)⁻¹ * (rg * re))
    have hGA : Represents ga sGA := fun _ => rfl
    have hGC : Represents gc sGC := fun _ => rfl
    have hEF : Represents ef sEF := fun _ => rfl
    have hAD : Represents ad rAD := repFactorRight hGA (repDotLeft x₁ (repComp hg hd))
    have hDF : Represents df rDF := repFactorRight hd (repDotLeft x₂ (repComp he hEF))
    have hCE : Represents ce rCE := repFactorRight hGC (repDotRight x₃ (repComp hg he))
    have x1eq : (x₁.element : U) = sGA * rAD * rd⁻¹ * rg⁻¹ := by dsimp [rAD]; group
    have x2eq : (x₂.element : U) = rd * rDF * sEF⁻¹ * re⁻¹ := by dsimp [rDF]; group
    have x3eq : (x₃.element : U) = rg * re * rCE⁻¹ * sGC⁻¹ := by dsimp [rCE]; group
    -- Step 3. With these choices both centralizing factors in Xiao's calculation
    -- are 1. The claimed intersection and its arbitrary conjugate still apply.
    have cancelP : (p : U) * (sGC * rCE * sEF) = sGA * rAD * rDF := by
      change (x₁.element : U) * (gb.toHom x₂.element : U) * (x₃.element : U) *
        (sGC * rCE * sEF) = _
      rw [hg, x1eq, x2eq, x3eq]
      group
    refine ⟨sGA, rAD, rDF, sGC, rCE, sEF, rg, rd, re, rg, rd, re,
      hGA, hAD, hDF, hGC, hCE, hEF, hg, hd, he, hg, hd, he, x1eq, x2eq, x3eq, ?_⟩
    intro τ B'' B'
    have hA' (b : B') : (rAD * rDF * τ⁻¹) * (b : U) * (rAD * rDF * τ⁻¹)⁻¹ ∈ A := by
      have hz : τ⁻¹ * (b : U) * τ ∈ B'' := mem_conjugate.mp b.property
      have hD : rDF * (τ⁻¹ * (b : U) * τ) * rDF⁻¹ ∈ D := by
        simpa only [inv_inv] using ((mem_conjugate (s := rDF⁻¹)).mp hz.1)
      have h := (ad.toHom ⟨_, hD⟩).property
      rw [hAD] at h
      convert h using 1
      group
    have hC' (b : B') : (rCE * sEF * τ⁻¹) * (b : U) * (rCE * sEF * τ⁻¹)⁻¹ ∈ C := by
      have hz : τ⁻¹ * (b : U) * τ ∈ B'' := mem_conjugate.mp b.property
      have hE : sEF * (τ⁻¹ * (b : U) * τ) * sEF⁻¹ ∈ E := by
        simpa only [inv_inv] using ((mem_conjugate (s := sEF⁻¹)).mp hz.2)
      have h := (ce.toHom ⟨_, hE⟩).property
      rw [hCE] at h
      convert h using 1
      group
    have hF' (f : F) : τ * (f : U) * τ⁻¹ ∈ B' := by
      refine ⟨(f : U), ⟨?_, ?_⟩, rfl⟩
      · apply (mem_conjugate (s := rDF⁻¹)).mpr
        simpa only [inv_inv, ← hDF f] using (df.toHom f).property
      · apply (mem_conjugate (s := sEF⁻¹)).mpr
        simpa only [inv_inv, ← hEF f] using (ef.toHom f).property
    let ab' := ConjEmbedding.ofConjugator _ hA'
    let cb' := ConjEmbedding.ofConjugator _ hC'
    let b'f := ConjEmbedding.ofConjugator _ hF'
    have hAB : Represents ab' (rAD * rDF * τ⁻¹) := fun _ => rfl
    have hCB : Represents cb' (rCE * sEF * τ⁻¹) := fun _ => rfl
    have hBF : Represents b'f τ := fun _ => rfl
    have outer₁ : ad.comp df = ab'.comp b'f := by
      apply repEq (repComp hAD hDF)
      simpa only [inv_mul_cancel_right] using (repComp hAB hBF)
    have outer₃ : cb'.comp b'f = ce.comp ef := by
      apply Eq.symm
      apply repEq (repComp hCE hEF)
      simpa only [inv_mul_cancel_right] using (repComp hCB hBF)
    obtain ⟨y₁, hy₁⟩ := idDotOfEq outer₁
    obtain ⟨y₃, hy₃⟩ := idDotOfEq outer₃
    have hpRep : sGA * (rAD * rDF * τ⁻¹) * (sGC * (rCE * sEF * τ⁻¹))⁻¹ =
        (p : U) := by
      calc
        _ = (sGA * rAD * rDF) * (sGC * rCE * sEF)⁻¹ := by group
        _ = (p : U) := by rw [← cancelP, mul_inv_cancel_right]
    let y₂ := Dot.ofRepresentatives _ _ (repComp hGA hAB) (repComp hGC hCB)
      (hpRep.symm ▸ p.property)
    have hy₂ : y₂.element = p := Subtype.ext hpRep
    let right : RightLabels := ⟨B', ab', cb', b'f, singleDot y₁, singleDot y₂, singleDot y₃⟩
    -- Step 4. Compare the two normalized products, then recover the evaluation
    -- at the same six boundary embeddings with the injectivity in Lemma 6.1.
    have leftValue : leftMultiplier left = MonoidAlgebra.single p (1 : Complex) := by
      have formula := (leftRule B gb bd be (singleDot x₁) (singleDot x₂) (singleDot x₃)).1
      change leftMultiplier left =
        MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot x₁)) *
        MonoidAlgebra.mapDomainAlgHom Complex Complex gb.toHom
          (MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot x₂))) *
        MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot x₃)) at formula
      rw [formula]
      dsimp only [singleDot]
      simp [p]
    have rightValue : rightMultiplier right = MonoidAlgebra.single p (1 : Complex) := by
      have formula := (rightRule B' ab' cb' b'f (singleDot y₁) (singleDot y₂) (singleDot y₃)).1
      change rightMultiplier right =
        MonoidAlgebra.mapDomainAlgHom Complex Complex ga.toHom
          (MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot y₁))) *
        MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot y₂)) *
        MonoidAlgebra.mapDomainAlgHom Complex Complex gc.toHom
          (MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (singleDot y₃))) at formula
      rw [formula]
      dsimp only [singleDot]
      simp only [singletonValue, hy₁, hy₂, hy₃, ← MonoidAlgebra.one_def, map_one, one_mul, mul_one]
    have equal : rightMultiplier right = leftMultiplier left := rightValue.trans leftValue.symm
    exact ⟨ab', cb', b'f, y₁, y₂, y₃, hAB, hCB, hBF, hy₁, hy₂, hy₃, equal,
      (compare (leftDiagram left) (rightDiagram right)).2 equal.symm⟩)
