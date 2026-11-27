import MackeyDiagrams
import Proofs.MultipliersUnderRelabelling

set_option maxHeartbeats 2000000

open MackeyDiagrams

private theorem roundTripSplitMerge {U : Type*} [Group U] {G : Subgroup U}
    (e : ConjEmbedding G G) :
    let w := Word.up e
    let ee := e.comp e
    let split := (Diagram.splitUp (R := Complex) ee e).eval.vertical
      ((Diagram.splitUp (R := Complex) e e).eval.horizontal (Biset.Hom.id w.basis))
    let merge := ((Diagram.mergeUp (R := Complex) e e).eval.horizontal (Biset.Hom.id w.basis)).vertical
      (Diagram.mergeUp (R := Complex) ee e).eval
    split.vertical merge = Biset.Hom.id (Word.up (ee.comp e)).basis := by
  intro w ee split merge
  have cancel (a b : ConjEmbedding G G) :
      (Diagram.splitUp (R := Complex) a b).eval.vertical (Diagram.mergeUp a b).eval =
        Biset.Hom.id (Word.up (a.comp b)).basis :=
    Diagram.splitUp_mergeUp a b
  dsimp only [split, merge]
  refine Biset.Hom.cancel_middle _ _ _ _ ?_ (cancel ee e)
  rw [Biset.Hom.horizontal_vertical, cancel, Biset.Hom.id_vertical, Biset.Hom.horizontal_id]

namespace RoundTripEvaluation

variable {U : Type*} [Group U] {G : Subgroup U}

private abbrev word (e : ConjEmbedding G G) := Word.tensor (Word.tensor (.up e) (.up e)) (.up e)

private noncomputable abbrev straight (e : ConjEmbedding G G) : LabelledDrawing Complex (.up e) (.up e) :=
  .ordinary (.id (.up e))

private noncomputable abbrev merge (e f : ConjEmbedding G G) : LabelledDrawing Complex
    (Word.tensor (.up e) (.up f)) (.up (e.comp f)) :=
  .trivalent (.mergeUp e f)

private noncomputable abbrev split (e f : ConjEmbedding G G) : LabelledDrawing Complex
    (.up (e.comp f)) (Word.tensor (.up e) (.up f)) :=
  .trivalent (.splitUp e f)

private noncomputable abbrev crossing (e : ConjEmbedding G G)
    (d : DotLabel Complex (e.comp e) (e.comp e)) :=
  (merge e e).vertical (d.upDrawing.vertical (split e e))

private noncomputable abbrev crossLeft (e : ConjEmbedding G G)
    (d : DotLabel Complex (e.comp e) (e.comp e)) : LabelledDrawing Complex (word e) (word e) :=
  (crossing e d).horizontal (straight e)

private noncomputable abbrev crossRight (e : ConjEmbedding G G)
    (d : DotLabel Complex (e.comp e) (e.comp e)) : LabelledDrawing Complex (word e) (word e) :=
  (LabelledDrawing.ordinary (Diagram.associate (.up e) (.up e) (.up e))).vertical
    (((straight e).horizontal (crossing e d)).vertical
      (LabelledDrawing.ordinary (Diagram.unassociate (.up e) (.up e) (.up e))))

private noncomputable abbrev multiplier {e : ConjEmbedding G G}
    (a : LabelledDrawing Complex (word e) (word e)) : MonoidAlgebra Complex G :=
  let start := (split (e.comp e) e).vertical ((split e e).horizontal (straight e))
  let finish := ((merge e e).horizontal (straight e)).vertical (merge (e.comp e) e)
  MonoidAlgebra.ofCoeff (((start.vertical (a.vertical finish)).interpret.eval).toLinearMap
    (Finsupp.single (1 : G) 1))

private noncomputable abbrev value {e : ConjEmbedding G G}
    (d : DotLabel Complex (e.comp e) (e.comp e)) : MonoidAlgebra Complex G :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element d)

private noncomputable abbrev along (e : ConjEmbedding G G) :=
  MonoidAlgebra.mapDomainAlgHom Complex Complex e.toHom

private theorem specialize (e : ConjEmbedding G G)
    (hrep : ∀ x : G, (1 : U) * (x : U) * (1 : U)⁻¹ ∈ G)
    (he : e = ConjEmbedding.ofConjugator 1 hrep) :
    (∀ d₁ d₂ d₃ : DotLabel Complex (e.comp e) (e.comp e),
      multiplier ((crossLeft e d₁).vertical ((crossRight e d₂).vertical (crossLeft e d₃))) =
        value d₁ * along e (value d₂) * value d₃) ∧
    (∀ d₁ d₂ d₃ : DotLabel Complex (e.comp e) (e.comp e),
      multiplier ((crossRight e d₁).vertical ((crossLeft e d₂).vertical (crossRight e d₃))) =
        along e (value d₁) * value d₂ * along e (value d₃)) ∧
    (∀ a b : LabelledDrawing Complex (word e) (word e),
      a.interpret.eval = b.interpret.eval ↔ multiplier a = multiplier b) := by
  subst e
  let e := ConjEmbedding.ofConjugator (1 : U) hrep
  have result := ThreeInductionCrossingMultipliers G G G G G G
    1 1 1 1 1 1 hrep hrep hrep hrep hrep hrep
  refine ⟨?_, ?_, ?_⟩
  · intro d₁ d₂ d₃
    exact (result.2.2.2.2.2.1 G e e e d₁ d₂ d₃).1
  · intro d₁ d₂ d₃
    exact (result.2.2.2.2.2.2 G e e e d₁ d₂ d₃).1
  · intro a b
    exact result.2.2.2.1 a b

end RoundTripEvaluation

theorem ThreeInductionLabelsChangeOnRoundTrip : (
let U := Multiplicative (ZMod 2)
let G : Subgroup U := ⊤
let g : G := ⟨Multiplicative.ofAdd (1 : ZMod 2), Subgroup.mem_top _⟩
let e := MackeyDiagrams.ConjEmbedding.id G
let ee := MackeyDiagrams.ConjEmbedding.comp e e
let w := MackeyDiagrams.Word.up e
let boundary := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.tensor w w) w
let Weights := fun {H K : Subgroup U} (a b : MackeyDiagrams.ConjEmbedding H K) =>
  MackeyDiagrams.DotLabel Complex a b
let LeftLabels :=
  Σ (B : Subgroup U) (gb : MackeyDiagrams.ConjEmbedding B G)
    (bd : MackeyDiagrams.ConjEmbedding G B) (be : MackeyDiagrams.ConjEmbedding G B),
    Weights ee (MackeyDiagrams.ConjEmbedding.comp gb bd) ×
    Weights (MackeyDiagrams.ConjEmbedding.comp bd e) (MackeyDiagrams.ConjEmbedding.comp be e) ×
    Weights (MackeyDiagrams.ConjEmbedding.comp gb be) ee
let RightLabels :=
  Σ (B' : Subgroup U) (ab' : MackeyDiagrams.ConjEmbedding B' G)
    (cb' : MackeyDiagrams.ConjEmbedding B' G) (b'f : MackeyDiagrams.ConjEmbedding G B'),
    Weights ee (MackeyDiagrams.ConjEmbedding.comp ab' b'f) ×
    Weights (MackeyDiagrams.ConjEmbedding.comp e ab') (MackeyDiagrams.ConjEmbedding.comp e cb') ×
    Weights (MackeyDiagrams.ConjEmbedding.comp cb' b'f) ee
let straight := fun {H K : Subgroup U} (a : MackeyDiagrams.ConjEmbedding H K) =>
  MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
let mergeUp := fun {P Q S : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
  MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.mergeUp a b)
let splitUp := fun {P Q S : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
  MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.splitUp a b)
let crossing := fun {P Q Q' S : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
    (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
    (d : Weights (MackeyDiagrams.ConjEmbedding.comp a b)
      (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
  MackeyDiagrams.LabelledDrawing.vertical (mergeUp a b)
    (MackeyDiagrams.LabelledDrawing.vertical (MackeyDiagrams.DotLabel.upDrawing d)
      (splitUp a' b'))
let crossLeft := fun {Q Q' S : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q G) (b : MackeyDiagrams.ConjEmbedding S Q)
    (a' : MackeyDiagrams.ConjEmbedding Q' G) (b' : MackeyDiagrams.ConjEmbedding S Q')
    (c : MackeyDiagrams.ConjEmbedding G S)
    (d : Weights (MackeyDiagrams.ConjEmbedding.comp a b)
      (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
  MackeyDiagrams.LabelledDrawing.horizontal (crossing a b a' b' d)
    (straight c)
let crossRight := fun {Q S S' : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q G)
    (b : MackeyDiagrams.ConjEmbedding S Q) (c : MackeyDiagrams.ConjEmbedding G S)
    (b' : MackeyDiagrams.ConjEmbedding S' Q) (c' : MackeyDiagrams.ConjEmbedding G S')
    (d : Weights (MackeyDiagrams.ConjEmbedding.comp b c)
      (MackeyDiagrams.ConjEmbedding.comp b' c')) =>
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.associate (MackeyDiagrams.Word.up a)
        (MackeyDiagrams.Word.up b) (MackeyDiagrams.Word.up c)))
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (straight a)
        (crossing b c b' c' d))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (MackeyDiagrams.Word.up a)
          (MackeyDiagrams.Word.up b') (MackeyDiagrams.Word.up c'))))
let leftDiagram : LeftLabels → MackeyDiagrams.LabelledDrawing Complex boundary boundary :=
  fun ⟨_, gb, bd, be, x₁, x₂, x₃⟩ =>
    MackeyDiagrams.LabelledDrawing.vertical (crossLeft e e gb bd e x₁)
      (MackeyDiagrams.LabelledDrawing.vertical (crossRight gb bd e be e x₂)
        (crossLeft gb be e e e x₃))
let rightDiagram : RightLabels → MackeyDiagrams.LabelledDrawing Complex boundary boundary :=
  fun ⟨_, ab', cb', b'f, y₁, y₂, y₃⟩ =>
    MackeyDiagrams.LabelledDrawing.vertical (crossRight e e e ab' b'f y₁)
      (MackeyDiagrams.LabelledDrawing.vertical (crossLeft e ab' e cb' b'f y₂)
        (crossRight e cb' b'f e e y₃))
let merge :=
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal (mergeUp e e) (straight e))
    (mergeUp ee e)
let split :=
  MackeyDiagrams.LabelledDrawing.vertical (splitUp ee e)
    (MackeyDiagrams.LabelledDrawing.horizontal (splitUp e e) (straight e))
let evaluate := fun {p q : MackeyDiagrams.Word G G}
    (drawing : MackeyDiagrams.LabelledDrawing Complex p q) =>
  MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
let multiplier := fun (drawing : MackeyDiagrams.LabelledDrawing Complex boundary boundary) =>
  MonoidAlgebra.ofCoeff
    (MackeyDiagrams.Biset.Hom.toLinearMap
      (evaluate
        (MackeyDiagrams.LabelledDrawing.vertical split
          (MackeyDiagrams.LabelledDrawing.vertical drawing merge)))
      (Finsupp.single (1 : G) 1))
let selfDot : G → MackeyDiagrams.Dot ee ee := fun p =>
  ⟨p, fun h => mul_comm (MackeyDiagrams.ConjEmbedding.toHom ee h) p⟩
let oneDot : Weights ee ee := Finsupp.single (selfDot 1) 1
let gDot : Weights ee ee := Finsupp.single (selfDot g) 1
let middleDot := fun (m : MonoidAlgebra Complex G) =>
  Finsupp.mapDomain selfDot (MonoidAlgebra.coeff m)
let φ : LeftLabels → RightLabels := fun d =>
  ⟨G, e, e, e, oneDot, middleDot (multiplier (leftDiagram d)), oneDot⟩
let ψ : RightLabels → LeftLabels := fun d =>
  ⟨G, e, e, e, oneDot, middleDot (multiplier (rightDiagram d)), oneDot⟩
let left : LeftLabels := ⟨G, e, e, e, gDot, oneDot, gDot⟩
let leftOne : LeftLabels := ⟨G, e, e, e, oneDot, oneDot, oneDot⟩
let right : RightLabels := ⟨G, e, e, e, gDot, oneDot, gDot⟩
let rightOne : RightLabels := ⟨G, e, e, e, oneDot, oneDot, oneDot⟩
let identity := evaluate (MackeyDiagrams.LabelledDrawing.ordinary
  (MackeyDiagrams.Diagram.id (R := Complex) boundary))
g ≠ 1 ∧ g ^ 2 = 1 ∧
  multiplier (leftDiagram left) = 1 ∧
  ψ (φ left) = leftOne ∧ left ≠ leftOne ∧
  evaluate (leftDiagram left) = identity ∧
  evaluate (leftDiagram leftOne) = identity ∧
  φ left = φ leftOne ∧
  (∀ recover : RightLabels → LeftLabels,
    ¬ (recover (φ left) = left ∧ recover (φ leftOne) = leftOne)) ∧
  multiplier (rightDiagram right) = 1 ∧
  φ (ψ right) = rightOne ∧ right ≠ rightOne ∧
  evaluate (rightDiagram right) = identity ∧
  evaluate (rightDiagram rightOne) = identity ∧
  ψ right = ψ rightOne ∧
  (∀ recover : LeftLabels → RightLabels,
    ¬ (recover (ψ right) = right ∧ recover (ψ rightOne) = rightOne))
) :=
(by
  classical
  intro U G g e ee w boundary Weights LeftLabels RightLabels straight mergeUp splitUp
    crossing crossLeft crossRight leftDiagram rightDiagram merge split evaluate multiplier
    selfDot oneDot gDot middleDot φ ψ left leftOne right rightOne identity
  -- Xiao, Example 6.1, archived PDF p. 21 and published revision p. 23.
  -- The two crossing orders are rendered on archive p. 19 and published p. 21.
  -- The source's "Round-trip calculations" paragraph describes the return rule.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=23
  -- MultipliersUnderRelabelling proves existence of preserving relabellings.
  -- Its registered supplier ThreeInductionCrossingMultipliers gives the actual
  -- formulas and equality test needed for the specified relabellings here.
  have hg : g ≠ 1 := by
    intro h
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    exact h10 (congrArg (fun x : G => Multiplicative.toAdd (x : U)) h)
  have hgg : g * g = 1 := by
    apply Subtype.ext
    change (1 : ZMod 2) + 1 = 0
    decide
  let hrep (x : G) : (1 : U) * (x : U) * (1 : U)⁻¹ ∈ G := by simp
  have he : ConjEmbedding.ofConjugator (1 : U) hrep = e := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (1 : U) * (x : U) * (1 : U)⁻¹ = x
    simp
  have supplier := RoundTripEvaluation.specialize e hrep he.symm
  let value (d : Weights ee ee) : MonoidAlgebra Complex G :=
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element d)
  let along := MonoidAlgebra.mapDomainAlgHom Complex Complex e.toHom
  have leftFormula (d₁ d₂ d₃ : Weights ee ee) :
      multiplier (leftDiagram ⟨G, e, e, e, d₁, d₂, d₃⟩) =
        value d₁ * along (value d₂) * value d₃ :=
    supplier.1 d₁ d₂ d₃
  have rightFormula (d₁ d₂ d₃ : Weights ee ee) :
      multiplier (rightDiagram ⟨G, e, e, e, d₁, d₂, d₃⟩) =
        along (value d₁) * value d₂ * along (value d₃) :=
    supplier.2.1 d₁ d₂ d₃
  have evaluationTest (a b : LabelledDrawing Complex boundary boundary) :
      evaluate a = evaluate b ↔ multiplier a = multiplier b :=
    supplier.2.2 a b
  -- The merge–dot–split calculation specializes at the six identity
  -- embeddings. The supplier already accounts for the embedding on right
  -- crossings through DotLabel.eval_upDrawing and the evaluated merge rules.
  -- Diagram.splitUp_mergeUp verifies the identity comparison, using the
  -- basis multiplication of Diagram.eval_mergeUp_single.
  have alongId (z : MonoidAlgebra Complex G) : along z = z := by
    change MonoidAlgebra.mapDomainAlgHom Complex Complex (MonoidHom.id G) z = z
    rw [MonoidAlgebra.mapDomainAlgHom_id]
    rfl
  have valueOne : value oneDot = 1 := by
    simp only [value, oneDot, Finsupp.mapDomain_single, MonoidAlgebra.one_def]
    rfl
  have valueG : value gDot = MonoidAlgebra.single g 1 := by
    simp only [value, gDot, Finsupp.mapDomain_single]
    rfl
  have valueSquare : value gDot * value gDot = 1 := by
    rw [valueG, MonoidAlgebra.single_mul_single, hgg, mul_one, MonoidAlgebra.one_def]
  have ml : multiplier (leftDiagram left) = 1 := by
    change multiplier (leftDiagram ⟨G, e, e, e, gDot, oneDot, gDot⟩) = 1
    simp only [leftFormula, alongId, valueOne, mul_one, valueSquare]
  have mlOne : multiplier (leftDiagram leftOne) = 1 := by
    change multiplier (leftDiagram ⟨G, e, e, e, oneDot, oneDot, oneDot⟩) = 1
    simp only [leftFormula, alongId, valueOne, mul_one]
  have mr : multiplier (rightDiagram right) = 1 := by
    change multiplier (rightDiagram ⟨G, e, e, e, gDot, oneDot, gDot⟩) = 1
    simp only [rightFormula, alongId, valueOne, mul_one, valueSquare]
  have mrOne : multiplier (rightDiagram rightOne) = 1 := by
    change multiplier (rightDiagram ⟨G, e, e, e, oneDot, oneDot, oneDot⟩) = 1
    simp only [rightFormula, alongId, valueOne, mul_one]
  let idDrawing := LabelledDrawing.ordinary (Diagram.id (R := Complex) boundary)
  have mi : multiplier idDrawing = 1 := by
    change MonoidAlgebra.ofCoeff
      (((evaluate split).vertical (Biset.Hom.id _ |>.vertical (evaluate merge))).toLinearMap
        (Finsupp.single (1 : G) 1)) = 1
    have cancel : (evaluate split).vertical (evaluate merge) =
        Biset.Hom.id (Word.up (ee.comp e)).basis := roundTripSplitMerge e
    rw [Biset.Hom.id_vertical, cancel]
    rfl
  -- The round-trip normal form puts the multiplier in the middle mark.
  -- At multiplier 1 its coefficientwise lift is the identity singleton.
  have middleOne : middleDot 1 = oneDot := by
    change Finsupp.mapDomain selfDot (Finsupp.single (1 : G) (1 : Complex)) = oneDot
    rw [Finsupp.mapDomain_single]
  have toRight : φ left = rightOne := by
    dsimp only [φ, rightOne]
    rw [ml, middleOne]
  have toRightOne : φ leftOne = rightOne := by
    dsimp only [φ, rightOne]
    rw [mlOne, middleOne]
  have toLeft : ψ right = leftOne := by
    dsimp only [ψ, leftOne]
    rw [mr, middleOne]
  have toLeftOne : ψ rightOne = leftOne := by
    dsimp only [ψ, leftOne]
    rw [mrOne, middleOne]
  -- Push the first marked label along its element projection. This gives
  -- a coefficient in the same group for every admissible interior labelling.
  let firstLeft : LeftLabels → G →₀ Complex :=
    fun ⟨_, _, _, _, d, _, _⟩ => Finsupp.mapDomain Dot.element d
  let firstRight : RightLabels → G →₀ Complex :=
    fun ⟨_, _, _, _, d, _, _⟩ => Finsupp.mapDomain Dot.element d
  have distinguish (h : Finsupp.mapDomain (Dot.element (a := ee) (b := ee)) gDot =
      Finsupp.mapDomain (Dot.element (a := ee) (b := ee)) oneDot) : False := by
    simp only [gDot, oneDot, Finsupp.mapDomain_single] at h
    change Finsupp.single g (1 : Complex) = Finsupp.single 1 1 at h
    have atG := DFunLike.congr_fun h g
    simp [hg] at atG
  have hl : left ≠ leftOne := fun h => distinguish (congrArg firstLeft h)
  have hr : right ≠ rightOne := fun h => distinguish (congrArg firstRight h)
  have hφ : φ left = φ leftOne := toRight.trans toRightOne.symm
  have hψ : ψ right = ψ rightOne := toLeft.trans toLeftOne.symm
  refine ⟨hg, by rwa [pow_two], ml, (congrArg ψ toRight).trans toLeftOne, hl,
    (evaluationTest _ idDrawing).2 (ml.trans mi.symm),
    (evaluationTest _ idDrawing).2 (mlOne.trans mi.symm), hφ, ?_,
    mr, (congrArg φ toLeft).trans toRightOne, hr,
    (evaluationTest _ idDrawing).2 (mr.trans mi.symm),
    (evaluationTest _ idDrawing).2 (mrOne.trans mi.symm), hψ, ?_⟩
  · rintro recover ⟨ha, hb⟩
    exact hl (ha.symm.trans ((congrArg recover hφ).trans hb))
  · rintro recover ⟨ha, hb⟩
    exact hr (ha.symm.trans ((congrArg recover hψ).trans hb)))
