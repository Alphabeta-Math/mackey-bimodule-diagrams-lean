import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention

universe u
namespace CaseFiveLeftShapeEvaluationAux

open MackeyDiagrams

variable {U : Type u} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (α : ConjEmbedding G B) (β : ConjEmbedding D B) (γ : ConjEmbedding E B)

private abbrev RDot := Dot (α.comp a) (β.comp b)
private abbrev TDot := Dot (β.comp d) (γ.comp f)
private abbrev SDot := Dot (α.comp c) (γ.comp e)

private noncomputable abbrev ev {K H : Subgroup U} {p q : Word K H} (drawing : LabelledDrawing Complex p q) :=
  drawing.interpret.eval.toLinearMap

private abbrev input (g : G) (x : D) :=
  ((Word.up a).tensor (.down b)).basis.pair (Word.up d).basis
    ((Biset.induction a).pair (Biset.restriction b) g x) 1

private abbrev middleBasis {J : Subgroup U} (η : ConjEmbedding J B) (j : ConjEmbedding F J) (z : B) :=
  ((Word.down α).tensor (.up η)).basis.pair (Word.up j).basis (Generator.mixedPair α η z) 1

private abbrev targetBasis := ((Word.up c).tensor (.down e)).basis

private abbrev output (p : (targetBasis c e).carrier) :=
  (targetBasis c e).pair (Word.up f).basis p 1

private abbrev finiteFibers (s : SDot c e α γ) :=
  ∀ z : B, Set.Finite {p | Generator.mixedProduct α γ
    (Generator.mixedMultiplicationBasis α γ c e s p) = z}

private abbrev projectionDot (s : SDot c e α γ) (hs : finiteFibers c e α γ s) :
    ProjectionDot.Mixed α γ c e :=
  ⟨s, fun z => Set.Finite.subset (hs (Generator.mixedProduct α γ z))
    (fun _ hz => congrArg (Generator.mixedProduct α γ) hz)⟩

private noncomputable abbrev column (s : SDot c e α γ) (hs : finiteFibers c e α γ s) (z : B) :=
  (hs z).toFinset.sum fun p => Finsupp.single (output c e f p) (1 : Complex)

private abbrev first (rs : List (Complex × RDot a b α β)) : LabelledDrawing Complex
    (((Word.up a).tensor (.down b)).tensor (.up d))
    (((Word.down α).tensor (.up β)).tensor (.up d)) :=
  .horizontal (.mixedMultiplication α β a b rs) (.ordinary (.id (.up d)))

private abbrev second (ts : List (Complex × TDot d f β γ)) : LabelledDrawing Complex
    (((Word.down α).tensor (.up β)).tensor (.up d))
    (((Word.down α).tensor (.up γ)).tensor (.up f)) :=
  .vertical (.ordinary (.associate (.down α) (.up β) (.up d)))
    (.vertical (.horizontal (.ordinary (.id (.down α))) (.parallelUp β d γ f ts))
      (.ordinary (.unassociate (.down α) (.up γ) (.up f))))

private abbrev third (ss : List (Complex × ProjectionDot.Mixed α γ c e)) : LabelledDrawing Complex
    (((Word.down α).tensor (.up γ)).tensor (.up f))
    (((Word.up c).tensor (.down e)).tensor (.up f)) :=
  .horizontal (.compactProjection α γ c e ss) (.ordinary (.id (.up f)))

/- Xiao, Lemma 6.6, equation (6.3) and its proof, first operation: the lower
   multiplication gives u(g) r v(x). The typed spectator contributes its
   unit. The Dot type supplies the first vertex condition, as required by
   the registered finite-fiber convention's multiplication formulas. -/
private theorem firstColumn (rs : List (Complex × RDot a b α β)) (g : G) (x : D) :
    ev (first a b d α β rs) (Finsupp.single (input a b d g x) 1) =
      (rs.map fun (k, r) => k • Finsupp.single
        (middleBasis α β d (α.toHom g * r.element * β.toHom x)) 1).sum := by
  let w := (Biset.induction a).pair (Biset.restriction b) g x
  let X := ((Word.down α).tensor (.up β)).basis
  let Y := (Word.up d).basis
  let frame := (Biset.pairLinear Complex X Y).flip (Finsupp.single 1 1)
  let terms := rs.map fun (k,r) => (k, ScopedDiagram.ordinary
    (Diagram.mixedMultiplication (R := Complex) α β a b r))
  change ((ScopedDiagram.linearCombination terms).eval.horizontal
    (Diagram.id (.up d)).eval).toLinearMap (Finsupp.single (input a b d g x) 1) = _
  rw [show Finsupp.single (input a b d g x) (1 : Complex) =
    Biset.pairLinear Complex ((Word.up a).tensor (.down b)).basis Y
      (Finsupp.single w 1) (Finsupp.single 1 1) by
        rw [Biset.pairLinear_single, one_mul]]
  rw [Biset.Hom.horizontal_pairLinear, Diagram.eval_id_apply]
  change frame ((ScopedDiagram.linearCombination terms).eval.toLinearMap (Finsupp.single w 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [terms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨k,r⟩ _
  simp only [Function.comp_apply, map_smul]
  obtain ⟨hprod, hpush, _⟩ := (MixedCrossingFiniteFiberConvention (U := U)).2.1 α β a b r
  change k • frame ((Diagram.mixedMultiplication α β a b r).eval.toLinearMap
    (Finsupp.single w 1)) = _
  rw [hpush w, hprod g x]
  change k • Biset.pairLinear Complex X Y
    (Finsupp.single (Generator.mixedPair α β _) 1) (Finsupp.single 1 1) = _
  rw [Biset.pairLinear_single, one_mul]

/- Lemma 6.6, second operation: the induction dot right-multiplies by t.
   The paper suppresses reassociation and the split's unit factor. After
   merging, multiplying and splitting, rebracket and use the inverse law
   of mixedEquiv (which is proved by balancing) to normalize (z,t) to
   (z*t,1). The induction merge and split are the basis rules underlying
   InductionRestrictionMergesAndSplits, valid for the given embeddings
   without choosing representatives. -/
private theorem secondColumn (ts : List (Complex × TDot d f β γ)) (z : B) :
    ev (second d f α β γ ts) (Finsupp.single (middleBasis α β d z) 1) =
      (ts.map fun (k, t) => k • Finsupp.single (middleBasis α γ f (z * t.element)) 1).sum := by
  let P := Word.down α
  let Q := (Word.up β).tensor (.up d)
  let S := (Word.up γ).tensor (.up f)
  let frame := (Biset.pairLinear Complex P.basis S.basis) (Finsupp.single z 1)
  let unassoc := (Diagram.unassociate (R := Complex) P (.up γ) (.up f)).eval.toLinearMap
  let terms := ts.map fun (k,t) => (k, ScopedDiagram.ordinary
    (Diagram.parallelUp (R := Complex) β d γ f t))
  change unassoc (((Diagram.id P).eval.horizontal
    (ScopedDiagram.linearCombination terms).eval).toLinearMap
    ((Diagram.associate (R := Complex) P (.up β) (.up d)).eval.toLinearMap
      (Finsupp.single (middleBasis α β d z) 1))) = _
  rw [show Finsupp.single (middleBasis α β d z) (1 : Complex) =
    Finsupp.single ((P.basis.tensor (Word.up β).basis).pair (Word.up d).basis
      (P.basis.pair (Word.up β).basis z 1) 1) 1 from rfl,
    Diagram.eval_associate_single P (.up β) (.up d) z 1 1 1]
  rw [show Finsupp.single (P.basis.pair Q.basis z ((Word.up β).basis.pair (Word.up d).basis 1 1)) (1 : Complex) =
    Biset.pairLinear Complex P.basis Q.basis (Finsupp.single z 1)
      (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1) by rw [Biset.pairLinear_single, one_mul]]
  rw [Biset.Hom.horizontal_pairLinear, Diagram.eval_id_apply]
  change unassoc (frame ((ScopedDiagram.linearCombination terms).eval.toLinearMap
    (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1))) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum, map_list_sum]
  simp only [terms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨k,t⟩ _
  simp only [Function.comp_apply, map_smul]
  have hpar :
      (Diagram.parallelUp (R := Complex) β d γ f t).eval.toLinearMap
        (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1) =
      Finsupp.single ((Word.up γ).basis.pair (Word.up f).basis t.element 1) 1 := by
    change (Diagram.splitUp (R := Complex) γ f).eval.toLinearMap
      ((Diagram.upDot t).eval.toLinearMap
        ((Diagram.mergeUp β d).eval.toLinearMap
          (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1))) = _
    rw [Diagram.eval_mergeUp_single β d, map_one, mul_one,
      Diagram.eval_upDot_single, one_mul, Diagram.eval_splitUp_single]
  change k • unassoc (frame ((Diagram.parallelUp β d γ f t).eval.toLinearMap _)) = _
  rw [hpar]
  change k • unassoc (Biset.pairLinear Complex P.basis S.basis
    (Finsupp.single z 1) (Finsupp.single ((Word.up γ).basis.pair (Word.up f).basis t.element 1) 1)) = _
  rw [Biset.pairLinear_single, one_mul]
  unfold unassoc
  rw [Diagram.eval_unassociate_single P (.up γ) (.up f) z t.element 1 1]
  let w := (Biset.restriction α).pair (Biset.induction γ) z t.element
  have hw : w = Generator.mixedPair α γ (z * t.element) :=
    (Generator.mixedPair_mixedProduct α γ w).symm
  change k • Finsupp.single (((Word.down α).tensor (.up γ)).basis.pair
    (Word.up f).basis w 1) 1 = _
  rw [hw]

/- Lemma 6.6, third operation: take the fiber of the upper multiplication
   over the value computed by the lower two crossings. The registered
   finite-fiber convention supplies the projection column with exactly the
   termwise group-fiber hypothesis here. Framing pairs each output with
   the spectator unit and preserves its coefficient. -/
private theorem thirdColumn (ss : List (Complex × {s : SDot c e α γ // finiteFibers c e α γ s}))
    (z : B) :
    ev (third c e f α γ (ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)))
      (Finsupp.single (middleBasis α γ f z) 1) =
      (ss.map fun (k,s) => k • column c e f α γ s.1 s.2 z).sum := by
  let X := ((Word.down α).tensor (.up γ)).basis
  let Y := (Word.up f).basis
  let frame := (Biset.pairLinear Complex (targetBasis c e) Y).flip (Finsupp.single 1 1)
  let labels := ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)
  let terms := labels.map fun (k,s) => (k, ScopedDiagram.ordinary
    (Diagram.mixedProjection (R := Complex) α γ c e s.dot s.finite))
  change ((ScopedDiagram.linearCombination terms).eval.horizontal
    (Diagram.id (.up f)).eval).toLinearMap (Finsupp.single (middleBasis α γ f z) 1) = _
  rw [show Finsupp.single (middleBasis α γ f z) (1 : Complex) =
    Biset.pairLinear Complex X Y (Finsupp.single (Generator.mixedPair α γ z) 1)
      (Finsupp.single 1 1) by
        rw [Biset.pairLinear_single, one_mul]]
  rw [Biset.Hom.horizontal_pairLinear, Diagram.eval_id_apply]
  change frame ((ScopedDiagram.linearCombination terms).eval.toLinearMap
    (Finsupp.single (Generator.mixedPair α γ z) 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [terms, List.map_map]
  simp only [labels, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨k,s⟩ _
  simp only [Function.comp_apply, map_smul]
  obtain ⟨_, _, _, hproj⟩ := (MixedCrossingFiniteFiberConvention (U := U)).2.1 α γ c e s.1
  change k • frame ((Diagram.mixedProjection α γ c e s.1
    (projectionDot c e α γ s.1 s.2).finite).eval.toLinearMap
      (Finsupp.single (Generator.mixedPair α γ z) 1)) = _
  have hcolumn :
      (Diagram.mixedProjection (R := Complex) α γ c e s.1
        (projectionDot c e α γ s.1 s.2).finite).eval.toLinearMap
        (Finsupp.single (Generator.mixedPair α γ z) 1) =
      (s.2 z).toFinset.sum (fun p => Finsupp.single p 1) := (hproj s.2).1 z
  rw [hcolumn, map_sum]
  simp only [frame, LinearMap.flip_apply, Biset.pairLinear_single, mul_one, column, output, Y]

/- Lemma 6.6, linear labels: expand the three marked stages in evaluation.
   Linearity at the two composition interfaces gives one product of
   coefficients for each ordered triple. Each projection term keeps
   its own finite-fiber certificate, including when no terms are present. -/
private theorem stackedColumn (rs : List (Complex × RDot a b α β))
    (ts : List (Complex × TDot d f β γ))
    (ss : List (Complex × {s : SDot c e α γ // finiteFibers c e α γ s}))
    (g : G) (x : D) :
    ev (.vertical (first a b d α β rs) (.vertical (second d f α β γ ts)
      (third c e f α γ (ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)))))
      (Finsupp.single (input a b d g x) 1) =
    (rs.map fun (cr,r) =>
      (ts.map fun (ct,t) =>
        (ss.map fun (cs,s) => (cr * ct * cs) •
          column c e f α γ s.1 s.2 (α.toHom g * r.element * β.toHom x * t.element)).sum).sum).sum := by
  let next := ev (second d f α β γ ts)
  let last := ev (third c e f α γ (ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)))
  change last (next (ev (first a b d α β rs) (Finsupp.single (input a b d g x) 1))) = _
  rw [firstColumn, map_list_sum, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cr,r⟩ _
  simp only [Function.comp_apply, map_smul]
  let z := α.toHom g * r.element * β.toHom x
  change cr • last (ev (second d f α β γ ts) (Finsupp.single (middleBasis α β d z) 1)) = _
  rw [secondColumn, map_list_sum]
  rw [show cr • (List.map _ ts).sum = _ from map_list_sum (DistribSMul.toAddMonoidHom _ cr) _]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨ct,t⟩ _
  change cr • last (ct • Finsupp.single (middleBasis α γ f (z * t.element)) 1) = _
  rw [map_smul, smul_smul]
  change (cr * ct) • ev (third c e f α γ _) (Finsupp.single (middleBasis α γ f (z * t.element)) 1) = _
  rw [thirdColumn]
  rw [show (cr * ct) • (List.map _ ss).sum = _ from map_list_sum (DistribSMul.toAddMonoidHom _ (cr * ct)) _]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cs,s⟩ _
  exact smul_smul (cr * ct) cs _

end CaseFiveLeftShapeEvaluationAux
