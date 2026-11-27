import Arithmetic

namespace CaseOneExample
open MackeyDiagrams

noncomputable section

-- Lemma 6.3: the public evaluation theorem hides the particular parameter
-- behind an existential. Connect to its checked backward-coordinate formula
-- to identify that parameter at the three unit labels of Xiao's Example 6.2.
-- This is the same checked adapter pattern used by the registered Case 1 supplier.
open Lean Elab Tactic in
private abbrev pullsLeft := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "pulls_left"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev pullsMixed := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "pulls_mixed"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev leftDotFormula := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "leftDot"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev singletonMixed := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "singleton_mixed"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

private theorem product_inclusion_injective :
    Function.Injective (fun gh : G × D => a.toHom gh.1 * b.toHom gh.2) := by
  intro gh gh' he
  exact product_injective (congrArg Subtype.val he)

private theorem product_trivial_injective :
    Function.Injective (fun gh : E × D => s.toHom gh.1 * c.toHom gh.2) := by
  intro gh gh' he
  have h₁ : gh.1 = gh'.1 := Subsingleton.elim _ _
  have h₂ : gh'.1 = 1 := Subsingleton.elim _ _
  change s.toHom gh.1 * c.toHom gh.2 = s.toHom gh'.1 * c.toHom gh'.2 at he
  rw [h₁, h₂, map_one, one_mul, one_mul] at he
  exact Prod.ext h₁ (c.injective he)

def leftX : ProjectionDot.Mixed a b r s := unitProjection a b r s product_inclusion_injective
def leftY : ProjectionDot.Mixed s c t f := unitProjection s c t f product_trivial_injective
def leftZ : Dot (r.comp t) (d.comp e) := unitDot _ _
def leftP : ProjectionDot.Mixed a (b.comp c) (d.comp e) f :=
  unitProjection _ _ _ _ product_inclusion_injective

theorem left_columns (g : G) (h : D) :
    (LabelledDrawing.compactProjection (R := Complex) a (b.comp c) (d.comp e) f [(1, leftP)]).interpret.eval.toLinearMap
      (Finsupp.single (Generator.mixedPair a (b.comp c) (a.toHom g * (b.comp c).toHom h)) 1) =
    Finsupp.single ((Biset.induction (d.comp e)).pair (Biset.restriction f) g h) 1 :=
  (LinearMap.congr_fun (singletonMixed a (b.comp c) (d.comp e) f leftP)
    (Finsupp.single (Generator.mixedPair a (b.comp c) (a.toHom g * (b.comp c).toHom h)) 1)).trans
    (unitProjection_column a (b.comp c) (d.comp e) f product_inclusion_injective g h)

-- The archived PDF puts the example on p. 24. The 28 November PDF puts it on p. 26.
theorem left_eval :
  let G := CaseOneExample.G
  let C := CaseOneExample.C
  let D := CaseOneExample.D
  let hCG := C_le_G
  let A : Subgroup CaseOneExample.U := ⊤
  let F : Subgroup CaseOneExample.U := D
  let B : Subgroup CaseOneExample.U := ⊥
  let E : Subgroup CaseOneExample.U := B
  let inclusion := fun {H K : Subgroup CaseOneExample.U} (h : H ≤ K) =>
    (⟨Subgroup.inclusion h, ⟨1, fun _ => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := inclusion le_top
  let b : MackeyDiagrams.ConjEmbedding D A := inclusion le_top
  let c : MackeyDiagrams.ConjEmbedding F D := MackeyDiagrams.ConjEmbedding.id D
  let d : MackeyDiagrams.ConjEmbedding C G := inclusion hCG
  let e : MackeyDiagrams.ConjEmbedding E C := inclusion bot_le
  let f : MackeyDiagrams.ConjEmbedding E F := inclusion bot_le
  let r : MackeyDiagrams.ConjEmbedding B G := inclusion bot_le
  let s : MackeyDiagrams.ConjEmbedding B D := inclusion bot_le
  let t : MackeyDiagrams.ConjEmbedding E B := MackeyDiagrams.ConjEmbedding.id B
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let _hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let de := comp d e
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let drawId := fun {K H : Subgroup CaseOneExample.U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let mergedEval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup CaseOneExample.U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let left := fun (x : MackeyDiagrams.ProjectionDot.Mixed a b r s)
      (y : MackeyDiagrams.ProjectionDot.Mixed s c t f)
      (z : MackeyDiagrams.Dot (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s [(1, x)]) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f [(1, y)]))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e [(1, z)]) (drawId (down f))))
  mergedEval (left leftX leftY leftZ) =
    (LabelledDrawing.compactProjection (R := Complex) a bc de f [(1, leftP)]).interpret.eval.toLinearMap := by
  classical
  dsimp only
  apply Eq.trans _ (singletonMixed a (b.comp c) (d.comp e) f leftP).symm
  have he : leftDotFormula a b c d e f leftX leftY leftZ = leftP.dot := by
    apply Dot.ext
    change a.toHom (1 : G)⁻¹ * (1 : A) * b.toHom (1 : D) = 1
    simp only [inv_one, map_one, one_mul]
  apply LinearMap.ext
  intro input
  apply Finsupp.ext
  intro output
  refine Quotient.inductionOn output (fun ⟨g,h⟩ => ?_)
  have hleft := pullsLeft a b c d e f leftX leftY leftZ g h
  have hright := pullsMixed a (b.comp c) (d.comp e) f leftP ((Biset.induction (d.comp e)).pair (Biset.restriction f) g h)
  have hcoords := congrArg (fun p =>
    input (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p
      ((Biset.induction (d.comp e)).pair (Biset.restriction f) g h))) he
  exact ((hleft input).trans hcoords).trans (hright input).symm

end
end CaseOneExample
