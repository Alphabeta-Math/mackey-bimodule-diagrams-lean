import Left
import Middle
import Rigidity
import BoundaryZero

namespace CaseOneExample
open MackeyDiagrams


theorem frame_zero {V : Type*} [Group V] {K H : Subgroup V}
    {p q r s : Word K H}
    (before : LabelledDrawing Complex p q) (middle : LabelledDrawing Complex q r)
    (after : LabelledDrawing Complex r s)
    (h : middle.interpret.eval.toLinearMap = 0) :
    (before.vertical (middle.vertical after)).interpret.eval.toLinearMap = 0 := by
  change after.interpret.eval.toLinearMap.comp
    (middle.interpret.eval.toLinearMap.comp before.interpret.eval.toLinearMap) = 0
  rw [h]
  simp

theorem caseOne_when_right_zero : (
let caseOne := fun {U : Type} [Group U] (G C D : Subgroup U) (hCG : C ≤ G) =>
  let A : Subgroup U := ⊤
  let F : Subgroup U := D
  let B : Subgroup U := ⊥
  let E : Subgroup U := B
  let inclusion := fun {H K : Subgroup U} (h : H ≤ K) =>
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
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
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
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
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
  let j := MackeyDiagrams.ConjEmbedding.id A
  let rightTemplate : MackeyDiagrams.LabelledDrawing Complex bottom top :=
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c j bc []))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d ad []) (drawId (up bc)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection ad bc e f [])))
  let rightShape := MackeyDiagrams.LabelledDrawing.planarShape rightTemplate
  let RightAtBoundary := MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex
    (MackeyDiagrams.Word.boundary bottom) (MackeyDiagrams.Word.boundary top) rightShape
  let P₁ : Subgroup A := MonoidHom.range (hom ad) ⊔ MonoidHom.range (hom bc)
  (∀ drawing : RightAtBoundary,
    (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret drawing).eval.toLinearMap = 0) →
  Subgroup.index (MonoidHom.range (hom s)) = 2 ∧
  Subgroup.index (MonoidHom.range (hom f)) = 2 ∧
  P₁ = ⊤ ∧
  Subgroup.relIndex (MonoidHom.range (hom ad)) (MonoidHom.range (hom a) ⊓ P₁) =
    Subgroup.relIndex C G ∧
  ¬ Subgroup.FiniteIndex (Subgroup.subgroupOf C G) ∧
  ¬ Subgroup.FiniteIndex
    (Subgroup.subgroupOf (MonoidHom.range (hom ad)) (MonoidHom.range (hom a) ⊓ P₁)) ∧
  (∃ (x : MackeyDiagrams.ProjectionDot.Mixed a b r s)
    (y : MackeyDiagrams.ProjectionDot.Mixed s c t f)
    (z : MackeyDiagrams.Dot (comp r t) de) (p : MackeyDiagrams.ProjectionDot.Mixed a bc de f),
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot x) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot y) = 1 ∧
    MackeyDiagrams.Dot.element z = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p) = 1 ∧
    mergedEval (left x y z) =
      MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
        (MackeyDiagrams.LabelledDrawing.interpret
          (MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex) a bc de f [(1, p)]))) ∧
    (∀ (g : G) (h : F),
      mergedEval (left x y z)
        (Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc (hom a g * hom bc h)) 1) =
      Finsupp.single (MackeyDiagrams.Biset.pair
        (MackeyDiagrams.Biset.induction de) (MackeyDiagrams.Biset.restriction f) g h) 1) ∧
    ¬ (∃ ds : List RightAtBoundary,
      List.sum (List.map (fun drawing => MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret drawing))) ds) =
      MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
        (MackeyDiagrams.ScopedDiagram.atBoundary
          (MackeyDiagrams.LabelledDrawing.interpret (left x y z))))))
let N := Fin 2 → Multiplicative Int
let swaps : Equiv.Perm (Fin 2) →* MulAut N :=
  { toFun := fun σ =>
      { toFun := fun x i => x (Equiv.symm σ i)
        invFun := fun x i => x (σ i)
        left_inv := fun x => funext fun i => congrArg x (Equiv.symm_apply_apply σ i)
        right_inv := fun x => funext fun i => congrArg x (Equiv.apply_symm_apply σ i)
        map_mul' := fun _ _ => rfl }
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
let U := SemidirectProduct N (Equiv.Perm (Fin 2)) swaps
let base : N →* U := SemidirectProduct.inl
let permutations : Equiv.Perm (Fin 2) →* U := SemidirectProduct.inr
let G := MonoidHom.range base
let C := Subgroup.map base (MonoidHom.ker (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative Int) 1))
let D := MonoidHom.range permutations
caseOne G C D (by
  intro u hu
  obtain ⟨n, _, rfl⟩ := hu
  exact ⟨n, rfl⟩)
) := by
  classical
  dsimp only
  intro hzero
  refine ⟨cup_index.1, cup_index.2, top_join, formula_relIndex, infinite_index,
    not_finite_formula, leftX, leftY, leftZ, leftP, rfl, rfl, rfl, rfl, left_eval, ?_, ?_⟩
  · intro g h
    exact (LinearMap.congr_fun left_eval _).trans (left_columns g h)
  · apply no_sum_zero _ hzero
    intro he
    have hleft := (boundary_zero_iff _).mp he

    have hz := left_eval.symm.trans (frame_zero _ _ _ hleft)
    have hcol := left_columns 1 1
    have hn := (LinearMap.congr_fun hz _).symm.trans hcol
    exact (Finsupp.single_ne_zero.mpr one_ne_zero) hn.symm

end CaseOneExample

#print axioms CaseOneExample.caseOne_when_right_zero
#print axioms CaseOneExample.right_code_eq
#print axioms CaseOneExample.middle_projection_empty
