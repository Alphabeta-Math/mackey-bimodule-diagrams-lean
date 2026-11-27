import Rigidity
import Mathlib.GroupTheory.SemidirectProduct
import Proofs.EvaluationForTwoProjections

namespace CaseOneExample
open MackeyDiagrams

-- The Cases 1 and 2 figure gives the three ordered positions in the right template.
theorem right_fiber_code : (
let caseOne := fun {U : Type} [Group U] (G C D : Subgroup U) (hCG : C ≤ G) =>
  let A : Subgroup U := ⊤
  let F : Subgroup U := D
  let E : Subgroup U := ⊥
  let inclusion := fun {H K : Subgroup U} (h : H ≤ K) =>
    (⟨Subgroup.inclusion h, ⟨1, fun _ => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := inclusion le_top
  let b : MackeyDiagrams.ConjEmbedding D A := inclusion le_top
  let c : MackeyDiagrams.ConjEmbedding F D := MackeyDiagrams.ConjEmbedding.id D
  let d : MackeyDiagrams.ConjEmbedding C G := inclusion hCG
  let e : MackeyDiagrams.ConjEmbedding E C := inclusion bot_le
  let f : MackeyDiagrams.ConjEmbedding E F := inclusion bot_le
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
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
  ∀ drawing : RightAtBoundary,
    PlanarCode.encode drawing.diagram.erase.geometry =
      [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]

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
  dsimp only
  intro drawing
  apply right_code_eq
  exact congrArg PlanarShape.wiring drawing.shape_eq

end CaseOneExample
