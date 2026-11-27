import Mathlib.Basic.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.SemidirectProduct
import MackeyDiagrams.PlanarShape

open scoped Classical
private theorem encodeAdd {U : Type} [Group U] {K H : Subgroup U}
    {p q : MackeyDiagrams.Word K H} (d e : MackeyDiagrams.LabelledDrawing Complex p q) :
    MackeyDiagrams.PlanarCode.encode (d.add e).erase.geometry =
      [.add 0 d.erase.geometry.inputs d.erase.geometry.outputs
        (MackeyDiagrams.PlanarCode.encode d.erase.geometry)
        (MackeyDiagrams.PlanarCode.encode e.erase.geometry)] := rfl

noncomputable def reviewedWiring : True :=
  let swap : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
  let action : Multiplicative (ZMod 2) →* MulAut (Multiplicative Int × Multiplicative Int) :=
    let act := fun i : Multiplicative (ZMod 2) =>
      if i = 1 then 1 else (MulEquiv.prodComm : MulAut (Multiplicative Int × Multiplicative Int))
    { toFun := act
      map_one' := ite_eq_left rfl
      map_mul' := by
        have cases₂ : ∀ i : Multiplicative (ZMod 2), i = 1 ∨ i = swap := by
          intro i
          change (Multiplicative.toAdd i : Fin 2) = 0 ∨ Multiplicative.toAdd i = (1 : ZMod 2)
          exact (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) (Multiplicative.toAdd i)
        have hs : swap * swap = 1 := by decide
        have hn : swap ≠ 1 := by decide
        intro i j
        rcases cases₂ i with rfl | rfl <;> rcases cases₂ j with rfl | rfl <;>
          simp only [act, one_mul, mul_one, hs, ite_eq_left rfl, ite_eq_right hn]
        rfl }
  let U := SemidirectProduct (Multiplicative Int × Multiplicative Int) (Multiplicative (ZMod 2)) action
  let A : Subgroup U := ⊤
  let G : Subgroup U := MonoidHom.range (MonoidHom.comp
    (SemidirectProduct.inl (φ := action))
    (MonoidHom.inl (Multiplicative Int) (Multiplicative Int)))
  let D := G
  let T : Subgroup U := ⊥
  let C := T
  let E := T
  let F := T
  let B' := T
  let τ : A := ⟨SemidirectProduct.inr (φ := action) swap, Subgroup.mem_top _⟩
  let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
    ({ toHom := Subgroup.inclusion h
       hasRepresentative := ⟨1, fun _ => by simp⟩ } : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := incl le_top
  let b : MackeyDiagrams.ConjEmbedding D A := incl le_top
  let c : MackeyDiagrams.ConjEmbedding F D := incl bot_le
  let d : MackeyDiagrams.ConjEmbedding C G := incl bot_le
  let e : MackeyDiagrams.ConjEmbedding E C := incl le_rfl
  let f : MackeyDiagrams.ConjEmbedding E F := incl le_rfl
  let u : MackeyDiagrams.ConjEmbedding B' A := incl bot_le
  let v : MackeyDiagrams.ConjEmbedding C B' := incl le_rfl
  let w : MackeyDiagrams.ConjEmbedding F B' := incl le_rfl
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
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
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
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
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let terms := fun {X : Type} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let Qstar := fun (p : ProjectionLabel a bc de f) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s (terms xs)) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f (terms ys)))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e (MackeyDiagrams.DotLabel.terms zs))
          (drawId (down f))))
  let right := fun
      (ells : MackeyDiagrams.DotLabel Complex bc (comp u w))
      (ms : Finsupp (ProjectionLabel a u d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c u w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a u d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))

  let code := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.PlanarCode.encode drawing.erase.geometry
  let lcode : MackeyDiagrams.PlanarCode.Code :=
    [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp]
  let rcode : MackeyDiagrams.PlanarCode.Code :=
    [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]
  have leftWiring {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de) :
      code (left r s t xs ys zs) = lcode := rfl
  have rightWiring (ells : MackeyDiagrams.DotLabel Complex bc (comp u w))
      (ms : Finsupp (ProjectionLabel a u d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) :
      code (right ells ms ns) = rcode := rfl
  have addScope {B₁ B₂ : Subgroup U}
      (r₁ : MackeyDiagrams.ConjEmbedding B₁ G) (r₂ : MackeyDiagrams.ConjEmbedding B₂ G)
      (s₁ : MackeyDiagrams.ConjEmbedding B₁ D) (s₂ : MackeyDiagrams.ConjEmbedding B₂ D)
      (t₁ : MackeyDiagrams.ConjEmbedding E B₁) (t₂ : MackeyDiagrams.ConjEmbedding E B₂)
      (xs₁ : Finsupp (ProjectionLabel a b r₁ s₁) Complex)
      (xs₂ : Finsupp (ProjectionLabel a b r₂ s₂) Complex)
      (ys₁ : Finsupp (ProjectionLabel s₁ c t₁ f) Complex)
      (ys₂ : Finsupp (ProjectionLabel s₂ c t₂ f) Complex)
      (zs₁ : MackeyDiagrams.DotLabel Complex (comp r₁ t₁) de)
      (zs₂ : MackeyDiagrams.DotLabel Complex (comp r₂ t₂) de) :
      code (MackeyDiagrams.LabelledDrawing.add (left r₁ s₁ t₁ xs₁ ys₁ zs₁)
        (left r₂ s₂ t₂ xs₂ ys₂ zs₂)) =
        [.add 0 [false, true, true] [true, true, false] lcode lcode] := by
    calc
      _ = [.add 0 (left r₁ s₁ t₁ xs₁ ys₁ zs₁).erase.geometry.inputs
            (left r₁ s₁ t₁ xs₁ ys₁ zs₁).erase.geometry.outputs
            (code (left r₁ s₁ t₁ xs₁ ys₁ zs₁))
            (code (left r₂ s₂ t₂ xs₂ ys₂ zs₂))] := encodeAdd _ _
      _ = _ := by
        rw [leftWiring r₁ s₁ t₁ xs₁ ys₁ zs₁, leftWiring r₂ s₂ t₂ xs₂ ys₂ zs₂]
        rfl
  True.intro
