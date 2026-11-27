import MackeyDiagrams.IndexedDrawing
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic

def endpoint : Prop :=
  let U := Multiplicative (ZMod 2)
  let T : Subgroup U := ⊥
  let H : Subgroup U := ⊤
  let pack := fun x : U => (⟨x, Subgroup.mem_top x⟩ : H)
  let g := pack (Multiplicative.ofAdd (1 : ZMod 2))
  let unitEmbedding := MackeyDiagrams.ConjEmbedding.id T
  let inclusion : MackeyDiagrams.ConjEmbedding T H :=
    ⟨Subgroup.inclusion (show T ≤ H from bot_le), ⟨1, fun _ => by simp⟩⟩
  let a := unitEmbedding
  let b := inclusion
  let d := inclusion
  let c := unitEmbedding
  let e := inclusion
  let f := inclusion
  let i := unitEmbedding
  let j := unitEmbedding
  let k := unitEmbedding
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bottom := tensor (up a) (tensor (down b) (up d))
  let top := tensor (up c) (tensor (down e) (up f))
  let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let beside := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let straight := fun {K J : Subgroup U} (p : MackeyDiagrams.Word K J) =>
    ordinary (MackeyDiagrams.Diagram.id p)
  let onLeft := fun {K J J' L M : Subgroup U}
      {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
      {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
      (w : MackeyDiagrams.Word L M)
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
    stack (ordinary (MackeyDiagrams.Diagram.unassociate p q w))
      (stack (beside crossing (straight w)) (ordinary (MackeyDiagrams.Diagram.associate p' q' w)))
  let left := fun {B : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding T B) (β γ : MackeyDiagrams.ConjEmbedding H B)
      (r : List (Complex × MackeyDiagrams.Dot (comp α a) (comp β b)))
      (t : List (Complex × MackeyDiagrams.Dot (comp β d) (comp γ f)))
      (s : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)) =>
    (stack
      (onLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication α β a b r))
      (stack (beside (straight (down α)) (MackeyDiagrams.LabelledDrawing.parallelUp β d γ f t))
        (onLeft (up f) (MackeyDiagrams.LabelledDrawing.compactProjection α γ c e s))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let IsLeft := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    ∃ (B : Subgroup U) (α : MackeyDiagrams.ConjEmbedding T B)
      (β γ : MackeyDiagrams.ConjEmbedding H B)
      (r : List (Complex × MackeyDiagrams.Dot (comp α a) (comp β b)))
      (t : List (Complex × MackeyDiagrams.Dot (comp β d) (comp γ f)))
      (s : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)),
      drawing = left α β γ r t s
  let right := fun (r : MackeyDiagrams.ProjectionDot.Mixed b d i j)
      (t : MackeyDiagrams.Dot (comp a i) (comp c k))
      (s : MackeyDiagrams.Dot (comp e k) (comp f j)) =>
    (stack (beside (straight (up a)) (MackeyDiagrams.LabelledDrawing.compactProjection b d i j [(1, r)]))
      (stack (onLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i c k [(1, t)]))
        (beside (straight (up c)) (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j [(1, s)]))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let input := fun x : H => Finsupp.single
    (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor (down b) (up d))) 1
      (MackeyDiagrams.Generator.mixedPair b d x)) (1 : Complex)
  let output := fun x : H => Finsupp.single
    (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
      (MackeyDiagrams.Word.basis (tensor (down e) (up f))) 1
      (MackeyDiagrams.Generator.mixedPair e f x)) (1 : Complex)
  let evaluate := fun {p q : MackeyDiagrams.Word T T}
      (drawing : MackeyDiagrams.LabelledDrawing Complex p q) =>
    MackeyDiagrams.Biset.Hom.toLinearMap
      (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
  let translate := fun (a₀ : MackeyDiagrams.ConjEmbedding T T)
      (b₀ d₀ : MackeyDiagrams.ConjEmbedding T H) =>
    let dot : MackeyDiagrams.Dot d₀ d₀ := ⟨g, fun x => mul_comm (hom d₀ x) g⟩
    evaluate (beside (straight (up a₀))
      (beside (straight (down b₀)) (MackeyDiagrams.LabelledDrawing.upDot [(1, dot)])))
  let translationIn := translate a b d
  let translationOut := translate c e f
  let Summand := Complex × MackeyDiagrams.LabelledDrawing Complex bottom top
  let sumLeft := fun (terms : List Summand) =>
    (⟨Finset.univ, fun i : Fin terms.length =>
      MackeyDiagrams.LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩ :
      MackeyDiagrams.IndexedDrawing Complex bottom top (Fin terms.length))
  (0 < Subgroup.index (MonoidHom.range (hom e)) ∧ Subgroup.index (MonoidHom.range (hom e)) ≤ 2) ∧
  (0 < Subgroup.index (MonoidHom.range (hom j)) ∧ Subgroup.index (MonoidHom.range (hom j)) ≤ 2) ∧
  (∀ (B : Subgroup U) (α : MackeyDiagrams.ConjEmbedding T B)
      (β γ : MackeyDiagrams.ConjEmbedding H B),
    B = H ∧
    (∀ x : H, (hom β x : U) = (x : U) ∧ (hom γ x : U) = (x : U)) ∧
    (∀ (r : MackeyDiagrams.Dot (comp α a) (comp β b))
        (t : MackeyDiagrams.Dot (comp β d) (comp γ f))
        (s : MackeyDiagrams.ProjectionDot.Mixed α γ c e) (x : H),
      evaluate (left α β γ [(1, r)] [(1, t)] [(1, s)]) (input x) =
        output ((pack (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot s) : U))⁻¹ *
          pack (MackeyDiagrams.Dot.element r : U) * x * pack (MackeyDiagrams.Dot.element t : U)))) ∧
  ∃ (r : MackeyDiagrams.ProjectionDot.Mixed b d i j)
      (t : MackeyDiagrams.Dot (comp a i) (comp c k))
      (s : MackeyDiagrams.Dot (comp e k) (comp f j)),
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot r) = 1 ∧
    MackeyDiagrams.Dot.element t = 1 ∧ MackeyDiagrams.Dot.element s = 1 ∧
    let R := evaluate (right r t s)
    R (input 1) = output 1 ∧ R (input g) = 0 ∧
    translationOut (R (input 1)) = output g ∧
    LinearMap.comp R translationIn ≠ LinearMap.comp translationOut R ∧
    (∀ (terms : List Summand), (∀ term ∈ terms, IsLeft term.2) →
      LinearMap.comp ((sumLeft terms).eval) translationIn =
        LinearMap.comp translationOut ((sumLeft terms).eval)) ∧
    (∀ (terms : List Summand), (∀ term ∈ terms, IsLeft term.2) → (sumLeft terms).eval ≠ R)
