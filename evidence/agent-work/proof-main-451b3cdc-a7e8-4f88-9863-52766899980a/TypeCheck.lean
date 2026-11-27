import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.FiniteParabolicJoinOfFamily

def endpoint : Prop :=
let P := Equiv.Perm Nat
let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let F : Subgroup U := ⊥
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H =
      iSup (fun i => MonoidHom.range
        (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ blocks i)))
∀ {G A D C E : Subgroup U},
  parabolic G → parabolic A → parabolic D → parabolic C → parabolic E →
  ∀ (GE : Subgroup U),
    (GE : Set U) = Set.image2 (fun g e : U => g * e) (G : Set U) (E : Set U) →
    ∀ (hA : D ⊓ GE = A) (hC : G ⊓ E = C) (hAG : A ≤ G),
  let B := (G ⊔ D) ⊔ E
  let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
    (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
  let a := incl hAG
  let b := incl (show A ≤ D by rw [← hA]; exact inf_le_left)
  let d := incl (show F ≤ D from bot_le)
  let c := incl (show C ≤ G by rw [← hC]; exact inf_le_left)
  let e := incl (show C ≤ E by rw [← hC]; exact inf_le_right)
  let f := incl (show F ≤ E from bot_le)
  let u := incl (show G ≤ B from le_trans le_sup_left le_sup_left)
  let v := incl (show D ≤ B from le_trans le_sup_right le_sup_left)
  let w := incl (show E ≤ B from le_sup_right)
  let i := incl (show F ≤ A from bot_le)
  let j := MackeyDiagrams.ConjEmbedding.id F
  let k := incl (show F ≤ C from bot_le)
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    ordinary (MackeyDiagrams.Diagram.id p)
  let bottom := tensor (up a) (tensor (down b) (up d))
  let top := tensor (up c) (tensor (down e) (up f))
  let atLeft := fun {K J J' L M : Subgroup U}
      {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
      {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
      (tail : MackeyDiagrams.Word L M)
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
    stack (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
      (stack (juxtapose crossing (drawId tail))
        (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
  let finiteFibers := fun {H K L M : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K M) (β : MackeyDiagrams.ConjEmbedding L M)
      (γ : MackeyDiagrams.ConjEmbedding H K) (δ : MackeyDiagrams.ConjEmbedding H L)
      (dot : MackeyDiagrams.Dot (comp α γ) (comp β δ)) =>
    ∀ z, Set.Finite {y | MackeyDiagrams.Generator.mixedMultiplicationBasis α β γ δ dot y = z}
  let lowerOne : MackeyDiagrams.Dot (comp u a) (comp v b) :=
    ⟨1, fun x => by simpa only [mul_one, one_mul] using
      (show MackeyDiagrams.ConjEmbedding.toHom (comp u a) x =
        MackeyDiagrams.ConjEmbedding.toHom (comp v b) x from rfl)⟩
  let upperOne : MackeyDiagrams.Dot (comp u c) (comp w e) :=
    ⟨1, fun x => by simpa only [mul_one, one_mul] using
      (show MackeyDiagrams.ConjEmbedding.toHom (comp u c) x =
        MackeyDiagrams.ConjEmbedding.toHom (comp w e) x from rfl)⟩
  let RightLower := MackeyDiagrams.Dot (comp b i) (comp d j)
  let RightMiddle := MackeyDiagrams.Dot (comp a i) (comp c k)
  let RightUpper := MackeyDiagrams.Dot (comp e k) (comp f j)
  let LeftMiddle := MackeyDiagrams.Dot (comp v d) (comp w f)
  let middleDot := fun (r : RightLower) (t : RightMiddle) (s : RightUpper) =>
    let z := (MackeyDiagrams.ConjEmbedding.toHom v (MackeyDiagrams.Dot.element r))⁻¹ *
      MackeyDiagrams.ConjEmbedding.toHom u (MackeyDiagrams.Dot.element t) *
      MackeyDiagrams.ConjEmbedding.toHom w (MackeyDiagrams.Dot.element s)
    (⟨z, fun x => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.property)
      simp [hx]⟩ : LeftMiddle)
  ∃ (hLeft : finiteFibers u w c e upperOne)
    (hRight : ∀ r : RightLower, finiteFibers b d i j r),
  let leftDrawing := fun (middle : List (Complex × LeftMiddle)) =>
    (stack
      (atLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b [(1, lowerOne)]))
      (stack (juxtapose (drawId (down u)) (MackeyDiagrams.LabelledDrawing.parallelUp v d w f middle))
        (atLeft (up f) (MackeyDiagrams.LabelledDrawing.compactProjection u w c e
          [(1, ⟨upperOne, hLeft⟩)]))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let rightDrawing := fun
      (lower : List (Complex × MackeyDiagrams.ProjectionDot.Mixed b d i j))
      (middle : List (Complex × RightMiddle)) (upper : List (Complex × RightUpper)) =>
    (stack
      (juxtapose (drawId (up a)) (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
      (stack (atLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i c k middle))
        (juxtapose (drawId (up c)) (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j upper))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let rightProjectionTerm := fun (r : RightLower) =>
    (⟨r, hRight r⟩ : MackeyDiagrams.ProjectionDot.Mixed b d i j)
  let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  parabolic B ∧
    (∀ (r : RightLower) (t : RightMiddle) (s : RightUpper),
      evaluate (leftDrawing [(1, middleDot r t s)]) =
        evaluate (rightDrawing [(1, rightProjectionTerm r)] [(1, t)] [(1, s)])) ∧
    (∀ (rs : MackeyDiagrams.DotLabel Complex (comp b i) (comp d j))
        (ts : MackeyDiagrams.DotLabel Complex (comp a i) (comp c k))
        (ss : MackeyDiagrams.DotLabel Complex (comp e k) (comp f j)),
      let middleLabel : MackeyDiagrams.DotLabel Complex (comp v d) (comp w f) :=
        Finsupp.sum rs (fun r cr =>
          Finsupp.sum ts (fun t ct =>
            Finsupp.sum ss (fun s cs => Finsupp.single (middleDot r t s) (cr * ct * cs))))
      let lowerTerms := List.map (fun (term : Complex × RightLower) =>
        (Prod.fst term, rightProjectionTerm (Prod.snd term))) (MackeyDiagrams.DotLabel.terms rs)
      evaluate (leftDrawing (MackeyDiagrams.DotLabel.terms middleLabel)) =
        evaluate (rightDrawing lowerTerms (MackeyDiagrams.DotLabel.terms ts)
          (MackeyDiagrams.DotLabel.terms ss)))
