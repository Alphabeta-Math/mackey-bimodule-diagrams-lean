import Proofs.ReidemeisterOne
import Proofs.FiniteParabolicClosure

example : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym : Finset Nat → Subgroup U :=
  fun S => Subgroup.comap (Subgroup.subtype finitary)
    (MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S)))
let blockGroup : Finset (Finset Nat) → Subgroup U :=
  fun P => iSup (fun S : ↥P => blockSym (S : Finset Nat))
let partition : Finset Nat → Finset (Finset Nat) → Prop :=
  fun T P =>
    (∀ S ∈ P, Finset.Nonempty S) ∧
    (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
    (∀ x : Nat, x ∈ T ↔ ∃ S ∈ P, x ∈ S)
let parabolic : Subgroup U → Prop :=
  fun L => ∃ T P, partition T P ∧ L = blockGroup P
let merge : Finset (Finset Nat) → Finset Nat → Finset Nat → Finset (Finset Nat) :=
  fun P A B => insert (A ∪ B) (Finset.erase (Finset.erase P A) B)
let inclusion : ∀ {A B : Subgroup U}, A ≤ B → MackeyDiagrams.ConjEmbedding A B :=
  fun h => ⟨Subgroup.inclusion h, ⟨1, fun x => by
    simp only [Subgroup.coe_inclusion, one_mul, inv_one, mul_one]⟩⟩
let curlPair : ∀ {A B : Subgroup U}, MackeyDiagrams.ConjEmbedding A B → Type :=
  fun a =>
    MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up a) ×
    MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.down a) (MackeyDiagrams.Word.down a)
let straightPair : ∀ {A B : Subgroup U} (a : MackeyDiagrams.ConjEmbedding A B), curlPair a :=
  fun a =>
    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up a)),
     MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down a)))
let indexedCurls :
    ∀ {A B C : Subgroup U} (a : MackeyDiagrams.ConjEmbedding B C)
      (d : MackeyDiagrams.ConjEmbedding A B),
      Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)) →
      Option (curlPair (MackeyDiagrams.ConjEmbedding.comp a d)) → curlPair a :=
  fun a d finite inner =>
    let openRight := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.upToUpDown a d finite)
    let closeRight := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.upDownToUp a d)
    let openLeft := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.downToUpDown a d finite)
    let closeLeft := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.upDownToDown a d)
    let rightUp := MackeyDiagrams.LabelledDrawing.vertical openRight
      (Option.elim inner closeRight (fun p =>
        MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal (Prod.fst p) (Prod.snd (straightPair d)))
          closeRight))
    let leftDown := MackeyDiagrams.LabelledDrawing.vertical openLeft
      (Option.elim inner closeLeft (fun p =>
        MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal (Prod.fst (straightPair d)) (Prod.snd p))
          closeLeft))
    (rightUp, leftDown)
let rightDownCurl :
    ∀ {A B C : Subgroup U} (a : MackeyDiagrams.ConjEmbedding B C)
      (d : MackeyDiagrams.ConjEmbedding A B),
      MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.down d) (MackeyDiagrams.Word.down d) :=
  fun a d =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.downToDownUp a d))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.downUpToDown a d))
let leftUpCurl :
    ∀ {A B C : Subgroup U} (a : MackeyDiagrams.ConjEmbedding B C)
      (d : MackeyDiagrams.ConjEmbedding A B),
      MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.up d) (MackeyDiagrams.Word.up d) :=
  fun a d =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.upToDownUp a d))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.downUpToUp a d))
let nestedCurls :
    ∀ (n : Nat) (L : Nat → Subgroup U)
      (h : ∀ i, i < n → L i ≤ L (i + 1)),
      (∀ i (hi : i < n), Subgroup.FiniteIndex
        (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (inclusion (h i hi))))) →
      ∀ t, t ≤ n → ∀ {D : Subgroup U} (a : MackeyDiagrams.ConjEmbedding (L t) D), curlPair a :=
  fun n L h finite =>
    Nat.rec
      (motive := fun t => t ≤ n → ∀ {D : Subgroup U}
        (a : MackeyDiagrams.ConjEmbedding (L t) D), curlPair a)
      (fun _ {_} a => straightPair a)
      (fun i prev hi {_} a =>
        let e := inclusion (h i hi)
        indexedCurls a e (finite i hi) (Option.some
          (prev (Nat.le_of_succ_le hi) (MackeyDiagrams.ConjEmbedding.comp a e))))
let atBoundary :
    ∀ {B H G : Subgroup U}, B = H → ∀ a : MackeyDiagrams.ConjEmbedding H G,
      (∀ b : MackeyDiagrams.ConjEmbedding B G, curlPair b) → curlPair a :=
  fun {B H G} h a f =>
    Eq.rec (motive := fun J _ => ∀ b : MackeyDiagrams.ConjEmbedding J G, curlPair b) f h a
let path : Finset (Finset Nat) → Finset (Finset Nat) → Nat →
    (Nat → Finset (Finset Nat)) → (Nat → Finset Nat) → (Nat → Finset Nat) → Prop :=
  fun Y X n P A B =>
    P 0 = Y ∧ P n = X ∧
    ∀ i, i < n →
      A i ∈ P i ∧ B i ∈ P i ∧ A i ≠ B i ∧ P (i + 1) = merge (P i) (A i) (B i)
(∀ (T : Finset Nat) (P : Finset (Finset Nat)) (A B : Finset Nat),
    partition T P → A ∈ P → B ∈ P → A ≠ B →
    let merged := blockGroup (merge P A B)
    blockGroup P ≤ merged ∧
    Subgroup.relIndex (blockGroup P) merged =
      Nat.choose (Finset.card A + Finset.card B) (Finset.card A)) ∧
(∀ (K H G : Subgroup U) (δ α : U)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  parabolic K → parabolic G →
  ∀ (T : Finset Nat) (X Y : Finset (Finset Nat)),
  partition T X → partition T Y →
  ∀ (hH : H = blockGroup X),
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)
  blockGroup Y = Subgroup.map (Subgroup.subtype H) S →
  ∃ finite : Subgroup.FiniteIndex S,
    let index := Subgroup.index S
    let direct := indexedCurls a d finite Option.none
    let straight := straightPair a
    (index : Rat) =
      Finset.prod X (fun V =>
        (Nat.factorial (Finset.card V) : Rat) /
          Finset.prod (Finset.filter (fun W => W ⊆ V) Y)
            (fun W => (Nat.factorial (Finset.card W) : Rat))) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.fst direct)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret
        (MackeyDiagrams.LabelledDrawing.scale (index : Complex) (Prod.fst straight))) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (rightDownCurl a d)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.snd (straightPair d))) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (leftUpCurl a d)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.fst (straightPair d))) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.snd direct)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret
        (MackeyDiagrams.LabelledDrawing.scale (index : Complex) (Prod.snd straight))) ∧
    (∃ n P A B, path Y X n P A B) ∧
    (∀ n P A B (hPath : path Y X n P A B),
      let L := fun i => blockGroup (P i)
      (∀ i, i ≤ n → partition T (P i)) ∧
      Finset.prod (Finset.range n) (fun i =>
        Nat.choose (Finset.card (A i) + Finset.card (B i)) (Finset.card (A i))) = index ∧
      ∃ (h : ∀ i, i < n → L i ≤ L (i + 1))
        (f : ∀ i (hi : i < n), Subgroup.FiniteIndex
          (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (inclusion (h i hi))))),
        let hEnd : L n = H := Eq.trans (congrArg blockGroup hPath.2.1) hH.symm
        let nested := atBoundary hEnd a
          (fun b => nestedCurls n L h f n (Nat.le_refl n) b)
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.fst direct)) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.fst nested)) ∧
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.snd direct)) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (Prod.snd nested))))
) → True := fun _ => True.intro
