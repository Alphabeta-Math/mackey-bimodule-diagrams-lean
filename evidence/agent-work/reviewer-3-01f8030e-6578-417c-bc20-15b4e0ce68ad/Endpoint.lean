import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Group
import MackeyDiagrams.DrawingShape

noncomputable def endpoint : Prop :=
  let U := ↥(Subgroup.closure {g : Equiv.Perm Nat | Equiv.Perm.IsSwap g})
  let blockPerm : Finset Nat → Subgroup (Equiv.Perm Nat) := fun X =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X))
  let parabolic : Subgroup U → Prop := fun S =>
    ∃ (n : Nat) (blocks : Fin n → Finset Nat),
      (∀ i, Finset.Nonempty (blocks i)) ∧
      Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
      Subgroup.map (Subgroup.subtype _) S = iSup (fun i => blockPerm (blocks i))
  let mackey := fun {V : Type} [Group V] (K : Subgroup V) (s : V) =>
    K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) K
  let inclusion := fun {V : Type} [Group V] (S T : Subgroup V) (h : S ≤ T) =>
    show MackeyDiagrams.ConjEmbedding S T from
      ⟨Subgroup.inclusion h, ⟨1, fun x => by
        change (x : V) = 1 * (x : V) * (1 : V)⁻¹
        simp⟩⟩
  let left := fun {V : Type} [Group V] (K : Subgroup V) (s : V)
      (S : Subgroup V) (h : S ≤ mackey K s) =>
    inclusion S K (le_trans h inf_le_left)
  let right := fun {V : Type} [Group V] (K : Subgroup V) (s : V)
      (S : Subgroup V) (h : S ≤ mackey K s) =>
    MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := K) s⁻¹ (by
      intro x
      obtain ⟨k, hk, heq⟩ := (h x.property).2
      change s * k * s⁻¹ = (x : V) at heq
      rw [← heq]
      change k ∈ K at hk
      convert hk using 1
      group)
  let common := fun (K G : Subgroup U) (t : U) =>
    (mackey K 1 ⊓ mackey K t) ⊓ (G ⊓ Subgroup.centralizer ({(1 : U) * t⁻¹} : Set U))
  let admissible := fun (K : Subgroup U) (t : U) (S : Subgroup U) =>
    parabolic S ∧
      ∃ (h₁ : S ≤ mackey K 1) (h₂ : S ≤ mackey K t),
        left K 1 S h₁ = left K t S h₂ ∧ right K 1 S h₁ = right K t S h₂
  let diagramIdentity := fun {V : Type} [Group V] (K G : Subgroup V)
      (hKG : K ≤ G) (s₁ s₂ : G) (L : Subgroup V) (c₁ : Complex)
      (c₂ : Option Complex) =>
    let a := inclusion K G hKG
    let down := MackeyDiagrams.Word.down a
    let up := MackeyDiagrams.Word.up a
    let M := MackeyDiagrams.Word.tensor down up
    let l := fun (s : G) (h : L ≤ mackey K (s : V)) => left K (s : V) L h
    let r := fun (s : G) (h : L ≤ mackey K (s : V)) => right K (s : V) L h
    let dot := fun (s : G) (h : L ≤ mackey K (s : V)) =>
      show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (l s h))
          (MackeyDiagrams.ConjEmbedding.comp a (r s h)) from
        ⟨s, by
          intro x
          apply Subtype.ext
          change (x : V) * (s : V) =
            (s : V) * ((s : V)⁻¹ * (x : V) * ((s : V)⁻¹)⁻¹)
          group⟩
    let finiteFibers := fun (s : G) (h : L ≤ mackey K (s : V)) =>
      ∀ z : (MackeyDiagrams.Word.basis M).carrier,
        Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis
          a a (l s h) (r s h) (dot s h) w = z}
    let outer := fun (s : G) (h : L ≤ mackey K (s : V)) (hf : finiteFibers s h) =>
      show MackeyDiagrams.LabelledDrawing Complex M M from
        MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.compactProjection a a (l s h) (r s h)
            [(1, ⟨dot s h, hf⟩)])
          (MackeyDiagrams.LabelledDrawing.mixedMultiplication a a (l s h) (r s h)
            [(1, dot s h)])
    let straight : MackeyDiagrams.LabelledDrawing Complex M M :=
      MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id down))
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id up))
    ∃ (h₁ : L ≤ mackey K (s₁ : V)) (h₂ : L ≤ mackey K (s₂ : V))
        (hf₁ : finiteFibers s₁ h₁) (hf₂ : finiteFibers s₂ h₂),
      let first := MackeyDiagrams.LabelledDrawing.scale c₁ (outer s₁ h₁ hf₁)
      let second := outer s₂ h₂ hf₂
      let weightedSecond := Option.elim c₂ second
        (fun c => MackeyDiagrams.LabelledDrawing.scale c second)
      straight.interpret.eval =
        (MackeyDiagrams.LabelledDrawing.add first weightedSecond).interpret.eval
  let swap := fun (i j : Nat) =>
    show U from ⟨Equiv.swap i j, by
      by_cases hij : i = j
      · subst j
        rw [Equiv.swap_self]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩
  let blockSym := fun X : Finset Nat =>
    Subgroup.comap (Subgroup.subtype (Subgroup.closure
      {g : Equiv.Perm Nat | Equiv.Perm.IsSwap g})) (blockPerm X)
  let S₃ := blockSym (Finset.Icc 1 3)
  let S₅ := blockSym (Finset.Icc 4 8)
  let G := S₃ ⊔ S₅
  let K := Subgroup.zpowers (swap 1 2) ⊔ S₅
  let cycle := swap 4 5 * swap 5 6
  let τ := swap 1 3
  let σ := τ * cycle
  let L := Subgroup.zpowers (swap 7 8)
  ∃ (hKG : K ≤ G) (hσ : σ ∈ G) (hτ : τ ∈ G),
    let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (inclusion K G hKG))
    let e : G := 1
    let s : G := ⟨σ, hσ⟩
    let t : G := ⟨τ, hτ⟩
    let q := DoubleCoset.mk A A
    q e ≠ q s ∧ q t = q s ∧ (∀ j : DoubleCoset.Quotient (A : Set G) (A : Set G),
      j = q e ∨ j = q s) ∧
    mackey K 1 ⊓ mackey K σ = S₅ ∧
    common K G σ = Subgroup.zpowers cycle ⊔ L ∧
    IsGreatest {S : Subgroup U | admissible K σ S} L ∧
    IsGreatest {S : Subgroup U | admissible K τ S} S₅ ∧
    Subgroup.relIndex L (mackey K 1) = 120 ∧
    Subgroup.relIndex L (mackey K σ) = 60 ∧
    Subgroup.relIndex S₅ (mackey K 1) = 2 ∧
    Subgroup.relIndex S₅ (mackey K τ) = 1 ∧
    diagramIdentity K G hKG e s L (1 / 120) (Option.some (1 / 60)) ∧
    diagramIdentity K G hKG e t S₅ (1 / 2) Option.none
