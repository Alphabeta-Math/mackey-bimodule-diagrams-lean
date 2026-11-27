import Left
import Right

set_option maxHeartbeats 2000000

open CaseSixTrivialAux

theorem CaseSixCounterexampleWithTrivialProjectedStabilizers : (
let P := Equiv.Perm Nat
let finitary : Subgroup P := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (S : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let points : Finset Nat := {1, 2, 3, 4}
let small : Subgroup P :=
  Subgroup.closure ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P)
let A : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) small
let D : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) (blockSym points)
let F : Subgroup U := ⊥
let swapInBlock := fun (S : Finset Nat) (m n : Nat) (hm : m ∈ S) (hn : n ∈ S) =>
  (show Equiv.swap m n ∈ blockSym S from
    ⟨Equiv.swap (⟨m, hm⟩ : {k : Nat // k ∈ S}) ⟨n, hn⟩,
      Equiv.Perm.ofSubtype_swap_eq _ _⟩)
let hAD : A ≤ D := by
  have hsmall : small ≤ blockSym points := by
    refine (Subgroup.closure_le (blockSym points)).2 ?_
    intro σ hσ
    change σ ∈ ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P) at hσ
    rcases Set.mem_insert_iff.mp hσ with hσ | hσ
    · rw [hσ]
      exact swapInBlock points 1 2 (by decide) (by decide)
    · rw [Set.mem_singleton_iff.mp hσ]
      exact swapInBlock points 3 4 (by decide) (by decide)
  exact Subgroup.comap_mono hsmall
let parabolic := fun (B : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) B = iSup (fun i => blockSym (blocks i))
let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
  (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
let a := MackeyDiagrams.ConjEmbedding.id A
let b := incl hAD
let d := incl (show F ≤ D from bot_le)
let i := incl (show F ≤ A from bot_le)
let j := MackeyDiagrams.ConjEmbedding.id F
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let straight := fun {K L : Subgroup U} (p : MackeyDiagrams.Word K L) =>
  ordinary (MackeyDiagrams.Diagram.id p)
let word := tensor (up a) (tensor (down b) (up d))
let atLeft := fun {K J J' L M : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
    (tail : MackeyDiagrams.Word L M)
    (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
  vertical (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
    (vertical (horizontal crossing (straight tail))
      (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
let left := fun {B : Subgroup U}
    (u : MackeyDiagrams.ConjEmbedding A B) (v w : MackeyDiagrams.ConjEmbedding D B)
    (lower : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
    (middle : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w d)))
    (upper : List (Complex × MackeyDiagrams.ProjectionDot.Mixed u w a b)) =>
  vertical
    (atLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b lower))
    (vertical
      (horizontal (straight (down u))
        (MackeyDiagrams.LabelledDrawing.parallelUp v d w d middle))
      (atLeft (up d) (MackeyDiagrams.LabelledDrawing.compactProjection u w a b upper)))
let IsLeft := fun (drawing : MackeyDiagrams.LabelledDrawing Complex word word) =>
  ∃ (B : Subgroup U), parabolic B ∧
    ∃ (u : MackeyDiagrams.ConjEmbedding A B) (v w : MackeyDiagrams.ConjEmbedding D B)
      (lower : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
      (middle : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w d)))
      (upper : List (Complex × MackeyDiagrams.ProjectionDot.Mixed u w a b)),
      drawing = left u v w lower middle upper
let endDot : MackeyDiagrams.Dot (comp b i) (comp d j) :=
  ⟨1, fun x => by
    have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.property)
    simp [hx]⟩
let right := fun
    (lower : List (Complex × MackeyDiagrams.ProjectionDot.Mixed b d i j))
    (middle : List (Complex × MackeyDiagrams.Dot (comp a i) (comp a i)))
    (upper : List (Complex × MackeyDiagrams.Dot (comp b i) (comp d j))) =>
  vertical
    (horizontal (straight (up a))
      (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
    (vertical
      (atLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i a i middle))
      (horizontal (straight (up a))
        (MackeyDiagrams.LabelledDrawing.mixedMultiplication b d i j upper)))
let basis := MackeyDiagrams.Word.basis word
let coordinate := fun (g : A) (x : D) =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor (down b) (up d))) g
    (MackeyDiagrams.Generator.mixedPair b d x)
let basisVector := fun x : D => Finsupp.single (coordinate 1 x) (1 : Complex)
let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex word word) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
let coefficientSum := fun (z : Finsupp basis.carrier Complex) => Finsupp.sum z (fun _ c => c)
let projectsToTrivial := fun (S : Set (A × F)) =>
  Set.image Prod.snd S = ({1} : Set F)
let stabilizes := fun (p : basis.carrier) (k : A × F) => MackeyDiagrams.Biset.act basis k p = p
(∃ coordinates : basis.carrier ≃ D,
  ∀ (g : A) (x : D), coordinates (coordinate g x) = MackeyDiagrams.ConjEmbedding.toHom b g * x) ∧
(∀ p q : basis.carrier,
  projectsToTrivial {k | stabilizes p k} ∧
  projectsToTrivial {k | stabilizes q k} ∧
  projectsToTrivial {k | stabilizes p k ∧ stabilizes q k}) ∧
∃ (hr : ∀ z, Set.Finite {w |
    MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j endDot w = z}),
  let rightEval := evaluate
    (right [(1, ⟨endDot, hr⟩)] [(1, MackeyDiagrams.Dot.id (comp a i))] [(1, endDot)])
  (∀ x : D,
    ((x : U) ∈ A → rightEval (basisVector x) = basisVector x) ∧
    ((x : U) ∉ A → rightEval (basisVector x) = 0)) ∧
  ∀ (ι : Type) (terms : MackeyDiagrams.IndexedDrawing Complex word word ι)
      (coefficients : ι → Complex),
    (∀ k ∈ terms.indices, IsLeft (terms.summand k)) →
    let leftEval := MackeyDiagrams.IndexedDrawing.eval
      { terms with summand := fun k =>
          MackeyDiagrams.LabelledDrawing.scale (coefficients k) (terms.summand k) }
    (∀ x y : D, coefficientSum (leftEval (basisVector x)) = coefficientSum (leftEval (basisVector y))) ∧
    leftEval ≠ rightEval
) :=
by
  -- Xiao, Example 8.6, archived p. 42 and published 28 November revision p. 44.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  classical
  change (∃ e : word.basis.carrier ≃ D, ∀ g x, e (coordinate g x) = b.toHom g * x) ∧ _
  refine ⟨⟨coordinates, coordinates_pair⟩, ?_, ?_⟩
  · -- The individual and joint stabilizers contain the identity.
    -- Their second coordinate belongs to F = 1.
    intro p q
    have trivial (S : Set (A × F)) (h : (1, 1) ∈ S) :
        Prod.snd '' S = ({1} : Set F) := by
      ext f
      exact ⟨fun _ => Set.mem_singleton_iff.mpr (F_eq_one f),
        fun hf => ⟨(1, 1), h, (Set.mem_singleton_iff.mp hf).symm⟩⟩
    have hp : word.basis.act (1, 1) p = p := word.basis.one_act p
    have hq : word.basis.act (1, 1) q = q := word.basis.one_act q
    exact ⟨trivial _ hp, trivial _ hq, trivial _ ⟨hp, hq⟩⟩
  · refine ⟨rightFinite, right_action, ?_⟩
    intro ι terms coefficients hterms
    let scaled : MackeyDiagrams.IndexedDrawing Complex word word ι :=
      {terms with summand := fun k => .scale (coefficients k) (terms.summand k)}
    have const (x y : D) :
        mass (scaled.eval (vector x)) = mass (scaled.eval (vector y)) := by
      rw [MackeyDiagrams.IndexedDrawing.eval_apply, MackeyDiagrams.IndexedDrawing.eval_apply,
        map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨B, _, u, v, w, rs, ts, ss, hs⟩ := hterms k hk
      change mass ((coefficients k) • ev (terms.summand k) (vector x)) =
        mass ((coefficients k) • ev (terms.summand k) (vector y))
      rw [map_smul, map_smul]
      congr 1
      change terms.summand k = left u v w rs ts ss at hs
      rw [hs]
      exact left_mass u v w rs ts ss x y
    refine ⟨fun x y => const x y, ?_⟩
    -- Step 6. Apply the two evaluated morphisms to the identity input
    -- and the explicit cross-block swap, then compare coefficients.
    change scaled.eval ≠ rightEval
    intro eq
    obtain ⟨x, hx⟩ := outside
    have disagree := const 1 x
    have h1 : ((1 : D) : U) ∈ A := A.one_mem
    rw [eq, (right_action 1).1 h1, (right_action x).2 hx, map_zero, mass_single] at disagree
    exact one_ne_zero disagree

#print axioms CaseSixCounterexampleWithTrivialProjectedStabilizers
