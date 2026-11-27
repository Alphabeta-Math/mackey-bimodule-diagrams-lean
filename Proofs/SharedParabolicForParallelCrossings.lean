import MackeyDiagrams
import Proofs.ParabolicSharedRegionParallelInduction
import Proofs.ParabolicSharedRegionParallelRestriction

set_option maxHeartbeats 2000000

theorem SharedParabolicForParallelCrossings : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) := fun X =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))
let parabolic : Subgroup U → Prop := fun L =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) L = iSup (fun i => blockSym (blocks i))
∀ {ι : Type*} [Finite ι] (G K : Subgroup U) (H B H' : ι → Subgroup U),
  parabolic G → parabolic K →
  (∀ i, parabolic (H i)) → (∀ i, parabolic (B i)) → (∀ i, parabolic (H' i)) →
  ∀ (α β γ δ α' β' : ι → U)
    (hα : ∀ i (h : H i), α i * (h : U) * (α i)⁻¹ ∈ G)
    (hβ : ∀ i (k : K), β i * (k : U) * (β i)⁻¹ ∈ H i)
    (hγ : ∀ i (b : B i), γ i * (b : U) * (γ i)⁻¹ ∈ G)
    (hδ : ∀ i (k : K), δ i * (k : U) * (δ i)⁻¹ ∈ B i)
    (hα' : ∀ i (h : H' i), α' i * (h : U) * (α' i)⁻¹ ∈ G)
    (hβ' : ∀ i (k : K), β' i * (k : U) * (β' i)⁻¹ ∈ H' i),
  let v := fun i => γ i * δ i
  let image := fun i => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (v i))) K
  let P := Subgroup.closure (Set.iUnion fun i => (image i : Set U))
  IsLeast {Q : Subgroup U | Q ≤ G ∧ parabolic Q ∧ ∀ i, image i ≤ Q} P ∧
  ∃ (hPG : P ≤ G) (hKP : ∀ i (k : K), v i * (k : U) * (v i)⁻¹ ∈ P),
    let inclusion : MackeyDiagrams.ConjEmbedding P G :=
      ⟨Subgroup.inclusion hPG, ⟨1, fun p => by
        simp only [Subgroup.coe_inclusion, one_mul, inv_one, mul_one]⟩⟩
    let throughP := fun i => MackeyDiagrams.ConjEmbedding.ofConjugator (v i) (hKP i)
    let evalDrawing {A C : Subgroup U} {p q : MackeyDiagrams.Word A C}
        (drawing : MackeyDiagrams.LabelledDrawing Complex p q) :=
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
    ∀ i,
      let a := MackeyDiagrams.ConjEmbedding.ofConjugator (α i) (hα i)
      let b := MackeyDiagrams.ConjEmbedding.ofConjugator (β i) (hβ i)
      let c := MackeyDiagrams.ConjEmbedding.ofConjugator (γ i) (hγ i)
      let d := MackeyDiagrams.ConjEmbedding.ofConjugator (δ i) (hδ i)
      let a' := MackeyDiagrams.ConjEmbedding.ofConjugator (α' i) (hα' i)
      let b' := MackeyDiagrams.ConjEmbedding.ofConjugator (β' i) (hβ' i)
      let bottom := MackeyDiagrams.ConjEmbedding.comp a b
      let middle := MackeyDiagrams.ConjEmbedding.comp c d
      let top := MackeyDiagrams.ConjEmbedding.comp a' b'
      let newMiddle := MackeyDiagrams.ConjEmbedding.comp inclusion (throughP i)
      ∃ sameMiddle : middle = newMiddle,
        ∀ (x : MackeyDiagrams.DotLabel Complex bottom middle)
          (y : MackeyDiagrams.DotLabel Complex middle top),
          let newX := Eq.ndrec
            (motive := fun m => MackeyDiagrams.DotLabel Complex bottom m) x sameMiddle
          let newY := Eq.ndrec
            (motive := fun m => MackeyDiagrams.DotLabel Complex m top) y sameMiddle
          let product := MackeyDiagrams.DotLabel.compose x y
          let originalUp := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.parallelUp a b c d (MackeyDiagrams.DotLabel.terms x))
            (MackeyDiagrams.LabelledDrawing.parallelUp c d a' b' (MackeyDiagrams.DotLabel.terms y))
          let sharedUp := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.parallelUp a b inclusion (throughP i)
              (MackeyDiagrams.DotLabel.terms newX))
            (MackeyDiagrams.LabelledDrawing.parallelUp inclusion (throughP i) a' b'
              (MackeyDiagrams.DotLabel.terms newY))
          let mergedUp := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
              (MackeyDiagrams.TrivalentVertex.mergeUp a b))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.DotLabel.upDrawing product)
              (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
                (MackeyDiagrams.TrivalentVertex.splitUp a' b')))
          let originalDown := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.parallelDown a b c d (MackeyDiagrams.DotLabel.terms x))
            (MackeyDiagrams.LabelledDrawing.parallelDown c d a' b' (MackeyDiagrams.DotLabel.terms y))
          let sharedDown := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.parallelDown a b inclusion (throughP i)
              (MackeyDiagrams.DotLabel.terms newX))
            (MackeyDiagrams.LabelledDrawing.parallelDown inclusion (throughP i) a' b'
              (MackeyDiagrams.DotLabel.terms newY))
          let mergedDown := MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
              (MackeyDiagrams.TrivalentVertex.mergeDown a b))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.DotLabel.downDrawing product)
              (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
                (MackeyDiagrams.TrivalentVertex.splitDown a' b')))
          (evalDrawing originalUp = evalDrawing sharedUp ∧
            evalDrawing sharedUp = evalDrawing mergedUp) ∧
          (evalDrawing originalDown = evalDrawing sharedDown ∧
            evalDrawing sharedDown = evalDrawing mergedDown)
) :=
(by
  -- Ian Xiao, Proposition 8.4 and its two diagram rows, archived original
  -- pp. 36–37 and published 28 November revision pp. 38–39.
  -- The archived original has SHA-256
  -- bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2.
  -- The published revision has SHA-256
  -- 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61.
  -- The distinct hashes and pagination correct the provenance in the
  -- reviewed translation's source note. The revised convention reads the
  -- identities after evaluation, as formalized by evalDrawing below.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  intro finitary U blockSym parabolic ι _ G K H B H' hG hK hH hB hH'
    α β γ δ α' β' hα hβ hγ hδ hα' hβ' v image P
  -- Alphabeta Math's transposition-generation proof, steps 1.1 and 2.1,
  -- decomposes finite permutations into swaps. The restriction supplier
  -- checks generation on the finite block subtypes by Mathlib's swap theorem,
  -- extends the swaps by identity and transports them by the conjugators.
  -- Step 3.1 uses generated-subgroup minimality. Here the restriction supplier
  -- applies it to the union of conjugate subgroups and proves parabolicity on
  -- the finite carrier of G by grouping points into orbits.
  -- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
  rcases ParabolicSharedRegionParallelRestriction G K H B H' hG hK
      (fun i => ⟨hH i, hB i, hH' i⟩) α β γ δ α' β' hα hβ hγ hδ hα' hβ' with
    ⟨least, hPG, hKP, down⟩
  rcases ParabolicSharedRegionParallelInduction G K H B H' hG hK hH hB hH'
      α β γ δ α' β' hα hβ hγ hδ hα' hβ' with ⟨_, _, up⟩
  -- Both suppliers use the same closure P. Reorder the two predicates
  -- in the restriction supplier's IsLeast and keep its containment witnesses.
  refine ⟨⟨⟨least.1.2.1, least.1.1, least.1.2.2⟩,
    fun Q hQ => least.2 ⟨hQ.2.1, hQ.1, hQ.2.2⟩⟩, hPG, hKP, ?_⟩
  intro inclusion throughP evalDrawing
  have hIncl : ∀ p : P, (1 : U) * (p : U) * (1 : U)⁻¹ ∈ G := by
    intro p
    simpa only [one_mul, inv_one, mul_one] using hPG p.property
  -- The induction supplier presents the inclusion by conjugation by 1.
  -- Compare underlying homomorphisms to transport its full dependent result.
  have inclusionEq : MackeyDiagrams.ConjEmbedding.ofConjugator (1 : U) hIncl = inclusion := by
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro p
    apply Subtype.ext
    change (1 : U) * (p : U) * (1 : U)⁻¹ = (p : U)
    simp only [one_mul, inv_one, mul_one]
  intro i a b c d a' b' bottom middle top newMiddle
  obtain ⟨same, _, downMaps⟩ := down i
  -- The finite-label clauses of the two suppliers implement Theorem 5.4
  -- and its restriction counterpart (archived p. 18, revised p. 20).
  -- Their evaluated product formulas use DotLabel.upDrawing_compose and
  -- DotLabel.downDrawing_compose through the respective Reidemeister II
  -- results. They already cover arbitrary eligible terms with coefficients.
  let twoUp {M : Subgroup U} (g : MackeyDiagrams.ConjEmbedding M G)
      (q : MackeyDiagrams.ConjEmbedding K M)
      (x : MackeyDiagrams.DotLabel Complex bottom (g.comp q))
      (y : MackeyDiagrams.DotLabel Complex (g.comp q) top) :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.parallelUp a b g q x.terms)
      (MackeyDiagrams.LabelledDrawing.parallelUp g q a' b' y.terms)
  let merge := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.mergeUp a b)
  let split := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.splitUp a' b')
  let upAgreement (g : MackeyDiagrams.ConjEmbedding P G) : Prop :=
    ∃ sameUp : middle = g.comp (throughP i),
      ∀ (x : MackeyDiagrams.DotLabel Complex bottom middle)
        (y : MackeyDiagrams.DotLabel Complex middle top),
        let shared := twoUp g (throughP i)
          (Eq.ndrec (motive := fun m => MackeyDiagrams.DotLabel Complex bottom m) x sameUp)
          (Eq.ndrec (motive := fun m => MackeyDiagrams.DotLabel Complex m top) y sameUp)
        evalDrawing (twoUp c d x y) = evalDrawing shared ∧
          evalDrawing shared =
            evalDrawing ((merge.vertical (MackeyDiagrams.DotLabel.upDrawing (x.compose y))).vertical split)
  have upAtOne : upAgreement (MackeyDiagrams.ConjEmbedding.ofConjugator (1 : U) hIncl) := up i
  have upAtInclusion : upAgreement inclusion := Eq.mp (congrArg upAgreement inclusionEq) upAtOne
  obtain ⟨_, upMaps⟩ := upAtInclusion
  -- Proof irrelevance identifies the two witnesses of equality of the
  -- middle embeddings. Thus the same dependent label transports serve
  -- both orientations, and the product uses the original labels in order.
  use same
  intro x y newX newY product originalUp sharedUp mergedUp originalDown sharedDown mergedDown
  refine ⟨?_, downMaps x y⟩
  obtain ⟨originalEq, sharedEq⟩ := upMaps x y
  -- The induction supplier groups merge with the product dot first.
  -- The endpoint groups the product dot with split first. Associate the
  -- evaluated vertical maps via Biset.Hom.vertical_assoc.
  exact ⟨originalEq, sharedEq.trans
    (MackeyDiagrams.Biset.Hom.vertical_assoc
      (evalDrawing merge) (evalDrawing (MackeyDiagrams.DotLabel.upDrawing product))
      (evalDrawing split))⟩)
