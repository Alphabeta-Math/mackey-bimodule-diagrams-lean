import MackeyDiagrams
import Proofs.CaseSixCounterexampleWithTrivialProjectedStabilizers

set_option maxHeartbeats 2000000

namespace CaseSixTrivialProposition
open CaseSixTrivialAux

private abbrev Parabolic (H : Subgroup U) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ k, (blocks k).Nonempty) ∧
    Pairwise (fun k l => Disjoint (blocks k) (blocks l)) ∧
    H.map finitary.subtype = ⨆ k, blockSym (blocks k)

private theorem map_comap_block {H : Subgroup P} (h : H ≤ finitary) :
    (H.comap finitary.subtype).map finitary.subtype = H :=
  Subgroup.map_comap_eq_self (finitary.range_subtype.symm ▸ h)

-- Example 8.6 chooses A as the product of the symmetric groups on two pairs.
-- Finite permutation swap induction reduces membership to the two generators.
private theorem pair_le_small (m n : Nat) (h : Equiv.swap m n ∈ small) :
    blockSym {m, n} ≤ small := by
  classical
  rintro _ ⟨σ, rfl⟩
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [map_one]; exact small.one_mem
  | swap_mul σ x y hxy ih =>
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq]
    apply small.mul_mem _ ih
    have hx : (x : Nat) = m ∨ (x : Nat) = n :=
      (Finset.mem_insert.mp x.property).imp id Finset.mem_singleton.mp
    have hy : (y : Nat) = m ∨ (y : Nat) = n :=
      (Finset.mem_insert.mp y.property).imp id Finset.mem_singleton.mp
    have hne : (x : Nat) ≠ (y : Nat) := fun eq => hxy (Subtype.ext eq)
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (hne (hx.trans hy.symm)).elim
    · simpa only [hx, hy] using h
    · simpa only [hx, hy, Equiv.swap_comm n m] using h
    · exact (hne (hx.trans hy.symm)).elim

private theorem parabolicA : Parabolic A := by
  let blocks : Fin 2 → Finset Nat := ![{1, 2}, {3, 4}]
  have leftGen : Equiv.swap (1 : Nat) 2 ∈ small :=
    Subgroup.subset_closure (by simp)
  have rightGen : Equiv.swap (3 : Nat) 4 ∈ small :=
    Subgroup.subset_closure (by simp)
  have hblocks : (⨆ k, blockSym (blocks k)) = small := by
    apply le_antisymm
    · refine iSup_le (fun k => ?_)
      fin_cases k
      · exact pair_le_small 1 2 leftGen
      · exact pair_le_small 3 4 rightGen
    · refine (Subgroup.closure_le _).2 (fun σ hσ => ?_)
      rcases Set.mem_insert_iff.mp hσ with rfl | hσ
      · exact (le_iSup (fun k => blockSym (blocks k)) (0 : Fin 2))
          (swap_block _ (by decide) (by decide))
      · rw [Set.mem_singleton_iff.mp hσ]
        exact (le_iSup (fun k => blockSym (blocks k)) (1 : Fin 2))
          (swap_block _ (by decide) (by decide))
  refine ⟨2, blocks, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> decide
  · intro k l hkl
    fin_cases k <;> fin_cases l
    · exact (hkl rfl).elim
    · decide
    · decide
    · exact (hkl rfl).elim
  · rw [hblocks]
    refine map_comap_block ((Subgroup.closure_le _).2 (fun σ hσ => ?_))
    rcases Set.mem_insert_iff.mp hσ with rfl | hσ
    · exact Subgroup.subset_closure ⟨1, 2, by decide, rfl⟩
    · rw [Set.mem_singleton_iff.mp hσ]
      exact Subgroup.subset_closure ⟨3, 4, by decide, rfl⟩

private theorem parabolicD : Parabolic D := by
  refine ⟨1, fun _ => points, fun _ => points_nonempty, ?_, ?_⟩
  · intro k l hkl
    exact (hkl (Subsingleton.elim k l)).elim
  · rw [iSup_unique]
    exact map_comap_block (block_finitary points)

private theorem parabolicF : Parabolic F := by
  refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, ?_⟩
  change (⊥ : Subgroup U).map finitary.subtype = ⨆ k : Fin 0, blockSym (Fin.elim0 k)
  simp

end CaseSixTrivialProposition

theorem ParabolicCaseSixObstructionWithTrivialProjectedStabilizer : (
let P := Equiv.Perm Nat
let finitary : Subgroup P := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (S : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let straight := fun {K L : Subgroup U} (p : MackeyDiagrams.Word K L) =>
  ordinary (MackeyDiagrams.Diagram.id p)
let atLeft := fun {K J J' L M : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
    (tail : MackeyDiagrams.Word L M)
    (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
  vertical (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
    (vertical (horizontal crossing (straight tail))
      (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
let ProjectionLabel := fun {K L M H : Subgroup U}
    (α : MackeyDiagrams.ConjEmbedding K M) (β : MackeyDiagrams.ConjEmbedding L M)
    (η : MackeyDiagrams.ConjEmbedding H K) (θ : MackeyDiagrams.ConjEmbedding H L) =>
  List (Complex × MackeyDiagrams.ProjectionDot.Mixed α β η θ)
∃ (G A D C E F B' : Subgroup U),
  parabolic G ∧ parabolic A ∧ parabolic D ∧ parabolic C ∧ parabolic E ∧ parabolic F ∧
  parabolic B' ∧
  ∃ (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E)
    (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
    (k : MackeyDiagrams.ConjEmbedding B' C)
    (r : MackeyDiagrams.ProjectionDot.Mixed b d i j) (t : MackeyDiagrams.Dot (comp a i) (comp c k))
    (s : MackeyDiagrams.Dot (comp e k) (comp f j)),
  let bottom := tensor (up a) (tensor (down b) (up d))
  let top := tensor (up c) (tensor (down e) (up f))
  let inputBasis := MackeyDiagrams.Word.basis bottom
  let outputBasis := MackeyDiagrams.Word.basis top
  let p : inputBasis.carrier :=
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor (down b) (up d))) 1
      (MackeyDiagrams.Generator.mixedPair b d (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot r)))
  let q : outputBasis.carrier :=
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
      (MackeyDiagrams.Word.basis (tensor (down e) (up f))) (MackeyDiagrams.Dot.element t)
      (MackeyDiagrams.Generator.mixedPair e f (MackeyDiagrams.Dot.element s))
  let sourceStabilizer : Set (G × F) := {z | MackeyDiagrams.Biset.act inputBasis z p = p}
  let targetStabilizer : Set (G × F) := {z | MackeyDiagrams.Biset.act outputBasis z q = q}
  let projectsToTrivial := fun (S : Set (G × F)) => Set.image Prod.snd S = ({1} : Set F)
  let right : MackeyDiagrams.LabelledDrawing Complex bottom top :=
    vertical
      (horizontal (straight (up a)) (MackeyDiagrams.LabelledDrawing.compactProjection b d i j [(1, r)]))
      (vertical (atLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i c k [(1, t)]))
        (horizontal (straight (up c))
          (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j [(1, s)])))
  let left := fun {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (rL : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
      (tL : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w f)))
      (sL : ProjectionLabel u w c e) =>
    vertical
      (atLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b rL))
      (vertical
        (horizontal (straight (down u)) (MackeyDiagrams.LabelledDrawing.parallelUp v d w f tL))
        (atLeft (up f) (MackeyDiagrams.LabelledDrawing.compactProjection u w c e sL)))
  let IsLeft := fun (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    ∃ (B : Subgroup U), parabolic B ∧
      ∃ (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
        (w : MackeyDiagrams.ConjEmbedding E B)
        (rL : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
        (tL : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w f)))
        (sL : ProjectionLabel u w c e),
        diagram = left u v w rL tL sL
  let evaluate := fun (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret diagram))
  projectsToTrivial (sourceStabilizer ∩ targetStabilizer) ∧
  projectsToTrivial sourceStabilizer ∧ projectsToTrivial targetStabilizer ∧
  ∀ (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top), IsLeft diagram →
    evaluate diagram ≠ evaluate right
) :=
(open CaseSixTrivialAux CaseSixTrivialProposition in
by
  -- Xiao, Proposition 8.9 and Example 8.6, archived p. 42, published
  -- 28 November revision p. 44. https://getcurious.cc/downloads/mackey-bimodules.pdf#page=44
  -- The proposition's proof invokes the example. Its Steps 1–5 compute the
  -- right action and establish constant column mass for all left labels.
  classical
  refine ⟨A, A, D, A, D, F, F, parabolicA, parabolicA, parabolicD, parabolicA,
    parabolicD, parabolicF, parabolicF, a, b, d, a, b, d, i, j, i, ?_⟩
  obtain ⟨_, hstabilizers, hr, _, hseparation⟩ :=
    CaseSixCounterexampleWithTrivialProjectedStabilizers
  refine ⟨⟨endDot, hr⟩, MackeyDiagrams.Dot.id (a.comp i), endDot, ?_⟩
  -- The example proves the three projection assertions for every pair
  -- of basis elements because the right boundary group is trivial.
  let p := coordinate 1 endDot.element
  let q := coordinate (MackeyDiagrams.Dot.id (a.comp i)).element endDot.element
  have h := hstabilizers p q
  refine ⟨h.2.2, h.1, h.2.1, ?_⟩
  intro drawing hleft
  -- Step 6 of the example separates the right evaluation from every finite
  -- linear combination of left drawings. Use a singleton of weight one
  -- to specialize that result to the typed single-drawing endpoint.
  let terms : MackeyDiagrams.IndexedDrawing Complex word word Unit :=
    ⟨{()}, fun _ => drawing⟩
  have hne := (hseparation Unit terms (fun _ => 1) (fun _ _ => hleft)).2
  intro heq
  apply hne
  change ev drawing = rightEval at heq
  apply LinearMap.ext
  intro x
  rw [MackeyDiagrams.IndexedDrawing.eval_apply]
  simp only [terms, Finset.sum_singleton]
  change (1 : Complex) • ev drawing x = rightEval x
  rw [one_smul, heq])
