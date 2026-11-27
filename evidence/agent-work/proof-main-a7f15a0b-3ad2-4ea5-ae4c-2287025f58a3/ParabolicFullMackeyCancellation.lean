import MackeyDiagrams
import Proofs.MixedReidemeisterTwoMackeyCancellation
import Proofs.MackeyDecompositionWithParabolicRepresentatives

set_option maxHeartbeats 2000000

open MackeyDiagrams

private theorem parabolicCancellation_finite
    {F : Subgroup (Equiv.Perm Nat)} (G : Subgroup F)
    {n : Nat} (blocks : Fin n → Finset Nat)
    (hblocks : G.map F.subtype =
      ⨆ i, (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ blocks i)).range) :
    Finite G := by
  classical
  let X := Finset.univ.biUnion blocks
  have fixesComplement (g : G) :
      ∀ x : Nat, x ∉ X → ((g : F) : Equiv.Perm Nat) x = x := by
    have hg : ((g : F) : Equiv.Perm Nat) ∈
        ⨆ i, (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ blocks i)).range := by
      rw [← hblocks]
      exact ⟨(g : F), g.property, rfl⟩
    refine Subgroup.iSup_induction _ (C := fun s : Equiv.Perm Nat =>
      ∀ x : Nat, x ∉ X → s x = x) hg ?_ ?_ ?_
    · rintro i _ ⟨s, rfl⟩ x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem s
        (fun hi => hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩))
    · exact fun _ _ => rfl
    · intro s t hs ht x hx
      change s (t x) = x
      rw [ht x hx, hs x hx]
  apply Finite.of_injective (fun g : G =>
    (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Nat => x ∈ X)).symm
      ⟨((g : F) : Equiv.Perm Nat), fixesComplement g⟩)
  intro g h heq
  have hh := (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Nat => x ∈ X)).symm.injective heq
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun s => s.val) hh

private theorem parabolicCancellation_eval_univ
    {U : Type} [Group U] {K H : Subgroup U} {M : Word K H} {J : Type}
    (finiteJ : Fintype J) (sum : PointwiseIndexedDrawing Complex M M J) :
    (IndexedDrawing.mk (@Finset.univ J finiteJ) sum.summand).eval = sum.eval := by
  classical
  let : Fintype J := finiteJ
  apply LinearMap.ext
  intro x
  rw [IndexedDrawing.eval_apply, PointwiseIndexedDrawing.eval_apply,
    PointwiseIndexedDrawing.evalAt_def]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro j _ hj
  simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hj

theorem ParabolicFullMackeyCancellation : (
let U := ↥(Subgroup.closure {s : Equiv.Perm Nat | Equiv.Perm.IsSwap s})
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) := fun X =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))
let parabolic : Subgroup U → Prop := fun S =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype _) S = iSup (fun i => blockSym (blocks i))
∀ (K H G : Subgroup U) (α β : U),
  parabolic K → parabolic H → parabolic G →
  let conjugate := fun (c : U) (S : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
  let Kα := conjugate α K
  let Hβ := conjugate β H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun k => hK ⟨(k : U), k.property, rfl⟩)
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun h => hH ⟨(h : U), h.property, rfl⟩)
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j, DoubleCoset.mk A B (σ j) = j),
      let L := fun j : J => Kα ⊓ conjugate ((σ j : U) * β) H
      let l := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹ (by
          intro ℓ
          obtain ⟨k, hk, heq⟩ := ℓ.property.1
          change α * k * α⁻¹ = (ℓ : U) at heq
          change k ∈ K at hk
          change α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹ ∈ K
          rw [← heq]
          convert hk using 1
          group)
      let r := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
          (β⁻¹ * (σ j : U)⁻¹) (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := ℓ.property.2
            change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
            change h ∈ H at hh
            change (β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) * (β⁻¹ * (σ j : U)⁻¹)⁻¹ ∈ H
            rw [← heq]
            convert hh using 1
            group)
      let d : ∀ j : J, MackeyDiagrams.Dot
          (MackeyDiagrams.ConjEmbedding.comp a (l j))
          (MackeyDiagrams.ConjEmbedding.comp b (r j)) := fun j =>
        ⟨σ j, by
          intro ℓ
          apply Subtype.ext
          change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (σ j : U) =
            (σ j : U) * (β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
              (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹)
          group⟩
      let down := MackeyDiagrams.Word.down a
      let up := MackeyDiagrams.Word.up b
      let M := MackeyDiagrams.Word.tensor down up
      let Mj := fun j : J =>
        MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (l j)) (MackeyDiagrams.Word.down (r j))
      ∃ (finiteJ : Fintype J)
        (finiteFibers : ∀ (j : J) (z : (MackeyDiagrams.Word.basis M).carrier),
          Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b (l j) (r j) (d j) w = z}),
        let ι : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex (Mj j) M := fun j =>
          MackeyDiagrams.LabelledDrawing.mixedMultiplication a b (l j) (r j) [(1, d j)]
        let p : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex M (Mj j) := fun j =>
          MackeyDiagrams.LabelledDrawing.compactProjection a b (l j) (r j)
            [(1, ⟨d j, finiteFibers j⟩)]
        let straight : MackeyDiagrams.LabelledDrawing Complex M M :=
          MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id down))
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id up))
        let straightj : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex (Mj j) (Mj j) :=
          fun j => MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.ordinary
              (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up (l j))))
            (MackeyDiagrams.LabelledDrawing.ordinary
              (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down (r j))))
        let eval := fun {bottom top : MackeyDiagrams.Word K H}
            (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
        let indices : Finset J := @Finset.univ J finiteJ
        let summands : J → MackeyDiagrams.LabelledDrawing Complex M M := fun j =>
          MackeyDiagrams.LabelledDrawing.vertical (p j) (ι j)
        let fullSum : MackeyDiagrams.IndexedDrawing Complex M M J :=
          MackeyDiagrams.IndexedDrawing.mk indices summands
        MackeyDiagrams.IndexedDrawing.shape fullSum =
          MackeyDiagrams.IndexedDrawing.Shape.mk indices
            (fun j => MackeyDiagrams.LabelledDrawing.planarShape (summands j)) ∧
        MackeyDiagrams.IndexedDrawing.eval fullSum =
          MackeyDiagrams.Biset.Hom.toLinearMap (eval straight) ∧
        ∀ j : J,
          eval (MackeyDiagrams.LabelledDrawing.vertical (ι j) (p j)) = eval (straightj j)
) :=
(by
  classical
  intro U blockSym parabolic K H G α β _ _ hG conjugate Kα Hβ hK hH
    a b A B J σ reps L l r d down up M Mj
  -- Xiao §8.2, the two identities after Proposition 8.3 (archived
  -- original p. 35, published 28 November revision p. 37). The equations
  -- compare evaluations of the drawn stacks. The plan has no exact
  -- Alphabeta Math entry with numbered steps for these identities.
  -- Step 1. Restrict G to the finite union of its blocks. The chosen
  -- section supplies surjectivity onto the double-coset quotient.
  obtain ⟨n, blocks, _, _, hblocks⟩ := hG
  let : Finite G := parabolicCancellation_finite G blocks hblocks
  let : Finite J := Finite.of_surjective (DoubleCoset.mk A B)
    (fun j => ⟨σ j, reps j⟩)
  let finiteJ := Fintype.ofFinite J

  -- Step 2. Use the registered §5.1 cancellation, which formalizes the
  -- splitting equations (2.3) at the full intersections for this section.
  -- The §7.4 decomposition supplies tableau representatives
  -- with its block hypotheses. Here the fixed crossing dots use the given
  -- section, for which the §5.1 supplier already proves both evaluations.
  let d₀ (j : J) : Dot (a.comp (l j)) (b.comp (r j)) :=
    Dot.ofRepresentatives (α * α⁻¹) (β * (β⁻¹ * (σ j : U)⁻¹))
      (by
        intro ℓ
        change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ = _
        simp only [mul_inv_rev, mul_assoc])
      (by
        intro ℓ
        change β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
          (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹ = _
        simp only [mul_inv_rev, mul_assoc])
      (by
        have he : (α * α⁻¹) * (β * (β⁻¹ * (σ j : U)⁻¹))⁻¹ = (σ j : U) := by
          group
        rw [he]
        exact (σ j).property)
  have hcancel := MixedReidemeisterTwoMackeyCancellation K H G α β hK hH σ reps
  have hd : d₀ = d := by
    funext j
    exact Dot.ext ((hcancel.2.2.1 j).1.trans (show (d j).element = σ j from rfl).symm)

  let eval {S T : Word K H} (drawing : LabelledDrawing Complex S T) :=
    drawing.interpret.eval
  let straight : LabelledDrawing Complex M M :=
    .horizontal (.ordinary (Diagram.id down)) (.ordinary (Diagram.id up))
  let straightj (j : J) : LabelledDrawing Complex (Mj j) (Mj j) :=
    .horizontal (.ordinary (Diagram.id (Word.up (l j))))
      (.ordinary (Diagram.id (Word.down (r j))))
  -- The compact projection uses the supplier’s finite multiplication
  -- fibers. A standalone reverse cup has a separate finite-index condition.
  let outcome (dots : ∀ j : J, Dot (a.comp (l j)) (b.comp (r j))) : Prop :=
    ∃ hf : ∀ (j : J) (z : M.basis.carrier),
        Set.Finite {w | Generator.mixedMultiplicationBasis a b (l j) (r j) (dots j) w = z},
      let ι (j : J) : LabelledDrawing Complex (Mj j) M :=
        .mixedMultiplication a b (l j) (r j) [(1, dots j)]
      let p (j : J) : LabelledDrawing Complex M (Mj j) :=
        .compactProjection a b (l j) (r j) [(1, ⟨dots j, hf j⟩)]
      let terms (j : J) := LabelledDrawing.vertical (p j) (ι j)
      (∀ j : J, eval (.vertical (ι j) (p j)) = eval (straightj j)) ∧
      ∃ hs : ∀ x : M.basis.carrier →₀ Complex,
          Set.Finite (Function.support fun j => (eval (terms j)).toLinearMap x),
        let pointwise : PointwiseIndexedDrawing Complex M M J := ⟨terms, hs⟩
        pointwise.eval = (eval straight).toLinearMap
  have hOutcome : outcome d := by
    rw [← hd]
    obtain ⟨hf, hdiag, _, hs, _, heval⟩ := hcancel.2.2.2
    refine ⟨hf, hdiag, hs, ?_⟩
    apply LinearMap.ext
    exact heval

  -- Step 3. The finite figure stores one sum over all classes with the full
  -- projection-then-inclusion stack at each index. The supplier sums just
  -- the nonzero evaluations at each input. Extending this sum by zero gives
  -- the evaluation of the finite figure. Its reverse stack uses hdiag.
  obtain ⟨hf, hdiag, hs, heval⟩ := hOutcome
  refine ⟨finiteJ, hf, ?_⟩
  intro ι p straight straightj eval indices summands fullSum
  refine ⟨rfl, ?_, hdiag⟩
  let pointwise : PointwiseIndexedDrawing Complex M M J := ⟨summands, hs⟩
  exact (parabolicCancellation_eval_univ finiteJ pointwise).trans heval)

#print axioms ParabolicFullMackeyCancellation
