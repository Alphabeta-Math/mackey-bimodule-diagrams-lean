import MackeyDiagrams
import Proofs.MackeyInclusionAndProjectionCrossings
import Proofs.SurvivingCosetRepresentative

set_option maxHeartbeats 2000000

theorem MackeySummandProjection : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U),
  let Kα := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K
  let Hβ := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj β)) H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let L := fun j : J =>
        Kα ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H
      let C := fun j : J =>
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (β⁻¹ * (σ j : U)⁻¹))) (L j)
      ∀ (I : J → Type v) (hRep : ∀ j : J, I j → H)
        (_ : ∀ (j : J) (h : H), ∃! i : I j, (h : U) * (hRep j i : U)⁻¹ ∈ C j)
        (j : J),
        let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
          (fun k => hK ⟨(k : U), k.property, rfl⟩)
        let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
          (fun h => hH ⟨(h : U), h.property, rfl⟩)
        let s := σ j
        let l := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹
          (by
            intro ℓ
            obtain ⟨k, hk, heq⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at heq
            change k ∈ K at hk
            rw [← heq]
            convert hk using 1
            group)
        let r := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
          (β⁻¹ * (s : U)⁻¹)
          (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := ℓ.property.2
            change ((s : U) * β) * h * ((s : U) * β)⁻¹ = (ℓ : U) at heq
            change h ∈ H at hh
            rw [← heq]
            convert hh using 1
            group)
        let d : MackeyDiagrams.Dot
            (MackeyDiagrams.ConjEmbedding.comp a l) (MackeyDiagrams.ConjEmbedding.comp b r) :=
          ⟨s, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (s : U) =
              (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
        let kg := MackeyDiagrams.Word.down a
        let gh := MackeyDiagrams.Word.up b
        let kl := MackeyDiagrams.Word.up l
        let lh := MackeyDiagrams.Word.down r
        let middle := MackeyDiagrams.Word.up (MackeyDiagrams.ConjEmbedding.comp a l)
        let M := MackeyDiagrams.Word.tensor kg gh
        let Mj := MackeyDiagrams.Word.tensor kl lh
        let surviving := fun (g : G) =>
          {i : I j | α⁻¹ * (g : U) * β * (hRep j i : U)⁻¹ * β⁻¹ * (s : U)⁻¹ * α ∈ K}
        ∃ (hf : ∀ z, Set.Finite
            {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b l r d w = z})
          (hs : ∀ g : G, Set.Finite (surviving g)),
          let projectionLabel : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b l r) :=
            [(1, ⟨d, hf⟩)]
          let inclusionLabel : List (Complex × MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a l) (MackeyDiagrams.ConjEmbedding.comp b r)) :=
            [(1, d)]
          let p : MackeyDiagrams.LabelledDrawing Complex M Mj :=
            MackeyDiagrams.LabelledDrawing.compactProjection a b l r projectionLabel
          let ι : MackeyDiagrams.LabelledDrawing Complex Mj M :=
            MackeyDiagrams.LabelledDrawing.mixedMultiplication a b l r inclusionLabel
          let expandedProjection : MackeyDiagrams.LabelledDrawing Complex M Mj :=
            MackeyDiagrams.LabelledDrawing.expandedProjection a b l r projectionLabel
              MackeyDiagrams.ProjectionOpening.junction MackeyDiagrams.ProjectionClosing.junction
          let expandedInclusion : MackeyDiagrams.LabelledDrawing Complex Mj M :=
            MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.horizontal
                (MackeyDiagrams.LabelledDrawing.trivalent
                  (MackeyDiagrams.TrivalentVertex.upToDownUp a l))
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id lh)))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.ordinary
                  (MackeyDiagrams.Diagram.associate kg middle lh))
                (MackeyDiagrams.LabelledDrawing.vertical
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                    (MackeyDiagrams.LabelledDrawing.horizontal
                      (MackeyDiagrams.DotLabel.upDrawing (R := Complex) (Finsupp.single d 1))
                      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id lh))))
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                    (MackeyDiagrams.LabelledDrawing.trivalent
                      (MackeyDiagrams.TrivalentVertex.upDownToUp b r)))))
          let composite : MackeyDiagrams.LabelledDrawing Complex M M :=
            MackeyDiagrams.LabelledDrawing.vertical p ι
          let expandedComposite : MackeyDiagrams.LabelledDrawing Complex M M :=
            MackeyDiagrams.LabelledDrawing.vertical expandedProjection expandedInclusion
          let compositeEval := MackeyDiagrams.ScopedDiagram.eval
            (MackeyDiagrams.LabelledDrawing.interpret composite)
          compositeEval = MackeyDiagrams.ScopedDiagram.eval
            (MackeyDiagrams.LabelledDrawing.interpret expandedComposite) ∧
          (∀ g : G,
            let z := MackeyDiagrams.Generator.mixedPair a b g
            let image := compositeEval.toLinearMap (Finsupp.single z (1 : Complex))
            image = Finsupp.single z (Finset.card (Set.Finite.toFinset (hs g)) : Complex) ∧
              (DoubleCoset.mk A B g = j → image = Finsupp.single z (1 : Complex)) ∧
              (DoubleCoset.mk A B g ≠ j → image = 0))
) :=
(by
  classical
  intro U _ K H G α β Kα Hβ hK hH A B J σ hσ L C I hRep hTrans j
    a b s l r d kg gh kl lh middle M Mj surviving
  /- Ian Xiao, § 2.2, Theorem 2.2. The archived PDF shows the two
     composites on p. 6 and (2.5) on p. 7. The revised published PDF
     places these on pp. 8 and 9. The web article has diagram-05 and the
     same numbered equations in the prose of the proof.
     https://getcurious.cc/articles/math-bimodule-string-diagrams#eq:first-chain -/
  -- Theorem 2.2 uses the double-coset representative (2.1), the full
  -- intersection (2.2), and the right transversal (2.4). Supply all
  -- three to the registered crossing theorem, with the same σ and hRep.
  obtain ⟨hf, hs, _, hι, hp, _, hstack, _⟩ :=
    MackeyInclusionAndProjectionCrossings K H G α β hK hH σ hσ I hRep hTrans j
  refine ⟨hf, hs, ?_⟩
  intro projectionLabel inclusionLabel p ι expandedProjection expandedInclusion
    composite expandedComposite compositeEval
  refine ⟨hstack, ?_⟩
  intro g z image
  let traceArg (i : I j) : U :=
    α⁻¹ * (g : U) * β * (hRep j i : U)⁻¹ * β⁻¹ * (s : U)⁻¹ * α
  let indices := (hs g).toFinset
  let k (i : {i // i ∈ indices}) : K :=
    ⟨traceArg i.val, (hs g).mem_toFinset.mp i.property⟩
  let inc := ι.interpret.eval.toLinearMap
  have hproj :
      p.interpret.eval.toLinearMap (Finsupp.single z 1) =
        ∑ i ∈ indices.attach, Finsupp.single (kl.basis.pair lh.basis (k i) (hRep j i.val)) 1 :=
    (hp g).2
  have ha (x : K) : (a.toHom x : U) = α * (x : U) * α⁻¹ := rfl
  have hb (x : H) : (b.toHom x : U) = β * (x : U) * β⁻¹ := rfl
  -- In (2.5), the inclusion cancels the inverse dot and the inverse
  -- transversal factor in each surviving term. Work in G after using
  -- the trace equation to identify the element of K.
  have hproduct (i : {i // i ∈ indices}) :
      a.toHom (k i) * s * b.toHom (hRep j i.val) = g := by
    have htrace := (MackeyCrossingProof.trace_eq_iff a b l r d α β ha hb
      g (hRep j i.val) (k i)).mpr rfl
    change a.toHom (k i) = g * (b.toHom (hRep j i.val)⁻¹ * s⁻¹) at htrace
    rw [htrace, map_inv]
    group
  have hterm (i : {i // i ∈ indices}) :
      inc (Finsupp.single (kl.basis.pair lh.basis (k i) (hRep j i.val)) 1) =
        Finsupp.single z 1 := by
    change ι.interpret.eval.toLinearMap _ = _
    rw [hι, hproduct]
  -- Finite-fiber transfer supplies the finite sum at each input.
  -- This is the scoped projection of the paper, so no standalone
  -- reverse cup or finite subgroup-index hypothesis is used.
  have himage : image = Finsupp.single z (indices.card : Complex) := by
    change inc (p.interpret.eval.toLinearMap (Finsupp.single z 1)) = _
    rw [hproj, map_sum]
    simp only [hterm, Finset.sum_const, Finset.card_attach,
      ← Nat.cast_smul_eq_nsmul Complex, Finsupp.smul_single_one]
  have hsurv :
      (DoubleCoset.mk A B g = j → ∃! i : I j, i ∈ surviving g) ∧
        (DoubleCoset.mk A B g ≠ j → surviving g = ∅) :=
    SurvivingCosetRepresentative K H G α β hK hH σ hσ I hRep hTrans j g
  -- Lemma 2.3 gives exactly one term on the class j and zero outside it.
  refine ⟨himage, ?_, ?_⟩
  · intro hclass
    obtain ⟨i, hi, huniq⟩ := hsurv.1 hclass
    have hcard : indices.card = 1 :=
      Finset.card_eq_one_iff_existsUnique.mpr
        ⟨i, (hs g).mem_toFinset.mpr hi, fun t ht => huniq t ((hs g).mem_toFinset.mp ht)⟩
    simpa only [hcard, Nat.cast_one] using himage
  · intro hclass
    have hempty : indices = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hm : i ∈ surviving g := (hs g).mem_toFinset.mp hi
      rw [hsurv.2 hclass] at hm
      exact hm
    simpa only [hempty, Finset.card_empty, Nat.cast_zero, Finsupp.single_zero] using himage)
