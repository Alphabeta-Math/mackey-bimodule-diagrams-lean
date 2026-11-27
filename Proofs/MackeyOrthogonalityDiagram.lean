import MackeyDiagrams
import Proofs.MackeyInclusionAndProjectionCrossings
import Proofs.MackeySummandProjection
import Proofs.MackeyIdentityDiagram
import Proofs.SurvivingCosetRepresentative

set_option maxHeartbeats 2000000

namespace MackeyOrthogonalityProof

open MackeyDiagrams

private theorem vertical_eval {U : Type u} [Group U] {K H : Subgroup U}
    {p q t : Word K H}
    {f : LabelledDrawing Complex p q} {g : LabelledDrawing Complex q t}
    {f' : LabelledDrawing Complex p q} {g' : LabelledDrawing Complex q t}
    (hf : f.interpret.eval = f'.interpret.eval)
    (hg : g.interpret.eval = g'.interpret.eval) :
    (LabelledDrawing.vertical f g).interpret.eval =
      (LabelledDrawing.vertical f' g').interpret.eval := by
  change f.interpret.eval.vertical g.interpret.eval =
    f'.interpret.eval.vertical g'.interpret.eval
  rw [hf, hg]

end MackeyOrthogonalityProof

theorem MackeyOrthogonalityDiagram : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U),
  let Kα := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K
  let Hβ := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj β)) H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun k => hK ⟨(k : U), k.property, rfl⟩)
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun h => hH ⟨(h : U), h.property, rfl⟩)
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let L := fun j : J =>
        Kα ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H
      let C := fun j : J =>
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (β⁻¹ * (σ j : U)⁻¹))) (L j)
      ∀ (I : J → Type v) (hRep : ∀ j : J, I j → H)
        (_rightTransversal : ∀ (j : J) (h : H),
          ∃! u : I j, (h : U) * (hRep j u : U)⁻¹ ∈ C j),
        let l := fun j : J =>
          MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹
            (by
              intro ℓ
              obtain ⟨k, hk, h⟩ := ℓ.property.1
              change α * k * α⁻¹ = (ℓ : U) at h
              change k ∈ K at hk
              rw [← h]
              convert hk using 1
              group)
        let r := fun j : J =>
          let s := σ j
          MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
            (β⁻¹ * (s : U)⁻¹)
            (by
              intro ℓ
              obtain ⟨h, hh, e⟩ := ℓ.property.2
              change (s : U) * β * h * ((s : U) * β)⁻¹ = (ℓ : U) at e
              change h ∈ H at hh
              rw [← e]
              convert hh using 1
              group)
        let d := fun j : J =>
          let s := σ j
          show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (l j))
            (MackeyDiagrams.ConjEmbedding.comp b (r j)) from
            ⟨s, by
              intro ℓ
              apply Subtype.ext
              change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (s : U) =
                (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
                  (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
              group⟩
        let kg := MackeyDiagrams.Word.down a
        let gh := MackeyDiagrams.Word.up b
        let kl := fun j : J => MackeyDiagrams.Word.up (l j)
        let lh := fun j : J => MackeyDiagrams.Word.down (r j)
        let M := MackeyDiagrams.Word.tensor kg gh
        let Mj := fun j : J => MackeyDiagrams.Word.tensor (kl j) (lh j)
        let elementaryTensor := fun (j : J) (k : K) (h : H) =>
          Finsupp.single
            (MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis (kl j))
              (MackeyDiagrams.Word.basis (lh j)) k h) (1 : Complex)
        let surviving := fun (j : J) (g : G) =>
          {u : I j | α⁻¹ * (g : U) * β * (hRep j u : U)⁻¹ * β⁻¹ * (σ j : U)⁻¹ * α ∈ K}
        let leftMiddle := fun j : J =>
          MackeyDiagrams.Word.up (MackeyDiagrams.ConjEmbedding.comp a (l j))
        let expandedInclusion : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex (Mj j) M :=
          fun j =>
            MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.horizontal
                (MackeyDiagrams.LabelledDrawing.trivalent
                  (MackeyDiagrams.TrivalentVertex.upToDownUp a (l j)))
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (lh j))))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.ordinary
                  (MackeyDiagrams.Diagram.associate kg (leftMiddle j) (lh j)))
                (MackeyDiagrams.LabelledDrawing.vertical
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                    (MackeyDiagrams.LabelledDrawing.horizontal
                      (MackeyDiagrams.DotLabel.upDrawing (R := Complex) (Finsupp.single (d j) 1))
                      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (lh j)))))
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                    (MackeyDiagrams.LabelledDrawing.trivalent
                      (MackeyDiagrams.TrivalentVertex.upDownToUp b (r j))))))
        let finiteProjection := fun (j : J)
            (hi : Subgroup.FiniteIndex (MackeyDiagrams.ConjEmbedding.toHom (r j)).range) =>
          show MackeyDiagrams.LabelledDrawing Complex M (Mj j) from
            MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.horizontal
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                (MackeyDiagrams.LabelledDrawing.trivalent
                  (MackeyDiagrams.TrivalentVertex.upToUpDown b (r j) hi)))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.horizontal
                  (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id kg))
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.DotLabel.upDrawing (R := Complex)
                      (Finsupp.single (MackeyDiagrams.Dot.inverse (d j)) 1))
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (lh j)))))
                (MackeyDiagrams.LabelledDrawing.vertical
                  (MackeyDiagrams.LabelledDrawing.ordinary
                    (MackeyDiagrams.Diagram.unassociate kg (leftMiddle j) (lh j)))
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.trivalent
                      (MackeyDiagrams.TrivalentVertex.downUpToUp a (l j)))
                    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (lh j))))))
        let cupContribution := fun (j : J) (z : (MackeyDiagrams.Word.basis M).carrier)
            (u : I j) =>
          MackeyDiagrams.RightCupTrace.term
            (MackeyDiagrams.Diagram.mixedProjectionTail (R := Complex) a b (l j) (r j) (d j))
            z (MackeyDiagrams.RightCupTrace.unitPair (r j) (hRep j u))
        ∃ (hf : ∀ (j : J) (z : (MackeyDiagrams.Word.basis M).carrier),
            Set.Finite {w |
              MackeyDiagrams.Generator.mixedMultiplicationBasis a b (l j) (r j) (d j) w = z})
          (transversalFinite : ∀ (j : J) (z : (MackeyDiagrams.Word.basis M).carrier),
            Set.Finite (Function.support (cupContribution j z))),
          let inclusion : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex (Mj j) M :=
            fun j => MackeyDiagrams.LabelledDrawing.mixedMultiplication a b (l j) (r j) [(1, d j)]
          let projectionLabel : ∀ j : J, List (Complex × MackeyDiagrams.ProjectionDot.Mixed a b (l j) (r j)) :=
            fun j => [(1, ⟨d j, hf j⟩)]
          let projection : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex M (Mj j) :=
            fun j => MackeyDiagrams.LabelledDrawing.compactProjection a b (l j) (r j) (projectionLabel j)
          let expandedProjection : ∀ j : J, MackeyDiagrams.LabelledDrawing Complex M (Mj j) :=
            fun j => MackeyDiagrams.LabelledDrawing.expandedProjection a b (l j) (r j) (projectionLabel j)
              MackeyDiagrams.ProjectionOpening.junction MackeyDiagrams.ProjectionClosing.junction
          let reverseCrossings := fun i j : J =>
            MackeyDiagrams.LabelledDrawing.vertical (inclusion i) (projection j)
          let expandedReverse := fun i j : J =>
            MackeyDiagrams.LabelledDrawing.vertical (expandedInclusion i) (expandedProjection j)
          let evaluate := fun {p q : MackeyDiagrams.Word K H}
              (diagram : MackeyDiagrams.LabelledDrawing Complex p q) =>
            MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret diagram)
          let term := fun (x : (MackeyDiagrams.Word.basis M).carrier →₀ Complex) (j : J) =>
            MackeyDiagrams.Biset.Hom.toLinearMap
              (evaluate (MackeyDiagrams.LabelledDrawing.vertical (projection j) (inclusion j))) x
          let straight : MackeyDiagrams.LabelledDrawing Complex M M :=
            MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id M)
          (∃ finite : ∀ x, Set.Finite (Function.support (term x)),
            ∀ x, MackeyDiagrams.Biset.Hom.toLinearMap (evaluate straight) x =
              Finset.sum (Set.Finite.toFinset (finite x)) (term x)) ∧
          (∀ j : J, evaluate (reverseCrossings j j) =
            evaluate (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (Mj j)))) ∧
          (∀ (i j : J), i ≠ j →
            evaluate (reverseCrossings i j) =
              evaluate (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero (Mj i) (Mj j)))) ∧
          (∀ (i j : J), evaluate (reverseCrossings i j) = evaluate (expandedReverse i j)) ∧
          (∀ j : J, evaluate (projection j) = evaluate (expandedProjection j)) ∧
          (∀ (j : J) (z : (MackeyDiagrams.Word.basis M).carrier),
            Function.support (cupContribution j z) =
              surviving j (MackeyDiagrams.Generator.mixedProduct a b z) ∧
            MackeyDiagrams.Biset.Hom.toLinearMap (evaluate (expandedProjection j))
                (Finsupp.single z 1) =
              Finset.sum (Set.Finite.toFinset (transversalFinite j z)) (cupContribution j z)) ∧
          (∀ (i j : J)
              (hi : Subgroup.FiniteIndex (MackeyDiagrams.ConjEmbedding.toHom (r j)).range),
            evaluate (reverseCrossings i j) = evaluate
              (MackeyDiagrams.LabelledDrawing.vertical (expandedInclusion i) (finiteProjection j hi))) ∧
          (∀ (j : J) (k : K) (h : H),
            let s := σ j
            let g := MackeyDiagrams.ConjEmbedding.toHom a k * s *
              MackeyDiagrams.ConjEmbedding.toHom b h
            ∃ u : I j,
              let ellValue := (s : U) * β * (h : U) * (hRep j u : U)⁻¹ * β⁻¹ * (s : U)⁻¹
              u ∈ surviving j g ∧ (∀ t ∈ surviving j g, t = u) ∧
              ∃ hℓ : ellValue ∈ L j,
                let ℓ : L j := ⟨ellValue, hℓ⟩
                let image := MackeyDiagrams.Biset.Hom.toLinearMap
                  (evaluate (reverseCrossings j j)) (elementaryTensor j k h)
                image = elementaryTensor j (k * MackeyDiagrams.ConjEmbedding.toHom (l j) ℓ) (hRep j u) ∧
                elementaryTensor j (k * MackeyDiagrams.ConjEmbedding.toHom (l j) ℓ) (hRep j u) =
                  elementaryTensor j k (MackeyDiagrams.ConjEmbedding.toHom (r j) ℓ * hRep j u) ∧
                elementaryTensor j k (MackeyDiagrams.ConjEmbedding.toHom (r j) ℓ * hRep j u) = elementaryTensor j k h)
) :=
(by
  classical
  intro U _ K H G α β Kα Hβ hK hH a b A B J σ hσ L C I hRep hTrans l r d
    kg gh kl lh M Mj elementaryTensor surviving leftMiddle expandedInclusion finiteProjection
    cupContribution
  /- Ian Xiao, § 2.2, Theorem 2.2 and Lemma 2.3. Equations (2.3) and
     (2.6) are on pp. 5 and 7 of the archived original PDF and pp. 7
     and 9 of the revised published PDF, respectively. The reverse
     composite is below (2.6) in both copies and is diagram-07 on the
     Alphabeta Math article. Its proof is unnumbered prose with numbered
     equations. The lower inclusion carries σᵢ and the upper projection
     carries σⱼ⁻¹. Both marks use coefficient-one labels in the shared
     finite complex dot language.
     See https://getcurious.cc/articles/math-bimodule-string-diagrams#eq:second-chain
     and https://getcurious.cc/downloads/mackey-bimodules.pdf. -/
  -- Equation (2.3) uses the indicated partition of G. The ordinary identity
  -- supplier proves pointwise finiteness and both reverse-order identities
  -- for the exact intersections (2.2) and representative family (2.1).
  obtain ⟨hf, hglobal, hdiag, hoff⟩ := MackeyIdentityDiagram K H G α β hK hH σ hσ
  let ordinaryInc (j : J) : MackeyDiagrams.Diagram Complex (Mj j) M :=
    .mixedMultiplication a b (l j) (r j) (d j)
  let ordinaryProj (j : J) : MackeyDiagrams.Diagram Complex M (Mj j) :=
    .mixedProjection a b (l j) (r j) (d j) (hf j)
  let traceArg (j : J) (g : G) (i : I j) : U :=
    α⁻¹ * (g : U) * β * (hRep j i : U)⁻¹ * β⁻¹ * (σ j : U)⁻¹ * α
  have crossing (j : J) : ∃ hs : ∀ g : G, Set.Finite (surviving j g),
      (∀ z : M.basis.carrier, Function.support (cupContribution j z) =
        surviving j (MackeyDiagrams.Generator.mixedProduct a b z)) ∧
      (∀ (k : K) (h : H), (ordinaryInc j).eval.toLinearMap (elementaryTensor j k h) =
        Finsupp.single (MackeyDiagrams.Generator.mixedPair a b (a.toHom k * σ j * b.toHom h)) 1) ∧
      (∀ g : G, (ordinaryProj j).eval.toLinearMap
        (Finsupp.single (MackeyDiagrams.Generator.mixedPair a b g) 1) =
          ∑ i ∈ (hs g).toFinset.attach,
            elementaryTensor j
              ⟨traceArg j g i.val, (hs g).mem_toFinset.mp i.property⟩ (hRep j i.val)) := by
    -- The crossing supplier uses the very same indexed transversal (2.4).
    obtain ⟨hf', hs, hsupport, hι, hp, _, _, _⟩ :=
      MackeyInclusionAndProjectionCrossings K H G α β hK hH σ hσ I hRep hTrans j
    have hι' := MackeyCrossingProof.compact_inclusion a b (l j) (r j) (d j)
    have hp' := MackeyCrossingProof.compact_projection a b (l j) (r j) (d j) hf'
    refine ⟨hs, hsupport, ?_, ?_⟩
    · intro k h
      exact (congrArg (fun f => f.toLinearMap (elementaryTensor j k h)) hι').symm.trans (hι k h)
    · intro g
      exact (congrArg (fun f => f.toLinearMap
        (Finsupp.single (MackeyDiagrams.Generator.mixedPair a b g) 1)) hp').symm.trans (hp g).2
  choose hs hsupport hι hp using crossing
  have hfinite (j : J) (z : M.basis.carrier) :
      Set.Finite (Function.support (cupContribution j z)) :=
    (hsupport j z).symm ▸ hs j (MackeyDiagrams.Generator.mixedProduct a b z)
  refine ⟨hf, hfinite, ?_⟩
  intro inclusion projectionLabel projection expandedProjection reverseCrossings expandedReverse
    evaluate term straight
  have hinc (j : J) : evaluate (inclusion j) = (ordinaryInc j).eval :=
    MackeyCrossingProof.compact_inclusion a b (l j) (r j) (d j)
  have hproj (j : J) : evaluate (projection j) = (ordinaryProj j).eval :=
    MackeyCrossingProof.compact_projection a b (l j) (r j) (d j) (hf j)
  have hExpandedInc (j : J) : evaluate (inclusion j) = evaluate (expandedInclusion j) :=
    (hinc j).trans (MackeyCrossingProof.eval_inclusion_expansion a b (l j) (r j) (d j)).symm
  have hExpandedProj (j : J) : evaluate (projection j) = evaluate (expandedProjection j) :=
    (MackeyDiagrams.LabelledDrawing.eval_expandProjection a b (l j) (r j)
      (projectionLabel j) .junction .junction).symm
  have hReverse (i j : J) : evaluate (reverseCrossings i j) =
      (ordinaryInc i).eval.vertical (ordinaryProj j).eval := by
    change (evaluate (inclusion i)).vertical (evaluate (projection j)) = _
    rw [hinc, hproj]
  refine ⟨?_, ?_, ?_, ?_, hExpandedProj, ?_, ?_, ?_⟩
  · -- MackeySummandProjection proves the fixed-j formula (2.5).
    -- Here MackeyIdentityDiagram directly supplies the pointwise sum
    -- in (2.3) with its support, using the same double-coset partition.
    let ordinaryTerm (x : M.basis.carrier →₀ Complex) (j : J) :=
      ((ordinaryProj j).eval.vertical (ordinaryInc j).eval).toLinearMap x
    have hterm (x : M.basis.carrier →₀ Complex) : term x = ordinaryTerm x := by
      funext j
      change ((evaluate (projection j)).vertical (evaluate (inclusion j))).toLinearMap x = _
      rw [hproj, hinc]
    let ordinaryStraight : MackeyDiagrams.Diagram Complex M M :=
      .horizontal (.id kg) (.id gh)
    have hstraight : ordinaryStraight.eval = evaluate straight :=
      MackeyDiagrams.Biset.Hom.horizontal_id kg.basis gh.basis
    change ∃ fin : ∀ x, Set.Finite (Function.support (ordinaryTerm x)),
      ∀ x, ordinaryStraight.eval.toLinearMap x = ∑ j ∈ (fin x).toFinset, ordinaryTerm x j
      at hglobal
    obtain ⟨finite, hsum⟩ := hglobal
    let finite' (x : M.basis.carrier →₀ Complex) : Set.Finite (Function.support (term x)) :=
      (hterm x).symm ▸ finite x
    refine ⟨finite', fun x => ?_⟩
    have hindices : (finite x).toFinset = (finite' x).toFinset := by
      ext j
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hterm]
    calc
      _ = ordinaryStraight.eval.toLinearMap x :=
        congrArg (fun f => f.toLinearMap x) hstraight.symm
      _ = ∑ j ∈ (finite x).toFinset, ordinaryTerm x j := hsum x
      _ = _ := by
        rw [hindices]
        exact congrArg ((finite' x).toFinset.sum) (hterm x).symm
  · intro j
    exact (hReverse j j).trans (hdiag j)
  · intro i j hij
    exact (hReverse i j).trans (hoff i j hij)
  · intro i j
    exact MackeyOrthogonalityProof.vertical_eval (hExpandedInc i) (hExpandedProj j)
  · -- The reverse cup is evaluated on surviving indices at this input.
    -- This is the termwise trace described after (2.4) when the index
    -- can be infinite. The typed junction frame evaluates that composite.
    -- Normalize the input and identify each attached summand with its
    -- trace term using the test in Lemma 2.3.
    intro j z
    refine ⟨hsupport j z, ?_⟩
    let g := MackeyDiagrams.Generator.mixedProduct a b z
    have hz : MackeyDiagrams.Generator.mixedPair a b g = z :=
      MackeyDiagrams.Generator.mixedPair_mixedProduct a b z
    have hindices : (hs j g).toFinset = (hfinite j z).toFinset := by
      ext i
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hsupport]
    rw [← hExpandedProj, hproj]
    calc
      _ = ∑ i ∈ (hs j g).toFinset.attach,
          elementaryTensor j ⟨traceArg j g i.val, (hs j g).mem_toFinset.mp i.property⟩
            (hRep j i.val) := by simpa only [hz] using hp j g
      _ = ∑ i ∈ (hs j g).toFinset.attach, cupContribution j z i.val := by
        apply Finset.sum_congr rfl
        intro i _
        let k : K := ⟨traceArg j g i.val, (hs j g).mem_toFinset.mp i.property⟩
        have ht : a.toHom k = g * (b.toHom (hRep j i.val)⁻¹ * (d j).element⁻¹) :=
          (MackeyCrossingProof.trace_eq_iff a b (l j) (r j) (d j) α β
            (fun _ => rfl) (fun _ => rfl) g (hRep j i.val) k).mpr rfl
        have ht' := MackeyDiagrams.RightCupTrace.projectionTerm_image (R := Complex)
          a b (l j) (r j) (d j) g (hRep j i.val) k ht
        change _ = MackeyDiagrams.RightCupTrace.term
          (MackeyDiagrams.Diagram.mixedProjectionTail (R := Complex) a b (l j) (r j) (d j))
          z (MackeyDiagrams.RightCupTrace.unitPair (r j) (hRep j i.val))
        rw [← hz, ht']
      _ = _ := by rw [Finset.sum_attach, hindices]
  · -- The separate ordinary trivalent expansion requires the supplied
    -- finite index of the image of the right embedding.
    intro i j hi
    have hFiniteProj : evaluate (projection j) = evaluate (finiteProjection j hi) :=
      (hproj j).trans (MackeyCrossingProof.eval_finite_expansion
        a b (l j) (r j) (d j) hi (hf j)).symm
    exact MackeyOrthogonalityProof.vertical_eval (hExpandedInc i) hFiniteProj
  · -- In (2.6), use the actual representative of the right coset of h.
    -- Conjugation returns its correction to L j, and balancing moves it
    -- between the two tensor factors.
    intro j k h s g
    obtain ⟨u, hu, _⟩ := hTrans j h
    obtain ⟨ell, hell, he⟩ := hu
    let ellValue := (s : U) * β * (h : U) * (hRep j u : U)⁻¹ * β⁻¹ * (s : U)⁻¹
    change (β⁻¹ * (s : U)⁻¹) * ell * (β⁻¹ * (s : U)⁻¹)⁻¹ =
      (h : U) * (hRep j u : U)⁻¹ at he
    have heq : ellValue = ell := by
      calc
        ellValue = (s : U) * β * ((h : U) * (hRep j u : U)⁻¹) * β⁻¹ * (s : U)⁻¹ := by
          dsimp only [ellValue]
          group
        _ = ell := by
          rw [← he]
          group
    have hℓ : ellValue ∈ L j := heq.symm ▸ hell
    let ℓ : L j := ⟨ellValue, hℓ⟩
    have hright : (r j).toHom ℓ * hRep j u = h := by
      apply Subtype.ext
      change (β⁻¹ * (s : U)⁻¹) * ellValue * (β⁻¹ * (s : U)⁻¹)⁻¹ * (hRep j u : U) = (h : U)
      dsimp only [ellValue]
      group
    have hleft : (↑(k * (l j).toHom ℓ) : U) = traceArg j g u := by
      change (k : U) * (α⁻¹ * ellValue * (α⁻¹)⁻¹) =
        α⁻¹ * ((α * (k : U) * α⁻¹) * (s : U) * (β * (h : U) * β⁻¹)) *
          β * (hRep j u : U)⁻¹ * β⁻¹ * (s : U)⁻¹ * α
      dsimp only [ellValue]
      group
    have huSurv : u ∈ surviving j g := by
      change traceArg j g u ∈ K
      rw [← hleft]
      exact (k * (l j).toHom ℓ).property
    have hclass : DoubleCoset.mk A B g = j := by
      have h : DoubleCoset.mk A B s = DoubleCoset.mk A B g :=
        DoubleCoset.eq.mpr ⟨a.toHom k, ⟨k, k.property, rfl⟩,
          b.toHom h, ⟨h, h.property, rfl⟩, rfl⟩
      exact h.symm.trans (hσ j)
    obtain ⟨i, _, hi⟩ :=
      (SurvivingCosetRepresentative K H G α β hK hH σ hσ I hRep hTrans j g).1 hclass
    have hunique (t : I j) (ht : t ∈ surviving j g) : t = u :=
      (hi t ht).trans (hi u huSurv).symm
    refine ⟨u, huSurv, hunique, hℓ, ?_, ?_, congrArg (elementaryTensor j k) hright⟩
    · have hsingle : (ordinaryProj j).eval.toLinearMap
          (Finsupp.single (MackeyDiagrams.Generator.mixedPair a b g) 1) =
            elementaryTensor j (k * (l j).toHom ℓ) (hRep j u) := by
        let indices := (hs j g).toFinset
        let lift (t : {t // t ∈ indices}) :=
          elementaryTensor j ⟨traceArg j g t.val, (hs j g).mem_toFinset.mp t.property⟩ (hRep j t.val)
        let picked : {t // t ∈ indices} := ⟨u, (hs j g).mem_toFinset.mpr huSurv⟩
        have honly : indices.attach = {picked} := by
          ext t
          simp only [Finset.mem_attach, Finset.mem_singleton, true_iff]
          exact Subtype.ext (hunique t.val ((hs j g).mem_toFinset.mp t.property))
        calc
          _ = ∑ t ∈ indices.attach, lift t := hp j g
          _ = lift picked := by rw [honly, Finset.sum_singleton]
          _ = _ := by
            change elementaryTensor j ⟨traceArg j g u, _⟩ (hRep j u) = _
            rw [show (⟨traceArg j g u, (hs j g).mem_toFinset.mp picked.property⟩ : K) =
              k * (l j).toHom ℓ from Subtype.ext hleft.symm]
      rw [hReverse]
      change (ordinaryProj j).eval.toLinearMap
        ((ordinaryInc j).eval.toLinearMap (elementaryTensor j k h)) = _
      rw [hι, hsingle]
    · change Finsupp.single ((kl j).basis.pair (lh j).basis
          (k * (l j).toHom ℓ) (hRep j u)) (1 : Complex) =
        Finsupp.single ((kl j).basis.pair (lh j).basis
          k ((r j).toHom ℓ * hRep j u)) 1
      apply congrArg (fun z => Finsupp.single z (1 : Complex))
      have hb := MackeyDiagrams.Biset.pair_balance (kl j).basis (lh j).basis ℓ k (hRep j u)
      change (kl j).basis.pair (lh j).basis
          (1 * k * ((l j).toHom ℓ⁻¹)⁻¹) (hRep j u) =
        (kl j).basis.pair (lh j).basis k ((r j).toHom ℓ * hRep j u * (1 : H)⁻¹) at hb
      simpa only [one_mul, map_inv, inv_inv, inv_one, mul_one] using hb)
