namespace SinglePairIdentitySupport

open MackeyDiagrams
universe u

private theorem fiber_clauses {U : Type u} [Group U]
    (K H G : Subgroup U) (α β : U)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G) :
  let conjSubgroup := fun (c : U) (S : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
  let Kα := conjSubgroup α K
  let eα := ConjEmbedding.ofConjugator α hα
  let eβ := ConjEmbedding.ofConjugator β hβ
  ∀ (A B : Subgroup G) (_ : A = eα.toHom.range) (_ : B = eβ.toHom.range),
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let orbit := fun j : J => DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
      let M := Word.tensor (Word.down eα) (Word.up eβ)
      let W := M.basis
      let eval := fun {bottom top : Word K H} (drawing : LabelledDrawing Complex bottom top) =>
        drawing.interpret.eval
      let crossingDot := fun {S : Subgroup U} (c d : U)
          (hc : ∀ ℓ : S, c * (ℓ : U) * c⁻¹ ∈ K)
          (hd : ∀ ℓ : S, d * (ℓ : U) * d⁻¹ ∈ H)
          (hs : (α * c) * (β * d)⁻¹ ∈ G) =>
        show Dot
          (ConjEmbedding.comp eα (ConjEmbedding.ofConjugator c hc))
          (ConjEmbedding.comp eβ (ConjEmbedding.ofConjugator d hd)) from
          Dot.ofRepresentatives (α * c) (β * d)
            (by
              intro ℓ
              change α * (c * (ℓ : U) * c⁻¹) * α⁻¹ = _
              simp only [mul_inv_rev, mul_assoc])
            (by
              intro ℓ
              change β * (d * (ℓ : U) * d⁻¹) * β⁻¹ = _
              simp only [mul_inv_rev, mul_assoc])
            hs
      ∀ (S : Subgroup U) (c d : U)
          (hc : ∀ ℓ : S, c * (ℓ : U) * c⁻¹ ∈ K)
          (hd : ∀ ℓ : S, d * (ℓ : U) * d⁻¹ ∈ H)
          (hs : (α * c) * (β * d)⁻¹ ∈ G),
        let ec := ConjEmbedding.ofConjugator c hc
        let ed := ConjEmbedding.ofConjugator d hd
        let δ := crossingDot c d hc hd hs
        let s := Dot.element δ
        let replyDot := Dot.inverse δ
        let ML := Word.tensor (Word.up ec) (Word.down ed)
        let j := DoubleCoset.mk A B s
        let Ls := Kα ⊓ conjSubgroup ((s : U) * β) H
        let finiteIndex := Subgroup.IsFiniteRelIndex (conjSubgroup (α * c) S) Ls
        let q := Generator.mixedMultiplicationBasis eα eβ ec ed δ
        let finiteFibers := ∀ z : W.carrier, Set.Finite {w | q w = z}
        let cupFinite := Subgroup.FiniteIndex (MonoidHom.range (ConjEmbedding.toHom ed))
        let isTransversal := fun T : Set H => ∀ h : H, ∃! t : H,
          t ∈ T ∧ h * t⁻¹ ∈ MonoidHom.range (ConjEmbedding.toHom ed)
        let traceArg := fun (g : G) (t : H) =>
          g * (ConjEmbedding.toHom eβ t)⁻¹ *
            (Dot.element replyDot)
        let survives := fun (T : Set H) (g : G) =>
          {t | t ∈ T ∧ traceArg g t ∈ MonoidHom.range (ConjEmbedding.toHom eα)}
        ((∀ h : H, Set.Finite {w | Generator.multiplicationCapBasis ed w = h}) ↔ cupFinite) ∧
        (finiteFibers ↔ finiteIndex) ∧
        (∀ (T : Set H), isTransversal T → ∀ g : G, g ∈ orbit j → ¬ finiteIndex →
          Set.Infinite (survives T g)) ∧
        (∀ hf : finiteFibers,
          let p : LabelledDrawing Complex M ML :=
            LabelledDrawing.expandedProjection eα eβ ec ed
              [(1, ⟨δ, hf⟩)] ProjectionOpening.cupAndMerge
              ProjectionClosing.splitAndTrace
          ∀ (T : Set H), isTransversal T → ∀ g : G,
            ∃ ht : Set.Finite (survives T g),
              Biset.Hom.toLinearMap (eval p)
                  (Finsupp.single (Generator.mixedPair eα eβ g) 1) =
                Finset.sum (Set.Finite.toFinset ht) (fun t =>
                  Biset.pairLinear Complex
                    (Biset.induction ec) (Biset.restriction ed)
                    (Generator.traceBasis Complex eα (traceArg g t))
                    (Finsupp.single t 1))) := by
  intro conjSubgroup Kα eα eβ A B hA hB
  subst A
  subst B
  intro J σ hσ orbit M W eval crossingDot S c d hc hd hs ec ed δ s replyDot
    ML j Ls finiteIndex q finiteFibers cupFinite isTransversal traceArg survives
  -- Proposition 5.1 and the surviving-trace convention on archive p. 16
  -- (published 28 November revision p. 18). The ordinary cup test uses
  -- the index in H. The trace-filtered crossing uses the relative index in Ls.
  -- Transport the original section along the range/comap equalities before
  -- applying the supplier, so its orbit is the one at the given representative.
  have fibers := MixedCrossingFiberMaps K H G S α β c d hα hβ hc hd hs σ hσ
  refine ⟨fibers.2.2.2.2.2.2.2.1, fibers.2.2.2.2.2.1, ?_, ?_⟩
  · exact fibers.2.2.2.2.2.2.2.2.1
  · intro hf p T hT g
    obtain ⟨ht, hcol⟩ := (fibers.2.2.2.2.2.2.2.2.2 hf).2 T hT g
    refine ⟨ht, ?_⟩
    -- The supplier computes the generator column. Evaluation of the
    -- specified opening and closing reduces to this same column.
    change (LabelledDrawing.expandedProjection eα eβ ec ed
      [(1, ⟨δ, hf⟩)] .cupAndMerge .splitAndTrace).interpret.eval.toLinearMap _ = _
    rw [LabelledDrawing.eval_expandProjection, MackeyCrossingProof.compact_projection]
    exact hcol

end SinglePairIdentitySupport
