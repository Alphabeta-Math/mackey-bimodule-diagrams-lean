by
  classical
  intro P Finitary conj conjugate blockSym forward backward Mod Res Ind
    K H G α β X g r c D A B hnD hnA hnB hdD hdA hdB hcD hcA hcB Kα Hβ
    hG hA hB hK hH left right Q rows cols row col Mat J rank αmap βmap
  -- Xiao, Theorem 7.4 (archived PDF p. 32, revised published PDF p. 34)
  -- uses Prop. 7.3 in each ambient block. The archived and revised PDFs
  -- have different checksums and pagination. No separate numbered
  -- Alphabeta Math proof is recorded for this endpoint.
  -- The product formula yields the refinements and quotient coordinates.
  have splitData := ProductParabolicDoubleCosets X g r c D A B hnD hnA hnB
    hdD hdA hdB hcD hcA hcB
  have hLeA : (iSup (fun a => blockSym (A a))) ≤ iSup (fun i => blockSym (D i)) :=
    hA ▸ hG ▸ hK
  have hLeB : (iSup (fun b => blockSym (B b))) ≤ iSup (fun i => blockSym (D i)) :=
    hB ▸ hG ▸ hH
  -- Transport the statement along the common ambient subgroup equality.
  obtain ⟨refA, refB, split, cosets, classes, _, _, split_val, _, cosets_mk,
    count, _, _, _, _, _, _⟩ := splitData hLeA hLeB
  subst G
  have partA (i : Fin g) := ParabolicMackeyAssembly.restrictedPartition D A hdD hnA hdA refA
    (fun i x hx => (hcA x).mp ((hcD x).mpr ⟨i, hx⟩)) i
  have partB (i : Fin g) := ParabolicMackeyAssembly.restrictedPartition D B hdD hnB hdB refB
    (fun i x hx => (hcB x).mp ((hcD x).mpr ⟨i, hx⟩)) i
  -- Prop. 7.3, steps 1 and 2: split rows and columns into ordered
  -- consecutive pieces and match corresponding pieces in order. The
  -- product supplier uses the identity in one-coset blocks (§7.3);
  -- Theorem 7.4 asks for the ordered matching even in those blocks.
  -- A row [0,1] and columns [1], [0] give one double coset, and
  -- the matching sends 1 to 0 and 0 to 1. Use the tableau section
  -- in all blocks to retain the endpoint's rank equations.
  have ordered (i : Fin g) := ParabolicDoubleCosetRepresentatives (D i)
    (rows i).card (cols i).card (row i) (col i)
    (partA i).1 (partB i).1 (partA i).2.1 (partB i).2.1 (partA i).2.2 (partB i).2.2
  choose localClass localCount localSection using ordered
  choose tableau tableau_class tableau_rank using localSection
  have class_eq (i : Fin g) : localClass i = classes i := by
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn' q (fun p => ?_)
    apply Subtype.ext
    funext a b
    exact (localCount i p a b).trans (count i p a b).symm
  have isA : left = Subgroup.comap (Subgroup.subtype _) (iSup (fun a => blockSym (A a))) :=
    congrArg (Subgroup.comap (Subgroup.subtype _)) hA
  have isB : right = Subgroup.comap (Subgroup.subtype _) (iSup (fun b => blockSym (B b))) :=
    congrArg (Subgroup.comap (Subgroup.subtype _)) hB
  -- Reindex with the coordinate classifications, transporting the quotient
  -- along equality of the ambient left and right subgroups.
  let qEquiv : Q ≃ _ := ParabolicMackeyAssembly.cosetCongr isA isB
  have q_mk s : qEquiv (DoubleCoset.mk left right s) = DoubleCoset.mk _ _ s :=
    ParabolicMackeyAssembly.cosetCongr_mk isA isB s
  let classify : Q ≃ J := (qEquiv.trans cosets).trans (Equiv.piCongrRight classes)
  let σ : J → _ := fun R => split.symm (fun i => tableau i (R i))
  have hsplit (R : J) (i : Fin g) : split (σ R) i = tableau i (R i) :=
    congrFun (split.apply_symm_apply _) i
  have hclass (s) (i : Fin g) :
      classify (DoubleCoset.mk left right s) i = classes i (cosets (DoubleCoset.mk _ _ s) i) :=
    congrArg (fun q => classes i (cosets q i)) (q_mk s)
  have hσ (R : J) : DoubleCoset.mk left right (σ R) = classify.symm R := by
    apply classify.injective
    rw [classify.apply_symm_apply]
    funext i
    rw [hclass, cosets_mk, hsplit, ← class_eq i, tableau_class]
    exact (localClass i).apply_symm_apply (R i)
  refine ⟨split, classify, σ, split_val, ?_, hσ, ?_, ?_⟩
  · intro s i a b
    rw [hclass, cosets_mk]
    exact count i (split s i) a b
  · intro R i a b x y
    rw [hsplit]
    exact tableau_rank i (R i) a b x y
  · intro L lambdaMap muMap
    have hDX (i : Fin g) : D i ⊆ X := fun _ hx => (hcD _).mpr ⟨i, hx⟩
    have preserve (s : ↥(iSup (fun i => blockSym (D i)))) (x : Nat) (hx : x ∈ X) :
        (s : P) x ∈ X := by
      obtain ⟨i, hi⟩ := (hcD x).mp hx
      let y : ↥(D i) := ⟨x, hi⟩
      have e := split_val s i y
      exact hDX i (e ▸ (split s i y).property)
    refine ⟨?_, ?_, ?_⟩
    · intro R
      let s := σ R
      have hs := ParabolicMackeyAssembly.productFinitary X D hDX (s : P) s.property
      have hsX (x : Nat) : x ∈ X ↔ (s : P) x ∈ X := by
        refine ⟨preserve s x, fun hx => ?_⟩
        have hh := preserve s⁻¹ ((s : P) x) hx
        change (s : P).symm ((s : P) x) ∈ X at hh
        simpa only [Equiv.symm_apply_apply] using hh
      change Kα ⊓ ParabolicMackeyAssembly.conjugate ((s : P) * (β : P)) H = _
      rw [ParabolicMackeyAssembly.conjugate_mul]
      change Kα ⊓ ParabolicMackeyAssembly.conjugate (s : P) Hβ = _
      rw [hA, hB]
      exact ParabolicMackeyAssembly.intersection X A B hnA hnB hdA hdB hcA hcB (s : P) hs hsX
    · exact ParabolicMackeyAssembly.mackeyIso K H _ (α : P) (β : P) hK hH classify σ hσ
    · intro hα hβ
      exact ParabolicMackeyAssembly.inclusionIso K H _ (α : P) (β : P) hK hH σ hα hβ
        (ParabolicMackeyAssembly.mackeyIso K H _ (α : P) (β : P) hK hH classify σ hσ)
