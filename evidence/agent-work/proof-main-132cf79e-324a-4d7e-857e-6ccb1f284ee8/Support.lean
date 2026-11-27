namespace ParabolicCurlTowerProof

open MackeyDiagrams

universe u

variable {U : Type u} [Group U]

private noncomputable def inclusion : ∀ {A B : Subgroup U}, A ≤ B → MackeyDiagrams.ConjEmbedding A B :=
  fun h => ⟨Subgroup.inclusion h, ⟨1, fun x => by
    simp only [Subgroup.coe_inclusion, one_mul, inv_one, mul_one]⟩⟩
private abbrev curlPair : ∀ {A B : Subgroup U}, MackeyDiagrams.ConjEmbedding A B → Type u :=
  fun a =>
    MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up a) ×
    MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.down a) (MackeyDiagrams.Word.down a)
private noncomputable def straightPair : ∀ {A B : Subgroup U} (a : MackeyDiagrams.ConjEmbedding A B), curlPair a :=
  fun a =>
    (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up a)),
     MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down a)))
private noncomputable def indexedCurls :
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
private noncomputable abbrev eval {K H : Subgroup U} {p q : Word K H}
    (d : LabelledDrawing Complex p q) :=
  d.interpret.eval

private abbrev curlEval {B G : Subgroup U} (a : ConjEmbedding B G)
    (p : curlPair a) (c : Complex) : Prop :=
  eval p.1 = (eval (straightPair a).1).scale c ∧
  eval p.2 = (eval (straightPair a).2).scale c

-- Theorem 4.1 is supplied for conjugators. Resolve a representative
-- of each embedding and transport along equality of the homomorphisms.
private theorem direct_eval {K H G : Subgroup U} (a : ConjEmbedding H G)
    (d : ConjEmbedding K H) (f : Subgroup.FiniteIndex d.toHom.range) :
    curlEval a (indexedCurls a d f none) (d.toHom.range.index : Complex) := by
  obtain ⟨α, hα⟩ := a.hasRepresentative
  obtain ⟨δ, hδ⟩ := d.hasRepresentative
  let ha : ∀ x : H, α * (x : U) * α⁻¹ ∈ G := fun x => hα x ▸ (a.toHom x).property
  let hd : ∀ x : K, δ * (x : U) * δ⁻¹ ∈ H := fun x => hδ x ▸ (d.toHom x).property
  have ea : a = ConjEmbedding.ofConjugator α ha :=
    ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (hα x))
  have ed : d = ConjEmbedding.ofConjugator δ hd :=
    ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (hδ x))
  clear_value ha hd
  clear hα hδ
  subst a
  subst d
  obtain ⟨up, _, _, down⟩ := ReidemeisterOne K H G δ α hd ha
  exact ⟨up f, down f⟩

private theorem hom_scale_mul {K H : Type u} [Group K] [Group H]
    {F B : Biset K H} (f : Biset.Hom Complex F B) (r s : Complex) :
    (f.scale r).scale s = f.scale (r * s) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change s • (r • f.toLinearMap x) = (r * s) • f.toLinearMap x
  rw [smul_smul, mul_comm s r]

-- The paper groups summands by two stages of coset representatives.
-- The checked direct curl and bilinearity on the balanced biset give
-- the same calculation at the two typed nested boundaries.
private theorem step_eval {K H G : Subgroup U} (a : ConjEmbedding H G)
    (d : ConjEmbedding K H) (f : Subgroup.FiniteIndex d.toHom.range)
    (p : curlPair (a.comp d)) (c : Complex) (hp : curlEval (a.comp d) p c) :
    curlEval a (indexedCurls a d f (some p)) (c * (d.toHom.range.index : Complex)) := by
  have dir := direct_eval a d f
  obtain ⟨pu, pd⟩ := hp
  obtain ⟨du, dd⟩ := dir
  -- For the upward bend, the inner up map is the left tensor factor.
  -- For the downward bend, the inner down map is the right factor.
  constructor
  · let opening := eval (.trivalent (TrivalentVertex.upToUpDown a d f))
    let closing := eval (.trivalent (TrivalentVertex.upDownToUp a d))
    let ix : Complex := d.toHom.range.index
    let idUp := Biset.Hom.id (R := Complex) (Word.up (a.comp d)).basis
    let idDown := Biset.Hom.id (R := Complex) (Word.down d).basis
    let idOuter := Biset.Hom.id (R := Complex) (Word.up a).basis
    change eval p.1 = idUp.scale c at pu
    change opening.vertical closing = idOuter.scale ix at du
    change opening.vertical (((eval p.1).horizontal idDown).vertical closing) =
      idOuter.scale (c * ix)
    rw [pu, Biset.Hom.horizontal_scale_left, Biset.Hom.horizontal_id,
      Biset.Hom.vertical_scale_left, Biset.Hom.id_vertical, Biset.Hom.vertical_scale_right,
      du, hom_scale_mul, mul_comm ix c]
  · let opening := eval (.trivalent (TrivalentVertex.downToUpDown a d f))
    let closing := eval (.trivalent (TrivalentVertex.upDownToDown a d))
    let ix : Complex := d.toHom.range.index
    let idUp := Biset.Hom.id (R := Complex) (Word.up d).basis
    let idDown := Biset.Hom.id (R := Complex) (Word.down (a.comp d)).basis
    let idOuter := Biset.Hom.id (R := Complex) (Word.down a).basis
    change eval p.2 = idDown.scale c at pd
    change opening.vertical closing = idOuter.scale ix at dd
    change opening.vertical ((idUp.horizontal (eval p.2)).vertical closing) =
      idOuter.scale (c * ix)
    rw [pd, Biset.Hom.horizontal_scale_right, Biset.Hom.horizontal_id,
      Biset.Hom.vertical_scale_left, Biset.Hom.id_vertical, Biset.Hom.vertical_scale_right,
      dd, hom_scale_mul, mul_comm ix c]

-- Alphabeta Math's finite index tower, Steps 1.1, 2.1 and 3.1, applies
-- Lagrange's theorem to all three inclusions, substitutes and cancels
-- the order of the smallest subgroup. Here relative-index multiplicativity
-- uses the same tower and requires only the two given inclusions. The
-- nonzero total index supplies finite index at both links for the reverse cups.
-- https://alphabetamath.cc/item/cor-index-tower-finite
-- Xiao counts products of right coset representatives. Bilinearity of the
-- balanced product evaluates the two nested drawings by extracting the
-- inner scalar, while the index tower supplies the count.
private theorem tower_eval {A B H G : Subgroup U} (a : ConjEmbedding H G)
    (hAB : A ≤ B) (hBH : B ≤ H) (index : Nat)
    (hIndex : A.relIndex H = index) (hNonzero : index ≠ 0) :
    let eAH := inclusion (hAB.trans hBH)
    let eAB := inclusion hAB
    let eBH := inclusion hBH
    ∃ (fAH : Subgroup.FiniteIndex eAH.toHom.range)
      (fAB : Subgroup.FiniteIndex eAB.toHom.range)
      (fBH : Subgroup.FiniteIndex eBH.toHom.range),
      let direct := indexedCurls a eAH fAH none
      let inner := indexedCurls (a.comp eBH) eAB fAB none
      let outer := indexedCurls a eBH fBH (some inner)
      let scalar := B.relIndex H * A.relIndex B
      scalar = index ∧
      curlEval a direct (scalar : Complex) ∧
      eval direct.1 = eval outer.1 ∧ eval direct.2 = eval outer.2 := by
  intro eAH eAB eBH
  have iAH : eAH.toHom.range.index = A.relIndex H :=
    congrArg Subgroup.index (Subgroup.inclusion_range (hAB.trans hBH))
  have iAB : eAB.toHom.range.index = A.relIndex B :=
    congrArg Subgroup.index (Subgroup.inclusion_range hAB)
  have iBH : eBH.toHom.range.index = B.relIndex H :=
    congrArg Subgroup.index (Subgroup.inclusion_range hBH)
  have tower := (Subgroup.relIndex_mul_relIndex A B H hAB hBH).trans hIndex
  have product : eAB.toHom.range.index * eBH.toHom.range.index = index :=
    (congrArg₂ Nat.mul iAB iBH).trans tower
  have nz : eAB.toHom.range.index * eBH.toHom.range.index ≠ 0 :=
    product ▸ hNonzero
  let fAH : Subgroup.FiniteIndex eAH.toHom.range := ⟨(iAH.trans hIndex).symm ▸ hNonzero⟩
  let fAB : Subgroup.FiniteIndex eAB.toHom.range := ⟨(mul_ne_zero_iff.mp nz).1⟩
  let fBH : Subgroup.FiniteIndex eBH.toHom.range := ⟨(mul_ne_zero_iff.mp nz).2⟩
  refine ⟨fAH, fAB, fBH, ?_⟩
  intro direct inner outer scalar
  have hScalar : scalar = index := (Nat.mul_comm _ _).trans tower
  have hDirect : curlEval a direct (scalar : Complex) := by
    have hc : eAH.toHom.range.index = scalar := (iAH.trans hIndex).trans hScalar.symm
    simpa only [hc] using direct_eval a eAH fAH
  have hOuter : curlEval a outer (scalar : Complex) := by
    have hc : (eAB.toHom.range.index : Complex) * (eBH.toHom.range.index : Complex) =
        (scalar : Complex) := by
      exact_mod_cast product.trans hScalar.symm
    have hInner := direct_eval (a.comp eBH) eAB fAB
    simpa only [hc] using step_eval a eBH fBH inner _ hInner
  exact ⟨hScalar, hDirect, hDirect.1.trans hOuter.1.symm, hDirect.2.trans hOuter.2.symm⟩

end ParabolicCurlTowerProof
