import MackeyDiagrams
import Proofs.MixedCrossingsThroughSmallerGroup
import Proofs.MackeyIdentityDiagram
set_option maxHeartbeats 2000000
namespace CommonMackeyIntersectionSumAux

open MackeyDiagrams

noncomputable section

variable {U : Type*} [Group U] {K H G S : Subgroup U}

private def cupProjection (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding S K) (r : ConjEmbedding S H)
    (d : Dot (a.comp l) (b.comp r)) (hc : r.toHom.range.FiniteIndex) :
    Diagram Complex ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r)) :=
  let kg := Word.down a
  let gk := Word.up a
  let gh := Word.up b
  let kl := Word.up l
  let hl := Word.up r
  let lh := Word.down r
  let target := kl.tensor lh
  let insertCup := (Diagram.horizontal (.id kg) (.insertRightUnit gh)).vertical
    (Diagram.horizontal (.id kg) (Diagram.horizontal (.id gh) (.reverseCup r hc)))
  let rebracket := Diagram.horizontal (.id kg) (.unassociate gh hl lh)
  let insertDot := Diagram.horizontal (.id kg)
    (Diagram.horizontal ((Diagram.mergeUp b r).vertical
      ((Diagram.upDot d.inverse).vertical (Diagram.splitUp a l))) (.id lh))
  let prepareTrace := (Diagram.horizontal (.id kg) (.associate gk kl lh)).vertical
    (.unassociate kg gk target)
  let trace := (Diagram.horizontal (.traceCap a) (.id target)).vertical (.leftUnit target)
  insertCup.vertical (rebracket.vertical (insertDot.vertical (prepareTrace.vertical trace)))

private theorem insertRightUnit_single {A B : Subgroup U} (p : Word A B) (x : p.basis.carrier) :
    (Diagram.insertRightUnit (R := Complex) p).eval.toLinearMap (Finsupp.single x 1) =
      Finsupp.single (p.basis.pair (Biset.regular B) x 1) 1 := by
  change (Biset.insertRightUnit p.basis Complex).toLinearMap _ = _
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]

private theorem cupProjection_eval (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding S K) (r : ConjEmbedding S H)
    (d : Dot (a.comp l) (b.comp r)) (hc : r.toHom.range.FiniteIndex)
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (cupProjection a b l r d hc).eval = (Diagram.mixedProjection a b l r d hf).eval := by
  classical
  let kg := Word.down a
  let gk := Word.up a
  let gh := Word.up b
  let kl := Word.up l
  let hl := Word.up r
  let lh := Word.down r
  let M := kg.tensor gh
  let target := kl.tensor lh
  let C := reverseCupWord r
  let cup : Diagram Complex (.empty H) C := .reverseCup r hc
  let prep : Diagram Complex M (kg.tensor (gh.tensor C)) :=
    (Diagram.horizontal (.id kg) (.insertRightUnit gh)).vertical
      (Diagram.horizontal (.id kg) (Diagram.horizontal (.id gh) cup))
  let middle : Diagram Complex (gh.tensor hl) (gk.tensor kl) :=
    (Diagram.mergeUp b r).vertical ((Diagram.upDot d.inverse).vertical (Diagram.splitUp a l))
  let tail' : Diagram Complex (kg.tensor (gh.tensor C)) target :=
    (Diagram.horizontal (.id kg) (.unassociate gh hl lh)).vertical
      ((Diagram.horizontal (.id kg) (Diagram.horizontal middle (.id lh))).vertical
        (((Diagram.horizontal (.id kg) (.associate gk kl lh)).vertical
          (.unassociate kg gk target)).vertical
          ((Diagram.horizontal (.traceCap a) (.id target)).vertical (.leftUnit target))))
  let tail := Diagram.mixedProjectionTail (R := Complex) a b l r d
  let scope := RightCupTrace.ofFiniteAfter tail
    (RightCupTrace.mixedProjectionTail_finiteAfter (R := Complex) a b l r d hf)
  -- Proposition 5.1 uses the transfer through the surviving fiber. At
  -- finite right index the checked cup agrees with the scoped transfer.
  -- Compare the article's placement of the split and trace on each cup term.
  have hscope : scope.eval = (Diagram.mixedProjection a b l r d hf).eval :=
    ScopedDiagram.eval_expandedMixedProjection a b l r d hf
  rw [← hscope, RightCupTrace.eval_eq_reverseCup scope hc]
  apply Diagram.eval_ext_on_generators
  intro z
  refine Quotient.inductionOn z fun ⟨x, y⟩ => ?_
  let fiber := Generator.multiplicationCap_finiteFiber r hc (1 : H)
  have hcup : cup.eval.toLinearMap (Finsupp.single (1 : H) 1) =
      ∑ s ∈ fiber.toFinset, Finsupp.single s (1 : Complex) := by
    change (Generator.reverseCup Complex r hc).toLinearMap (Finsupp.single (1 : H) 1) = _
    rw [Generator.reverseCup, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]
  have hprep (x y : G) :
      prep.eval.toLinearMap (Finsupp.single (kg.basis.pair gh.basis x y) 1) =
        ∑ s ∈ fiber.toFinset,
          Finsupp.single (kg.basis.pair (gh.tensor C).basis x (gh.basis.pair C.basis y s)) 1 := by
    dsimp only [prep]
    rw [Diagram.eval_vertical_apply, Diagram.eval_horizontal_single, one_smul,
      Diagram.eval_id_apply, insertRightUnit_single, Biset.pairLinear_single, one_mul,
      Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
      Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
      hcup, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul]
  change tail'.eval.toLinearMap (prep.eval.toLinearMap
      (Finsupp.single (kg.basis.pair gh.basis x y) 1)) =
    tail.eval.toLinearMap ((Diagram.horizontal (.id M) cup).eval.toLinearMap
      ((Diagram.insertRightUnit M).eval.toLinearMap
        (Finsupp.single (kg.basis.pair gh.basis x y) 1)))
  rw [hprep, map_sum, insertRightUnit_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, hcup, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Biset.pairLinear_single, one_mul]
  refine Quotient.inductionOn s fun ⟨h₁, h₂⟩ => ?_
  change tail'.eval.toLinearMap
      (Finsupp.single (kg.basis.pair (gh.tensor C).basis x
        (gh.basis.pair C.basis y (hl.basis.pair lh.basis h₁ h₂))) 1) =
    tail.eval.toLinearMap (Finsupp.single (M.basis.pair C.basis
      (kg.basis.pair gh.basis x y) (hl.basis.pair lh.basis h₁ h₂)) 1)
  let v := y * b.toHom h₁ * d.element⁻¹
  have hmiddle : middle.eval.toLinearMap (Finsupp.single (gh.basis.pair hl.basis y h₁) 1) =
      Finsupp.single (gk.basis.pair kl.basis v 1) 1 := by
    dsimp only [middle]
    rw [Diagram.eval_vertical_apply, Diagram.eval_mergeUp_single, Diagram.eval_vertical_apply,
      Diagram.eval_upDot_single, Diagram.eval_splitUp_single]
    rfl
  rw [show tail.eval.toLinearMap (Finsupp.single (M.basis.pair C.basis
      (kg.basis.pair gh.basis x y) (hl.basis.pair lh.basis h₁ h₂)) 1) = _ from
    Diagram.eval_mixedProjectionTail_single a b l r d x y h₁ h₂]
  dsimp only [tail']
  simp only [Diagram.eval_vertical_apply]
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
    Diagram.eval_unassociate_single, Biset.pairLinear_single, one_mul,
    Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
    Diagram.eval_horizontal_single, one_smul, hmiddle, Diagram.eval_id_apply,
    Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul,
    Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
    Diagram.eval_associate_single, Biset.pairLinear_single, one_mul,
    Diagram.eval_unassociate_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_traceCap_single, one_smul, Diagram.eval_id_apply,
    Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply]
  by_cases himage : ∃ k, a.toHom k = x * v
  · obtain ⟨k, hk⟩ := himage
    rw [← hk, Generator.traceBasis_image, Diagram.eval_traceCapOnLeft_image a l x v k hk.symm,
      Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul,
      Diagram.eval_leftUnit_single]
    change Finsupp.single ((target.basis.act (k, 1)) (kl.basis.pair lh.basis 1 h₂)) 1 =
      Finsupp.single (kl.basis.pair lh.basis k h₂) 1
    congr 1
    simp [Biset.tensor, Biset.pair, Biset.induction, Biset.restriction]
  · rw [Generator.traceBasis_outside Complex a _ himage,
      Diagram.eval_traceCapOnLeft_outside a l x v himage, map_zero, LinearMap.zero_apply, map_zero,
      map_zero, LinearMap.zero_apply]

end

end CommonMackeyIntersectionSumAux


theorem CommonMackeyIntersectionSum : (
∀ {U : Type*} [Group U] (K H G : Subgroup U) (α β : U),
  let conjugate := fun (c : U) (S : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
  ∀ (hα : conjugate α K ≤ G) (hβ : conjugate β H ≤ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun k => hα ⟨(k : U), k.property, rfl⟩)
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun h => hβ ⟨(h : U), h.property, rfl⟩)
    let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
    let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b)
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let Lj := fun j : J => conjugate α K ⊓ conjugate ((σ j : U) * β) H
      let left := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := K) α⁻¹ (by
          intro ℓ
          obtain ⟨k, hk, heq⟩ := (hS ℓ.property).1
          change α * k * α⁻¹ = (ℓ : U) at heq
          rw [← heq]
          change k ∈ K at hk
          convert hk using 1
          group)
      let right := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := H) (β⁻¹ * (σ j : U)⁻¹) (by
          intro ℓ
          obtain ⟨h, hh, heq⟩ := (hS ℓ.property).2
          change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
          rw [← heq]
          change h ∈ H at hh
          convert hh using 1
          group)
      let dot := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (left j S hS))
          (MackeyDiagrams.ConjEmbedding.comp b (right j S hS)) from
          ⟨σ j, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (σ j : U) =
              (σ j : U) * (β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
      let kg := MackeyDiagrams.Word.down a
      let gk := MackeyDiagrams.Word.up a
      let gh := MackeyDiagrams.Word.up b
      let M := MackeyDiagrams.Word.tensor kg gh
      let inner := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (left j S hS)) (MackeyDiagrams.Word.down (right j S hS))
      let finiteFibers := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        ∀ z : (MackeyDiagrams.Word.basis M).carrier,
          Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b
            (left j S hS) (right j S hS) (dot j S hS) w = z}
      let inclusion := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        show MackeyDiagrams.Diagram Complex (inner j S hS) M from
          MackeyDiagrams.Diagram.mixedMultiplication a b (left j S hS) (right j S hS) (dot j S hS)
      let projection := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
          (hf : finiteFibers j S hS) =>
        show MackeyDiagrams.Diagram Complex M (inner j S hS) from
          MackeyDiagrams.Diagram.mixedProjection a b (left j S hS) (right j S hS) (dot j S hS) hf
      let outer := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
          (hf : finiteFibers j S hS) =>
        MackeyDiagrams.Diagram.vertical (projection j S hS hf) (inclusion j S hS)
      let full := fun j : J => le_refl (Lj j)
      let cupProjection := fun {S : Subgroup U} (l : MackeyDiagrams.ConjEmbedding S K)
          (r : MackeyDiagrams.ConjEmbedding S H)
          (d : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a l) (MackeyDiagrams.ConjEmbedding.comp b r))
          (hc : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom r))) =>
        let kl := MackeyDiagrams.Word.up l
        let hl := MackeyDiagrams.Word.up r
        let lh := MackeyDiagrams.Word.down r
        let target := MackeyDiagrams.Word.tensor kl lh
        let insertCup := MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg) (MackeyDiagrams.Diagram.insertRightUnit gh))
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg)
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id gh) (MackeyDiagrams.Diagram.reverseCup r hc)))
        let rebracket := MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg)
          (MackeyDiagrams.Diagram.unassociate gh hl lh)
        let insertDot := MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg)
          (MackeyDiagrams.Diagram.horizontal
            (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.mergeUp b r)
              (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.upDot (MackeyDiagrams.Dot.inverse d))
                (MackeyDiagrams.Diagram.splitUp a l)))
            (MackeyDiagrams.Diagram.id lh))
        let prepareTrace := MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id kg) (MackeyDiagrams.Diagram.associate gk kl lh))
          (MackeyDiagrams.Diagram.unassociate kg gk target)
        let trace := MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.traceCap a) (MackeyDiagrams.Diagram.id target))
          (MackeyDiagrams.Diagram.leftUnit target)
        show MackeyDiagrams.Diagram Complex M target from
          MackeyDiagrams.Diagram.vertical insertCup (MackeyDiagrams.Diagram.vertical rebracket
            (MackeyDiagrams.Diagram.vertical insertDot (MackeyDiagrams.Diagram.vertical prepareTrace trace)))
      (∀ (j : J) (S : Subgroup U) (hS : S ≤ Lj j), Subgroup.IsFiniteRelIndex S (Lj j) →
        ∃ (hf : finiteFibers j S hS) (hfJ : finiteFibers j (Lj j) (full j)),
          MackeyDiagrams.Diagram.eval (outer j S hS hf) =
            MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.scale (Subgroup.relIndex S (Lj j) : Complex)
              (outer j (Lj j) (full j) hfJ))) ∧
      (∀ (J₀ : Set J), Set.Nonempty J₀ →
        let I := {j : J // j ∈ J₀}
        let L := ⨅ j : I, Lj j.val
        let hL := fun j : I => iInf_le (fun i : I => Lj i.val) j
        (∀ i j : I, right i.val L (hL i) = right j.val L (hL j) ↔
          (σ i.val : U) * (σ j.val : U)⁻¹ ∈ Subgroup.centralizer (L : Set U)) ∧
        ((∀ j : I, Subgroup.IsFiniteRelIndex L (Lj j.val)) →
          ∃ (hfL : ∀ j : I, finiteFibers j.val L (hL j))
            (hfJ : ∀ j : I, finiteFibers j.val (Lj j.val) (full j.val)),
            let n := fun j : I => (Subgroup.relIndex L (Lj j.val) : Complex)
            let restricted := fun j : I => outer j.val L (hL j) (hfL j)
            let usual := fun j : I => outer j.val (Lj j.val) (full j.val) (hfJ j)
            let normalized := fun j : I => MackeyDiagrams.Diagram.scale (n j)⁻¹ (restricted j)
            let V := (MackeyDiagrams.Word.basis M).carrier →₀ Complex
            let term := fun (diagrams : I → MackeyDiagrams.Diagram Complex M M) (x : V) (j : I) =>
              MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval (diagrams j)) x
            (∀ j : I, MackeyDiagrams.Diagram.eval (normalized j) = MackeyDiagrams.Diagram.eval (usual j)) ∧
            (∀ (i j : I), i ≠ j →
              MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical
                (inclusion i.val L (hL i)) (projection j.val L (hL j) (hfL j))) =
              MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.zero (inner i.val L (hL i)) (inner j.val L (hL j)))) ∧
            (∀ z : (MackeyDiagrams.Word.basis M).carrier,
              let basis := Finsupp.single z (1 : Complex)
              let coset := DoubleCoset.mk A B (MackeyDiagrams.Generator.mixedProduct a b z)
              let selected := {j : I | j.val = coset}
              Function.support (term normalized basis) = selected ∧
              Function.support (term usual basis) = selected) ∧
            (∃ (finiteL : ∀ x : V, Set.Finite (Function.support (term normalized x)))
              (finiteJ : ∀ x : V, Set.Finite (Function.support (term usual x))),
              ∀ x : V,
                Finset.sum (Set.Finite.toFinset (finiteL x)) (term normalized x) =
                Finset.sum (Set.Finite.toFinset (finiteJ x)) (term usual x)) ∧
            (∀ (hJ₀ : Set.Finite J₀)
                (cupsL : ∀ j : I, Subgroup.FiniteIndex
                  (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (right j.val L (hL j)))))
                (cupsJ : ∀ j : I, Subgroup.FiniteIndex
                  (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom (right j.val (Lj j.val) (full j.val))))),
              let indices :=
                letI : Fintype I := Set.Finite.fintype hJ₀
                Finset.toList (Finset.univ : Finset I)
              let withCupL := fun j : I =>
                MackeyDiagrams.Diagram.scale (n j)⁻¹
                  (MackeyDiagrams.Diagram.vertical
                    (cupProjection (left j.val L (hL j)) (right j.val L (hL j))
                      (dot j.val L (hL j)) (cupsL j))
                    (inclusion j.val L (hL j)))
              let withCupJ := fun j : I =>
                let S := Lj j.val
                let hS := full j.val
                MackeyDiagrams.Diagram.vertical
                  (cupProjection (left j.val S hS) (right j.val S hS) (dot j.val S hS) (cupsJ j))
                  (inclusion j.val S hS)
              let sumDiagrams := fun (diagrams : I → MackeyDiagrams.Diagram Complex M M) =>
                List.foldr (fun j acc => MackeyDiagrams.Diagram.add (diagrams j) acc)
                  (MackeyDiagrams.Diagram.zero M M) indices
              MackeyDiagrams.Diagram.eval (sumDiagrams withCupL) = MackeyDiagrams.Diagram.eval (sumDiagrams withCupJ) ∧
              (∀ j : I, MackeyDiagrams.Diagram.eval (withCupL j) = MackeyDiagrams.Diagram.eval (normalized j) ∧
                MackeyDiagrams.Diagram.eval (withCupJ j) = MackeyDiagrams.Diagram.eval (usual j)))))
) :=
open MackeyDiagrams in
by
  classical
  intro U inst K H G α β conjugate hα hβ a b A B J σ hσ Lj left right dot
    kg gk gh M inner finiteFibers inclusion projection outer full cupProjection
  have hK (k : K) : α * (k : U) * α⁻¹ ∈ G := (a.toHom k).property
  have hH (h : H) : β * (h : U) * β⁻¹ ∈ G := (b.toHom h).property
  let f (j : J) (S : Subgroup U) (hS : S ≤ Lj j) :=
    Generator.mixedMultiplicationBasis a b (left j S hS) (right j S hS) (dot j S hS)
  let orbit (j : J) := DoubleCoset.doubleCoset (σ j) (A : Set G) (B : Set G)
  -- Xiao, §5.1, Proposition 5.1 and “Smaller internal groups and
  -- intersections” (archived p. 17, revised published p. 19).
  -- Steps 1–4 of the registered MixedCrossingComposites proof identify the
  -- multiplication and finite transfer on basis vectors. The registered
  -- smaller-group supplier gives their composite after fixing this exact
  -- representative, including the image and the relative fiber cardinality.
  have data (j : J) (S : Subgroup U) (hS : S ≤ Lj j) (h : S.IsFiniteRelIndex (Lj j)) :
      (∃ (hf : finiteFibers j S hS) (hfJ : finiteFibers j (Lj j) (full j)),
        (outer j S hS hf).eval =
          (Diagram.scale (S.relIndex (Lj j) : Complex) (outer j (Lj j) (full j) hfJ)).eval) ∧
      Set.range (fun w => Generator.mixedProduct a b (f j S hS w)) = orbit j ∧
      (∀ g ∈ orbit j, Nat.card {w | Generator.mixedProduct a b (f j S hS w) = g}
        = S.relIndex (Lj j)) := by
    obtain ⟨hf, hfJ, houter, hRange, _, _, hCard, _, _⟩ :=
      MixedCrossingsThroughSmallerGroup K H G α β hK hH σ hσ j S hS h
    exact ⟨⟨hf, hfJ, houter⟩, hRange, fun g hg => (hCard g hg).1⟩
  refine ⟨fun j S hS h => (data j S hS h).1, ?_⟩
  intro J₀ _ I L hL
  refine ⟨?_, ?_⟩
  · intro i j
    have hInv : (β⁻¹ * (σ i.val : U)⁻¹)⁻¹ * (β⁻¹ * (σ j.val : U)⁻¹) =
        (σ i.val : U) * (σ j.val : U)⁻¹ := by group
    exact (ConjEmbedding.ofConjugator_eq_iff _ _ _ _).trans (by rw [hInv])
  intro hIndex
  choose hfL hfJ hOuter using fun j : I => (data j.val L (hL j) (hIndex j)).1
  refine ⟨hfL, hfJ, ?_⟩
  intro n restricted usual normalized V term
  have hNorm (j : I) : (normalized j).eval = (usual j).eval := by
    haveI : L.IsFiniteRelIndex (Lj j.val) := hIndex j
    have hn : n j ≠ 0 := by
      change (L.relIndex (Lj j.val) : Complex) ≠ 0
      exact_mod_cast (Subgroup.relIndex_ne_zero : L.relIndex (Lj j.val) ≠ 0)
    apply Biset.Hom.ext
    apply LinearMap.ext
    intro x
    change (n j)⁻¹ • ((restricted j).eval.toLinearMap x) = (usual j).eval.toLinearMap x
    rw [hOuter j]
    change (n j)⁻¹ • (n j • (usual j).eval.toLinearMap x) = _
    rw [← mul_smul, inv_mul_cancel₀ hn, one_smul]
  have orbit_iff (j : J) (g : G) : g ∈ orbit j ↔ DoubleCoset.mk A B g = j := by
    rw [← hσ j, eq_comm, DoubleCoset.eq]
    exact DoubleCoset.mem_doubleCoset
  have range_iff (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
      (hi : S.IsFiniteRelIndex (Lj j)) (z : M.basis.carrier) :
      z ∈ Set.range (f j S hS) ↔ DoubleCoset.mk A B (Generator.mixedProduct a b z) = j := by
    let e := Generator.mixedEquiv a b
    change z ∈ Set.range (f j S hS) ↔ DoubleCoset.mk A B (e z) = j
    rw [← orbit_iff, ← (data j S hS hi).2.1]
    exact ⟨fun ⟨w, hw⟩ => ⟨w, congrArg e hw⟩,
      fun ⟨w, hw⟩ => ⟨w, e.injective hw⟩⟩
  have hOrth (i j : I) (hij : i ≠ j) :
      (Diagram.vertical (inclusion i.val L (hL i)) (projection j.val L (hL j) (hfL j))).eval =
        (Diagram.zero (inner i.val L (hL i)) (inner j.val L (hL j))).eval := by
    apply Biset.Hom.projection_between_disjoint (f j.val L (hL j))
      (Generator.mixedMultiplication_equivariant a b _ _ _) (hfL j)
      (f i.val L (hL i)) (Generator.mixedMultiplication_equivariant a b _ _ _)
    apply Set.disjoint_left.mpr
    intro z hzj hzi
    exact hij (Subtype.ext (((range_iff i.val L (hL i) (hIndex i) z).mp hzi).symm.trans
      ((range_iff j.val L (hL j) (hIndex j) z).mp hzj)))
  have hSelf (j : J) : (Lj j).IsFiniteRelIndex (Lj j) :=
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr (by rw [Subgroup.relIndex_self]; decide)
  have hColumn (z : M.basis.carrier) (j : I) :
      term usual (Finsupp.single z 1) j =
        if j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)
        then Finsupp.single z 1 else 0 := by
    rw [show term usual (Finsupp.single z 1) j =
        Finsupp.single z ((hfJ j z).toFinset.card : Complex) from
      Diagram.projection_then_inclusion_single Complex a b _ _ _ (hfJ j) z]
    by_cases h : j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)
    · rw [if_pos h]
      have hs : {w | f j.val (Lj j.val) (full j.val) w = z} =
          {w | Generator.mixedProduct a b (f j.val (Lj j.val) (full j.val) w) =
            Generator.mixedProduct a b z} :=
        Set.ext fun w => (Generator.mixedEquiv a b).injective.eq_iff.symm
      letI : Fintype {w | f j.val (Lj j.val) (full j.val) w = z} := (hfJ j z).fintype
      have hc : (hfJ j z).toFinset.card = 1 := by
        rw [← (hfJ j z).card_toFinset, ← Nat.card_eq_fintype_card, hs,
          (data j.val (Lj j.val) (full j.val) (hSelf j.val)).2.2 _
            ((orbit_iff j.val _).mpr h.symm), Subgroup.relIndex_self]
      rw [hc, Nat.cast_one]
    · rw [if_neg h]
      have hempty : (hfJ j z).toFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact h (((range_iff j.val (Lj j.val) (full j.val) (hSelf j.val) z).mp
          ⟨w, (hfJ j z).mem_toFinset.mp hw⟩).symm)
      rw [hempty, Finset.card_empty, Nat.cast_zero, Finsupp.single_zero]
  have hTerm (x : V) : term normalized x = term usual x :=
    funext fun j => congrArg (fun m => m.toLinearMap x) (hNorm j)
  have hBasis (z : M.basis.carrier) :
      Function.support (term usual (Finsupp.single z 1)) =
        {j : I | j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)} := by
    ext j
    change (term usual (Finsupp.single z 1) j ≠ 0) ↔ _
    rw [hColumn]
    by_cases h : j.val = DoubleCoset.mk A B (Generator.mixedProduct a b z)
    · simp [h]
    · simp [h]
  -- MackeyIdentityDiagram sums a complete partition and uses comap
  -- subgroups to index its quotient. The selected family need not cover
  -- the basis. Use its basis-support argument on the selected subtype:
  -- active indices inject into the finite image of the support of x.
  let coset := fun z : M.basis.carrier => DoubleCoset.mk A B (Generator.mixedProduct a b z)
  have finiteJ (x : V) : Set.Finite (Function.support (term usual x)) := by
    have hb : Set.Finite {j : I | j.val ∈ x.support.image coset} :=
      (x.support.image coset).finite_toSet.preimage Subtype.val_injective.injOn
    apply hb.subset
    intro j hj
    by_contra h
    apply hj
    have hs : (∑ z ∈ x.support, Finsupp.single z (x z)) = x := Finsupp.sum_single x
    change (usual j).eval.toLinearMap x = 0
    rw [← hs, map_sum]
    apply Finset.sum_eq_zero
    intro z hz
    have hne : j.val ≠ coset z := fun he => h (Finset.mem_image.mpr ⟨z, hz, he.symm⟩)
    have hp : Finsupp.single z (x z) = (x z) • Finsupp.single z (1 : Complex) := by
      simp [Finsupp.smul_single, smul_eq_mul]
    rw [hp, map_smul]
    change (x z) • term usual (Finsupp.single z 1) j = 0
    rw [hColumn, if_neg hne, smul_zero]
  have finiteL (x : V) : Set.Finite (Function.support (term normalized x)) :=
    hTerm x ▸ finiteJ x
  refine ⟨hNorm, hOrth, ?_, ⟨finiteL, finiteJ, ?_⟩, ?_⟩
  · intro z
    exact ⟨(congrArg Function.support (hTerm _)).trans (hBasis z), hBasis z⟩
  · intro x
    have hFinset : (finiteL x).toFinset = (finiteJ x).toFinset := by
      ext j
      simp only [Set.Finite.mem_toFinset, hTerm x]
    rw [hFinset, hTerm x]
  · intro hJ₀ cupsL cupsJ indices withCupL withCupJ sumDiagrams
    have hCups (j : I) :
        (withCupL j).eval = (normalized j).eval ∧ (withCupJ j).eval = (usual j).eval := by
      have hleft := CommonMackeyIntersectionSumAux.cupProjection_eval a b
        (left j.val L (hL j)) (right j.val L (hL j)) (dot j.val L (hL j)) (cupsL j) (hfL j)
      have hright := CommonMackeyIntersectionSumAux.cupProjection_eval a b
        (left j.val (Lj j.val) (full j.val)) (right j.val (Lj j.val) (full j.val))
        (dot j.val (Lj j.val) (full j.val)) (cupsJ j) (hfJ j)
      exact ⟨congrArg (fun p => (p.vertical (inclusion j.val L (hL j))).scale (n j)⁻¹) hleft,
        congrArg (fun p => p.vertical (inclusion j.val (Lj j.val) (full j.val)).eval) hright⟩
    refine ⟨?_, hCups⟩
    have heval (ls : List I) :
        (ls.foldr (fun j acc => Diagram.add (withCupL j) acc) (Diagram.zero M M)).eval =
          (ls.foldr (fun j acc => Diagram.add (withCupJ j) acc) (Diagram.zero M M)).eval := by
      induction ls with
      | nil => rfl
      | cons j ls ih =>
        change (withCupL j).eval.add _ = (withCupJ j).eval.add _
        rw [ih, (hCups j).1, hNorm j, ← (hCups j).2]
    exact heval indices

#print axioms CommonMackeyIntersectionSum
