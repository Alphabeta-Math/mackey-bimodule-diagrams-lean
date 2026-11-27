import MackeyDiagrams
import Proofs.MixedCrossingComposites
import Proofs.MixedCrossingFiberMaps

set_option maxHeartbeats 2000000

namespace MixedCrossingsThroughSmallerGroupAux

private theorem fiberCard {X Y : Type*} (f : X → Y) (y : Y)
    (hf : Set.Finite {x | f x = y}) :
    (hf.toFinset).card = Nat.card {x | f x = y} := by
  let := hf.fintype
  rw [Nat.card_eq_fintype_card, hf.card_toFinset]

private theorem sumSingleApply {X : Type*} [DecidableEq X] (S : Finset X) (w : X) :
    (S.sum (fun x => Finsupp.single x (1 : Complex))) w =
      if w ∈ S then 1 else 0 := by
  change (Finsupp.lapply w : (X →₀ Complex) →ₗ[Complex] Complex) _ = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply, Finset.sum_ite_eq']

end MixedCrossingsThroughSmallerGroupAux

theorem MixedCrossingsThroughSmallerGroup : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let eα := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let eβ := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eα)
  let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eβ)
  let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
  ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j) (j : J),
    let s := σ j
    let orbit := DoubleCoset.doubleCoset s (A : Set G) (B : Set G)
    let a := α⁻¹
    let b := β⁻¹ * (s : U)⁻¹
    let Lj := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((s : U) * β))) H
    let left := fun (S : Subgroup U) (hS : S ≤ Lj) =>
      MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := K) a (by
        intro ℓ
        obtain ⟨k, hk, heq⟩ := (hS ℓ.property).1
        change α * k * α⁻¹ = (ℓ : U) at heq
        change α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹ ∈ K
        rw [← heq]
        change k ∈ K at hk
        convert hk using 1
        group)
    let right := fun (S : Subgroup U) (hS : S ≤ Lj) =>
      MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := H) b (by
        intro ℓ
        obtain ⟨h, hh, heq⟩ := (hS ℓ.property).2
        change (s : U) * β * h * ((s : U) * β)⁻¹ = (ℓ : U) at heq
        change (β⁻¹ * (s : U)⁻¹) * (ℓ : U) * (β⁻¹ * (s : U)⁻¹)⁻¹ ∈ H
        rw [← heq]
        change h ∈ H at hh
        convert hh using 1
        group)
    let dot := fun (S : Subgroup U) (hS : S ≤ Lj) =>
      show MackeyDiagrams.Dot
          (MackeyDiagrams.ConjEmbedding.comp eα (left S hS))
          (MackeyDiagrams.ConjEmbedding.comp eβ (right S hS)) from
        ⟨s, by
          intro ℓ
          apply Subtype.ext
          change (α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹) * (s : U) =
            (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
              (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
          group⟩
    ∀ (L : Subgroup U) (hL : L ≤ Lj), Subgroup.IsFiniteRelIndex L Lj →
      let leftL := left L hL
      let rightL := right L hL
      let leftJ := left Lj (le_refl Lj)
      let rightJ := right Lj (le_refl Lj)
      let dL := dot L hL
      let dJ := dot Lj (le_refl Lj)
      let M := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.down eα) (MackeyDiagrams.Word.up eβ)
      let ML := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.up leftL) (MackeyDiagrams.Word.down rightL)
      let MJ := MackeyDiagrams.Word.tensor
        (MackeyDiagrams.Word.up leftJ) (MackeyDiagrams.Word.down rightJ)
      let qBasis := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ leftL rightL dL
      let qBasisJ := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ leftJ rightJ dJ
      let q := fun z : (MackeyDiagrams.Word.basis ML).carrier =>
        MackeyDiagrams.Generator.mixedProduct eα eβ (qBasis z)
      let fiber := fun g : G => {w | q w = g}
      let n := Subgroup.relIndex L Lj
      ∃ (hLFinite : ∀ z : (MackeyDiagrams.Word.basis M).carrier,
          Set.Finite {w | qBasis w = z})
        (hJFinite : ∀ z : (MackeyDiagrams.Word.basis M).carrier,
          Set.Finite {w | qBasisJ w = z}),
        let hf := fun g : G => show Set.Finite (fiber g) from
          Set.Finite.subset (hLFinite (MackeyDiagrams.Generator.mixedPair eα eβ g)) (by
            intro w hw
            apply (MackeyDiagrams.Generator.mixedEquiv eα eβ).injective
            change q w = MackeyDiagrams.Generator.mixedProduct eα eβ
              (MackeyDiagrams.Generator.mixedPair eα eβ g)
            rw [MackeyDiagrams.Generator.mixedProduct_mixedPair]
            exact hw)
        let fiberSum := fun g : G =>
          Finset.sum (Set.Finite.toFinset (hf g)) (fun w => Finsupp.single w (1 : Complex))
        let iotaL : MackeyDiagrams.Diagram Complex ML M :=
          MackeyDiagrams.Diagram.mixedMultiplication eα eβ leftL rightL dL
        let pL : MackeyDiagrams.Diagram Complex M ML :=
          MackeyDiagrams.Diagram.mixedProjection eα eβ leftL rightL dL hLFinite
        let iotaJ : MackeyDiagrams.Diagram Complex MJ M :=
          MackeyDiagrams.Diagram.mixedMultiplication eα eβ leftJ rightJ dJ
        let pJ : MackeyDiagrams.Diagram Complex M MJ :=
          MackeyDiagrams.Diagram.mixedProjection eα eβ leftJ rightJ dJ hJFinite
        let outerL := MackeyDiagrams.Diagram.vertical pL iotaL
        let outerJ := MackeyDiagrams.Diagram.vertical pJ iotaJ
        let innerL := MackeyDiagrams.Diagram.vertical iotaL pL
        let straight := MackeyDiagrams.Diagram.id (R := Complex) ML
        MackeyDiagrams.Diagram.eval outerL =
          MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.scale (n : Complex) outerJ) ∧
        Set.range q = orbit ∧
        (∀ (k : K) (h : H),
          q (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction leftL)
              (MackeyDiagrams.Biset.restriction rightL) k h) =
            MackeyDiagrams.ConjEmbedding.toHom eα k * s *
              MackeyDiagrams.ConjEmbedding.toHom eβ h) ∧
        (∀ z : (MackeyDiagrams.Word.basis ML).carrier,
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval iotaL)
              (Finsupp.single z 1) =
            Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ (q z)) 1) ∧
        (∀ g : G, g ∈ orbit →
          Nat.card (fiber g) = n ∧
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval pL)
              (Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ g) 1) = fiberSum g) ∧
        (∀ z : (MackeyDiagrams.Word.basis ML).carrier,
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval innerL)
              (Finsupp.single z 1) = fiberSum (q z)) ∧
        (MackeyDiagrams.Diagram.eval innerL = MackeyDiagrams.Diagram.eval straight ↔ L = Lj)
) :=
(by
  classical
  intro U inst K H G α β hα hβ eα eβ A B J σ hσ j s orbit a b Lj left right dot
    L hL hIndex leftL rightL leftJ rightJ dL dJ M ML MJ qBasis qBasisJ q fiber n
  -- Xiao, §5.1, “Smaller internal groups and intersections,” following
  -- Proposition 5.1. There is no matching numbered Alphabeta Math proof in
  -- the reviewed plan. As in steps 1–3 of the registered MixedCrossingComposites
  -- proof, use the balanced push and its finite-fiber transfer. Here both
  -- subgroup choices use the fixed representative s. The registered
  -- MixedCrossingFiberMaps theorem supplies the stabilizer calculation
  -- directly, so neither representative transport nor a coset tower is needed.
  have haComp : α * a = 1 := mul_inv_cancel α
  have hbComp : β * b = (s : U)⁻¹ := mul_inv_cancel_left β _
  have hsVal : (α * a) * (β * b)⁻¹ = (s : U) := by
    rw [haComp, hbComp, inv_inv, one_mul]
  have hsG : (α * a) * (β * b)⁻¹ ∈ G := hsVal ▸ s.property
  have fiberData (S : Subgroup U) (hS : S ≤ Lj) (hIndexS : S.IsFiniteRelIndex Lj) :
      let l := left S hS
      let r := right S hS
      let d := dot S hS
      let f := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ l r d
      let qS := fun w => MackeyDiagrams.Generator.mixedProduct eα eβ (f w)
      Set.range qS = orbit ∧
      (∀ (k : K) (h : H),
        qS (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction l)
          (MackeyDiagrams.Biset.restriction r) k h) = eα.toHom k * s * eβ.toHom h) ∧
      (∀ w, (MackeyDiagrams.Diagram.mixedMultiplication (R := Complex) eα eβ l r d).eval.toLinearMap
        (Finsupp.single w 1) =
        Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ (qS w)) 1) ∧
      (∀ g ∈ orbit, Nat.card {w | qS w = g} = S.relIndex Lj) ∧
      (∀ z, Set.Finite {w | f w = z}) := by
    intro l r d f qS
    have ha (ℓ : S) : a * (ℓ : U) * a⁻¹ ∈ K := (l.toHom ℓ).property
    have hb (ℓ : S) : b * (ℓ : U) * b⁻¹ ∈ H := (r.toHom ℓ).property
    let d' : MackeyDiagrams.Dot (eα.comp l) (eβ.comp r) :=
      MackeyDiagrams.Dot.ofRepresentatives (α * a) (β * b)
        (by
          intro ℓ
          change α * (a * (ℓ : U) * a⁻¹) * α⁻¹ = _
          simp only [mul_inv_rev, mul_assoc])
        (by
          intro ℓ
          change β * (b * (ℓ : U) * b⁻¹) * β⁻¹ = _
          simp only [mul_inv_rev, mul_assoc]) hsG
    have hs' : d'.element = s := Subtype.ext hsVal
    have hd : d' = d := MackeyDiagrams.Dot.ext hs'
    have hc : DoubleCoset.mk A B d'.element = j := hs' ▸ hσ j
    have hImage : Subgroup.map (MulAut.conj (α * a)).toMonoidHom S = S := by
      rw [haComp]
      ext x
      simp [Subgroup.mem_map]
    let Ls := Subgroup.map (MulAut.conj α).toMonoidHom K ⊓
      Subgroup.map (MulAut.conj ((d'.element : U) * β)).toMonoidHom H
    have hLs : Ls = Lj := by
      dsimp only [Ls]
      rw [hs']
    let orbit' := DoubleCoset.doubleCoset (σ (DoubleCoset.mk A B d'.element)) (A : Set G) (B : Set G)
    have hOrbit : orbit' = orbit := by
      dsimp only [orbit']
      rw [hc]
    let f' := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ l r d'
    let q' := fun w => MackeyDiagrams.Generator.mixedProduct eα eβ (f' w)
    have hf' : f' = f := congrArg
      (MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ l r) hd
    have hq' : q' = qS := congrArg
      (fun m w => MackeyDiagrams.Generator.mixedProduct eα eβ (m w)) hf'
    obtain ⟨_, hPair, hPush, hRange, hCard, hFinite, _⟩ :=
      MixedCrossingFiberMaps K H G S α β a b hα hβ ha hb hsG σ hσ
    change Set.range q' = orbit' at hRange
    change ∀ g ∈ orbit', (Subgroup.map (MulAut.conj (α * a)).toMonoidHom S).IsFiniteRelIndex Ls →
      Nat.card {w | q' w = g} = (Subgroup.map (MulAut.conj (α * a)).toMonoidHom S).relIndex Ls at hCard
    change (∀ z, Set.Finite {w | f' w = z}) ↔
      (Subgroup.map (MulAut.conj (α * a)).toMonoidHom S).IsFiniteRelIndex Ls at hFinite
    change ∀ k h, q' ((MackeyDiagrams.Biset.induction l).pair
      (MackeyDiagrams.Biset.restriction r) k h) = eα.toHom k * d'.element * eβ.toHom h at hPair
    change ∀ w, (MackeyDiagrams.Diagram.mixedMultiplication (R := Complex) eα eβ l r d').eval.toLinearMap
      (Finsupp.single w 1) = Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ (q' w)) 1 at hPush
    rw [hq', hOrbit] at hRange
    rw [hOrbit, hImage, hLs, hq'] at hCard
    rw [hImage, hLs, hf'] at hFinite
    rw [hq', hs'] at hPair
    rw [hq', hd] at hPush
    exact ⟨hRange, hPair, hPush, fun g hg => hCard g hg hIndexS, hFinite.mpr hIndexS⟩
  have hJIndex : Lj.IsFiniteRelIndex Lj :=
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr (by rw [Subgroup.relIndex_self]; decide)
  obtain ⟨hRangeL, hPairL, hPushL, hCardL, hLFinite⟩ := fiberData L hL hIndex
  obtain ⟨hRangeJ, _, _, hCardJ, hJFinite⟩ := fiberData Lj (le_refl Lj) hJIndex
  refine ⟨hLFinite, hJFinite, ?_⟩
  intro hf fiberSum iotaL pL iotaJ pJ outerL outerJ innerL straight
  let outer := MackeyDiagrams.Generator.mixedEquiv eα eβ
  -- Step 4 of MixedCrossingComposites checks the two orders on basis columns.
  -- The endpoint already uses ordinary typed crossings, i.e. the
  -- coefficient-one singleton terms, so the labelled-drawing adapters of
  -- that proof are unnecessary. Use the two checked column identities.
  have outerCard {X : Type u} (f : X → M.basis.carrier)
      (finite : ∀ y, Set.Finite {w | f w = y}) (m : Nat)
      (hRange : Set.range (fun w => outer (f w)) = orbit)
      (hCard : ∀ g ∈ orbit, Nat.card {w | outer (f w) = g} = m)
      (y : M.basis.carrier) :
      (finite y).toFinset.card = if outer y ∈ orbit then m else 0 := by
    by_cases hy : outer y ∈ orbit
    · have hSet : {w | f w = y} = {w | outer (f w) = outer y} :=
        Set.ext fun w => outer.injective.eq_iff.symm
      rw [ite_eq_left hy, MixedCrossingsThroughSmallerGroupAux.fiberCard, hSet]
      exact hCard (outer y) hy
    · rw [ite_eq_right hy]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have heq : f w = y := (finite y).mem_toFinset.mp hw
      exact hy (hRange ▸ ⟨w, congrArg outer heq⟩)
  have hOuter : outerL.eval = (MackeyDiagrams.Diagram.scale (n : Complex) outerJ).eval := by
    apply MackeyDiagrams.Biset.Hom.ext
    apply Finsupp.lhom_ext'
    intro y
    apply LinearMap.ext_ring
    change outerL.eval.toLinearMap (Finsupp.single y 1) =
      (n : Complex) • outerJ.eval.toLinearMap (Finsupp.single y 1)
    rw [show outerL.eval.toLinearMap (Finsupp.single y 1) =
        Finsupp.single y ((hLFinite y).toFinset.card : Complex) from
      MackeyDiagrams.Diagram.projection_then_inclusion_single Complex eα eβ leftL rightL dL hLFinite y,
      show outerJ.eval.toLinearMap (Finsupp.single y 1) =
        Finsupp.single y ((hJFinite y).toFinset.card : Complex) from
      MackeyDiagrams.Diagram.projection_then_inclusion_single Complex eα eβ leftJ rightJ dJ hJFinite y,
      outerCard qBasis hLFinite n hRangeL hCardL,
      outerCard qBasisJ hJFinite (Lj.relIndex Lj) hRangeJ hCardJ,
      Subgroup.relIndex_self]
    by_cases hy : outer y ∈ orbit <;> simp [hy, Finsupp.smul_single]
  have hFinset (g : G) :
      (hLFinite (MackeyDiagrams.Generator.mixedPair eα eβ g)).toFinset = (hf g).toFinset := by
    apply Finset.ext
    intro w
    rw [(hLFinite _).mem_toFinset, (hf g).mem_toFinset]
    change qBasis w = MackeyDiagrams.Generator.mixedPair eα eβ g ↔ q w = g
    calc
      _ ↔ q w = MackeyDiagrams.Generator.mixedProduct eα eβ
          (MackeyDiagrams.Generator.mixedPair eα eβ g) := outer.injective.eq_iff.symm
      _ ↔ q w = g := by rw [MackeyDiagrams.Generator.mixedProduct_mixedPair]
  have hProject (g : G) :
      pL.eval.toLinearMap (Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ g) 1) =
        fiberSum g := by
    change (MackeyDiagrams.Biset.Hom.transfer Complex qBasis
      (MackeyDiagrams.Generator.mixedMultiplication_equivariant eα eβ leftL rightL dL) hLFinite).toLinearMap
      (Finsupp.single (MackeyDiagrams.Generator.mixedPair eα eβ g) 1) =
        Finset.sum (hf g).toFinset (fun w => Finsupp.single w 1)
    rw [MackeyDiagrams.Biset.Hom.transfer_single, one_smul,
      MackeyDiagrams.Biset.Hom.transferBasis_sum, hFinset]
  have hInner (z : ML.basis.carrier) :
      innerL.eval.toLinearMap (Finsupp.single z 1) = fiberSum (q z) := by
    have hF := hFinset (q z)
    rw [show MackeyDiagrams.Generator.mixedPair eα eβ (q z) = qBasis z from
      MackeyDiagrams.Generator.mixedPair_mixedProduct eα eβ (qBasis z)] at hF
    change _ = Finset.sum (hf (q z)).toFinset (fun w => Finsupp.single w 1)
    rw [← hF]
    exact MackeyDiagrams.Diagram.inclusion_then_projection_single Complex eα eβ leftL rightL dL hLFinite z
  refine ⟨hOuter, hRangeL, hPairL, hPushL, fun g hg => ⟨hCardL g hg, hProject g⟩, hInner, ?_⟩
  -- Step 5 of MixedCrossingComposites detects the identity from the support
  -- of a column. Every fiber over q z contains z and has cardinal n.
  have hSelf (z : ML.basis.carrier) : z ∈ (hf (q z)).toFinset :=
    (hf (q z)).mem_toFinset.mpr rfl
  have hSize (z : ML.basis.carrier) : (hf (q z)).toFinset.card = n := by
    rw [MixedCrossingsThroughSmallerGroupAux.fiberCard]
    exact hCardL (q z) (hRangeL ▸ ⟨z, rfl⟩)
  constructor
  · intro hIdentity
    let z : ML.basis.carrier :=
      MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction leftL)
        (MackeyDiagrams.Biset.restriction rightL) 1 1
    have hz := hInner z
    rw [hIdentity] at hz
    change Finsupp.single z (1 : Complex) =
      Finset.sum (hf (q z)).toFinset (fun w => Finsupp.single w 1) at hz
    have hOnly (w : ML.basis.carrier) (hw : w ∈ (hf (q z)).toFinset) : w = z := by
      by_contra hne
      have hCoeff := congrArg (fun v : ML.basis.carrier →₀ Complex => v w) hz
      rw [Finsupp.single_eq_of_ne hne, MixedCrossingsThroughSmallerGroupAux.sumSingleApply,
        ite_eq_left hw] at hCoeff
      exact zero_ne_one hCoeff
    have hSingleton : (hf (q z)).toFinset = {z} := by
      apply Finset.ext
      intro w
      rw [Finset.mem_singleton]
      exact ⟨hOnly w, fun hw => hw.symm ▸ hSelf z⟩
    have hn : n = 1 := by rw [← hSize z, hSingleton, Finset.card_singleton]
    exact le_antisymm hL (Subgroup.relIndex_eq_one.mp hn)
  · intro hEq
    have hn : n = 1 := by
      change L.relIndex Lj = 1
      rw [hEq, Subgroup.relIndex_self]
    apply MackeyDiagrams.Biset.Hom.ext
    apply Finsupp.lhom_ext'
    intro z
    apply LinearMap.ext_ring
    change innerL.eval.toLinearMap (Finsupp.single z 1) = Finsupp.single z 1
    rw [hInner]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ((hSize z).trans hn)
    have hz := hSelf z
    rw [hw, Finset.mem_singleton] at hz
    change Finset.sum (hf (q z)).toFinset (fun w => Finsupp.single w (1 : Complex)) = _
    rw [hw, Finset.sum_singleton, hz])
