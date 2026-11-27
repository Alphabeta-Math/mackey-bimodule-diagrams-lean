import MackeyDiagrams
import Proofs.MixedCrossingComposites

set_option maxHeartbeats 2000000

theorem SinglePairCannotProjectOntoSeveralDoubleCosets : (
∀ {U : Type u} [Group U] (K H G L : Subgroup U) (α β a b : U)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G)
    (ha : ∀ ℓ : L, a * (ℓ : U) * a⁻¹ ∈ K)
    (hb : ∀ ℓ : L, b * (ℓ : U) * b⁻¹ ∈ H)
    (hs : (α * a) * (β * b)⁻¹ ∈ G),
  let eα := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let eβ := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let ea := MackeyDiagrams.ConjEmbedding.ofConjugator a ha
  let eb := MackeyDiagrams.ConjEmbedding.ofConjugator b hb
  let d : MackeyDiagrams.Dot
      (MackeyDiagrams.ConjEmbedding.comp eα ea)
      (MackeyDiagrams.ConjEmbedding.comp eβ eb) :=
    MackeyDiagrams.Dot.ofRepresentatives (α * a) (β * b)
      (by
        intro ℓ
        change α * (a * (ℓ : U) * a⁻¹) * α⁻¹ = _
        simp only [mul_inv_rev, mul_assoc])
      (by
        intro ℓ
        change β * (b * (ℓ : U) * b⁻¹) * β⁻¹ = _
        simp only [mul_inv_rev, mul_assoc]) hs
  let s := MackeyDiagrams.Dot.element d
  let _returnLabel := MackeyDiagrams.Dot.inverse d
  let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eα)
  let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom eβ)
  let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
  ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
    let conjSubgroup := fun (c : U) (S : Subgroup U) =>
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
    let Lj := fun j : J => conjSubgroup α K ⊓ conjSubgroup ((σ j : U) * β) H
    let leftJ := fun j : J =>
      MackeyDiagrams.ConjEmbedding.ofConjugator (H := Lj j) (G := K) α⁻¹
        (by
          intro ℓ
          obtain ⟨k, hk, heq⟩ := ℓ.property.1
          change α * k * α⁻¹ = (ℓ : U) at heq
          rw [← heq]
          change k ∈ K at hk
          convert hk using 1
          group)
    let rightJ := fun j : J =>
      MackeyDiagrams.ConjEmbedding.ofConjugator (H := Lj j) (G := H)
        (β⁻¹ * (σ j : U)⁻¹)
        (by
          intro ℓ
          obtain ⟨h, hh, heq⟩ := ℓ.property.2
          change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
          rw [← heq]
          change h ∈ H at hh
          convert hh using 1
          group)
    let _Mj := fun j : J =>
      MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (leftJ j))
        (MackeyDiagrams.Word.down (rightJ j))
    let M := MackeyDiagrams.Word.tensor
      (MackeyDiagrams.Word.down eα) (MackeyDiagrams.Word.up eβ)
    let ML := MackeyDiagrams.Word.tensor
      (MackeyDiagrams.Word.up ea) (MackeyDiagrams.Word.down eb)
    let Ls := conjSubgroup α K ⊓ conjSubgroup ((s : U) * β) H
    let Limage := conjSubgroup (α * a) L
    let _n := ENat.card (Ls ⧸ Subgroup.subgroupOf Limage Ls)
    let X := MackeyDiagrams.Word.basis M
    let Y := MackeyDiagrams.Word.basis ML
    let projection := fun (selected : Set J) =>
      show (MackeyDiagrams.Biset.carrier X →₀ Complex) →ₗ[Complex]
          (MackeyDiagrams.Biset.carrier X →₀ Complex) from by
        classical
        exact MackeyDiagrams.freeLift Complex (fun z =>
          if DoubleCoset.mk A B (MackeyDiagrams.Generator.mixedProduct eα eβ z) ∈ selected
          then Finsupp.single z 1 else 0)
    ∀ (selected : Set J), (∃ i ∈ selected, ∃ j ∈ selected, i ≠ j) →
      ∀ (p : MackeyDiagrams.Biset.Hom Complex X Y)
        (ι : MackeyDiagrams.Biset.Hom Complex Y X),
        MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Biset.Hom.vertical p ι) ≠
          projection selected
) :=
(by
  classical
  intro U inst K H G L α β a b hα hβ ha hb hs eα eβ ea eb d s returnLabel A B J σ hσ
    conjSubgroup Lj leftJ rightJ Mj M ML Ls Limage n X Y projection selected hSelected p ι hcomp
  obtain ⟨i, hi, j, hj, hij⟩ := hSelected
  -- Xiao, Proposition 5.3 (archive p. 17, revised published PDF p. 19).
  -- Steps 1–2 below follow the order of the unnumbered proof on the Alphabeta Math portal.
  -- Realize the outer coinvariant coordinates by sending each basis point to its orbit.
  -- The action uses the inverse on the right, so the right factor lies in B via h⁻¹.
  let classOf : X.carrier → J := fun z =>
    DoubleCoset.mk A B (MackeyDiagrams.Generator.mixedProduct eα eβ z)
  let coords : (X.carrier →₀ Complex) →ₗ[Complex] (J →₀ Complex) :=
    Finsupp.lmapDomain Complex Complex classOf
  have class_act (g : K × H) (z : X.carrier) : classOf (X.act g z) = classOf z := by
    have product_act :
        MackeyDiagrams.Generator.mixedProduct eα eβ (X.act g z) =
          eα.toHom g.1 * MackeyDiagrams.Generator.mixedProduct eα eβ z * eβ.toHom g.2⁻¹ := by
      refine Quotient.inductionOn z (fun xy => ?_)
      change (eα.toHom g.1 * xy.1 * (1 : G)⁻¹) *
          (1 * xy.2 * (eβ.toHom g.2)⁻¹) =
        eα.toHom g.1 * (xy.1 * xy.2) * eβ.toHom g.2⁻¹
      simp [mul_assoc]
    change DoubleCoset.mk A B _ = DoubleCoset.mk A B _
    exact ((DoubleCoset.eq (H := A) (K := B)).mpr ⟨eα.toHom g.1, ⟨g.1, rfl⟩,
      eβ.toHom g.2⁻¹, ⟨g.2⁻¹, rfl⟩, product_act⟩).symm
  have coords_action (g : K × H) (v : X.carrier →₀ Complex) :
      coords (X.actLinear Complex g v) = coords v := by
    have h : coords.comp (X.actLinear Complex g) = coords := by
      apply Finsupp.lhom_ext
      intro z r
      simp [coords, class_act]
    exact LinearMap.congr_fun h v
  -- Step 3: the inner balanced basis is transitive. Every pair is the action
  -- of (k,h⁻¹) on [1,1]. This computation passes to the balanced classes.
  let Y₁ := MackeyDiagrams.Biset.induction ea
  let Y₂ := MackeyDiagrams.Biset.restriction eb
  let z₀ : Y.carrier := Y₁.pair Y₂ 1 1
  have orbit (z : Y.carrier) : ∃ g : K × H, Y.act g z₀ = z := by
    refine Quotient.inductionOn z (fun xy => ?_)
    refine ⟨(xy.1, xy.2⁻¹), ?_⟩
    change Y₁.pair Y₂ (xy.1 * 1 * (ea.toHom 1)⁻¹)
      (eb.toHom 1 * 1 * (xy.2⁻¹)⁻¹) = Y₁.pair Y₂ xy.1 xy.2
    simp
  -- Step 4: equivariance forces all inner basis points to have the same
  -- class-coordinate image. Implement the resulting rank bound by a
  -- factorization through augmentation into Complex. Proposition 5.1
  -- computes specific crossings at finite index. Here the maps are arbitrary.
  -- The factorization of the return map suffices for the composite with p.
  let v₀ := coords (ι.toLinearMap (Finsupp.single z₀ 1))
  have coords_column (z : Y.carrier) :
      coords (ι.toLinearMap (Finsupp.single z 1)) = v₀ := by
    obtain ⟨g, hg⟩ := orbit z
    rw [← hg, ← Y.actLinear_single Complex g, ι.commutes, coords_action]
  let aug : (Y.carrier →₀ Complex) →ₗ[Complex] Complex :=
    MackeyDiagrams.freeLift Complex (fun _ => 1)
  have factor :
      coords.comp ι.toLinearMap =
        (LinearMap.toSpanSingleton Complex (J →₀ Complex) v₀).comp aug := by
    apply Finsupp.lhom_ext'
    intro z
    apply LinearMap.ext_ring
    simp [aug, coords_column, LinearMap.toSpanSingleton_apply]
  -- Step 5: selected classes supply independent columns. Only two
  -- coefficients are needed, so neither the groups nor J need be finite.
  have selected_column (k : J) (hk : k ∈ selected) :
      ∃ c : Complex, c • v₀ = Finsupp.single k 1 := by
    let z : X.carrier := (MackeyDiagrams.Generator.mixedEquiv eα eβ).symm (σ k)
    have hz : classOf z = k := by
      change DoubleCoset.mk A B
        ((MackeyDiagrams.Generator.mixedEquiv eα eβ) z) = k
      rw [Equiv.apply_symm_apply, hσ]
    have hcol := LinearMap.congr_fun hcomp (Finsupp.single z (1 : Complex))
    have hpz : projection selected (Finsupp.single z (1 : Complex)) = Finsupp.single z 1 := by
      change MackeyDiagrams.freeLift Complex
        (fun w => if classOf w ∈ selected then Finsupp.single w (1 : Complex) else 0)
        (Finsupp.single z 1) = _
      rw [MackeyDiagrams.freeLift_single, hz, ite_eq_left hk, one_smul]
    change ι.toLinearMap (p.toLinearMap (Finsupp.single z 1)) = _ at hcol
    rw [hpz] at hcol
    refine ⟨aug (p.toLinearMap (Finsupp.single z 1)), ?_⟩
    have h := LinearMap.congr_fun factor (p.toLinearMap (Finsupp.single z 1))
    change coords (ι.toLinearMap (p.toLinearMap (Finsupp.single z 1))) = _ at h
    rw [hcol] at h
    simpa [coords, hz, LinearMap.toSpanSingleton_apply] using h.symm
  obtain ⟨ci, hci⟩ := selected_column i hi
  obtain ⟨cj, hcj⟩ := selected_column j hj
  have hii : ci * v₀ i = 1 := by
    simpa [Finsupp.smul_apply, smul_eq_mul] using congrArg (fun v : J →₀ Complex => v i) hci
  have hji : cj * v₀ i = 0 := by
    simpa [Finsupp.smul_apply, smul_eq_mul, hij, Ne.symm hij] using
      congrArg (fun v : J →₀ Complex => v i) hcj
  have hvi : v₀ i ≠ 0 := by
    intro h
    simp [h] at hii
  have hcj0 : cj = 0 := (mul_eq_zero.mp hji).resolve_right hvi
  have hjj := congrArg (fun v : J →₀ Complex => v j) hcj
  simp [hcj0] at hjj)
