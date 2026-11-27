by
  classical
  intro U inst K H G α β Kα Hβ hK hH a b A B J σ reps L l r down up M Mj
    W Wj V Vj groupAlgebra coordinates groupAlgebraAction Mod Res Ind summand
  -- Xiao, Section 2.2, Theorem 2.2 and the proof following Lemma 2.3.
  -- Equations (2.1)–(2.3) occur on page 5 of the archived original
  -- and page 7 of the revised published PDF.
  refine ⟨GeneralizedMackeySupport.mixedCoordinates_action a b, ?_⟩
  let d (j : J) : MackeyDiagrams.Dot (a.comp (l j)) (b.comp (r j)) :=
    ⟨σ j, by
      intro ℓ
      apply Subtype.ext
      change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (σ j : U) =
        (σ j : U) * (β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
          (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹)
      group⟩
  -- The checked identity supplier packages the two composites in (2.3),
  -- including the finite support on each vector. Its proof implements the
  -- surviving terms (2.4)–(2.6) by their common multiplication fiber.
  obtain ⟨hf, hsum, hdiag, hoff⟩ := MackeyIdentityDiagram K H G α β hK hH σ reps
  let p (j : J) : MackeyDiagrams.Diagram Complex M (Mj j) :=
    .mixedProjection a b (l j) (r j) (d j) (hf j)
  let i (j : J) : MackeyDiagrams.Diagram Complex (Mj j) M :=
    .mixedMultiplication a b (l j) (r j) (d j)
  -- The compact crossings are the coefficient-one labels checked by
  -- MackeyCrossingProof.compact_projection and compact_inclusion.
  -- The finite fiber permits the compact projection at arbitrary index.
  refine ⟨p, i, hsum, hdiag, hoff, ?_, ?_⟩
  · obtain ⟨finite, sum⟩ := hsum
    let inc (j : J) : Vj j →ₗ[Complex] V := (i j).eval.toLinearMap
    let proj (j : J) : V →ₗ[Complex] Vj j := (p j).eval.toLinearMap
    have diag (j : J) (y : Vj j) : proj j (inc j y) = y :=
      congrArg (fun f : MackeyDiagrams.Biset.Hom Complex (Wj j) (Wj j) => f.toLinearMap y) (hdiag j)
    have off (j k : J) (h : j ≠ k) (y : Vj j) : proj k (inc j y) = 0 :=
      congrArg (fun f : MackeyDiagrams.Biset.Hom Complex (Wj j) (Wj k) => f.toLinearMap y) (hoff j k h)
    have addUp (x : V) : x = ∑ j ∈ (finite x).toFinset, inc j (proj j x) := by
      have straight :
          (MackeyDiagrams.Diagram.horizontal (R := Complex)
            (MackeyDiagrams.Diagram.id down) (MackeyDiagrams.Diagram.id up)).eval =
          MackeyDiagrams.Biset.Hom.id W :=
        MackeyDiagrams.Biset.Hom.horizontal_id down.basis up.basis
      have hx := sum x
      change _ = ∑ j ∈ (finite x).toFinset, inc j (proj j x) at hx
      exact (congrArg (fun f : MackeyDiagrams.Biset.Hom Complex W W => f.toLinearMap x) straight).symm.trans hx
    let equiv := MackeyDiagrams.orthogonalDirectSum inc proj finite addUp diag off
    have coord (x : V) (j : J) : equiv x j = proj j x :=
      MackeyDiagrams.orthogonalDirectSum_apply inc proj finite addUp diag off x j
    refine ⟨coordinates.symm.trans equiv, ?_, ?_⟩
    · intro x j
      change equiv (coordinates.symm (coordinates x)) j = proj j x
      rw [LinearEquiv.symm_apply_apply, coord]
    · intro g x j
      have hx := GeneralizedMackeySupport.mixedCoordinates_action a b g (coordinates.symm x)
      change coordinates (MackeyDiagrams.Biset.actLinear Complex W g (coordinates.symm x)) =
        groupAlgebraAction g (coordinates (coordinates.symm x)) at hx
      rw [LinearEquiv.apply_symm_apply] at hx
      change equiv (coordinates.symm (groupAlgebraAction g x)) j =
        MackeyDiagrams.Biset.actLinear Complex (Wj j) g (equiv (coordinates.symm x) j)
      rw [← hx, LinearEquiv.symm_apply_apply, coord, coord]
      exact (p j).eval.commutes g (coordinates.symm x)
  · -- The last paragraph after (2.6) tensors the decomposition on the right.
    -- The proof uses Mathlib's induced representation presentation. Its pure
    -- tensor at g is indexed by g⁻¹, and the coproduct inclusions send k ⊗ x
    -- to a(k)σⱼ ⊗ x. Descent on balanced pairs gives the coproduct property.
    have index_mul (j : J) (k : K) (h : H) :
        DoubleCoset.mk A B (a.toHom k * σ j * b.toHom h) = j := by
      have hj : DoubleCoset.mk A B (σ j) = DoubleCoset.mk A B (a.toHom k * σ j * b.toHom h) :=
        DoubleCoset.eq.mpr ⟨a.toHom k, ⟨k, k.property, rfl⟩,
          b.toHom h, ⟨h, h.property, rfl⟩, rfl⟩
      exact hj.symm.trans (reps j)
    have factor (g : G) : ∃ (j : J) (k : K) (h : H), a.toHom k * σ j * b.toHom h = g := by
      let j := DoubleCoset.mk A B g
      obtain ⟨x,hx,y,hy,hg⟩ := DoubleCoset.eq.mp (reps j)
      change (x : U) ∈ Kα at hx
      change (y : U) ∈ Hβ at hy
      obtain ⟨k,hk,hx⟩ := hx
      obtain ⟨h,hh,hy⟩ := hy
      have hx' : a.toHom ⟨k,hk⟩ = x := Subtype.ext hx
      have hy' : b.toHom ⟨h,hh⟩ = y := Subtype.ext hy
      exact ⟨j, ⟨k,hk⟩, ⟨h,hh⟩, by rw [hx', hy']; exact hg.symm⟩
    have intersection (j : J) (k : K) (h : H)
        (e : a.toHom k = σ j * b.toHom h * (σ j)⁻¹) :
        ∃ t : L j, (l j).toHom t = k := by
      let ell := α * (k : U) * α⁻¹
      have hleft : ell ∈ Kα := ⟨k, k.property, rfl⟩
      have hright : ell ∈ Subgroup.map
          (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H := by
        refine ⟨h, h.property, ?_⟩
        have he := congrArg Subtype.val e
        change α * (k : U) * α⁻¹ =
          (σ j : U) * (β * (h : U) * β⁻¹) * (σ j : U)⁻¹ at he
        change ((σ j : U) * β) * (h : U) * ((σ j : U) * β)⁻¹ = α * (k : U) * α⁻¹
        rw [he]
        group
      refine ⟨⟨ell, hleft, hright⟩, ?_⟩
      apply Subtype.ext
      change α⁻¹ * (α * (k : U) * α⁻¹) * (α⁻¹)⁻¹ = (k : U)
      group
    have bijective := GeneralizedMackeySupport.multiplication_bijective a b l r σ
      (fun j => (d j).intertwines) (DoubleCoset.mk A B) index_mul factor intersection
    let adjA := (GeneralizedMackeySupport.existsModuleAdjunction.{u,v} a).some
    let adjR (j : J) := (GeneralizedMackeySupport.existsModuleAdjunction.{u,v} (r j)).some
    exact ⟨GeneralizedMackeySupport.moduleMackey a.toHom b.toHom (fun j => (l j).toHom)
      (fun j => (r j).toHom) σ (fun j => (d j).intertwines) bijective adjA adjR⟩
