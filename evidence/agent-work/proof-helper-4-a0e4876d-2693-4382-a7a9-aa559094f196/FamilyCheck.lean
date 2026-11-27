import Final
import Batteries.Tactic.OpenPrivate

open CategoryTheory MackeyDiagrams

open private P Parabolic
  blockProduct Object
  Span quotientFamily
  resultBasis spanBasis
  familyTensorIso unitAdmissible
  Admissible tensorAdmissible
  classOf Mor from Final

open private Reg tensor
  linearize sumBasis
  repIsoLinearEquiv reindexSum
  basisCoords basisCoords_single
  liftBasisEquiv liftBisetEquiv
  assoc_natural leftUnit_natural
  rightUnit_natural pentagon
  triangle flattenSum from Final

universe u

def emptyParabolic : Object := by
  refine ⟨⊥, ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩⟩
  simp [blockProduct]

example : Admissible emptyParabolic emptyParabolic (Reg.{u} emptyParabolic.val) :=
  unitAdmissible emptyParabolic

section Family
variable {K H J : Object} {m n : Nat}
variable (S : Fin m → Span K.val H.val) (T : Fin n → Span H.val J.val)

example [Fintype (Σ i, Σ j, quotientFamily S T i j)] (hm : 0 < m) (hn : 0 < n) :
    0 < Fintype.card (Σ i, Σ j, quotientFamily S T i j) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨0, hm⟩, ⟨0, hn⟩, classOf _ _ _ 1⟩⟩

example (S₀ : Fin 0 → Span K.val H.val) [Fintype (Σ i, Σ j, quotientFamily S₀ T i j)] :
    Fintype.card (Σ i, Σ j, quotientFamily S₀ T i j) = 0 := by
  exact Fintype.card_eq_zero_iff.mpr ⟨fun w => Fin.elim0 w.1⟩

example (T₀ : Fin 0 → Span H.val J.val) [Fintype (Σ i, Σ j, quotientFamily S T₀ i j)] :
    Fintype.card (Σ i, Σ j, quotientFamily S T₀ i j) = 0 := by
  exact Fintype.card_eq_zero_iff.mpr ⟨fun w => Fin.elim0 w.2.1⟩

example (S₀ : Fin 0 → Span K.val H.val)
    (M : Rep.{u} Complex (K.val × H.val)) (N : Rep.{u} Complex (H.val × J.val))
    (hM : Nonempty (M ≅ linearize (sumBasis (fun i => spanBasis (S₀ i)))))
    (hN : Nonempty (N ≅ linearize (sumBasis (fun j => spanBasis (T j))))) :
    Subsingleton (tensor M N).V := by
  let r (i : Fin 0) (j : Fin n) : quotientFamily S₀ T i j → H.val := Fin.elim0 i
  obtain ⟨e⟩ := familyTensorIso S₀ T r (fun i => Fin.elim0 i) M N hM hN
  let Z := sumBasis (resultBasis S₀ T r)
  have h : Subsingleton (Z.carrier →₀ Complex) :=
    ⟨fun f g => Finsupp.ext fun x => Fin.elim0 x.1.1⟩
  have : Subsingleton (linearize.{u} Z).V := (basisCoords.{u} Z).symm.injective.subsingleton
  exact (repIsoLinearEquiv e).injective.subsingleton

example (T₀ : Fin 0 → Span H.val J.val)
    (M : Rep.{u} Complex (K.val × H.val)) (N : Rep.{u} Complex (H.val × J.val))
    (hM : Nonempty (M ≅ linearize (sumBasis (fun i => spanBasis (S i)))))
    (hN : Nonempty (N ≅ linearize (sumBasis (fun j => spanBasis (T₀ j))))) :
    Subsingleton (tensor M N).V := by
  let r (i : Fin m) (j : Fin 0) : quotientFamily S T₀ i j → H.val := Fin.elim0 j
  obtain ⟨e⟩ := familyTensorIso S T₀ r (fun _ j => Fin.elim0 j) M N hM hN
  let Z := sumBasis (resultBasis S T₀ r)
  have h : Subsingleton (Z.carrier →₀ Complex) :=
    ⟨fun f g => Finsupp.ext fun x => Fin.elim0 x.1.2.1⟩
  have : Subsingleton (linearize.{u} Z).V := (basisCoords.{u} Z).symm.injective.subsingleton
  exact (repIsoLinearEquiv e).injective.subsingleton
end Family

section Coordinates
variable {K H : Type} [Group K] [Group H]

private theorem liftBasisEquiv_single {X Y : Biset K H} (e : X.carrier ≃ Y.carrier)
    (he : ∀ g x, e (X.act g x) = Y.act g (e x)) (x : X.carrier) (c : Complex) :
    (liftBasisEquiv.{u} e he).hom.hom (basisCoords.{u} X (Finsupp.single x c)) =
      basisCoords.{u} Y (Finsupp.single (e x) c) := by
  change basisCoords.{u} Y (Finsupp.domLCongr e
    ((basisCoords.{u} X).symm (basisCoords.{u} X (Finsupp.single x c)))) = _
  rw [LinearEquiv.symm_apply_apply, Finsupp.domLCongr_single]

example {ι κ : Type} (e : ι ≃ κ) (X : κ → Biset K H) (i : ι)
    (x : (X (e i)).carrier) (c : Complex) :
    (reindexSum.{u} e X).hom.hom
      (basisCoords.{u} (sumBasis (fun i => X (e i))) (Finsupp.single ⟨i, x⟩ c)) =
    basisCoords.{u} (sumBasis X) (Finsupp.single ⟨e i, x⟩ c) :=
  liftBasisEquiv_single (X := sumBasis (fun i => X (e i))) (Y := sumBasis X)
    (Equiv.sigmaCongrLeft (β := fun j => (X j).carrier) e) (fun _ _ => rfl) ⟨i, x⟩ c

example {ι : Type} {κ : ι → Type} (X : (i : ι) → κ i → Biset K H)
    (i : ι) (j : κ i) (x : (X i j).carrier) (c : Complex) :
    (flattenSum.{u} X).hom.hom
      (basisCoords.{u} (sumBasis (fun i => sumBasis (X i))) (Finsupp.single ⟨i, j, x⟩ c)) =
    basisCoords.{u} (sumBasis (fun ij : Sigma κ => X ij.1 ij.2))
      (Finsupp.single ⟨⟨i, j⟩, x⟩ c) := by
  unfold flattenSum
  rw [liftBasisEquiv_single]
  rfl
end Coordinates

#check assoc_natural
#check leftUnit_natural
#check rightUnit_natural
#check pentagon
#check triangle
#check Equiv.sigmaCongrLeft
#check Fintype.equivFin
#check sigmaFinsuppLequivDFinsupp
#check DFinsupp.mapRange.linearEquiv
