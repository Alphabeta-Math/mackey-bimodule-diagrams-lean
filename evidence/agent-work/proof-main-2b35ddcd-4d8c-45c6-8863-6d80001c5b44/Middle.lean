import Arithmetic

namespace CaseOneExample
open MackeyDiagrams

private theorem range_coe_conj {H K : Subgroup U} (h : ConjEmbedding H K) :
    ∃ x : U, h.toHom.range.map K.subtype = H.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := h.hasRepresentative
  refine ⟨x, ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, g.2, (hx g).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨h.toHom ⟨g, hg⟩, ⟨_, rfl⟩, hx ⟨g, hg⟩⟩

private theorem map_conj_mul (H : Subgroup U) (x y : U) :
    (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      H.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  apply congrArg (fun f : U →* U => H.map f)
  apply MonoidHom.ext
  intro z
  change x * (y * z * y⁻¹) * x⁻¹ = (x * y) * z * (x * y)⁻¹
  group

theorem middle_group_eq_top {J : Subgroup U} (v : ConjEmbedding C J)
    (w : ConjEmbedding D J) : J = ⊤ := by
  obtain ⟨x, hx⟩ := range_coe_conj v
  obtain ⟨y, hy⟩ := range_coe_conj w
  let xinv := (MulAut.conj x⁻¹).toMonoidHom
  have hC : C ≤ J.map xinv := by
    have hle := Subgroup.map_mono (f := xinv)
      (show (v.toHom.range.map J.subtype) ≤ J by
        rintro _ ⟨z, _, rfl⟩
        exact z.2)
    rw [hx] at hle
    change (C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤ _ at hle
    rw [map_conj_mul, inv_mul_cancel, map_one] at hle
    change C.map (MonoidHom.id U) ≤ _ at hle
    rwa [Subgroup.map_id] at hle
  have hD : D.map (MulAut.conj (x⁻¹ * y)).toMonoidHom ≤ J.map xinv := by
    have hle := Subgroup.map_mono (f := xinv)
      (show (w.toHom.range.map J.subtype) ≤ J by
        rintro _ ⟨z, _, rfl⟩
        exact z.2)
    rw [hy] at hle
    change (D.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤ _ at hle
    rwa [map_conj_mul] at hle
  have ht := sup_le hC hD
  rw [conjugate_join_top] at ht
  apply (Subgroup.map_injective (f := xinv) (MulAut.conj x⁻¹).injective)
  rw [Subgroup.map_top_of_surjective (f := xinv) (MulAut.conj x⁻¹).surjective]
  exact top_unique ht

private theorem G_normal : G.Normal := by
  change (SemidirectProduct.inl (φ := swaps)).range.Normal
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

private theorem conj_range_index {P : Subgroup U} (α : ConjEmbedding G P)
    (η : ConjEmbedding C G) :
    (α.comp η).toHom.range.relIndex α.toHom.range = C.relIndex G := by
  obtain ⟨x, hx⟩ := range_coe_conj (α.comp η)
  obtain ⟨y, hy⟩ := range_coe_conj α
  let _ : G.Normal := G_normal
  have hnormal (z : U) : G.map (MulAut.conj z).toMonoidHom = G :=
    Subgroup.Normal.map_conj_eq G z
  rw [← Subgroup.relIndex_map_map_of_injective _ _ P.subtype_injective, hx, hy, hnormal y]
  let φ := (MulAut.conj x).toMonoidHom
  calc
    (C.map φ).relIndex G = (C.map φ).relIndex (G.map φ) :=
      congrArg ((C.map φ).relIndex) (hnormal x).symm
    _ = C.relIndex G := Subgroup.relIndex_map_map_of_injective (f := φ) _ _ (MulAut.conj x).injective

private theorem top_src_range {P J : Subgroup U} (hJ : J = ⊤)
    (β : ConjEmbedding J P) : β.toHom.range = ⊤ := by
  obtain ⟨z, hz⟩ := β.hasRepresentative
  apply MonoidHom.range_eq_top.mpr
  intro u
  refine ⟨⟨z⁻¹ * u * z, hJ.symm ▸ trivial⟩, Subtype.ext ?_⟩
  rw [hz]
  group

-- The middle crossing alone is impossible once the spectator up-strand
-- gives an embedding of F = D into the middle crossing's other lower group.
theorem middle_projection_empty {P J : Subgroup U} (α : ConjEmbedding G P)
    (β : ConjEmbedding J P) (η : ConjEmbedding C G) (θ : ConjEmbedding C J)
    (w : ConjEmbedding D J) (m : ProjectionDot.Mixed α β η θ) : False := by
  have hfinite := ((EvaluationForTwoProjections α β (ConjEmbedding.id J)
    (ConjEmbedding.id G) η θ).1 m.dot).2.1.mp m.finite
  have hrange := top_src_range (middle_group_eq_top θ w) β
  rw [Subgroup.finiteIndex_iff] at hfinite
  change (α.comp η).toHom.range.relIndex
    (α.toHom.range ⊓ β.toHom.range.map (MulAut.conj m.dot.element).toMonoidHom) ≠ 0 at hfinite
  rw [hrange, Subgroup.map_top_of_surjective _ (MulAut.conj m.dot.element).surjective,
    inf_top_eq, conj_range_index] at hfinite
  exact infinite_index (Subgroup.finiteIndex_iff.mpr hfinite)

end CaseOneExample
