namespace OutsideRegionsAux
open MackeyDiagrams

section
variable {U : Type*} [Group U] {G A D F C E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private theorem finite_mixed {K H P L : Subgroup U} [Finite K] [Finite H]
    (α : ConjEmbedding K P) (β : ConjEmbedding H P)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (x : Dot (α.comp l) (β.comp r)) :
    ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis α β l r x w = z} := by
  let _ : Finite ((Word.up l).tensor (.down r)).basis.carrier :=
    Finite.of_surjective (fun p : K × H => (Biset.induction l).pair (Biset.restriction r) p.1 p.2)
      (fun w => Quotient.exists_rep w)
  exact fun _ => Set.toFinite _

private theorem lower_le_max (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) :
    (a.comp (d.comp e)).toHom.range ≤ leftBound a b p.element := by
  apply le_inf (range_comp_le a (d.comp e))
  rw [dot_ranges p]
  exact Subgroup.map_mono (range_comp_le b (c.comp f))

-- The Case 2 supplier constructs the full intersection. For the interval
-- here, use inverses of the given embeddings restricted to any H in the
-- interval, and construct both singleton crossings on this same group.
private theorem left_witness [Finite G] [Finite D] [Finite F]
    (p : Dot (a.comp (d.comp e)) ((b.comp c).comp f)) (H : Subgroup A)
    (hlo : (a.comp (d.comp e)).toHom.range ≤ H) (hhi : H ≤ leftBound a b p.element) :
    let B := H.map A.subtype
    ∃ (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
      (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
      (z : Dot (r.comp t) (d.comp e)),
      conj (a.toHom z.element⁻¹) (a.comp r).toHom.range = H ∧
        leftParameter a b c d e f x.dot y.dot z = p.element := by
  intro B
  let j := inclusion H
  have hj : j.toHom.range = H := inclusion_range H
  obtain ⟨r, hr⟩ := lift_through a j (by
    rw [hj]
    exact hhi.trans inf_le_left)
  let _ : Finite B := Finite.of_injective r.toHom r.injective
  have hs' : (conjugated j p.element⁻¹).toHom.range ≤ b.toHom.range := by
    rw [conjugated_range, hj]
    calc
      _ ≤ conj p.element⁻¹ (conj p.element b.toHom.range) :=
        Subgroup.map_mono (hhi.trans inf_le_right)
      _ = _ := by rw [conj_mul, inv_mul_cancel, conj_one]
  obtain ⟨s, hs⟩ := lift_through b (conjugated j p.element⁻¹) hs'
  let t := restrictTo (a.comp (d.comp e)) H hlo
  have hjt : j.comp t = a.comp (d.comp e) := ConjEmbedding.ext (MonoidHom.ext fun _ => rfl)
  have ht₁ : r.comp t = d.comp e := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro v
    apply a.injective
    have h₁ := congrArg (fun m : ConjEmbedding B A => m.toHom (t.toHom v)) hr
    have h₂ := congrArg (fun m : ConjEmbedding E A => m.toHom v) hjt
    exact h₁.trans h₂
  have hbs (v : B) : b.toHom (s.toHom v) =
      p.element⁻¹ * j.toHom v * p.element := by
    have hv := congrArg (fun m : ConjEmbedding B A => m.toHom v) hs
    change b.toHom (s.toHom v) = p.element⁻¹ * j.toHom v * (p.element⁻¹)⁻¹ at hv
    rwa [inv_inv] at hv
  have ht₂ : s.comp t = c.comp f := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro v
    apply b.injective
    change b.toHom (s.toHom (t.toHom v)) = ((b.comp c).comp f).toHom v
    rw [hbs]
    change p.element⁻¹ * (j.comp t).toHom v * p.element = _
    rw [hjt, mul_assoc, p.intertwines, inv_mul_cancel_left]
  let x : Dot (a.comp r) (b.comp s) := ⟨p.element, by
    intro v
    rw [hr]
    change j.toHom v * p.element = p.element * b.toHom (s.toHom v)
    rw [hbs]
    group⟩
  let y : Dot (s.comp t) (c.comp f) := ⟨1, by intro v; rw [ht₂, mul_one, one_mul]⟩
  let z : Dot (r.comp t) (d.comp e) := ⟨1, by intro v; rw [ht₁, mul_one, one_mul]⟩
  refine ⟨r, s, t, ⟨x, finite_mixed a b r s x⟩, ⟨y, finite_mixed s c t f y⟩, z, ?_, ?_⟩
  · change conj (a.toHom (1 : G)⁻¹) (a.comp r).toHom.range = H
    rw [inv_one, map_one, conj_one, hr, hj]
  · change a.toHom (1 : G)⁻¹ * p.element * b.toHom (1 : D) = p.element
    rw [inv_one, map_one, map_one, one_mul, mul_one]

private theorem right_witness [Finite A]
    (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f) :
    let S := rightBound a b c d p.dot.element
    let B := S.map A.subtype
    ∃ (j : ConjEmbedding B A) (v : ConjEmbedding C B) (w : ConjEmbedding F B)
      (ell : Dot (b.comp c) (j.comp w)) (m : ProjectionDot.Mixed a j d v)
      (n : ProjectionDot.Mixed v w e f),
      conj m.dot.element j.toHom.range = S ∧
      rightParameter a b c d e f ell m.dot n.dot = p.dot.element := by
  intro S B
  -- Theorem 6.4(1) supplies the join construction once the middle
  -- intersection has finite index. Its ambient group is a subgroup of A.
  have hindex : Subgroup.FiniteIndex
      ((a.comp d).toHom.range.subgroupOf (a.toHom.range ⊓ S)) := inferInstance
  obtain ⟨j, v, w, ell, m, n, hj, _, _, he, hm, hn, _, _⟩ :=
    (CaseOneRightProjectionConstruction a b c d e f).1 p hindex
  refine ⟨j, v, w, ell, m, n, ?_, ?_⟩
  · have h : j = inclusion S :=
      ConjEmbedding.ext (MonoidHom.ext fun u => Subtype.ext (hj u))
    rw [hm, conj_one, h, inclusion_range]
  · unfold rightParameter
    simp only [he, hm, hn, map_one, one_mul, inv_inv]

end
end OutsideRegionsAux
