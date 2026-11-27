import MackeyDiagrams.StructuralBasis
import MackeyDiagrams.MixedIdentities

/-! The expanded projection sums exactly the fiber of the reverse crossing. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace RightCupTrace

def unitPair (r : ConjEmbedding L H) (h : H) : reverseCupUnitFiber r :=
  ⟨(Biset.induction r).pair (Biset.restriction r) h⁻¹ h, by
    change h⁻¹ * h = 1
    exact inv_mul_cancel h⟩

theorem unitPair_surjective (r : ConjEmbedding L H) :
    Function.Surjective (unitPair r) := by
  rintro ⟨z,hz⟩
  obtain ⟨⟨x,h⟩, he⟩ := Quotient.exists_rep z
  have heq : (Biset.induction r).pair (Biset.restriction r) x h = z := he
  rw [← heq] at hz
  change x * h = 1 at hz
  have hx : x = h⁻¹ := by
    calc
      x = (x * h) * h⁻¹ := by group
      _ = h⁻¹ := by rw [hz, one_mul]
  subst x
  exact ⟨h, Subtype.ext heq⟩

variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

theorem projectionTerm_image (g : G) (h : H) (k : K)
    (hk : a.toHom k = g * (b.toHom h⁻¹ * d.element⁻¹)) :
    term (Diagram.mixedProjectionTail (R := R) a b l r d)
      (Generator.mixedPair a b g) (unitPair r h) =
    Finsupp.single ((Biset.induction l).pair (Biset.restriction r) k h) 1 := by
  unfold term
  rw [show (unitPair r h).val = (Biset.induction r).pair (Biset.restriction r) h⁻¹ h from rfl]
  change (Diagram.mixedProjectionTail (R := R) a b l r d).eval.toLinearMap
      (Finsupp.single _ 1) = _
  unfold Generator.mixedPair
  rw [Diagram.eval_mixedProjectionTail_single (R := R) a b l r d g 1 h⁻¹ h]
  rw [Diagram.eval_horizontal_single (Diagram.traceCapOnLeft a l) (Diagram.id (.down r)),
    one_smul, Diagram.eval_id_apply]
  simp only [one_mul]
  rw [Diagram.eval_traceCapOnLeft_image (R := R) a l _ _ k hk.symm,
    Biset.pairLinear_single, one_mul]

theorem projectionTerm_outside (g : G) (h : H)
    (hk : ¬ ∃ k, a.toHom k = g * (b.toHom h⁻¹ * d.element⁻¹)) :
    term (Diagram.mixedProjectionTail (R := R) a b l r d)
      (Generator.mixedPair a b g) (unitPair r h) = 0 := by
  unfold term
  rw [show (unitPair r h).val = (Biset.induction r).pair (Biset.restriction r) h⁻¹ h from rfl]
  change (Diagram.mixedProjectionTail (R := R) a b l r d).eval.toLinearMap
      (Finsupp.single _ 1) = _
  unfold Generator.mixedPair
  rw [Diagram.eval_mixedProjectionTail_single (R := R) a b l r d g 1 h⁻¹ h]
  rw [Diagram.eval_horizontal_single (Diagram.traceCapOnLeft a l) (Diagram.id (.down r)), one_smul]
  simp only [one_mul]
  rw [Diagram.eval_traceCapOnLeft_outside (R := R) a l _ _ hk, map_zero, LinearMap.zero_apply]

def outputCupIndex :
    ((Biset.induction l).tensor (Biset.restriction r)).carrier → reverseCupUnitFiber r :=
  Quotient.lift (fun z : K × H => unitPair r z.2) (by
    intro x y hxy
    obtain ⟨k, _, hy⟩ := hxy
    change r.toHom k * x.2 * (1 : H)⁻¹ = y.2 at hy
    simp only [inv_one, mul_one] at hy
    apply Subtype.ext
    apply Quotient.sound
    refine ⟨k, ?_, ?_⟩
    · change 1 * x.2⁻¹ * (r.toHom k)⁻¹ = y.2⁻¹
      simp [← hy]
    · change r.toHom k * x.2 * (1 : H)⁻¹ = y.2
      simpa using hy)

theorem projectionTerm_eq_single
    (x : ((Biset.restriction a).tensor (Biset.induction b)).carrier)
    (w : ((Biset.induction l).tensor (Biset.restriction r)).carrier)
    (hw : Generator.mixedMultiplicationBasis a b l r d w = x) :
    term (Diagram.mixedProjectionTail (R := R) a b l r d) x (outputCupIndex l r w) =
      Finsupp.single w 1 := by
  subst x
  refine Quotient.inductionOn w (fun z => ?_)
  rcases z with ⟨k,h⟩
  change term (Diagram.mixedProjectionTail (R := R) a b l r d)
      (Generator.mixedPair a b (a.toHom k * d.element * b.toHom h)) (unitPair r h) =
    Finsupp.single ((Biset.induction l).pair (Biset.restriction r) k h) 1
  apply projectionTerm_image
  rw [map_inv]
  group

end RightCupTrace
end MackeyDiagrams

namespace MackeyDiagrams.RightCupTrace

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

theorem preimage_of_projectionTerm_ne_zero
    (x : ((Biset.restriction a).tensor (Biset.induction b)).carrier)
    (i : reverseCupUnitFiber r)
    (hi : term (Diagram.mixedProjectionTail (R := R) a b l r d) x i ≠ 0) :
    ∃ w, Generator.mixedMultiplicationBasis a b l r d w = x ∧ outputCupIndex l r w = i := by
  obtain ⟨h,rfl⟩ := unitPair_surjective r i
  obtain ⟨g,rfl⟩ := (Generator.mixedEquiv a b).symm.surjective x
  change term (Diagram.mixedProjectionTail (R := R) a b l r d)
    (Generator.mixedPair a b g) (unitPair r h) ≠ 0 at hi
  have hex : ∃ k, a.toHom k = g * (b.toHom h⁻¹ * d.element⁻¹) := by
    by_contra hc
    exact hi (projectionTerm_outside a b l r d g h hc)
  obtain ⟨k,hk⟩ := hex
  refine ⟨(Biset.induction l).pair (Biset.restriction r) k h, ?_, rfl⟩
  change Generator.mixedPair a b (a.toHom k * d.element * b.toHom h) =
    Generator.mixedPair a b g
  apply congrArg (Generator.mixedPair a b)
  rw [hk, map_inv]
  group

theorem mixedProjectionTail_finiteAfter
    (finite : ∀ x, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = x}) :
    FiniteAfter (Diagram.mixedProjectionTail (R := R) a b l r d) := by
  intro x
  apply ((finite x).image (outputCupIndex l r)).subset
  intro i hi
  exact preimage_of_projectionTerm_ne_zero a b l r d x i hi

theorem projectionTerm_ne_zero [Nontrivial R]
    (x : ((Biset.restriction a).tensor (Biset.induction b)).carrier)
    (w : ((Biset.induction l).tensor (Biset.restriction r)).carrier)
    (hw : Generator.mixedMultiplicationBasis a b l r d w = x) :
    term (Diagram.mixedProjectionTail (R := R) a b l r d) x (outputCupIndex l r w) ≠ 0 := by
  rw [projectionTerm_eq_single a b l r d x w hw]
  intro hzero
  have hv := DFunLike.congr_fun hzero w
  simpa using hv

theorem outputCupIndex_injOnFiber [Nontrivial R]
    (x : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    Set.InjOn (outputCupIndex l r) {w | Generator.mixedMultiplicationBasis a b l r d w = x} := by
  intro w hw z hz h
  have he : (Finsupp.single w 1 : ((Biset.induction l).tensor (Biset.restriction r)).carrier →₀ R) =
      Finsupp.single z 1 := by
    rw [← projectionTerm_eq_single a b l r d x w hw,
      ← projectionTerm_eq_single a b l r d x z hz, h]
  by_contra hn
  have hv := DFunLike.congr_fun he w
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hn] at hv
  exact one_ne_zero hv

end MackeyDiagrams.RightCupTrace

namespace MackeyDiagrams.ScopedDiagram

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]

variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))
variable (finite : ∀ x, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = x})

/-- The crossing-fiber condition suffices to draw the prescribed expanded projection. -/
def expandedMixedProjectionOfFinite :
    ScopedDiagram R ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r)) :=
  expandedMixedProjection a b l r d (RightCupTrace.mixedProjectionTail_finiteAfter a b l r d finite)

theorem eval_expandedMixedProjection :
    (expandedMixedProjectionOfFinite (R := R) a b l r d finite).eval =
      (Diagram.mixedProjection a b l r d finite).eval := by
  classical
  apply Biset.Hom.ext
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  apply Finsupp.lhom_ext
  intro x c
  have hsingle : ∀ x, (expandedMixedProjectionOfFinite (R := R) a b l r d finite).eval.toLinearMap
      (Finsupp.single x 1) =
      (Diagram.mixedProjection (R := R) a b l r d finite).eval.toLinearMap (Finsupp.single x 1) := by
    intro x
    let tail := Diagram.mixedProjectionTail (R := R) a b l r d
    let after := RightCupTrace.mixedProjectionTail_finiteAfter (R := R) a b l r d finite
    have hfinite := after x
    change (RightCupTrace.ofFiniteAfter tail after).eval.toLinearMap (Finsupp.single x 1) =
      (Generator.mixedProjection a b l r d R finite).toLinearMap (Finsupp.single x 1)
    rw [RightCupTrace.eval_single, Generator.mixedProjection, Biset.Hom.transfer_single,
      one_smul, Biset.Hom.transferBasis_sum]
    unfold RightCupTrace.basisSum
    symm
    refine Finset.sum_bij (fun w _ => RightCupTrace.outputCupIndex l r w) ?_ ?_ ?_ ?_
    · intro w hw
      exact hfinite.mem_toFinset.mpr <| RightCupTrace.projectionTerm_ne_zero a b l r d x w
          ((finite x).mem_toFinset.mp hw)
    · intro w hw z hz heq
      exact RightCupTrace.outputCupIndex_injOnFiber (R := R) a b l r d x
        ((finite x).mem_toFinset.mp hw) ((finite x).mem_toFinset.mp hz) heq
    · intro i hi
      obtain ⟨w,hw,hwi⟩ := RightCupTrace.preimage_of_projectionTerm_ne_zero a b l r d x i
        (hfinite.mem_toFinset.mp hi)
      exact ⟨w, (finite x).mem_toFinset.mpr hw, hwi⟩
    · intro w hw
      exact (RightCupTrace.projectionTerm_eq_single a b l r d x w
        ((finite x).mem_toFinset.mp hw)).symm
  have hc : Finsupp.single x c = c • Finsupp.single x (1 : R) := by
    simp [Finsupp.smul_single, smul_eq_mul]
  rw [hc, map_smul, map_smul, hsingle]

end MackeyDiagrams.ScopedDiagram
