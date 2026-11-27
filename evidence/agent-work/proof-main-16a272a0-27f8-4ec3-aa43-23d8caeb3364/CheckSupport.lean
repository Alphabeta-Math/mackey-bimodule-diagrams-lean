import MackeyDiagrams
import Proofs.ConjugationEmbeddingCentralizerCoset
import Proofs.SurvivingCosetRepresentative

set_option maxHeartbeats 2000000
namespace TransportToMackeyRepresentativeAux

open MackeyDiagrams

universe u v

section Quotients

variable {U : Type u} [Group U]

private theorem conjugate_mul (c d : U) (S : Subgroup U) :
    (S.map (MulAut.conj d).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      S.map (MulAut.conj (c * d)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change c * (d * x * d⁻¹) * c⁻¹ = (c * d) * x * (c * d)⁻¹
  group

private theorem coset_card_of_map (e : U ≃* U) (S T : Subgroup U) :
    Cardinal.mk (Quotient (QuotientGroup.leftRel (T.subgroupOf S))) =
      Cardinal.mk (Quotient (QuotientGroup.leftRel
        ((T.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)))) := by
  let f := e.subgroupMap S
  apply Cardinal.mk_congr
  refine Quotient.congr f.toEquiv (fun x y => ?_)
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
  change ((x : U)⁻¹ * (y : U)) ∈ T ↔
    ((f (x⁻¹ * y) : S.map e.toMonoidHom) : U) ∈ T.map e.toMonoidHom
  change ((x : U)⁻¹ * (y : U)) ∈ T ↔
    e ((x : U)⁻¹ * (y : U)) ∈ T.map e.toMonoidHom
  rw [Subgroup.mem_map_equiv, e.symm_apply_apply]

end Quotients

section Transport

variable {U : Type u} [Group U] {K H G L L' : Subgroup U}
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (l' : ConjEmbedding L' K) (r' : ConjEmbedding L' H)
variable (k : K) (h : H) (f : L ≃ L')

private def shiftBasis
    (hl : ∀ t, l'.toHom (f t) = k⁻¹ * l.toHom t * k)
    (hr : ∀ t, r'.toHom (f t) = h * r.toHom t * h⁻¹) :
    ((Biset.induction l).tensor (Biset.restriction r)).carrier ≃
      ((Biset.induction l').tensor (Biset.restriction r')).carrier := by
  refine Quotient.congr ((Equiv.mulRight k).prodCongr (Equiv.mulLeft h)) (fun x y => ?_)
  change
    (∃ t : L, 1 * x.1 * (l.toHom t)⁻¹ = y.1 ∧
      r.toHom t * x.2 * (1 : H)⁻¹ = y.2) ↔
    (∃ t : L', 1 * (x.1 * k) * (l'.toHom t)⁻¹ = y.1 * k ∧
      r'.toHom t * (h * x.2) * (1 : H)⁻¹ = h * y.2)
  simp only [one_mul, inv_one, mul_one]
  have left (t : L) : (x.1 * k) * (l'.toHom (f t))⁻¹ =
      (x.1 * (l.toHom t)⁻¹) * k := by
    rw [hl]
    group
  have right (t : L) : r'.toHom (f t) * (h * x.2) = h * (r.toHom t * x.2) := by
    rw [hr]
    group
  constructor
  · rintro ⟨t, hx, hy⟩
    exact ⟨f t, (left t).trans (congrArg (· * k) hx), (right t).trans (congrArg (h * ·) hy)⟩
  · rintro ⟨t, hx, hy⟩
    obtain ⟨t, rfl⟩ := f.surjective t
    exact ⟨t, mul_right_cancel ((left t).symm.trans hx),
      mul_left_cancel ((right t).symm.trans hy)⟩

private theorem shiftBasis_equivariant
    (hl : ∀ t, l'.toHom (f t) = k⁻¹ * l.toHom t * k)
    (hr : ∀ t, r'.toHom (f t) = h * r.toHom t * h⁻¹)
    (g : K × H) (w : ((Biset.induction l).tensor (Biset.restriction r)).carrier) :
    shiftBasis l r l' r' k h f hl hr
        (((Biset.induction l).tensor (Biset.restriction r)).act g w) =
      ((Biset.induction l').tensor (Biset.restriction r')).act g
        (shiftBasis l r l' r' k h f hl hr w) := by
  refine Quotient.inductionOn w (fun ⟨x, y⟩ => ?_)
  change (Biset.induction l').pair (Biset.restriction r')
      ((g.1 * x * (l.toHom 1)⁻¹) * k) (h * (r.toHom 1 * y * g.2⁻¹)) =
    (Biset.induction l').pair (Biset.restriction r')
      (g.1 * (x * k) * (l'.toHom 1)⁻¹) (r'.toHom 1 * (h * y) * g.2⁻¹)
  simp only [map_one, inv_one, mul_one, one_mul, mul_assoc]

end Transport

section Linear

variable {K H : Type u} [Group K] [Group H]
variable {X X' Y : Biset K H} {R : Type v} [CommSemiring R]
variable (e : X.carrier ≃ X'.carrier)
variable (he : ∀ g x, e (X.act g x) = X'.act g (e x))
variable (q : X.carrier → Y.carrier) (q' : X'.carrier → Y.carrier)
variable (hq : ∀ g x, q (X.act g x) = Y.act g (q x))
variable (hq' : ∀ g x, q' (X'.act g x) = Y.act g (q' x))
variable (hcomm : ∀ x, q' (e x) = q x)

private theorem multiplication_commutes :
    (Biset.Hom.ofFunction e he : Biset.Hom R X X').vertical (Biset.Hom.ofFunction q' hq') =
      Biset.Hom.ofFunction q hq := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  simp only [Biset.Hom.vertical, LinearMap.comp_apply, Biset.Hom.ofFunction_single, hcomm]

private theorem projection_commutes
    (hf : ∀ z, Set.Finite {w | q w = z}) (hf' : ∀ z, Set.Finite {w | q' w = z}) :
    (Biset.Hom.transfer R q hq hf).vertical (Biset.Hom.ofFunction e he) =
      Biset.Hom.transfer R q' hq' hf' := by
  classical
  have hpush : (Biset.Hom.ofFunction e he : Biset.Hom R X X').toLinearMap =
      Finsupp.lmapDomain R R e := by
    apply Finsupp.lhom_ext
    intro x c
    simp
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z c
  simp only [Biset.Hom.vertical, LinearMap.comp_apply, Biset.Hom.transfer_single, map_smul]
  congr 1
  apply Finsupp.ext
  intro x'
  obtain ⟨x, rfl⟩ := e.surjective x'
  rw [hpush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply_of_injective e.injective,
    Biset.Hom.transferBasis_apply, Biset.Hom.transferBasis_apply, hcomm]

end Linear

section Drawings

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

private theorem eval_multiplication_singleton :
    (LabelledDrawing.mixedMultiplication (R := R) a b l r [(1, d)]).interpret.eval =
      Generator.mixedMultiplication a b l r d R := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval, Diagram.eval]

private theorem eval_projection_singleton
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (LabelledDrawing.compactProjection (R := R) a b l r [(1, ⟨d, hf⟩)]).interpret.eval =
      Generator.mixedProjection a b l r d R hf := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval, Diagram.eval]

end Drawings

end TransportToMackeyRepresentativeAux
