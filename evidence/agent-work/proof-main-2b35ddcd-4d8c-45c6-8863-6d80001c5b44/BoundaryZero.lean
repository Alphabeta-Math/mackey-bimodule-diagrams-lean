import MackeyDiagrams

namespace CaseOneExample

open MackeyDiagrams

universe u v
variable {V : Type u} [Group V] {K H : Subgroup V}
variable {R : Type v} [CommSemiring R] {p q : Word K H}

theorem boundary_zero_iff (d : ScopedDiagram R p q) :
    d.atBoundary.eval.toLinearMap = 0 ↔ d.eval.toLinearMap = 0 := by
  let Z := ScopedDiagram.ordinary (Diagram.zero (R := R) p q)
  have hz : Z.atBoundary.eval.toLinearMap = 0 := by
    change (q.reorderToBoundary (R := R)).eval.toLinearMap.comp
      ((0 : (p.basis.carrier →₀ R) →ₗ[R] (q.basis.carrier →₀ R)).comp
        (p.reorderFromBoundary (R := R)).eval.toLinearMap) = 0
    simp
  constructor
  · intro h
    have he : d.atBoundary.eval = Z.atBoundary.eval :=
      Biset.Hom.ext (h.trans hz.symm)
    exact congrArg Biset.Hom.toLinearMap ((ScopedDiagram.eval_atBoundary_eq_iff d Z).mp he)
  · intro h
    have he : d.eval = Z.eval := Biset.Hom.ext h
    exact (congrArg Biset.Hom.toLinearMap ((ScopedDiagram.eval_atBoundary_eq_iff d Z).mpr he)).trans hz

theorem planar_boundary_zero {bot top : Boundary K H} {s : PlanarShape}
    (d : LabelledDrawing.PlanarAtBoundary R bot top s)
    (h : d.diagram.interpret.eval.toLinearMap = 0) :
    d.interpret.eval.toLinearMap = 0 := by
  obtain ⟨bot', top', drawing, hb, ht, _⟩ := d
  subst bot
  subst top
  exact (boundary_zero_iff drawing.interpret).mpr h

theorem no_sum_zero {I M : Type*} [AddMonoid M] (v : I → M)
    (h : ∀ i, v i = 0) {target : M} (hne : target ≠ 0) :
    ¬ ∃ ds : List I, (ds.map v).sum = target := by
  rintro ⟨ds, he⟩
  have hsum : (ds.map v).sum = 0 := by induction ds <;> simp_all
  exact hne (he.symm.trans hsum)

end CaseOneExample
