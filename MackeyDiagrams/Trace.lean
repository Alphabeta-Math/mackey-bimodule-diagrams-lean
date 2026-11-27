import MackeyDiagrams.Generators

/-!
# Subgroup trace and trace cap

On a basis element in the embedded subgroup the trace applies the inverse
embedding. Elsewhere it is zero. This construction uses no index assumption.
-/

namespace MackeyDiagrams.Generator

universe u v
open MackeyDiagrams
noncomputable section

variable {U : Type u} [Group U] {A B : Subgroup U}
variable (R : Type v) [CommSemiring R]

def traceBasis (a : ConjEmbedding A B) (x : B) : A →₀ R := by
  classical
  exact if h : ∃ y : A, a.toHom y = x then Finsupp.single (Classical.choose h) 1 else 0

@[simp] theorem traceBasis_image (a : ConjEmbedding A B) (x : A) :
    traceBasis R a (a.toHom x) = Finsupp.single x 1 := by
  have h : ∃ y : A, a.toHom y = a.toHom x := ⟨x, rfl⟩
  unfold traceBasis
  rw [dif_pos h]
  rw [a.injective (Classical.choose_spec h)]

theorem traceBasis_outside (a : ConjEmbedding A B) (x : B)
    (h : ¬ ∃ y : A, a.toHom y = x) : traceBasis R a x = 0 := by
  unfold traceBasis
  rw [dif_neg h]

theorem traceBasis_equivariant (a : ConjEmbedding A B) (x : B) (g h : A) :
    traceBasis R a (a.toHom g * x * (a.toHom h)⁻¹) =
      (Biset.regular A).actLinear R (g,h) (traceBasis R a x) := by
  by_cases hx : ∃ t : A, a.toHom t = x
  · obtain ⟨t, rfl⟩ := hx
    have heq : a.toHom g * a.toHom t * (a.toHom h)⁻¹ = a.toHom (g * t * h⁻¹) := by
      simp
    rw [heq, traceBasis_image, traceBasis_image, Biset.actLinear_single]
  · have hy : ¬ ∃ t : A, a.toHom t = a.toHom g * x * (a.toHom h)⁻¹ := by
      rintro ⟨t, ht⟩
      apply hx
      refine ⟨g⁻¹ * t * h, ?_⟩
      simp only [map_mul, map_inv, ht]
      group
    rw [traceBasis_outside R a _ hx, traceBasis_outside R a _ hy, map_zero]

def traceCapBasis (a : ConjEmbedding A B) :
    ((Biset.restriction a).tensor (Biset.induction a)).carrier → A →₀ R :=
  Quotient.lift (fun (z : B × B) => traceBasis R a (z.1 * z.2)) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    change a.toHom 1 * x.1 * h⁻¹ = y.1 at hx
    change h * x.2 * (a.toHom 1)⁻¹ = y.2 at hy
    rw [← hx, ← hy]
    simp [mul_assoc])

def traceCap (a : ConjEmbedding A B) :
    Biset.Hom R ((Biset.restriction a).tensor (Biset.induction a)) (Biset.regular A) :=
  Biset.Hom.ofBasis (traceCapBasis R a) (by
    intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    rcases g with ⟨g,h⟩
    change traceBasis R a ((a.toHom g * x.1 * (1 : B)⁻¹) *
          (1 * x.2 * (a.toHom h)⁻¹)) =
      (Biset.regular A).actLinear R (g,h) (traceBasis R a (x.1 * x.2))
    simpa [mul_assoc] using traceBasis_equivariant R a (x.1 * x.2) g h)

end
end MackeyDiagrams.Generator

