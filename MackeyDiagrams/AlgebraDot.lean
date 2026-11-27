import MackeyDiagrams.LinearDots

/-! A group-algebra intertwiner can label one upward dot. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {H G : Subgroup U}

structure AlgebraUpDot (R : Type v) [CommSemiring R] (a b : ConjEmbedding H G) where
  label : MonoidAlgebra R G
  intertwines : ∀ h : H,
    MonoidAlgebra.single (a.toHom h) 1 * label =
      label * MonoidAlgebra.single (b.toHom h) 1

namespace AlgebraUpDot

variable {R : Type v} [CommSemiring R] {a b : ConjEmbedding H G}

noncomputable section

private theorem actLinear_eq (a : ConjEmbedding H G) (g : G × H)
    (x : G →₀ R) :
    (Biset.induction a).actLinear R g x =
      (MonoidAlgebra.single g.1 1 * MonoidAlgebra.ofCoeff x *
        MonoidAlgebra.single (a.toHom g.2)⁻¹ 1).coeff := by
  let f : (G →₀ R) →ₗ[R] G →₀ R :=
    ⟨⟨fun y => (MonoidAlgebra.single g.1 1 * MonoidAlgebra.ofCoeff y *
        MonoidAlgebra.single (a.toHom g.2)⁻¹ 1).coeff,
      by intro y z; rw [MonoidAlgebra.ofCoeff_add, mul_add, add_mul]; rfl⟩,
      by
        intro r y
        change (MonoidAlgebra.single g.1 1 * MonoidAlgebra.ofCoeff (r • y) *
          MonoidAlgebra.single (a.toHom g.2)⁻¹ 1).coeff = _
        change (MonoidAlgebra.single g.1 1 * (r • MonoidAlgebra.ofCoeff y) *
          MonoidAlgebra.single (a.toHom g.2)⁻¹ 1).coeff = _
        rw [mul_smul_comm, smul_mul_assoc]
        rfl⟩
  change (Biset.induction a).actLinear R g x = f x
  have hh : (Biset.induction a).actLinear R g = f := by
    apply Finsupp.lhom_ext
    intro y r
    rw [Biset.actLinear_single]
    change Finsupp.single (g.1 * y * (a.toHom g.2)⁻¹) r =
      (MonoidAlgebra.single g.1 (1 : R) * MonoidAlgebra.single y r *
        MonoidAlgebra.single (a.toHom g.2)⁻¹ 1).coeff
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, one_mul, mul_one]
    rfl
  rw [hh]

def eval (d : AlgebraUpDot R a b) : Biset.Hom R (Biset.induction a) (Biset.induction b) where
  toLinearMap := ⟨⟨fun x => (MonoidAlgebra.ofCoeff x * d.label).coeff,
    fun x y => by
      change (MonoidAlgebra.ofCoeff (x + y) * d.label).coeff = _
      rw [MonoidAlgebra.ofCoeff_add, add_mul]
      rfl⟩,
    fun r x => by
      change ((r • MonoidAlgebra.ofCoeff x) * d.label).coeff = _
      rw [smul_mul_assoc]
      rfl⟩
  commutes := by
    intro g x
    change (MonoidAlgebra.ofCoeff ((Biset.induction a).actLinear R g x) * d.label).coeff =
      (Biset.induction b).actLinear R g (MonoidAlgebra.ofCoeff x * d.label).coeff
    rw [actLinear_eq a, actLinear_eq b, MonoidAlgebra.ofCoeff_coeff, MonoidAlgebra.ofCoeff_coeff]
    apply congrArg MonoidAlgebra.coeff
    rw [mul_assoc (MonoidAlgebra.single g.1 1 * MonoidAlgebra.ofCoeff x),
      ← map_inv, d.intertwines, map_inv]
    simp only [MonoidAlgebra.ofCoeff_coeff, mul_assoc]

@[simp] theorem eval_apply (d : AlgebraUpDot R a b) (x : G →₀ R) :
    d.eval.toLinearMap x = (MonoidAlgebra.ofCoeff x * d.label).coeff := rfl

def ofGroupDot (d : Dot a b) : AlgebraUpDot R a b where
  label := MonoidAlgebra.single d.element 1
  intertwines := by intro h; simp [d.intertwines]

theorem eval_ofGroupDot (d : Dot a b) :
    (ofGroupDot (R := R) d).eval = (Diagram.upDot (R := R) d).eval := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  rw [Diagram.eval_upDot_single]
  change (MonoidAlgebra.single x r * MonoidAlgebra.single d.element 1).coeff =
    Finsupp.single (x * d.element) r
  rw [MonoidAlgebra.single_mul_single, mul_one]
  rfl

end
end AlgebraUpDot
end MackeyDiagrams
