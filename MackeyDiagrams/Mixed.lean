import MackeyDiagrams.Transfer

/-!
# Mixed crossings

The four embeddings specify the exterior boundary on both levels.
An actual element of the ambient region intertwines the composite embeddings
on the intermediate group. Multiplication always exists. Projection uses
the same underlying function, with a separate finite-fiber hypothesis.
-/

namespace MackeyDiagrams.Generator

universe u v
noncomputable section

variable {U : Type u} [Group U] {H K G L : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)

def mixedProduct : ((Biset.restriction a).tensor (Biset.induction b)).carrier → G :=
  Quotient.lift (fun (z : G × G) => z.1 * z.2) (by
    intro x y hxy
    obtain ⟨g, hx, hy⟩ := hxy
    change a.toHom 1 * x.1 * g⁻¹ = y.1 at hx
    change g * x.2 * (b.toHom 1)⁻¹ = y.2 at hy
    rw [← hx, ← hy]
    simp [mul_assoc])

def mixedPair (x : G) : ((Biset.restriction a).tensor (Biset.induction b)).carrier :=
  (Biset.restriction a).pair (Biset.induction b) x 1

@[simp] theorem mixedProduct_mixedPair (x : G) : mixedProduct a b (mixedPair a b x) = x := by
  change x * 1 = x
  exact mul_one x

@[simp] theorem mixedPair_mixedProduct (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    mixedPair a b (mixedProduct a b z) = z := by
  refine Quotient.inductionOn z (fun xy => ?_)
  let X := Biset.restriction a
  let Y := Biset.induction b
  change X.pair Y (xy.1 * xy.2) 1 = X.pair Y xy.1 xy.2
  simpa [X,Y,Biset.restriction,Biset.induction] using X.pair_balance Y xy.2 xy.1 1

def mixedEquiv : ((Biset.restriction a).tensor (Biset.induction b)).carrier ≃ G where
  toFun := mixedProduct a b
  invFun := mixedPair a b
  left_inv := mixedPair_mixedProduct a b
  right_inv := mixedProduct_mixedPair a b

variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

def mixedMultiplicationBasis :
    ((Biset.induction l).tensor (Biset.restriction r)).carrier →
      ((Biset.restriction a).tensor (Biset.induction b)).carrier :=
  Quotient.lift (fun (z : K × H) => mixedPair a b (a.toHom z.1 * d.element * b.toHom z.2)) (by
    intro x y hxy
    obtain ⟨t, hx, hy⟩ := hxy
    change 1 * x.1 * (l.toHom t)⁻¹ = y.1 at hx
    change r.toHom t * x.2 * (1 : H)⁻¹ = y.2 at hy
    rw [← hx, ← hy]
    apply congrArg (mixedPair a b)
    simp only [one_mul, inv_one, mul_one, map_mul, map_inv]
    have ht : a.toHom (l.toHom t) * d.element = d.element * b.toHom (r.toHom t) :=
      d.intertwines t
    calc
      a.toHom x.1 * d.element * b.toHom x.2 =
        a.toHom x.1 * (a.toHom (l.toHom t))⁻¹ *
          (a.toHom (l.toHom t) * d.element) * b.toHom x.2 := by group
      _ = _ := by rw [ht]; group)

theorem mixedMultiplication_equivariant (k : K × H)
    (w : ((Biset.induction l).tensor (Biset.restriction r)).carrier) :
    mixedMultiplicationBasis a b l r d (((Biset.induction l).tensor (Biset.restriction r)).act k w) =
      ((Biset.restriction a).tensor (Biset.induction b)).act k (mixedMultiplicationBasis a b l r d w) := by
  apply (mixedEquiv a b).injective
  refine Quotient.inductionOn w (fun x => ?_)
  change mixedProduct a b (mixedPair a b
      (a.toHom (k.1 * x.1 * (l.toHom 1)⁻¹) * d.element *
        b.toHom (r.toHom 1 * x.2 * k.2⁻¹))) =
    (a.toHom k.1 * (a.toHom x.1 * d.element * b.toHom x.2) * (1 : G)⁻¹) *
      (1 * 1 * (b.toHom k.2)⁻¹)
  simp [mul_assoc]

variable (R : Type v) [CommSemiring R]

def mixedMultiplication :
    Biset.Hom R ((Biset.induction l).tensor (Biset.restriction r))
      ((Biset.restriction a).tensor (Biset.induction b)) :=
  Biset.Hom.ofFunction (mixedMultiplicationBasis a b l r d) (mixedMultiplication_equivariant a b l r d)

def mixedProjection
    (finite : ∀ z, Set.Finite {w | mixedMultiplicationBasis a b l r d w = z}) :
    Biset.Hom R ((Biset.restriction a).tensor (Biset.induction b))
      ((Biset.induction l).tensor (Biset.restriction r)) :=
  Biset.Hom.transfer R (mixedMultiplicationBasis a b l r d)
    (mixedMultiplication_equivariant a b l r d) finite

end
end MackeyDiagrams.Generator

