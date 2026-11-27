import MackeyDiagrams.Dot
import MackeyDiagrams.Linear

/-!
# Diagram generators

The basis formulas descend through balancing before they are extended
linearly. The finite-index reverse cup and crossing transfers are developed
separately from the ordinary adjunction maps.
-/

namespace MackeyDiagrams

universe u v

noncomputable section

variable {U : Type u} [Group U]
variable (R : Type v) [CommSemiring R] {A B C : Subgroup U}

namespace Generator

def upDot {a b : ConjEmbedding A B} (d : Dot a b) :
    Biset.Hom R (Biset.induction a) (Biset.induction b) :=
  Biset.Hom.ofFunction (fun x => x * d.element) (by
    rintro ⟨g,h⟩ x
    change (g * x * (a.toHom h)⁻¹) * d.element =
      g * (x * d.element) * (b.toHom h)⁻¹
    have hd : (a.toHom h)⁻¹ * d.element = d.element * (b.toHom h)⁻¹ := by
      simpa using d.intertwines h⁻¹
    simp only [mul_assoc, hd])

def downDot {a b : ConjEmbedding A B} (d : Dot a b) :
    Biset.Hom R (Biset.restriction a) (Biset.restriction b) :=
  Biset.Hom.ofFunction (fun x => d.element⁻¹ * x) (by
    rintro ⟨h,g⟩ x
    change d.element⁻¹ * (a.toHom h * x * g⁻¹) =
      b.toHom h * (d.element⁻¹ * x) * g⁻¹
    have hd : b.toHom h * d.element⁻¹ = d.element⁻¹ * a.toHom h :=
      d.inverse.intertwines h
    simp only [← mul_assoc, hd])

def mergeUpBasis (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    ((Biset.induction b).tensor (Biset.induction a)).carrier → C :=
  Quotient.lift (fun (z : C × B) => z.1 * b.toHom z.2) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    change 1 * x.1 * (b.toHom h)⁻¹ = y.1 at hx
    change h * x.2 * (a.toHom 1)⁻¹ = y.2 at hy
    rw [← hx, ← hy]
    simp [mul_assoc])

def mergeUp (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Biset.Hom R ((Biset.induction b).tensor (Biset.induction a))
      (Biset.induction (b.comp a)) :=
  Biset.Hom.ofFunction (mergeUpBasis b a) (by
    intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    rcases g with ⟨g,h⟩
    change (g * x.1 * (b.toHom 1)⁻¹) * b.toHom (1 * x.2 * (a.toHom h)⁻¹) =
      g * (x.1 * b.toHom x.2) * (b.toHom (a.toHom h))⁻¹
    simp [mul_assoc])

def splitUp (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Biset.Hom R (Biset.induction (b.comp a))
      ((Biset.induction b).tensor (Biset.induction a)) :=
  Biset.Hom.ofFunction (fun (x : C) => (Biset.induction b).pair (Biset.induction a) x 1)
    (by
      rintro ⟨g,h⟩ x
      let X := Biset.induction b
      let Y := Biset.induction a
      change X.pair Y (g * x * (b.toHom (a.toHom h))⁻¹) 1 =
        X.pair Y (g * x * (b.toHom 1)⁻¹) (1 * 1 * (a.toHom h)⁻¹)
      simpa [X, Y, Biset.induction] using X.pair_balance Y (a.toHom h)⁻¹ (g*x) 1)

def multiplicationCapBasis (a : ConjEmbedding A B) :
    ((Biset.induction a).tensor (Biset.restriction a)).carrier → B :=
  Quotient.lift (fun (z : B × B) => z.1 * z.2) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    change 1 * x.1 * (a.toHom h)⁻¹ = y.1 at hx
    change a.toHom h * x.2 * (1 : B)⁻¹ = y.2 at hy
    rw [← hx, ← hy]
    simp [mul_assoc])

def multiplicationCap (a : ConjEmbedding A B) :
    Biset.Hom R ((Biset.induction a).tensor (Biset.restriction a)) (Biset.regular B) :=
  Biset.Hom.ofFunction (multiplicationCapBasis a) (by
    intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    rcases g with ⟨g,h⟩
    change (g * x.1 * (a.toHom 1)⁻¹) * (a.toHom 1 * x.2 * h⁻¹) =
      g * (x.1 * x.2) * h⁻¹
    simp [mul_assoc])

def ordinaryCup (a : ConjEmbedding A B) :
    Biset.Hom R (Biset.regular A) ((Biset.restriction a).tensor (Biset.induction a)) :=
  Biset.Hom.ofFunction (fun (x : A) => (Biset.restriction a).pair (Biset.induction a) (a.toHom x) 1)
    (by
      rintro ⟨g,h⟩ x
      let X := Biset.restriction a
      let Y := Biset.induction a
      change X.pair Y (a.toHom (g * x * h⁻¹)) 1 =
        X.pair Y (a.toHom g * a.toHom x * (1 : B)⁻¹) (1 * 1 * (a.toHom h)⁻¹)
      simpa [X, Y, Biset.restriction, Biset.induction] using
        X.pair_balance Y (a.toHom h)⁻¹ (a.toHom g * a.toHom x) 1)

def mergeDownBasis (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    ((Biset.restriction a).tensor (Biset.restriction b)).carrier → C :=
  Quotient.lift (fun (z : B × C) => b.toHom z.1 * z.2) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    change a.toHom 1 * x.1 * h⁻¹ = y.1 at hx
    change b.toHom h * x.2 * (1 : C)⁻¹ = y.2 at hy
    rw [← hx, ← hy]
    simp [mul_assoc])

def mergeDown (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Biset.Hom R ((Biset.restriction a).tensor (Biset.restriction b))
      (Biset.restriction (b.comp a)) :=
  Biset.Hom.ofFunction (mergeDownBasis b a) (by
    intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    rcases g with ⟨h,g⟩
    change b.toHom (a.toHom h * x.1 * (1 : B)⁻¹) *
      (b.toHom 1 * x.2 * g⁻¹) =
      b.toHom (a.toHom h) * (b.toHom x.1 * x.2) * g⁻¹
    simp [mul_assoc])

def splitDown (b : ConjEmbedding B C) (a : ConjEmbedding A B) :
    Biset.Hom R (Biset.restriction (b.comp a))
      ((Biset.restriction a).tensor (Biset.restriction b)) :=
  Biset.Hom.ofFunction (fun (x : C) => (Biset.restriction a).pair (Biset.restriction b) 1 x)
    (by
      rintro ⟨h,g⟩ x
      let X := Biset.restriction a
      let Y := Biset.restriction b
      change X.pair Y 1 (b.toHom (a.toHom h) * x * g⁻¹) =
        X.pair Y (a.toHom h * 1 * (1 : B)⁻¹) (b.toHom 1 * x * g⁻¹)
      simpa [X, Y, Biset.restriction, mul_assoc] using
        (X.pair_balance Y (a.toHom h) 1 (x*g⁻¹)).symm)


end Generator

end

end MackeyDiagrams

