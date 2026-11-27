import MackeyDiagrams.ProjectionFiber

/-! The mixed multiplication crossing for the full intersection is injective. -/

namespace MackeyDiagrams.Generator

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

theorem injective_mixedMultiplicationBasis
    (intersection : ∀ (k : K) (h : H),
      a.toHom k = d.element * b.toHom h * d.element⁻¹ → k ∈ l.toHom.range) :
    Function.Injective (mixedMultiplicationBasis a b l r d) := by
  intro x y
  refine Quotient.inductionOn₂ x y (fun z w hz => ?_)
  rcases z with ⟨k,h⟩
  rcases w with ⟨k',h'⟩
  have hm := congrArg (mixedProduct a b) hz
  change mixedProduct a b (mixedPair a b (a.toHom k * d.element * b.toHom h)) =
    mixedProduct a b (mixedPair a b (a.toHom k' * d.element * b.toHom h')) at hm
  simp only [mixedProduct_mixedPair] at hm
  have he : a.toHom (k⁻¹ * k') = d.element * b.toHom (h * h'⁻¹) * d.element⁻¹ := by
    simp only [map_mul, map_inv]
    calc
      (a.toHom k)⁻¹ * a.toHom k' =
          (a.toHom k)⁻¹ * (a.toHom k' * d.element * b.toHom h') * (b.toHom h')⁻¹ * d.element⁻¹ := by
        group
      _ = (a.toHom k)⁻¹ * (a.toHom k * d.element * b.toHom h) * (b.toHom h')⁻¹ * d.element⁻¹ := by
        rw [hm]
      _ = _ := by group
  obtain ⟨t,ht⟩ := intersection (k⁻¹*k') (h*h'⁻¹) he
  have hr : r.toHom t = h * h'⁻¹ := by
    apply b.injective
    apply mul_left_cancel (a := d.element)
    calc
      d.element * b.toHom (r.toHom t) = a.toHom (l.toHom t) * d.element :=
        (d.intertwines t).symm
      _ = (d.element * b.toHom (h * h'⁻¹) * d.element⁻¹) * d.element := by rw [ht, he]
      _ = _ := by group
  apply Quotient.sound
  refine ⟨t⁻¹, ?_, ?_⟩
  · change 1 * k * (l.toHom t⁻¹)⁻¹ = k'
    rw [one_mul, map_inv, inv_inv, ht, ← mul_assoc, mul_inv_cancel, one_mul]
  · change r.toHom t⁻¹ * h * (1 : H)⁻¹ = h'
    rw [map_inv, hr, inv_one, mul_one]
    group

theorem finiteFiber_of_injective (injective : Function.Injective (mixedMultiplicationBasis a b l r d))
    (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    Set.Finite {w | mixedMultiplicationBasis a b l r d w = z} :=
  Set.Subsingleton.finite (fun _ hx _ hy => injective (hx.trans hy.symm))

theorem mixedRange_eq_doubleCoset (g : G) :
    Generator.mixedPair a b g ∈ Set.range (mixedMultiplicationBasis a b l r d) ↔
      ∃ (k : K) (h : H), g = a.toHom k * d.element * b.toHom h := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨⟨k,h⟩,hr⟩ := Quotient.exists_rep w
    rw [← hr] at hw
    refine ⟨k,h,?_⟩
    have he := congrArg (mixedProduct a b) hw
    change mixedProduct a b (mixedPair a b (a.toHom k * d.element * b.toHom h)) =
      mixedProduct a b (mixedPair a b g) at he
    simpa only [mixedProduct_mixedPair] using he.symm
  · rintro ⟨k,h,rfl⟩
    exact ⟨(Biset.induction l).pair (Biset.restriction r) k h,rfl⟩

end MackeyDiagrams.Generator
