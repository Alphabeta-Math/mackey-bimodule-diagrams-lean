
section Biset

open MackeyDiagrams

variable {U : Type u} [Group U] {K H G : Subgroup U}
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)

private theorem mixedProduct_action (g : K × H)
    (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    Generator.mixedProduct a b (((Biset.restriction a).tensor (Biset.induction b)).act g z) =
      a.toHom g.1 * Generator.mixedProduct a b z * (b.toHom g.2)⁻¹ := by
  refine Quotient.inductionOn z (fun p => ?_)
  change (a.toHom g.1 * p.1 * (1 : G)⁻¹) * (1 * p.2 * (b.toHom g.2)⁻¹) =
    a.toHom g.1 * (p.1 * p.2) * (b.toHom g.2)⁻¹
  simp [mul_assoc]

private theorem mixedCoordinates_action (g : K × H)
    (x : Finsupp ((Biset.restriction a).tensor (Biset.induction b)).carrier Complex) :
    let coord := (Finsupp.domLCongr (Generator.mixedEquiv a b)).trans
      (MonoidAlgebra.coeffLinearEquiv Complex).symm
    coord ((Biset.restriction a |>.tensor (Biset.induction b)).actLinear Complex g x) =
      MonoidAlgebra.of Complex G (a.toHom g.1) * coord x *
        MonoidAlgebra.of Complex G ((b.toHom g.2)⁻¹) := by
  intro coord
  have single (z : ((Biset.restriction a).tensor (Biset.induction b)).carrier) (c : Complex) :
      coord (Finsupp.single z c) = MonoidAlgebra.single (Generator.mixedProduct a b z) c := by
    change (MonoidAlgebra.coeffLinearEquiv Complex).symm
      (Finsupp.domLCongr (Generator.mixedEquiv a b) (Finsupp.single z c)) = _
    rw [Finsupp.domLCongr_single]
    rfl
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]
  | single z c =>
    rw [Biset.actLinear_single, single, single, mixedProduct_action]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul, mul_one]

private def sharedBasis {L : Subgroup U} (l : ConjEmbedding L K) (r : ConjEmbedding L H) :
    Quotient (summandBasis (fun _ : Unit => l.toHom) (fun _ : Unit => r.toHom) ()) ≃
      ((Biset.induction l).tensor (Biset.restriction r)).carrier :=
  Quotient.congrRight (fun _ _ => by
    change (∃ t : L, _ * (l.toHom t)⁻¹ = _ ∧ r.toHom t * _ = _) ↔
      (∃ t : L, (1 : K) * _ * (l.toHom t)⁻¹ = _ ∧ r.toHom t * _ * (1 : H)⁻¹ = _)
    simp)

private theorem multiplication_bijective {J : Type u} {S : J → Subgroup U}
    (l : ∀ j, ConjEmbedding (S j) K) (r : ∀ j, ConjEmbedding (S j) H)
    (s : J → G) (ht : ∀ j t, a.toHom ((l j).toHom t) * s j = s j * b.toHom ((r j).toHom t))
    (index : G → J) (index_mul : ∀ j k h, index (a.toHom k * s j * b.toHom h) = j)
    (factor : ∀ g : G, ∃ j k h, a.toHom k * s j * b.toHom h = g)
    (intersection : ∀ j (k : K) (h : H),
      a.toHom k = s j * b.toHom h * (s j)⁻¹ → ∃ t, (l j).toHom t = k) :
    Function.Bijective
      (toGroup a.toHom b.toHom (fun j => (l j).toHom) (fun j => (r j).toHom) s ht) := by
  let f := toGroup a.toHom b.toHom (fun j => (l j).toHom) (fun j => (r j).toHom) s ht
  let d (j : J) : Dot (a.comp (l j)) (b.comp (r j)) := ⟨s j, ht j⟩
  have factorIndex (j : J) (q : Quotient (summandBasis
      (fun j => (l j).toHom) (fun j => (r j).toHom) j)) :
      index (f ⟨j,q⟩) = j := Quotient.inductionOn q (fun p => index_mul j p.1 p.2)
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hij : i = j := (factorIndex i x).symm.trans ((congrArg index he).trans (factorIndex j y))
    subst j
    apply congrArg (Sigma.mk i)
    apply (sharedBasis (l i) (r i)).injective
    apply Generator.injective_mixedMultiplicationBasis a b (l i) (r i) (d i) (intersection i)
    apply (Generator.mixedEquiv a b).injective
    revert he
    refine Quotient.inductionOn₂ x y (fun p q he => ?_)
    change Generator.mixedProduct a b (Generator.mixedPair a b
        (a.toHom p.1 * s i * b.toHom p.2)) =
      Generator.mixedProduct a b (Generator.mixedPair a b
        (a.toHom q.1 * s i * b.toHom q.2))
    simpa only [Generator.mixedProduct_mixedPair] using he
  · intro g
    obtain ⟨j,k,h,hg⟩ := factor g
    exact ⟨⟨j, Quotient.mk _ (k,h)⟩, hg⟩

end Biset
