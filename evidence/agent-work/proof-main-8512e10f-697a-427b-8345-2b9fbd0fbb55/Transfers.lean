import Fibers

namespace CaseTwoAudit

open MackeyDiagrams

private theorem trivial_dot {P : Subgroup U} (alpha beta : ConjEmbedding T P) (q : P) :
    ∀ h, alpha.toHom h * q = q * beta.toHom h := by
  intro h
  have hh : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.property)
  simp [hh]

noncomputable def proj {J K P : Subgroup U} (alpha : ConjEmbedding J P)
    (beta : ConjEmbedding K P) (eta : ConjEmbedding T J) (theta : ConjEmbedding T K)
    (q : P) (hinj : Function.Injective (fun z : J × K =>
      alpha.toHom z.1 * q * beta.toHom z.2)) : ProjectionLabel alpha beta eta theta := by
  let dot : Dot (alpha.comp eta) (beta.comp theta) :=
    ⟨q, trivial_dot (alpha.comp eta) (beta.comp theta) q⟩
  refine ⟨dot, Generator.finiteFiber_of_injective alpha beta eta theta dot ?_⟩
  intro x y
  refine Quotient.inductionOn₂ x y (fun j k he => ?_)
  change Generator.mixedPair alpha beta (alpha.toHom j.1 * q * beta.toHom j.2) =
    Generator.mixedPair alpha beta (alpha.toHom k.1 * q * beta.toHom k.2) at he
  exact congrArg (Quotient.mk _) (hinj ((Generator.mixedEquiv alpha beta).symm.injective he))

theorem trivial_right_injective {J P : Subgroup U} (alpha : ConjEmbedding J P)
    (beta : ConjEmbedding T P) (q : P) :
    Function.Injective (fun z : J × T => alpha.toHom z.1 * q * beta.toHom z.2) := by
  intro j k he
  have hbot (g : T) : g = 1 := Subtype.ext (Subgroup.mem_bot.mp g.property)
  change alpha.toHom j.1 * q * beta.toHom j.2 =
    alpha.toHom k.1 * q * beta.toHom k.2 at he
  simp only [hbot j.2, hbot k.2, map_one, mul_one] at he
  exact Prod.ext (alpha.injective (mul_right_cancel he)) ((hbot j.2).trans (hbot k.2).symm)

noncomputable def overall (q : A) : ProjectionLabel a bc de f :=
  proj a bc de f q (trivial_right_injective a bc q)

noncomputable def mid (q : A) : ProjectionLabel a u d v :=
  proj a u d v q (trivial_right_injective a u q)

noncomputable def last : ProjectionLabel v w e f :=
  proj v w e f 1 (trivial_right_injective v w 1)

noncomputable def first : Dot bc (comp u w) :=
  ⟨1, trivial_dot bc (comp u w) 1⟩

noncomputable abbrev unitOut :=
  (Biset.induction de).pair (Biset.restriction f) 1 1

theorem transfer_probe (q z : A) :
    Qstar (overall q) (basisVector z) unitOut =
      if q = z then (1 : Complex) else 0 := by
  classical
  let p := overall q
  change
    (Biset.Hom.transfer Complex (Generator.mixedMultiplicationBasis a bc de f p.dot)
        (Generator.mixedMultiplication_equivariant a bc de f p.dot) p.finite).toLinearMap
      (Finsupp.single (Generator.mixedPair a bc z) 1) unitOut = _
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_apply]
  change (if Generator.mixedPair a bc (a.toHom 1 * q * bc.toHom 1) =
      Generator.mixedPair a bc z then 1 else 0) = _
  rw [map_one, map_one, one_mul, mul_one]
  have he : Generator.mixedPair a bc q = Generator.mixedPair a bc z ↔ q = z :=
    (Generator.mixedEquiv a bc).symm.injective.eq_iff
  simp only [he]

end CaseTwoAudit
