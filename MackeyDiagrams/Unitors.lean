import MackeyDiagrams.Associator

/-! Empty words act by the regular biset. -/

namespace MackeyDiagrams.Biset

universe u v
noncomputable section

variable {K H : Type u} [Group K] [Group H]
variable (X : Biset K H)

def leftUnitBasis : ((regular K).tensor X).carrier → X.carrier :=
  Quotient.lift (fun z => X.act (z.1,1) z.2) (by
    intro a b hab
    obtain ⟨k, ha, hb⟩ := hab
    rw [← ha, ← hb, ← X.mul_act]
    change X.act (a.1,1) a.2 = X.act ((1 * a.1 * k⁻¹,1) * (k,1)) a.2
    simp [mul_assoc])

def rightUnitBasis : (X.tensor (regular H)).carrier → X.carrier :=
  Quotient.lift (fun z => X.act (1,z.2⁻¹) z.1) (by
    intro a b hab
    obtain ⟨h, ha, hb⟩ := hab
    rw [← ha, ← hb, ← X.mul_act]
    change X.act (1,a.2⁻¹) a.1 = X.act ((1,(h * a.2 * (1 : H)⁻¹)⁻¹) * (1,h)) a.1
    simp [mul_assoc])

variable (R : Type v) [CommSemiring R]

def leftUnit : Hom R ((regular K).tensor X) X :=
  Hom.ofFunction (leftUnitBasis X) (by
    intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    change X.act (g.1 * x.1 * (1 : K)⁻¹, 1) (X.act (1,g.2) x.2) =
      X.act g (X.act (x.1,1) x.2)
    rw [← X.mul_act, ← X.mul_act]
    rcases g with ⟨k,h⟩
    simp)

def rightUnit : Hom R (X.tensor (regular H)) X :=
  Hom.ofFunction (rightUnitBasis X) (by
    intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    change X.act (1, (1 * x.2 * g.2⁻¹)⁻¹) (X.act (g.1,1) x.1) =
      X.act g (X.act (1,x.2⁻¹) x.1)
    rw [← X.mul_act, ← X.mul_act]
    rcases g with ⟨k,h⟩
    simp)

def insertLeftUnit : Hom R X ((regular K).tensor X) :=
  Hom.ofFunction (fun x => (regular K).pair X 1 x) (by
    intro g x
    change (regular K).pair X 1 (X.act g x) =
      (regular K).pair X (g.1 * 1 * (1 : K)⁻¹) (X.act (1,g.2) x)
    have eq := ((regular K).pair_balance X g.1 1 (X.act (1,g.2) x)).symm
    rw [← X.mul_act] at eq
    rcases g with ⟨k,h⟩
    simpa [regular] using eq)

def insertRightUnit : Hom R X (X.tensor (regular H)) :=
  Hom.ofFunction (fun x => X.pair (regular H) x 1) (by
    intro g x
    change X.pair (regular H) (X.act g x) 1 =
      X.pair (regular H) (X.act (g.1,1) x) (1 * 1 * g.2⁻¹)
    have eq := X.pair_balance (regular H) g.2⁻¹ (X.act (g.1,1) x) 1
    rw [← X.mul_act] at eq
    rcases g with ⟨k,h⟩
    simpa [regular] using eq)

end
end MackeyDiagrams.Biset

