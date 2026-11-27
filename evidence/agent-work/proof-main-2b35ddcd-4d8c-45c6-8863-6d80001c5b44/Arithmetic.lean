import Groups
import Proofs.EvaluationForTwoProjections

namespace CaseOneExample

open MackeyDiagrams

universe u
variable {V : Type u} [Group V]

def incl {H K : Subgroup V} (h : H ≤ K) : ConjEmbedding H K :=
  ⟨Subgroup.inclusion h, ⟨1, fun _ => by simp⟩⟩

theorem range_incl {H K : Subgroup V} (h : H ≤ K) :
    (incl h).toHom.range = H.subgroupOf K := Subgroup.inclusion_range h

theorem range_bot {K : Subgroup V} :
    (incl (bot_le : (⊥ : Subgroup V) ≤ K)).toHom.range = ⊥ := by
  rw [range_incl, Subgroup.bot_subgroupOf]

theorem comp_incl {H K L : Subgroup V} (h : H ≤ K) (k : K ≤ L) :
    (incl k).comp (incl h) = incl (h.trans k) := by
  apply ConjEmbedding.ext
  ext x
  rfl

theorem comp_id_incl {H K : Subgroup V} (h : H ≤ K) :
    (incl h).comp (ConjEmbedding.id H) = incl h := by
  apply ConjEmbedding.ext
  ext x
  rfl

abbrev A : Subgroup U := ⊤
abbrev E : Subgroup U := ⊥
abbrev a := incl (le_top : G ≤ A)
abbrev b := incl (le_top : D ≤ A)
abbrev c := ConjEmbedding.id D
abbrev d := incl C_le_G
abbrev e := incl (bot_le : E ≤ C)
abbrev f := incl (bot_le : E ≤ D)
abbrev r := incl (bot_le : E ≤ G)
abbrev s := incl (bot_le : E ≤ D)
abbrev t := ConjEmbedding.id E

theorem cup_index : s.toHom.range.index = 2 ∧ f.toHom.range.index = 2 := by
  rw [range_bot, Subgroup.index_bot, card_D]
  exact ⟨rfl, rfl⟩

theorem top_join :
    (a.comp d).toHom.range ⊔ (b.comp c).toHom.range = ⊤ := by
  rw [comp_incl, comp_id_incl, range_incl, range_incl,
    ← Subgroup.subgroupOf_sup (le_top : C ≤ A) (le_top : D ≤ A),
    join_top, Subgroup.subgroupOf_self]

theorem formula_relIndex :
    (a.comp d).toHom.range.relIndex (a.toHom.range ⊓ ((a.comp d).toHom.range ⊔
      (b.comp c).toHom.range)) = C.relIndex G := by
  rw [top_join, inf_top_eq, comp_incl, range_incl, range_incl,
    ← Subgroup.relIndex_map_map_of_injective _ _ A.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le (le_top : C ≤ A),
    Subgroup.map_subgroupOf_eq_of_le (le_top : G ≤ A)]

theorem not_finite_formula :
    ¬ ((a.comp d).toHom.range.subgroupOf (a.toHom.range ⊓ ((a.comp d).toHom.range ⊔
      (b.comp c).toHom.range))).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff]
  change ¬ (a.comp d).toHom.range.relIndex _ ≠ 0
  rw [formula_relIndex]
  exact fun h => infinite_index (Subgroup.finiteIndex_iff.mpr h)

section Units
variable {K H P L : Subgroup V}
variable (α : ConjEmbedding K P) (β : ConjEmbedding H P)
variable (η : ConjEmbedding L K) (θ : ConjEmbedding L H)

def unitDot [Subsingleton L] {P : Subgroup V} (x y : ConjEmbedding L P) : Dot x y :=
  ⟨1, fun l => by rw [Subsingleton.elim l 1, map_one, map_one]⟩

theorem mixed_injective [Subsingleton L]
    (hinj : Function.Injective fun z : K × H => α.toHom z.1 * β.toHom z.2) :
    Function.Injective (Generator.mixedMultiplicationBasis α β η θ
      (unitDot (α.comp η) (β.comp θ))) := by
  intro x y
  refine Quotient.inductionOn₂ x y (fun p q hpq => ?_)
  have he := congrArg (Generator.mixedProduct α β) hpq
  change Generator.mixedProduct α β (Generator.mixedPair α β (α.toHom p.1 * 1 * β.toHom p.2)) =
    Generator.mixedProduct α β (Generator.mixedPair α β (α.toHom q.1 * 1 * β.toHom q.2)) at he
  simp only [Generator.mixedProduct_mixedPair, mul_one] at he
  rw [hinj he]

def unitProjection [Subsingleton L]
    (hinj : Function.Injective fun z : K × H => α.toHom z.1 * β.toHom z.2) :
    ProjectionDot.Mixed α β η θ where
  dot := unitDot (α.comp η) (β.comp θ)
  finite y := (Set.finite_singleton y).preimage (mixed_injective α β η θ hinj).injOn

theorem unitProjection_column [Subsingleton L]
    (hinj : Function.Injective fun z : K × H => α.toHom z.1 * β.toHom z.2)
    (k : K) (h : H) :
    let p := unitProjection α β η θ hinj
    let y := (Biset.induction η).pair (Biset.restriction θ) k h
    let x := Generator.mixedPair α β (α.toHom k * β.toHom h)
    (Diagram.mixedProjection (R := Complex) α β η θ p.dot p.finite).eval.toLinearMap
      (Finsupp.single x 1) = Finsupp.single y 1 := by
  classical
  intro p y x
  change (Biset.Hom.transfer Complex (Generator.mixedMultiplicationBasis α β η θ p.dot)
    (Generator.mixedMultiplication_equivariant α β η θ p.dot) p.finite).toLinearMap
      (Finsupp.single x 1) = _
  rw [Biset.Hom.transfer_single, one_smul]
  ext w
  rw [Biset.Hom.transferBasis_apply]
  have hy : Generator.mixedMultiplicationBasis α β η θ p.dot y = x := by
    change Generator.mixedPair α β (α.toHom k * 1 * β.toHom h) = x
    rw [mul_one]
  by_cases hw : w = y
  · subst w
    rw [hy, ite_eq_left rfl, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hw, ite_eq_right]
    exact fun he => hw (mixed_injective α β η θ hinj (he.trans hy.symm))

end Units
end CaseOneExample
