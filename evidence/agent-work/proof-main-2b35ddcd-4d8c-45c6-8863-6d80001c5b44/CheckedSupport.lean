import Mathlib.GroupTheory.SemidirectProduct
import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
import Proofs.CaseOneRightProjectionConstruction

/-
Xiao, Example 6.2, archived original PDF p. 24 and published 28 November
revision p. 26 (SHA-256 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
The Cases 1 and 2 drawings are on archived p. 22 and revised p. 24.
The middle-index criterion (6.2) and Theorem 6.4(1) are on archived p. 23
and revised p. 25. The Alphabeta Math portal reproduces Example 6.2 in prose
without numbered proof steps.

The explicit CaseOneRightProjectionConstruction criterion quantifies over
the displayed constructor form. Here the reviewed endpoint uses the entire
PlanarAtBoundary fiber. The stronger middle-crossing obstruction uses the
finite-fiber implication of EvaluationForTwoProjections. A spectator up
embedding of D and the middle crossing's embedding of C already force
its internal group to be all of U. The order of the three events is forced
even after the planar quotient, since two width-two events at positions
zero or one cannot exchange as disjoint events.
-/


namespace CaseOneExample
open MackeyDiagrams

abbrev N := Fin 2 → Multiplicative Int

def swaps : Equiv.Perm (Fin 2) →* MulAut N :=
  { toFun := fun σ =>
      { toFun := fun x i => x (Equiv.symm σ i)
        invFun := fun x i => x (σ i)
        left_inv := fun x => funext fun i => congrArg x (Equiv.symm_apply_apply σ i)
        right_inv := fun x => funext fun i => congrArg x (Equiv.apply_symm_apply σ i)
        map_mul' := fun _ _ => rfl }
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

abbrev U := SemidirectProduct N (Equiv.Perm (Fin 2)) swaps
abbrev base : N →* U := SemidirectProduct.inl
abbrev permutations : Equiv.Perm (Fin 2) →* U := SemidirectProduct.inr
abbrev G := MonoidHom.range base
abbrev C := Subgroup.map base (MonoidHom.ker (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative Int) 1))
abbrev D := MonoidHom.range permutations

theorem C_le_G : C ≤ G := Subgroup.map_le_range _ _

theorem card_D : Nat.card D = 2 := by
  change Nat.card ↑(Set.range permutations) = 2
  rw [← Nat.card_congr (Equiv.ofInjective permutations SemidirectProduct.inr_injective),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem join_top : C ⊔ D = ⊤ := by
  classical
  apply top_unique
  intro u _
  let τ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hτ : permutations τ ∈ C ⊔ D := (le_sup_right : D ≤ C ⊔ D) ⟨τ, rfl⟩
  let x : N := fun i => if i = 0 then u.left 0 else 1
  let y : N := fun i => if i = 0 then u.left 1 else 1
  have hx : base x ∈ C ⊔ D := (le_sup_left : C ≤ C ⊔ D) ⟨x, by simp [x], rfl⟩
  have hy : base y ∈ C ⊔ D := (le_sup_left : C ≤ C ⊔ D) ⟨y, by simp [y], rfl⟩
  have hz : base (swaps τ y) ∈ C ⊔ D := by
    rw [SemidirectProduct.inl_aut]
    exact (C ⊔ D).mul_mem ((C ⊔ D).mul_mem hτ hy) ((C ⊔ D).inv_mem hτ)
  have hprod : x * swaps τ y = u.left := by
    funext i
    fin_cases i
    · change u.left 0 * 1 = u.left 0
      rw [mul_one]
    · change 1 * u.left 1 = u.left 1
      rw [one_mul]
  rw [← SemidirectProduct.inl_left_mul_inr_right u, ← hprod, map_mul]
  exact (C ⊔ D).mul_mem ((C ⊔ D).mul_mem hx hz) ((le_sup_right : D ≤ C ⊔ D) ⟨_, rfl⟩)

theorem infinite_index : ¬ (C.subgroupOf G).FiniteIndex := by
  let second : G →* Multiplicative Int :=
    (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative Int) 1).comp
      { toFun := fun g => g.1.left
        map_one' := rfl
        map_mul' := by
          rintro ⟨g, n, rfl⟩ ⟨h, m, rfl⟩
          change (base n * base m).left = n * m
          rw [← map_mul]
          rfl }
  have hker : second.ker = C.subgroupOf G := by
    ext g
    obtain ⟨n, hn⟩ := g.2
    have hg : g.1.left = n := by rw [← hn]; rfl
    change g.1.left 1 = 1 ↔ g.1 ∈ C
    rw [hg]
    constructor
    · intro h
      exact ⟨n, h, hn⟩
    · rintro ⟨m, hm, hmg⟩
      rwa [← SemidirectProduct.inl_injective (hmg.trans hn.symm)]
  have hsurj : Function.Surjective second := by
    intro z
    exact ⟨⟨base (fun _ => z), ⟨_, rfl⟩⟩, rfl⟩
  rw [← hker]
  intro h
  let _ : Finite (Multiplicative Int) :=
    Finite.of_equiv (G ⧸ second.ker)
      (QuotientGroup.quotientKerEquivOfSurjective second hsurj).toEquiv
  let _ : Finite Int := Finite.of_equiv (Multiplicative Int) Multiplicative.toAdd
  exact not_finite Int

theorem product_injective : Function.Injective (fun gh : G × D => (gh.1 : U) * (gh.2 : U)) := by
  rintro ⟨g, h⟩ ⟨g', h'⟩ heq
  obtain ⟨n, hn⟩ := g.2
  obtain ⟨n', hn'⟩ := g'.2
  obtain ⟨σ, hσ⟩ := h.2
  obtain ⟨σ', hσ'⟩ := h'.2
  change (g : U) * (h : U) = (g' : U) * (h' : U) at heq
  rw [← hn, ← hn', ← hσ, ← hσ'] at heq
  rw [← SemidirectProduct.mk_eq_inl_mul_inr, ← SemidirectProduct.mk_eq_inl_mul_inr] at heq
  have h₁ := congrArg SemidirectProduct.left heq
  have h₂ := congrArg SemidirectProduct.right heq
  change n = n' at h₁
  change σ = σ' at h₂
  subst n' σ'
  exact Prod.ext (Subtype.ext (hn.symm.trans hn')) (Subtype.ext (hσ.symm.trans hσ'))

private theorem perm_fix_zero (σ : Equiv.Perm (Fin 2)) (h : σ 0 = 0) : σ = 1 := by
  have h₁ : σ 1 = 1 := by
    rcases Fin.eq_zero_or_eq_succ (σ 1) with hh | ⟨i, hi⟩
    · have he : (1 : Fin 2) = 0 := σ.injective (hh.trans h.symm)
      exact (by decide : (1 : Fin 2) ≠ 0) he |> False.elim
    · have hi' : i = 0 := Subsingleton.elim _ _
      rw [hi, hi']
      rfl
  apply Equiv.ext
  intro i
  fin_cases i
  · exact h
  · exact h₁

private theorem perm_not_one (σ : Equiv.Perm (Fin 2)) (h : σ ≠ 1) :
    σ = Equiv.swap 0 1 := by
  have h₀ : σ 0 = 1 := by
    have hne : σ 0 ≠ 0 := fun h₀ => h (perm_fix_zero σ h₀)
    omega
  have h₁ : σ 1 = 0 := by
    have hne : σ 1 ≠ 1 := fun h₁ => (by decide : (1 : Fin 2) ≠ 0)
      (σ.injective (h₁.trans h₀.symm))
    omega
  apply Equiv.ext
  intro i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem subgroup_of_line_and_swap (J : Subgroup U) (hC : C ≤ J)
    (q : U) (hq : q ∈ J) (hqr : q.right ≠ 1) : J = ⊤ := by
  classical
  let τ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hright : q.right = τ := perm_not_one q.right hqr
  have hall (u : N) : base u ∈ J := by
    let x : N := fun i => if i = 0 then u 0 else 1
    let y : N := fun i => if i = 0 then u 1 else 1
    have hx : base x ∈ J := hC ⟨x, by simp [x], rfl⟩
    have hy : base y ∈ J := hC ⟨y, by simp [y], rfl⟩
    have hz : base (swaps τ y) ∈ J := by
      have he : q * base y * q⁻¹ = base (swaps τ y) := by
        have hsplit : q = base q.left * permutations τ := by
          simpa only [hright] using (SemidirectProduct.inl_left_mul_inr_right q).symm
        calc
          q * base y * q⁻¹ =
              base q.left * (permutations τ * base y * (permutations τ)⁻¹) * (base q.left)⁻¹ := by
            conv_lhs => rw [hsplit]
            group
          _ = base (swaps τ y) := by
            rw [← map_inv, ← SemidirectProduct.inl_aut, ← map_inv, ← map_mul, ← map_mul]
            rw [mul_comm q.left, mul_inv_cancel_right]
      rw [← he]
      exact J.mul_mem (J.mul_mem hq hy) (J.inv_mem hq)
    have he : x * swaps τ y = u := by
      funext i
      fin_cases i
      · change u 0 * 1 = u 0
        rw [mul_one]
      · change 1 * u 1 = u 1
        rw [one_mul]
    rw [← he, map_mul]
    exact J.mul_mem hx hz
  have hswap : permutations τ ∈ J := by
    have hm := J.mul_mem (J.inv_mem (hall q.left)) hq
    have he : (base q.left)⁻¹ * q = permutations τ := by
      apply (inv_mul_eq_iff_eq_mul).mpr
      simpa only [hright] using (SemidirectProduct.inl_left_mul_inr_right q).symm
    rwa [he] at hm
  apply top_unique
  intro u _
  rw [← SemidirectProduct.inl_left_mul_inr_right u]
  apply J.mul_mem (hall u.left)
  by_cases h : u.right = 1
  · rw [h, map_one]
    exact J.one_mem
  · rw [perm_not_one u.right h]
    exact hswap

theorem conjugate_join_top (p : U) :
    C ⊔ D.map (MulAut.conj p).toMonoidHom = ⊤ := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let q := (MulAut.conj p) (permutations τ)
  apply subgroup_of_line_and_swap _ le_sup_left q
  · have hq : q ∈ D.map (MulAut.conj p).toMonoidHom :=
      ⟨permutations τ, ⟨τ, rfl⟩, rfl⟩
    exact (le_sup_right : D.map (MulAut.conj p).toMonoidHom ≤ _) hq
  · change (p * permutations τ * p⁻¹).right ≠ 1
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.right_inr]
    intro h
    apply (by decide : Equiv.swap (0 : Fin 2) 1 ≠ 1)
    calc
      τ = p.right⁻¹ * (p.right * τ * p.right⁻¹) * p.right := by group
      _ = 1 := by rw [h]; simp

end CaseOneExample

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

namespace CaseOneExample
open MackeyDiagrams

noncomputable section

-- Lemma 6.3: the public evaluation theorem hides the particular parameter
-- behind an existential. Connect to its checked backward-coordinate formula
-- to identify that parameter at the three unit labels of Xiao's Example 6.2.
-- This is the same checked adapter pattern used by the registered Case 1 supplier.
open Lean Elab Tactic in
private abbrev pullsLeft := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "pulls_left"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev pullsMixed := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "pulls_mixed"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev leftDotFormula := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "leftDot"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev singletonMixed := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "singleton_mixed"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

private theorem product_inclusion_injective :
    Function.Injective (fun gh : G × D => a.toHom gh.1 * b.toHom gh.2) := by
  intro gh gh' he
  exact product_injective (congrArg Subtype.val he)

private theorem product_trivial_injective :
    Function.Injective (fun gh : E × D => s.toHom gh.1 * c.toHom gh.2) := by
  intro gh gh' he
  have h₁ : gh.1 = gh'.1 := Subsingleton.elim _ _
  have h₂ : gh'.1 = 1 := Subsingleton.elim _ _
  change s.toHom gh.1 * c.toHom gh.2 = s.toHom gh'.1 * c.toHom gh'.2 at he
  rw [h₁, h₂, map_one, one_mul, one_mul] at he
  exact Prod.ext h₁ (c.injective he)

def leftX : ProjectionDot.Mixed a b r s := unitProjection a b r s product_inclusion_injective
def leftY : ProjectionDot.Mixed s c t f := unitProjection s c t f product_trivial_injective
def leftZ : Dot (r.comp t) (d.comp e) := unitDot _ _
def leftP : ProjectionDot.Mixed a (b.comp c) (d.comp e) f :=
  unitProjection _ _ _ _ product_inclusion_injective

theorem left_columns (g : G) (h : D) :
    (LabelledDrawing.compactProjection (R := Complex) a (b.comp c) (d.comp e) f [(1, leftP)]).interpret.eval.toLinearMap
      (Finsupp.single (Generator.mixedPair a (b.comp c) (a.toHom g * (b.comp c).toHom h)) 1) =
    Finsupp.single ((Biset.induction (d.comp e)).pair (Biset.restriction f) g h) 1 :=
  (LinearMap.congr_fun (singletonMixed a (b.comp c) (d.comp e) f leftP)
    (Finsupp.single (Generator.mixedPair a (b.comp c) (a.toHom g * (b.comp c).toHom h)) 1)).trans
    (unitProjection_column a (b.comp c) (d.comp e) f product_inclusion_injective g h)

-- The archived PDF puts the example on p. 24. The 28 November PDF puts it on p. 26.
theorem left_eval :
  let G := CaseOneExample.G
  let C := CaseOneExample.C
  let D := CaseOneExample.D
  let hCG := C_le_G
  let A : Subgroup CaseOneExample.U := ⊤
  let F : Subgroup CaseOneExample.U := D
  let B : Subgroup CaseOneExample.U := ⊥
  let E : Subgroup CaseOneExample.U := B
  let inclusion := fun {H K : Subgroup CaseOneExample.U} (h : H ≤ K) =>
    (⟨Subgroup.inclusion h, ⟨1, fun _ => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := inclusion le_top
  let b : MackeyDiagrams.ConjEmbedding D A := inclusion le_top
  let c : MackeyDiagrams.ConjEmbedding F D := MackeyDiagrams.ConjEmbedding.id D
  let d : MackeyDiagrams.ConjEmbedding C G := inclusion hCG
  let e : MackeyDiagrams.ConjEmbedding E C := inclusion bot_le
  let f : MackeyDiagrams.ConjEmbedding E F := inclusion bot_le
  let r : MackeyDiagrams.ConjEmbedding B G := inclusion bot_le
  let s : MackeyDiagrams.ConjEmbedding B D := inclusion bot_le
  let t : MackeyDiagrams.ConjEmbedding E B := MackeyDiagrams.ConjEmbedding.id B
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let _hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let de := comp d e
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let drawId := fun {K H : Subgroup CaseOneExample.U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let mergedEval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup CaseOneExample.U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let left := fun (x : MackeyDiagrams.ProjectionDot.Mixed a b r s)
      (y : MackeyDiagrams.ProjectionDot.Mixed s c t f)
      (z : MackeyDiagrams.Dot (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s [(1, x)]) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f [(1, y)]))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e [(1, z)]) (drawId (down f))))
  mergedEval (left leftX leftY leftZ) =
    (LabelledDrawing.compactProjection (R := Complex) a bc de f [(1, leftP)]).interpret.eval.toLinearMap := by
  classical
  dsimp only
  apply Eq.trans _ (singletonMixed a (b.comp c) (d.comp e) f leftP).symm
  have he : leftDotFormula a b c d e f leftX leftY leftZ = leftP.dot := by
    apply Dot.ext
    change a.toHom (1 : G)⁻¹ * (1 : A) * b.toHom (1 : D) = 1
    simp only [inv_one, map_one, one_mul]
  apply LinearMap.ext
  intro input
  apply Finsupp.ext
  intro output
  refine Quotient.inductionOn output (fun ⟨g,h⟩ => ?_)
  have hleft := pullsLeft a b c d e f leftX leftY leftZ g h
  have hright := pullsMixed a (b.comp c) (d.comp e) f leftP ((Biset.induction (d.comp e)).pair (Biset.restriction f) g h)
  have hcoords := congrArg (fun p =>
    input (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f p
      ((Biset.induction (d.comp e)).pair (Biset.restriction f) g h))) he
  exact ((hleft input).trans hcoords).trans (hright input).symm

end
end CaseOneExample

namespace CaseOneExample
open MackeyDiagrams

private theorem range_coe_conj {H K : Subgroup U} (h : ConjEmbedding H K) :
    ∃ x : U, h.toHom.range.map K.subtype = H.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := h.hasRepresentative
  refine ⟨x, ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, g.2, (hx g).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨h.toHom ⟨g, hg⟩, ⟨_, rfl⟩, hx ⟨g, hg⟩⟩

private theorem map_conj_mul (H : Subgroup U) (x y : U) :
    (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      H.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  apply congrArg (fun f : U →* U => H.map f)
  apply MonoidHom.ext
  intro z
  change x * (y * z * y⁻¹) * x⁻¹ = (x * y) * z * (x * y)⁻¹
  group

theorem middle_group_eq_top {J : Subgroup U} (v : ConjEmbedding C J)
    (w : ConjEmbedding D J) : J = ⊤ := by
  obtain ⟨x, hx⟩ := range_coe_conj v
  obtain ⟨y, hy⟩ := range_coe_conj w
  let xinv := (MulAut.conj x⁻¹).toMonoidHom
  have hC : C ≤ J.map xinv := by
    have hle := Subgroup.map_mono (f := xinv)
      (show (v.toHom.range.map J.subtype) ≤ J by
        rintro _ ⟨z, _, rfl⟩
        exact z.2)
    rw [hx] at hle
    change (C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤ _ at hle
    rw [map_conj_mul, inv_mul_cancel, map_one] at hle
    change C.map (MonoidHom.id U) ≤ _ at hle
    rwa [Subgroup.map_id] at hle
  have hD : D.map (MulAut.conj (x⁻¹ * y)).toMonoidHom ≤ J.map xinv := by
    have hle := Subgroup.map_mono (f := xinv)
      (show (w.toHom.range.map J.subtype) ≤ J by
        rintro _ ⟨z, _, rfl⟩
        exact z.2)
    rw [hy] at hle
    change (D.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤ _ at hle
    rwa [map_conj_mul] at hle
  have ht := sup_le hC hD
  rw [conjugate_join_top] at ht
  apply (Subgroup.map_injective (f := xinv) (MulAut.conj x⁻¹).injective)
  rw [Subgroup.map_top_of_surjective (f := xinv) (MulAut.conj x⁻¹).surjective]
  exact top_unique ht

private theorem G_normal : G.Normal := by
  change (SemidirectProduct.inl (φ := swaps)).range.Normal
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

private theorem conj_range_index {P : Subgroup U} (α : ConjEmbedding G P)
    (η : ConjEmbedding C G) :
    (α.comp η).toHom.range.relIndex α.toHom.range = C.relIndex G := by
  obtain ⟨x, hx⟩ := range_coe_conj (α.comp η)
  obtain ⟨y, hy⟩ := range_coe_conj α
  let _ : G.Normal := G_normal
  have hnormal (z : U) : G.map (MulAut.conj z).toMonoidHom = G :=
    Subgroup.Normal.map_conj_eq G z
  rw [← Subgroup.relIndex_map_map_of_injective _ _ P.subtype_injective, hx, hy, hnormal y]
  let φ := (MulAut.conj x).toMonoidHom
  calc
    (C.map φ).relIndex G = (C.map φ).relIndex (G.map φ) :=
      congrArg ((C.map φ).relIndex) (hnormal x).symm
    _ = C.relIndex G := Subgroup.relIndex_map_map_of_injective (f := φ) _ _ (MulAut.conj x).injective

private theorem top_src_range {P J : Subgroup U} (hJ : J = ⊤)
    (β : ConjEmbedding J P) : β.toHom.range = ⊤ := by
  obtain ⟨z, hz⟩ := β.hasRepresentative
  apply MonoidHom.range_eq_top.mpr
  intro u
  refine ⟨⟨z⁻¹ * u * z, hJ.symm ▸ trivial⟩, Subtype.ext ?_⟩
  rw [hz]
  group

-- The middle crossing alone is impossible once the spectator up-strand
-- gives an embedding of F = D into the middle crossing's other lower group.
theorem middle_projection_empty {P J : Subgroup U} (α : ConjEmbedding G P)
    (β : ConjEmbedding J P) (η : ConjEmbedding C G) (θ : ConjEmbedding C J)
    (w : ConjEmbedding D J) (m : ProjectionDot.Mixed α β η θ) : False := by
  have hfinite := ((EvaluationForTwoProjections α β (ConjEmbedding.id J)
    (ConjEmbedding.id G) η θ).1 m.dot).2.1.mp m.finite
  have hrange := top_src_range (middle_group_eq_top θ w) β
  rw [Subgroup.finiteIndex_iff] at hfinite
  change (α.comp η).toHom.range.relIndex
    (α.toHom.range ⊓ β.toHom.range.map (MulAut.conj m.dot.element).toMonoidHom) ≠ 0 at hfinite
  rw [hrange, Subgroup.map_top_of_surjective _ (MulAut.conj m.dot.element).surjective,
    inf_top_eq, conj_range_index] at hfinite
  exact infinite_index (Subgroup.finiteIndex_iff.mpr hfinite)

end CaseOneExample

namespace CaseOneExample
open MackeyDiagrams

private def ThreeWireCode (code : PlanarCode.Code) : Prop :=
  ∀ event ∈ code,
    event.position ≤ 1 ∧ event.inputs.length = 2 ∧ event.outputs.length = 2 ∧
      ∃ k, event = .vertex event.position k

private theorem ThreeWireCode.middle {pre post code : PlanarCode.Code}
    (h : ThreeWireCode (pre ++ code ++ post)) : ThreeWireCode code := by
  intro event he
  exact h event (List.mem_append_left _ (List.mem_append_right _ he))

private theorem position_place (e : PlanarEvent) (i : Nat) :
    (e.place i).position = i := by cases e <;> rfl

private theorem inputs_place (e : PlanarEvent) (i : Nat) :
    (e.place i).inputs = e.inputs := by cases e <;> rfl

private theorem outputs_place (e : PlanarEvent) (i : Nat) :
    (e.place i).outputs = e.outputs := by cases e <;> rfl

private theorem equivalent_eq_of_three_wires {a b : PlanarCode.Code}
    (h : PlanarCode.Equivalent a b) :
    (ThreeWireCode a → a = b) ∧ (ThreeWireCode b → a = b) := by
  induction h with
  | refl a => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact ⟨fun h => (ih.2 h).symm, fun h => (ih.1 h).symm⟩
  | trans _ _ ih₁ ih₂ =>
    constructor
    · intro ha
      have hab := ih₁.1 ha
      exact hab.trans (ih₂.1 (hab ▸ ha))
    · intro hc
      have hbc := ih₂.2 hc
      exact (ih₁.2 (hbc.symm ▸ hc)).trans hbc
  | context pre post _ ih =>
    constructor
    · intro ha
      rw [ih.1 ha.middle]
    · intro hb
      rw [ih.2 hb.middle]
  | exchange pre post i gap left right =>
    constructor
    · intro ha
      have hleft := ha.middle (left.place i) (by simp)
      have hright := ha.middle (right.place (i + left.outputs.length + gap)) (by simp)
      have hw : left.outputs.length = 2 := by simpa only [outputs_place] using hleft.2.2.1
      have hi : i + left.outputs.length + gap ≤ 1 := by simpa only [position_place] using hright.1
      omega
    · intro hb
      have hleft := hb.middle (left.place i) (by simp)
      have hright := hb.middle (right.place (i + left.inputs.length + gap)) (by simp)
      have hw : left.inputs.length = 2 := by simpa only [inputs_place] using hleft.2.1
      have hi : i + left.inputs.length + gap ≤ 1 := by simpa only [position_place] using hright.1
      omega
  | @scale i below above a b _ _ =>
    constructor <;> intro h
    · obtain ⟨k, hk⟩ := (h (.scale i below above a) (by simp)).2.2.2
      cases hk
    · obtain ⟨k, hk⟩ := (h (.scale i below above b) (by simp)).2.2.2
      cases hk
  | @add i below above a b c d _ _ _ _ =>
    constructor <;> intro h
    · obtain ⟨k, hk⟩ := (h (.add i below above a c) (by simp)).2.2.2
      cases hk
    · obtain ⟨k, hk⟩ := (h (.add i below above b d) (by simp)).2.2.2
      cases hk

theorem right_code_eq {code : PlanarCode.Code}
    (h : Quotient.mk PlanarCode.setoid code =
      Quotient.mk PlanarCode.setoid [.vertex 1 .parallelUp, .vertex 0 .mixedProjection,
        .vertex 1 .mixedProjection]) :
    code = [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection] := by
  apply (equivalent_eq_of_three_wires (Quotient.exact h)).2
  intro event he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl <;> exact ⟨by decide, rfl, rfl, ⟨_, rfl⟩⟩

end CaseOneExample

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

namespace CaseOneExample
open MackeyDiagrams

-- The Cases 1 and 2 figure gives the three ordered positions in the right template.
theorem right_fiber_code : (
let caseOne := fun {U : Type} [Group U] (G C D : Subgroup U) (hCG : C ≤ G) =>
  let A : Subgroup U := ⊤
  let F : Subgroup U := D
  let E : Subgroup U := ⊥
  let inclusion := fun {H K : Subgroup U} (h : H ≤ K) =>
    (⟨Subgroup.inclusion h, ⟨1, fun _ => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := inclusion le_top
  let b : MackeyDiagrams.ConjEmbedding D A := inclusion le_top
  let c : MackeyDiagrams.ConjEmbedding F D := MackeyDiagrams.ConjEmbedding.id D
  let d : MackeyDiagrams.ConjEmbedding C G := inclusion hCG
  let e : MackeyDiagrams.ConjEmbedding E C := inclusion bot_le
  let f : MackeyDiagrams.ConjEmbedding E F := inclusion bot_le
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let j := MackeyDiagrams.ConjEmbedding.id A
  let rightTemplate : MackeyDiagrams.LabelledDrawing Complex bottom top :=
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c j bc []))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d ad []) (drawId (up bc)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection ad bc e f [])))
  let rightShape := MackeyDiagrams.LabelledDrawing.planarShape rightTemplate
  let RightAtBoundary := MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex
    (MackeyDiagrams.Word.boundary bottom) (MackeyDiagrams.Word.boundary top) rightShape
  ∀ drawing : RightAtBoundary,
    PlanarCode.encode drawing.diagram.erase.geometry =
      [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]

let N := Fin 2 → Multiplicative Int
let swaps : Equiv.Perm (Fin 2) →* MulAut N :=
  { toFun := fun σ =>
      { toFun := fun x i => x (Equiv.symm σ i)
        invFun := fun x i => x (σ i)
        left_inv := fun x => funext fun i => congrArg x (Equiv.symm_apply_apply σ i)
        right_inv := fun x => funext fun i => congrArg x (Equiv.apply_symm_apply σ i)
        map_mul' := fun _ _ => rfl }
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
let U := SemidirectProduct N (Equiv.Perm (Fin 2)) swaps
let base : N →* U := SemidirectProduct.inl
let permutations : Equiv.Perm (Fin 2) →* U := SemidirectProduct.inr
let G := MonoidHom.range base
let C := Subgroup.map base (MonoidHom.ker (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative Int) 1))
let D := MonoidHom.range permutations
caseOne G C D (by
  intro u hu
  obtain ⟨n, _, rfl⟩ := hu
  exact ⟨n, rfl⟩)
) := by
  dsimp only
  intro drawing
  apply right_code_eq
  exact congrArg PlanarShape.wiring drawing.shape_eq

end CaseOneExample

namespace CaseOneExample
open MackeyDiagrams


theorem frame_zero {V : Type*} [Group V] {K H : Subgroup V}
    {p q r s : Word K H}
    (before : LabelledDrawing Complex p q) (middle : LabelledDrawing Complex q r)
    (after : LabelledDrawing Complex r s)
    (h : middle.interpret.eval.toLinearMap = 0) :
    (before.vertical (middle.vertical after)).interpret.eval.toLinearMap = 0 := by
  change after.interpret.eval.toLinearMap.comp
    (middle.interpret.eval.toLinearMap.comp before.interpret.eval.toLinearMap) = 0
  rw [h]
  simp

theorem caseOne_when_right_zero : (
let caseOne := fun {U : Type} [Group U] (G C D : Subgroup U) (hCG : C ≤ G) =>
  let A : Subgroup U := ⊤
  let F : Subgroup U := D
  let B : Subgroup U := ⊥
  let E : Subgroup U := B
  let inclusion := fun {H K : Subgroup U} (h : H ≤ K) =>
    (⟨Subgroup.inclusion h, ⟨1, fun _ => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := inclusion le_top
  let b : MackeyDiagrams.ConjEmbedding D A := inclusion le_top
  let c : MackeyDiagrams.ConjEmbedding F D := MackeyDiagrams.ConjEmbedding.id D
  let d : MackeyDiagrams.ConjEmbedding C G := inclusion hCG
  let e : MackeyDiagrams.ConjEmbedding E C := inclusion bot_le
  let f : MackeyDiagrams.ConjEmbedding E F := inclusion bot_le
  let r : MackeyDiagrams.ConjEmbedding B G := inclusion bot_le
  let s : MackeyDiagrams.ConjEmbedding B D := inclusion bot_le
  let t : MackeyDiagrams.ConjEmbedding E B := MackeyDiagrams.ConjEmbedding.id B
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let mergedEval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let left := fun (x : MackeyDiagrams.ProjectionDot.Mixed a b r s)
      (y : MackeyDiagrams.ProjectionDot.Mixed s c t f)
      (z : MackeyDiagrams.Dot (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s [(1, x)]) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f [(1, y)]))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e [(1, z)]) (drawId (down f))))
  let j := MackeyDiagrams.ConjEmbedding.id A
  let rightTemplate : MackeyDiagrams.LabelledDrawing Complex bottom top :=
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c j bc []))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d ad []) (drawId (up bc)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection ad bc e f [])))
  let rightShape := MackeyDiagrams.LabelledDrawing.planarShape rightTemplate
  let RightAtBoundary := MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex
    (MackeyDiagrams.Word.boundary bottom) (MackeyDiagrams.Word.boundary top) rightShape
  let P₁ : Subgroup A := MonoidHom.range (hom ad) ⊔ MonoidHom.range (hom bc)
  (∀ drawing : RightAtBoundary,
    (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret drawing).eval.toLinearMap = 0) →
  Subgroup.index (MonoidHom.range (hom s)) = 2 ∧
  Subgroup.index (MonoidHom.range (hom f)) = 2 ∧
  P₁ = ⊤ ∧
  Subgroup.relIndex (MonoidHom.range (hom ad)) (MonoidHom.range (hom a) ⊓ P₁) =
    Subgroup.relIndex C G ∧
  ¬ Subgroup.FiniteIndex (Subgroup.subgroupOf C G) ∧
  ¬ Subgroup.FiniteIndex
    (Subgroup.subgroupOf (MonoidHom.range (hom ad)) (MonoidHom.range (hom a) ⊓ P₁)) ∧
  (∃ (x : MackeyDiagrams.ProjectionDot.Mixed a b r s)
    (y : MackeyDiagrams.ProjectionDot.Mixed s c t f)
    (z : MackeyDiagrams.Dot (comp r t) de) (p : MackeyDiagrams.ProjectionDot.Mixed a bc de f),
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot x) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot y) = 1 ∧
    MackeyDiagrams.Dot.element z = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p) = 1 ∧
    mergedEval (left x y z) =
      MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
        (MackeyDiagrams.LabelledDrawing.interpret
          (MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex) a bc de f [(1, p)]))) ∧
    (∀ (g : G) (h : F),
      mergedEval (left x y z)
        (Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc (hom a g * hom bc h)) 1) =
      Finsupp.single (MackeyDiagrams.Biset.pair
        (MackeyDiagrams.Biset.induction de) (MackeyDiagrams.Biset.restriction f) g h) 1) ∧
    ¬ (∃ ds : List RightAtBoundary,
      List.sum (List.map (fun drawing => MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret drawing))) ds) =
      MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
        (MackeyDiagrams.ScopedDiagram.atBoundary
          (MackeyDiagrams.LabelledDrawing.interpret (left x y z))))))
let N := Fin 2 → Multiplicative Int
let swaps : Equiv.Perm (Fin 2) →* MulAut N :=
  { toFun := fun σ =>
      { toFun := fun x i => x (Equiv.symm σ i)
        invFun := fun x i => x (σ i)
        left_inv := fun x => funext fun i => congrArg x (Equiv.symm_apply_apply σ i)
        right_inv := fun x => funext fun i => congrArg x (Equiv.apply_symm_apply σ i)
        map_mul' := fun _ _ => rfl }
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
let U := SemidirectProduct N (Equiv.Perm (Fin 2)) swaps
let base : N →* U := SemidirectProduct.inl
let permutations : Equiv.Perm (Fin 2) →* U := SemidirectProduct.inr
let G := MonoidHom.range base
let C := Subgroup.map base (MonoidHom.ker (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative Int) 1))
let D := MonoidHom.range permutations
caseOne G C D (by
  intro u hu
  obtain ⟨n, _, rfl⟩ := hu
  exact ⟨n, rfl⟩)
) := by
  classical
  dsimp only
  intro hzero
  refine ⟨cup_index.1, cup_index.2, top_join, formula_relIndex, infinite_index,
    not_finite_formula, leftX, leftY, leftZ, leftP, rfl, rfl, rfl, rfl, left_eval, ?_, ?_⟩
  · intro g h
    exact (LinearMap.congr_fun left_eval _).trans (left_columns g h)
  · apply no_sum_zero _ hzero
    intro he
    have hleft := (boundary_zero_iff _).mp he

    have hz := left_eval.symm.trans (frame_zero _ _ _ hleft)
    have hcol := left_columns 1 1
    have hn := (LinearMap.congr_fun hz _).symm.trans hcol
    exact (Finsupp.single_ne_zero.mpr one_ne_zero) hn.symm

end CaseOneExample

#print axioms CaseOneExample.caseOne_when_right_zero
#print axioms CaseOneExample.right_fiber_code
#print axioms CaseOneExample.middle_projection_empty
#print axioms CaseOneExample.planar_boundary_zero
