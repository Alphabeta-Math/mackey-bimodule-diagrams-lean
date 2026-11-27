import Mathlib.GroupTheory.SemidirectProduct
import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
import Proofs.CaseOneRightProjectionConstruction

set_option maxHeartbeats 2000000

/-
Ian Xiao, Bimodule String Diagrams and the Generalized Mackey Decomposition.
The archived PDF gives the Cases 1 and 2 drawings on p. 22, equation (6.2)
on p. 23 and Example 6.2 on p. 24. The published 28 November revision gives
these on pp. 24, 25 and 26, respectively.
https://getcurious.cc/downloads/mackey-bimodules.pdf#page=26
Published revision SHA-256
813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61.

Example 6.2 is presented in prose. Its left calculation follows the
backward basis maps of Lemma 6.3. The checked supplier
Proofs.EvaluationForTwoProjections gives the coordinate formulas
pulls_left and pulls_mixed, the parameter leftDot and the singleton
evaluation singleton_mixed. Specializing the first three labels to
coefficient-one unit dots makes the parameter one. The two mixed
multiplication basis maps on the left and the map for Q₁ have finite
fibers by injectivity, using the semidirect product splitting and
the trivial balancing group. Thus each Q₁ transfer column over gh
has exactly the basis entry [g,h] with coefficient one.

Theorem 6.4(1) uses the middle index (6.2) for the displayed right
constructor. The checked CaseOneRightProjectionConstruction theorem
uses that constructor family. To apply the obstruction to the full
reviewed PlanarAtBoundary fiber, the proof directly recovers a middle
mixed projection from any putative nonzero evaluation. In this example
the middle internal group contains conjugates of C and F because it
receives the middle outgoing strand from C and the spectator from F.
The two coordinate lines then lie in that group, together with a
conjugate of the swap. The public finite-fiber criterion from
EvaluationForTwoProjections applies to the recovered projection term
with its own finite-fiber proof. The middle index is [G:C] even after
conjugation because G is normal and relative index is preserved under
injective maps. This contradicts finiteness. Every right evaluation
therefore vanishes, while the left column at the unit pair is nonzero.

Alphabeta Math, The Morita data satisfy the bicategory coherence axioms,
Steps 1.1–1.3, motivates the use of associators, unitors and horizontal
composition. The structural constructors here preserve the ordered typed
boundary by Word.boundary_associate and the unit boundary equalities.
The trace checks the exact shared interfaces before stacking and shifts
horizontal positions by the left factor's output width.
https://alphabetamath.cc/item/lem-bimodule-tensor-associators-and-unitors-satisfy-bicategory-coherence

Alphabeta Math, Universal property of module tensor products, Steps 5.1
and 6.1, motivates checking horizontal zero propagation on generators.
Here the inputs are quotient representatives of the balanced biset basis.
The proof uses the checked horizontal formula on Biset.pair generators
and extends by Finsupp linearity. An empty compact projection preserves
its marked vertex and has zero evaluation, so it supplies no witness to
the trace of a nonzero drawing.
https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
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

theorem no_sum_zero {I M : Type*} [AddMonoid M] (v : I → M)
    (h : ∀ i, v i = 0) {target : M} (hne : target ≠ 0) :
    ¬ ∃ ds : List I, (ds.map v).sum = target := by
  rintro ⟨ds, he⟩
  have hsum : (ds.map v).sum = 0 := by induction ds <;> simp_all
  exact hne (he.symm.trans hsum)

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

end CaseOneExample

namespace MackeyDiagrams.CaseOneLocal
universe u v
variable {U : Type u} [Group U]
variable {R : Type v} [CommSemiring R]
variable {K H J : Subgroup U}

open DrawingShape PlanarCode

private theorem shift_append (n : Nat) (a b : Code) :
    shift n (a ++ b) = shift n a ++ shift n b := by simp [shift]

private theorem shift_shift (n m : Nat) (a : Code) :
    shift n (shift m a) = shift (n + m) a := by
  induction a with
  | nil => rfl
  | cons e es ih =>
    change (e.place (m + e.position)).place
      (n + (e.place (m + e.position)).position) ::
        shift n (shift m es) = e.place (n + m + e.position) :: shift (n + m) es
    rw [ih]
    cases e <;> simp [PlanarEvent.place, PlanarEvent.position, Nat.add_assoc]

private theorem encode_stack (a b : DrawingShape) :
    encode (a.stack b) = encode a ++ encode b := by
  induction a generalizing b <;> cases b <;>
    simp [stack, encode, *, List.append_assoc]

private theorem outputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).outputs = a.outputs ++ b.outputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.outputs, List.nil_append, List.append_nil, *, List.append_assoc]

@[simp] private theorem shift_nil (n : Nat) : shift n [] = [] := rfl

@[simp] private theorem shift_zero (xs : Code) : shift 0 xs = xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    change e.place (0 + e.position) :: shift 0 es = e :: es
    rw [Nat.zero_add, ih]
    cases e <;> rfl

private theorem encode_juxtapose (a b : DrawingShape) :
    encode (a.juxtapose b) = encode a ++ shift a.outputs.length (encode b) := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [encode, DrawingShape.outputs, List.length_nil, List.length_append,
      List.nil_append, List.append_nil, shift_nil, shift_zero, shift_append, shift_shift, List.append_assoc, *]

private def geomCode (s : DrawingShape) := encode s.geometry

private theorem geomCode_stack (a b : DrawingShape) :
    geomCode (a.stack b) = geomCode a ++ geomCode b := by
  fun_induction DrawingShape.stack <;>
    simp only [geomCode, DrawingShape.geometry, encode, encode_stack, List.nil_append,
      List.append_nil, List.append_assoc] at *
  simp only [*]

private theorem geomOutputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).geometry.outputs = a.geometry.outputs ++ b.geometry.outputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.geometry, outputs_juxtapose, DrawingShape.outputs,
      List.nil_append, List.append_nil, List.append_assoc] at *
  simp only [*]

private theorem geomCode_juxtapose (a b : DrawingShape) :
    geomCode (a.juxtapose b) = geomCode a ++ shift a.geometry.outputs.length (geomCode b) := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [geomCode, DrawingShape.geometry, encode_juxtapose, outputs_juxtapose, encode,
      DrawingShape.outputs, List.length_nil, List.length_append,
      shift_zero, shift_nil, List.nil_append, List.append_nil,
      List.append_assoc] at *
  rename_i ih
  rw [ih, shift_append, shift_shift]

private theorem stack_assoc (a b c : DrawingShape) :
    (a.stack b).stack c = a.stack (b.stack c) := by
  induction a generalizing b c <;> cases b <;> cases c <;> simp [stack, *]

private theorem inputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).inputs = a.inputs ++ b.inputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.inputs, List.nil_append, List.append_nil, *, List.append_assoc]

private theorem geomInputs_juxtapose (a b : DrawingShape) :
    (a.juxtapose b).geometry.inputs = a.geometry.inputs ++ b.geometry.inputs := by
  fun_induction DrawingShape.juxtapose <;>
    simp only [DrawingShape.geometry, inputs_juxtapose, DrawingShape.inputs,
      List.nil_append, List.append_nil, List.append_assoc] at *
  simp only [*]

private theorem inputs_stack (a b : DrawingShape) (h : a.outputs = b.inputs) :
    (a.stack b).inputs = a.inputs := by
  fun_induction DrawingShape.stack <;> simp_all [DrawingShape.inputs, DrawingShape.outputs]

private theorem outputs_stack (a b : DrawingShape) (h : a.outputs = b.inputs) :
    (a.stack b).outputs = b.outputs := by
  fun_induction DrawingShape.stack <;> simp_all [DrawingShape.inputs, DrawingShape.outputs]

private def VFit : DrawingShape → Prop
  | .vertical first rest => VFit rest ∧ first.geometry.outputs = rest.geometry.inputs
  | _ => True

private theorem geom_stack (a b : DrawingShape) (ha : VFit a)
    (h : a.geometry.outputs = b.geometry.inputs) :
    (a.stack b).geometry = a.geometry.stack b.geometry := by
  fun_induction DrawingShape.stack
  · simp [geometry, stack]
  · rename_i below ds _
    simp only [geometry, DrawingShape.inputs] at h ⊢
    cases hg : below.geometry <;> try rfl
    exact congrArg DrawingShape.straight (by simpa only [hg, DrawingShape.outputs] using h)
  · rename_i first rest above _ ih
    change VFit rest ∧ first.geometry.outputs = rest.geometry.inputs at ha
    simp only [DrawingShape.geometry, outputs_stack _ _ ha.2] at h
    simp only [DrawingShape.geometry, ih ha.1 h, stack_assoc]
  · rfl

private theorem vfit_stack (a b : DrawingShape) (ha : VFit a) (hb : VFit b)
    (h : a.geometry.outputs = b.geometry.inputs) : VFit (a.stack b) := by
  fun_induction DrawingShape.stack
  · exact hb
  · exact ha
  · rename_i first rest above _ ih
    change VFit rest ∧ first.geometry.outputs = rest.geometry.inputs at ha
    simp only [DrawingShape.geometry, outputs_stack _ _ ha.2] at h
    exact ⟨ih ha.1 hb h, by rw [geom_stack _ _ ha.1 h, inputs_stack _ _ h]; exact ha.2⟩
  · exact ⟨hb, h⟩

private theorem vfit_juxtapose (a b : DrawingShape) (ha : VFit a) (hb : VFit b) :
    VFit (a.juxtapose b) := by
  fun_induction DrawingShape.juxtapose <;> first | exact ha | exact hb | trivial

private def Boundary.strands : {A B : Subgroup U} → Boundary A B → Nat
  | _, _, .empty _ => 0
  | _, _, .cons _ p => 1 + Boundary.strands p

private theorem strands_append {A B C : Subgroup U} (p : Boundary A B) (q : Boundary B C) :
    Boundary.strands (p.append q) = Boundary.strands p + Boundary.strands q := by
  induction p with
  | empty => simp [Boundary.strands, Boundary.append]
  | cons s p ih => simp [Boundary.strands, Boundary.append, ih, Nat.add_assoc]

private theorem strands_boundary {A B : Subgroup U} (p : Word A B) :
    Boundary.strands p.boundary = p.directions.length := by
  induction p with
  | empty | up | down => rfl
  | tensor p q ih₁ ih₂ => simp [Word.boundary, Word.directions, strands_append, ih₁, ih₂]

private inductive Crossing : {A B : Subgroup U} → VertexKind → Boundary A B → Boundary A B → Prop
  | parallelUp {A B C D : Subgroup U}
      (b : ConjEmbedding C A) (a : ConjEmbedding B C)
      (b' : ConjEmbedding D A) (a' : ConjEmbedding B D) :
      Crossing .parallelUp (Word.tensor (.up b) (.up a)).boundary
        (Word.tensor (.up b') (.up a')).boundary
  | mixedProjection {A B C D : Subgroup U}
      (a : ConjEmbedding A C) (b : ConjEmbedding B C)
      (l : ConjEmbedding D A) (r : ConjEmbedding D B)
      (term : ProjectionDot.Mixed a b l r) :
      Crossing .mixedProjection (Word.tensor (.down a) (.up b)).boundary
        (Word.tensor (.up l) (.down r)).boundary

private inductive Edge : PlanarEvent → Boundary K H → Boundary K H → Prop
  | padded {A B : Subgroup U} {p q : Boundary A B} {kind : VertexKind}
      (pre : Boundary K A) (suffix : Boundary B H) (c : Crossing kind p q) :
      Edge (.vertex (Boundary.strands pre) kind)
        (pre.append (p.append suffix)) (pre.append (q.append suffix))

private inductive Trace : Code → Boundary K H → Boundary K H → Prop
  | nil (p : Boundary K H) : Trace [] p p
  | cons {e : PlanarEvent} {es : Code} {p q r : Boundary K H}
      (edge : Edge e p q) (tail : Trace es q r) : Trace (e :: es) p r

private theorem Trace.append {p q r : Boundary K H} {xs ys : Code}
    (hx : Trace xs p q) (hy : Trace ys q r) : Trace (xs ++ ys) p r := by
  induction hx with
  | nil => exact hy
  | cons edge _ ih => exact .cons edge (ih hy)

private theorem Edge.padLeft {e : PlanarEvent} {p q : Boundary H J}
    (h : Edge e p q) (pre : Boundary K H) :
    Edge (e.place (Boundary.strands pre + e.position)) (pre.append p) (pre.append q) := by
  cases h with
  | padded inner suffix c =>
    simpa only [strands_append, Boundary.append_assoc, PlanarEvent.place, PlanarEvent.position]
      using (Edge.padded (pre.append inner) suffix c)

private theorem Edge.padRight {e : PlanarEvent} {p q : Boundary K H}
    (h : Edge e p q) (suffix : Boundary H J) :
    Edge e (p.append suffix) (q.append suffix) := by
  cases h with
  | padded pre inner c =>
    simpa only [Boundary.append_assoc] using (Edge.padded pre (inner.append suffix) c)

private theorem Trace.padLeft {p q : Boundary H J} {xs : Code}
    (h : Trace xs p q) (pre : Boundary K H) :
    Trace (shift (Boundary.strands pre) xs) (pre.append p) (pre.append q) := by
  induction h with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (edge.padLeft pre) ih

private theorem Trace.padRight {p q : Boundary K H} {xs : Code}
    (h : Trace xs p q) (suffix : Boundary H J) :
    Trace xs (p.append suffix) (q.append suffix) := by
  induction h with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (edge.padRight suffix) ih

private theorem Trace.one {p q : Boundary K H} {kind : VertexKind} (c : Crossing kind p q) :
    Trace [.vertex 0 kind] p q := by
  have h := Edge.padded (.empty K) (.empty H) c
  rw [Boundary.append, Boundary.append_empty, Boundary.append, Boundary.append_empty] at h
  exact .cons h (.nil _)

private def AllowedEvent : PlanarEvent → Prop
  | .vertex _ k => k = .parallelUp ∨ k = .mixedProjection
  | _ => False

private def Allowed (xs : Code) : Prop := ∀ e ∈ xs, AllowedEvent e

private theorem allowed_append (a b : Code) : Allowed (a ++ b) ↔ Allowed a ∧ Allowed b := by
  simp only [Allowed, List.mem_append, or_imp, forall_and]

private theorem allowed_shift (n : Nat) (xs : Code) : Allowed (shift n xs) ↔ Allowed xs := by
  constructor
  · intro h e he
    have hh := h (e.place (n + e.position)) (List.mem_map_of_mem he)
    cases e <;> exact hh
  · intro h e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    have hh := h f hf
    cases f <;> exact hh

private theorem allowed_single (e : PlanarEvent) : Allowed [e] ↔ AllowedEvent e := by
  simp [Allowed]

private theorem allowed_cons (e : PlanarEvent) (es : Code) :
    Allowed (e :: es) ↔ AllowedEvent e ∧ Allowed es := by
  simp only [Allowed, List.mem_cons, or_imp, forall_and, forall_eq]

private theorem allowed_equivalent {xs ys : Code} (h : Equivalent xs ys) :
    Allowed xs ↔ Allowed ys := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | context _ _ _ ih => simp only [allowed_append, ih]
  | exchange before after i gap l r =>
    have hp (e : PlanarEvent) (n : Nat) : AllowedEvent (e.place n) ↔ AllowedEvent e := by
      cases e <;> rfl
    simp only [allowed_append, allowed_cons, hp]
    tauto
  | add | scale => simp [allowed_single, AllowedEvent]

private theorem horizontal_zero_left {X X' : Biset K H} {Y Y' : Biset H J}
    (f : Biset.Hom R X X') (g : Biset.Hom R Y Y') (hf : f.toLinearMap = 0) :
    (f.horizontal g).toLinearMap = 0 := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change (f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r) = _
  simp [Biset.Hom.horizontal_single, hf]

private theorem horizontal_zero_right {X X' : Biset K H} {Y Y' : Biset H J}
    (f : Biset.Hom R X X') (g : Biset.Hom R Y Y') (hg : g.toLinearMap = 0) :
    (f.horizontal g).toLinearMap = 0 := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change (f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r) = _
  simp [Biset.Hom.horizontal_single, hg]

private theorem compact_empty {A B C D : Subgroup U}
    (a : ConjEmbedding A C) (b : ConjEmbedding B C)
    (l : ConjEmbedding D A) (r : ConjEmbedding D B) :
    (LabelledDrawing.compactProjection (R := R) a b l r []).interpret.eval.toLinearMap = 0 :=
  rfl

private theorem vertical_nonzero {X Y Z : Biset K H}
    (f : Biset.Hom R X Y) (g : Biset.Hom R Y Z)
    (h : (f.vertical g).toLinearMap ≠ 0) : f.toLinearMap ≠ 0 ∧ g.toLinearMap ≠ 0 := by
  change g.toLinearMap.comp f.toLinearMap ≠ 0 at h
  exact ⟨fun hf => h (by simp only [hf, LinearMap.comp_zero]),
    fun hg => h (by simp only [hg, LinearMap.zero_comp])⟩

private def Traced (s : DrawingShape) (p q : Word K H) : Prop :=
  VFit s ∧ s.geometry.inputs = p.directions ∧ s.geometry.outputs = q.directions ∧
    Trace (geomCode s) p.boundary q.boundary

private theorem traced_straight {p q : Word K H} {ds : List Bool}
    (hi : ds = p.directions) (ho : ds = q.directions) (hpq : p.boundary = q.boundary) :
    Traced (.straight ds) p q := by
  refine ⟨trivial, hi, ho, ?_⟩
  change Trace [] p.boundary q.boundary
  rw [hpq]
  exact .nil _

private theorem traced_stack {a b : DrawingShape} {p q r : Word K H}
    (ha : Traced a p q) (hb : Traced b q r) : Traced (a.stack b) p r := by
  obtain ⟨av, ai, ao, ap⟩ := ha
  obtain ⟨bv, bi, bo, bp⟩ := hb
  have link := ao.trans bi.symm
  exact ⟨vfit_stack _ _ av bv link, by rw [geom_stack _ _ av link, inputs_stack _ _ link, ai],
    by rw [geom_stack _ _ av link, outputs_stack _ _ link, bo],
    by rw [geomCode_stack]; exact ap.append bp⟩

private theorem traced_juxtapose {a b : DrawingShape} {p p' : Word K H} {q q' : Word H J}
    (ha : Traced a p p') (hb : Traced b q q') : Traced (a.juxtapose b) (p.tensor q) (p'.tensor q') := by
  obtain ⟨av, ai, ao, ap⟩ := ha
  obtain ⟨bv, bi, bo, bp⟩ := hb
  refine ⟨vfit_juxtapose _ _ av bv, by rw [geomInputs_juxtapose, ai, bi]; rfl,
    by rw [geomOutputs_juxtapose, ao, bo]; rfl, ?_⟩
  rw [geomCode_juxtapose, ao, ← strands_boundary]
  exact (ap.padRight q.boundary).append (bp.padLeft p'.boundary)

private theorem ordinary_trace {p q : Word K H} (d : Diagram R p q)
    (hc : Allowed (geomCode d.drawing)) (hn : d.eval.toLinearMap ≠ 0) :
    Traced d.drawing p q := by
  induction d with
  | id p => exact traced_straight rfl rfl rfl
  | leftUnit p => exact traced_straight rfl rfl rfl
  | insertLeftUnit p => exact traced_straight rfl rfl rfl
  | rightUnit p => exact traced_straight (List.append_nil _).symm rfl (Word.boundary_rightUnit p)
  | insertRightUnit p => exact traced_straight rfl (List.append_nil _).symm (Word.boundary_rightUnit p).symm
  | associate p q r =>
    exact traced_straight rfl (List.append_assoc _ _ _) (Word.boundary_associate p q r)
  | unassociate p q r =>
    exact traced_straight (List.append_assoc _ _ _) rfl (Word.boundary_associate p q r).symm
  | mixedProjection a b l r d fin =>
    exact ⟨trivial, rfl, rfl, Trace.one (.mixedProjection a b l r ⟨d, fin⟩)⟩
  | vertical a b ia ib =>
    have hz := vertical_nonzero a.eval b.eval hn
    have hab : Allowed (geomCode a.drawing ++ geomCode b.drawing) := by
      simpa only [Diagram.drawing, geomCode_stack] using hc
    have ⟨ha, hb⟩ := (allowed_append _ _).mp hab
    exact traced_stack (ia ha hz.1) (ib hb hz.2)
  | horizontal a b ia ib =>
    have hab := hc
    simp only [Diagram.drawing, geomCode_juxtapose, allowed_append, allowed_shift] at hab
    exact traced_juxtapose (ia hab.1 (fun hf => hn (horizontal_zero_left a.eval b.eval hf)))
      (ib hab.2 (fun hg => hn (horizontal_zero_right a.eval b.eval hg)))
  | _ =>
    exfalso
    simp only [Diagram.drawing, geomCode, geometry, encode, allowed_single, AllowedEvent,
      VertexKind.canonical, reduceCtorEq, or_self] at hc

private theorem projectionGeometry_forbidden (n : Nat)
    (opening : ProjectionOpening) (closing : ProjectionClosing) :
    ¬ Allowed (encode (expandedProjectionGeometry n opening closing)) := by
  unfold expandedProjectionGeometry
  cases opening <;>
    simp [encode_stack, allowed_append, allowed_shift, encode,
      allowed_single, AllowedEvent, VertexKind.canonical]

private theorem labelled_trace {p q : Word K H} (d : LabelledDrawing R p q)
    (hc : Allowed (geomCode d.erase)) (hn : d.interpret.eval.toLinearMap ≠ 0) :
    Traced d.erase p q := by
  induction d with
  | ordinary d => exact ordinary_trace d hc hn
  | parallelUp b a b' a' labels =>
    exact ⟨trivial, rfl, rfl, Trace.one (.parallelUp b a b' a')⟩
  | compactProjection a b l r labels =>
    cases labels with
    | nil => exact (hn (compact_empty a b l r)).elim
    | cons term rest =>
      exact ⟨trivial, rfl, rfl, Trace.one (.mixedProjection a b l r term.2)⟩
  | vertical a b ia ib =>
    have hz := vertical_nonzero a.interpret.eval b.interpret.eval hn
    have hab := hc
    simp only [LabelledDrawing.erase, geomCode_stack, allowed_append] at hab
    exact traced_stack (ia hab.1 hz.1) (ib hab.2 hz.2)
  | horizontal a b ia ib =>
    have hab := hc
    simp only [LabelledDrawing.erase, geomCode_juxtapose, allowed_append, allowed_shift] at hab
    exact traced_juxtapose
      (ia hab.1 (fun hf => hn (horizontal_zero_left a.interpret.eval b.interpret.eval hf)))
      (ib hab.2 (fun hg => hn (horizontal_zero_right a.interpret.eval b.interpret.eval hg)))
  | expandedProjection a b l r marks opening closing =>
    exact (projectionGeometry_forbidden 1 opening closing hc).elim
  | expandedProjectionChain a b l r chain fin opening closing =>
    exact (projectionGeometry_forbidden chain.length opening closing hc).elim
  | expandedLinearDotProjection a b l r chain fin opening closing =>
    exact (projectionGeometry_forbidden chain.length opening closing hc).elim
  | bentVertex b =>
    exfalso
    cases b <;> simp [LabelledDrawing.erase, BentVertex.kind, geomCode, geometry, encode,
      allowed_single, AllowedEvent, VertexKind.canonical] at hc
  | _ =>
    exfalso
    simp [LabelledDrawing.erase, geomCode, geometry, rightCurlGeometry, encode_stack,
      encode, allowed_append, allowed_cons, AllowedEvent,
      VertexKind.canonical] at hc

private theorem atBoundary_zero {p q : Word K H} (d : ScopedDiagram R p q)
    (h : d.eval.toLinearMap = 0) : d.atBoundary.eval.toLinearMap = 0 := by
  unfold ScopedDiagram.atBoundary
  change (q.reorderToBoundary.eval.toLinearMap.comp
    (d.eval.toLinearMap.comp p.reorderFromBoundary.eval.toLinearMap)) = 0
  simp only [h, LinearMap.zero_comp, LinearMap.comp_zero]

private theorem planarAtBoundary_trace {p q : Boundary K H} {s : PlanarShape} {template : Code}
    (d : LabelledDrawing.PlanarAtBoundary R p q s)
    (hcode : s.wiring = Quotient.mk PlanarCode.setoid template)
    (hc : Allowed template) (hn : d.interpret.eval.toLinearMap ≠ 0) :
    ∃ xs : Code, Equivalent xs template ∧ Trace xs p q := by
  rcases d with ⟨bottom, top, diagram, rfl, rfl, shape_eq⟩
  have he : Equivalent (geomCode diagram.erase) template :=
    Quotient.exact ((congrArg PlanarShape.wiring shape_eq).trans hcode)
  have ha := (allowed_equivalent he).mpr hc
  have ht := labelled_trace diagram ha (fun h => hn (atBoundary_zero diagram.interpret h))
  exact ⟨_, he, ht.2.2.2⟩


/-- At most three wires are live, so two allowed crossings cannot be disjoint. -/
private def OnThree (xs : Code) : Prop :=
  ∀ e ∈ xs, AllowedEvent e ∧ e.position < 2

private theorem place_allowedEvent (e : PlanarEvent) (i : Nat) :
    AllowedEvent (e.place i) ↔ AllowedEvent e := by cases e <;> rfl

private theorem place_position (e : PlanarEvent) (i : Nat) : (e.place i).position = i := by
  cases e <;> rfl

private theorem allowed_widths (e : PlanarEvent) (h : AllowedEvent e) :
    e.inputs.length = 2 ∧ e.outputs.length = 2 := by
  cases e with
  | vertex i k =>
    rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩
  | zero | add | scale => exact h.elim

private theorem onThree_forbidden (pre post : Code) (e : PlanarEvent)
    (hf : ¬ AllowedEvent e) : ¬ OnThree (pre ++ [e] ++ post) :=
  fun h => hf (h e (by simp)).1

private theorem equivalent_eq_onThree {xs ys : Code} (h : Equivalent xs ys) :
    ∀ pre post : Code,
      (OnThree (pre ++ xs ++ post) → (pre ++ xs ++ post) = (pre ++ ys ++ post)) ∧
      (OnThree (pre ++ ys ++ post) → (pre ++ ys ++ post) = (pre ++ xs ++ post)) := by
  induction h with
  | refl => exact fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact fun pre post => ⟨(ih pre post).2, (ih pre post).1⟩
  | trans _ _ ih₁ ih₂ =>
    intro pre post
    constructor
    · intro ha
      have h₁ := (ih₁ pre post).1 ha
      exact h₁.trans ((ih₂ pre post).1 (h₁ ▸ ha))
    · intro hc
      have h₂ := (ih₂ pre post).2 hc
      exact h₂.trans ((ih₁ pre post).2 (h₂ ▸ hc))
  | context bef aft _ ih =>
    intro pre post
    simpa only [List.append_assoc] using ih (pre ++ bef) (aft ++ post)
  | exchange bef aft i gap l r =>
    intro pre post
    constructor
    · intro h
      have hl := (h (l.place i) (by simp)).1
      have hr := (h (r.place (i + l.outputs.length + gap)) (by simp)).2
      rw [place_position, (allowed_widths l ((place_allowedEvent l i).1 hl)).2] at hr
      omega
    · intro h
      have hl := (h (l.place i) (by simp)).1
      have hr := (h (r.place (i + l.inputs.length + gap)) (by simp)).2
      rw [place_position, (allowed_widths l ((place_allowedEvent l i).1 hl)).1] at hr
      omega
  | @scale i below above a b _ _ =>
    intro pre post
    exact ⟨fun h => (onThree_forbidden pre post (.scale i below above a) (fun he => he) h).elim,
      fun h => (onThree_forbidden pre post (.scale i below above b) (fun he => he) h).elim⟩
  | @add i below above a b c d _ _ _ _ =>
    intro pre post
    exact ⟨fun h => (onThree_forbidden pre post (.add i below above a c) (fun he => he) h).elim,
      fun h => (onThree_forbidden pre post (.add i below above b d) (fun he => he) h).elim⟩

private def rightCode : Code :=
  [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]

private theorem rightCode_onThree : OnThree rightCode := by
  intro e h
  simp only [rightCode, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [AllowedEvent, PlanarEvent.position]

private theorem rightFiber_trace {p q : Boundary K H} {s : PlanarShape}
    (d : LabelledDrawing.PlanarAtBoundary R p q s)
    (hcode : s.wiring = Quotient.mk PlanarCode.setoid rightCode)
    (hn : d.interpret.eval.toLinearMap ≠ 0) : Trace rightCode p q := by
  obtain ⟨xs, he, ht⟩ := planarAtBoundary_trace d hcode (fun e he => (rightCode_onThree e he).1) hn
  have hh := (equivalent_eq_onThree he [] []).2
  simp only [List.nil_append, List.append_nil] at hh
  rw [hh rightCode_onThree]
  exact ht

private theorem rightTemplate_code {A C D E F G : Subgroup U}
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F) :
    let bc := b.comp c
    let ad := a.comp d
    let j := ConjEmbedding.id A
    let drawId := fun {K H : Subgroup U} (p : Word K H) =>
      LabelledDrawing.ordinary (Diagram.id (R := R) p)
    let atRight := fun {K H J L J' : Subgroup U} (p : Word K H)
        {q : Word H J} {r : Word J L} {q' : Word H J'} {r' : Word J' L}
        (crossing : LabelledDrawing R (q.tensor r) (q'.tensor r')) =>
      LabelledDrawing.vertical (LabelledDrawing.ordinary (Diagram.associate p q r))
        (LabelledDrawing.vertical (LabelledDrawing.horizontal (drawId p) crossing)
          (LabelledDrawing.ordinary (Diagram.unassociate p q' r')))
    let rightTemplate :=
      LabelledDrawing.vertical
        (atRight (Word.down a) (LabelledDrawing.parallelUp b c j bc []))
        (LabelledDrawing.vertical
          (LabelledDrawing.horizontal
            (LabelledDrawing.compactProjection a j d ad []) (drawId (Word.up bc)))
          (atRight (Word.up d) (LabelledDrawing.compactProjection ad bc e f [])))
    rightTemplate.planarShape.wiring = Quotient.mk PlanarCode.setoid rightCode := rfl

private abbrev two {K L H : Subgroup U} (s : Strand K L) (t : Strand L H) :
    Boundary K H :=
  .cons s (.cons t (.empty H))

universe w

private abbrev MixedEvidence (U : Type u) [Group U] :=
  ∀ {G J C P : Subgroup U}, ConjEmbedding G P → ConjEmbedding J P →
    ConjEmbedding C G → ConjEmbedding C J → Type w

variable (Evidence : MixedEvidence.{u, w} U)

private inductive TraceEdge :
    {K H : Subgroup U} → Nat → VertexKind → Boundary K H → Boundary K H → Prop
  | parallelUp {K H J J' L : Subgroup U}
      (a : ConjEmbedding J K) (b : ConjEmbedding L J)
      (a' : ConjEmbedding J' K) (b' : ConjEmbedding L J') (suffix : Boundary L H) :
      TraceEdge 0 .parallelUp ((two (.up a) (.up b)).append suffix)
        ((two (.up a') (.up b')).append suffix)
  | mixedProjection {K H P J C : Subgroup U}
      (α : ConjEmbedding K P) (β : ConjEmbedding J P)
      (η : ConjEmbedding C K) (θ : ConjEmbedding C J)
      (label : Evidence α β η θ) (suffix : Boundary J H) :
      TraceEdge 0 .mixedProjection ((two (.down α) (.up β)).append suffix)
        ((two (.up η) (.down θ)).append suffix)
  | prepend {K L H : Subgroup U} {pos : Nat} {kind : VertexKind}
      {p q : Boundary L H} (strand : Strand K L) (edge : TraceEdge pos kind p q) :
      TraceEdge (pos + 1) kind (.cons strand p) (.cons strand q)

private theorem TraceEdge.pad {K L H : Subgroup U} {p q : Boundary L H}
    {pos : Nat} {kind : VertexKind} (edge : TraceEdge Evidence pos kind p q)
    (pre : Boundary K L) :
    TraceEdge Evidence (pos + Boundary.strands pre) kind (pre.append p) (pre.append q) := by
  induction pre with
  | empty => exact edge
  | cons strand tail ih =>
    simpa only [Boundary.strands, Boundary.append, Nat.add_assoc, Nat.add_comm 1 (Boundary.strands tail)] using
      (TraceEdge.prepend (Evidence := Evidence) strand (ih edge))

private inductive TracePath {K H : Subgroup U} :
    PlanarCode.Code → Boundary K H → Boundary K H → Prop
  | nil (p : Boundary K H) : TracePath [] p p
  | cons {p q r : Boundary K H} {pos : Nat} {kind : VertexKind} {code : PlanarCode.Code}
      (edge : TraceEdge Evidence pos kind p q) (rest : TracePath code q r) :
      TracePath (.vertex pos kind :: code) p r

private theorem trace_middle {G A C D E : Subgroup U}
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding D D)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E D)
    (path : TracePath Evidence
      [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]
      (Boundary.cons (.down a) (two (.up b) (.up c)))
      (Boundary.cons (.up d) (two (.up e) (.down f)))) :
    ∃ (P J : Subgroup U) (α : ConjEmbedding G P) (β : ConjEmbedding J P)
      (η : ConjEmbedding C G) (θ : ConjEmbedding C J) (_w : ConjEmbedding D J),
      Nonempty (Evidence α β η θ) := by
  cases path with
  | cons first rest =>
    cases rest with
    | cons middle rest =>
      cases rest with
      | cons last tail =>
        cases tail
        cases last with
        | prepend strand last =>
          cases last with
          | mixedProjection α β η θ label suffix =>
            cases middle with
            | mixedProjection αm βm ηm θm m suffix =>
              exact ⟨_, _, αm, βm, d, α, β, ⟨m⟩⟩


private abbrev MixedWitness : MixedEvidence.{u, u} U :=
  fun α β η θ => ProjectionDot.Mixed α β η θ

private theorem edge_to_inversion {p q : Boundary K H} {ev : PlanarEvent}
    (edge : Edge ev p q) :
    ∃ i kind, ev = .vertex i kind ∧ TraceEdge MixedWitness i kind p q := by
  cases edge with
  | padded pre suffix crossing =>
    refine ⟨_, _, rfl, ?_⟩
    cases crossing with
    | parallelUp b a b' a' =>
      simpa only [Nat.zero_add, Word.boundary, Boundary.append] using
        (TraceEdge.parallelUp (Evidence := MixedWitness) b a b' a' suffix).pad MixedWitness pre
    | mixedProjection a b l r label =>
      simpa only [Nat.zero_add, Word.boundary, Boundary.append] using
        (TraceEdge.mixedProjection (Evidence := MixedWitness) a b l r label suffix).pad MixedWitness pre

private theorem trace_to_inversion {p q : Boundary K H} {es : Code} (t : Trace es p q) :
    TracePath MixedWitness es p q := by
  induction t with
  | nil => exact .nil _
  | cons edge _ ih =>
    obtain ⟨i, kind, rfl, h⟩ := edge_to_inversion edge
    exact .cons h ih

private theorem rightFiber_zero {A E : Subgroup CaseOneExample.U}
    (a : ConjEmbedding CaseOneExample.G A) (b : ConjEmbedding CaseOneExample.D A)
    (c : ConjEmbedding CaseOneExample.D CaseOneExample.D)
    (d : ConjEmbedding CaseOneExample.C CaseOneExample.G) (e : ConjEmbedding E CaseOneExample.C)
    (f : ConjEmbedding E CaseOneExample.D) {s : PlanarShape}
    (hcode : s.wiring = Quotient.mk PlanarCode.setoid rightCode)
    (drawing : LabelledDrawing.PlanarAtBoundary Complex
      (((Word.down a).tensor (.up b)).tensor (.up c)).boundary
      (((Word.up d).tensor (.up e)).tensor (.down f)).boundary s) :
    drawing.interpret.eval.toLinearMap = 0 := by
  by_contra hn
  have path := trace_to_inversion (rightFiber_trace drawing hcode hn)
  obtain ⟨_, _, α, β, η, θ, w, ⟨m⟩⟩ := trace_middle MixedWitness a b c d e f path
  exact CaseOneExample.middle_projection_empty α β η θ w m

end MackeyDiagrams.CaseOneLocal


theorem CaseOneNoFiniteRightReplacement : (
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
) :=
(by
  classical
  dsimp only
  refine ⟨CaseOneExample.cup_index.1, CaseOneExample.cup_index.2,
    CaseOneExample.top_join, CaseOneExample.formula_relIndex, CaseOneExample.infinite_index,
    CaseOneExample.not_finite_formula, CaseOneExample.leftX, CaseOneExample.leftY,
    CaseOneExample.leftZ, CaseOneExample.leftP, rfl, rfl, rfl, rfl,
    CaseOneExample.left_eval, ?_, ?_⟩
  · intro g h
    exact (LinearMap.congr_fun CaseOneExample.left_eval _).trans (CaseOneExample.left_columns g h)
  · apply CaseOneExample.no_sum_zero
    · intro drawing
      exact MackeyDiagrams.CaseOneLocal.rightFiber_zero CaseOneExample.a CaseOneExample.b
        CaseOneExample.c CaseOneExample.d CaseOneExample.e CaseOneExample.f
        (MackeyDiagrams.CaseOneLocal.rightTemplate_code (R := Complex) _ _ _ _ _ _) drawing
    · intro he
      have hleft := (CaseOneExample.boundary_zero_iff _).mp he
      have hz := CaseOneExample.left_eval.symm.trans (CaseOneExample.frame_zero _ _ _ hleft)
      have hn := (LinearMap.congr_fun hz _).symm.trans (CaseOneExample.left_columns 1 1)
      exact (Finsupp.single_ne_zero.mpr one_ne_zero) hn.symm)
