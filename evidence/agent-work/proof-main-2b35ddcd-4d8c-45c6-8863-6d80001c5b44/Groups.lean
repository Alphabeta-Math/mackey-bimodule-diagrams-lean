import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.Fintype.Perm
import Proofs.CaseOneRightProjectionConstruction

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

theorem disjoint_G_D : G ⊓ D = ⊥ := by
  apply le_antisymm _ bot_le
  rintro u ⟨⟨n, hn⟩, ⟨σ, hσ⟩⟩
  have hσ' : σ = 1 := by
    have h := congrArg SemidirectProduct.right (hσ.trans hn.symm)
    exact h
  subst σ
  exact Subgroup.mem_bot.mpr ((map_one permutations).symm.trans hσ).symm

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
