import Core

namespace CaseTwoAudit

open MackeyDiagrams

private theorem swap_ne_one : swap ≠ 1 := by decide
private theorem sq_swap : swap * swap = 1 := by decide

theorem line_iff (x : A) : x ∈ line ↔ x.val.left.2 = 1 ∧ x.val.right = 1 := by
  constructor
  · rintro ⟨⟨_, i, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hr⟩
    let g := (SemidirectProduct.inl (φ := action))
      ((MonoidHom.inl (Multiplicative Int) (Multiplicative Int)) x.val.left.1)
    refine ⟨⟨g, ⟨x.val.left.1, rfl⟩⟩, Subtype.ext ?_⟩
    apply SemidirectProduct.ext
    · exact Prod.ext rfl hl.symm
    · exact hr.symm

theorem swapCoset_iff (x : A) : x ∈ swapCoset ↔ x.val.right = swap := by
  constructor
  · intro hx
    obtain ⟨l, hl, r, hr, he⟩ := DoubleCoset.mem_doubleCoset.mp hx
    have h := congrArg (fun a : A => a.val.right) he
    change x.val.right = l.val.right * swap * r.val.right at h
    rw [(line_iff l).mp hl |>.2, (line_iff r).mp hr |>.2, one_mul, mul_one] at h
    exact h
  · intro hx
    let l : A := ⟨⟨(x.val.left.1, 1), 1⟩, Subgroup.mem_top _⟩
    let r : A := ⟨⟨(x.val.left.2, 1), 1⟩, Subgroup.mem_top _⟩
    apply DoubleCoset.mem_doubleCoset.mpr
    refine ⟨l, (line_iff l).mpr ⟨rfl,rfl⟩, r, (line_iff r).mpr ⟨rfl,rfl⟩, ?_⟩
    symm
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change ((x.val.left.1, 1) * action 1 1) * action (1 * swap) (x.val.left.2, 1) = x.val.left
      rw [map_one, one_mul, mul_one]
      change (x.val.left.1, 1) * (if swap = 1 then 1 else
        (MulEquiv.prodComm : MulAut (Multiplicative Int × Multiplicative Int))) (x.val.left.2, 1) = _
      rw [ite_eq_right swap_ne_one]
      exact Prod.ext (mul_one _) (one_mul _)
    · exact (by simpa using hx.symm : (1 : Multiplicative (ZMod 2)) * swap * 1 = x.val.right)

theorem intersect_calc (x : A) : (x ∈ line → intersection x = line) ∧
    (x ∈ swapCoset → intersection x = ⊥) := by
  have conjugation (h : A) (hh : h ∈ line) :
      (x * h * x⁻¹).val.left =
        if x.val.right = 1 then h.val.left else (h.val.left.2, h.val.left.1) := by
    have hr := (line_iff h).mp hh |>.2
    have hx' : action x.val.right h.val.left =
        if x.val.right = 1 then h.val.left else (h.val.left.2, h.val.left.1) := by
      change (if x.val.right = 1 then 1 else MulEquiv.prodComm) h.val.left = _
      split <;> rfl
    change x.val.left * action x.val.right h.val.left *
      action (x.val.right * h.val.right) (action x.val.right⁻¹ x.val.left⁻¹) = _
    rw [hr, mul_one]
    change x.val.left * action x.val.right h.val.left *
      (action x.val.right * action x.val.right⁻¹) x.val.left⁻¹ = _
    rw [← MonoidHom.map_mul, mul_inv_cancel, map_one]
    change x.val.left * action x.val.right h.val.left * x.val.left⁻¹ = _
    rw [mul_comm x.val.left, mul_assoc, mul_inv_cancel, mul_one, hx']
  constructor
  · intro h
    apply le_antisymm inf_le_left
    intro y hy
    have hx := (line_iff x).mp h |>.2
    refine ⟨hy, y, hy, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simpa [MulAut.conj_apply, hx] using conjugation y hy
    · change x.val.right * y.val.right * x.val.right⁻¹ = _
      rw [hx, one_mul, inv_one, mul_one]
  · intro hxcoset
    have hx := (swapCoset_iff x).mp hxcoset
    apply le_antisymm _ bot_le
    rintro y ⟨hy, z, hz, rfl⟩
    change (x * z * x⁻¹) ∈ (⊥ : Subgroup A)
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply SemidirectProduct.ext
    · have hc := conjugation z hz
      rw [hx, ite_eq_right swap_ne_one] at hc
      have hz₂ := (line_iff z).mp hz |>.1
      have hy₂ := (line_iff (x * z * x⁻¹)).mp hy |>.1
      rw [hc] at hy₂
      change z.val.left.1 = 1 at hy₂
      rw [hc, hz₂, hy₂]
      rfl
    · change x.val.right * z.val.right * x.val.right⁻¹ = 1
      rw [(line_iff z).mp hz |>.2, mul_one, mul_inv_cancel]

end CaseTwoAudit
