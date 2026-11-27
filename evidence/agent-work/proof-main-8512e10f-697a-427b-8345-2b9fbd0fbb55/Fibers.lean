import GroupPart

namespace CaseTwoAudit

open MackeyDiagrams

private theorem bot_el (j : T) : j = 1 :=
  Subtype.ext (Subgroup.mem_bot.mp j.property)

private theorem unit_index {J K : Subgroup U} [Subsingleton K]
    (i : ConjEmbedding J K) : i.toHom.range.index = 1 := by
  apply Subgroup.index_eq_one.mpr
  ext g
  change (∃ j, i.toHom j = g) ↔ True
  exact iff_true_intro ⟨1, Subsingleton.elim _ _⟩

theorem cup_indices : v.toHom.range.index = 1 ∧ f.toHom.range.index = 1 := by
  let _ : Subsingleton T := ⟨fun j k => (bot_el j).trans (bot_el k).symm⟩
  exact ⟨unit_index v, unit_index f⟩

theorem forced_bot {B : Subgroup U} (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (x : Dot (comp a r) (comp b s)) (hx : x.element ∈ swapCoset) : B = ⊥ := by
  apply le_antisymm _ bot_le
  intro j hj
  let j' : B := ⟨j, hj⟩
  have h : a.toHom (r.toHom j') ∈ intersection x.element := by
    refine ⟨⟨r.toHom j',rfl⟩, b.toHom (s.toHom j'), ⟨s.toHom j',rfl⟩, ?_⟩
    change x.element * b.toHom (s.toHom j') * x.element⁻¹ = a.toHom (r.toHom j')
    have he := x.intertwines j'
    change a.toHom (r.toHom j') * x.element = x.element * b.toHom (s.toHom j') at he
    rw [← he, mul_assoc, mul_inv_cancel, mul_one]
  rw [(intersect_calc x.element).2 hx, Subgroup.mem_bot] at h
  apply Subgroup.mem_bot.mpr
  have h' : a.toHom (r.toHom j') = a.toHom (r.toHom 1) := by simpa only [map_one] using h
  exact congrArg Subtype.val (r.injective (a.injective h'))

theorem line_infinite : Infinite G := by
  apply Infinite.of_injective
    (f := fun n : Int =>
      let i := Multiplicative.ofAdd n
      (⟨⟨(i, 1), 1⟩, ⟨i, rfl⟩⟩ : G))
  intro j k h
  exact congrArg (fun x : G => Multiplicative.toAdd x.val.left.1) h

theorem line_commutes (x y : A) (hx : x ∈ line) (hy : y ∈ line) :
    x * y = y * x := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change x.val.left * action x.val.right y.val.left = y.val.left * action y.val.right x.val.left
    rw [(line_iff x).mp hx |>.2, (line_iff y).mp hy |>.2, map_one]
    exact mul_comm _ _
  · change x.val.right * y.val.right = y.val.right * x.val.right
    rw [(line_iff x).mp hx |>.2, one_mul, mul_one]

theorem unbounded_line_fiber (r : ConjEmbedding T G) (s : ConjEmbedding T D)
    (y : Dot (comp a r) (comp b s)) (hy : y.element ∈ line) :
    ¬ Set.Finite {j | Generator.mixedMultiplicationBasis a b r s y j =
      Generator.mixedPair a b y.element} := by
  let _ : Infinite G := line_infinite
  apply Set.infinite_of_injective_forall_mem
    (f := fun j : G => (Biset.induction r).pair (Biset.restriction s) j j⁻¹)
  · intro j k hk
    have h : (Biset.balance (Biset.induction r) (Biset.restriction s)).r (j,j⁻¹) (k,k⁻¹) :=
      Quotient.exact hk
    obtain ⟨i, hi, _⟩ := h
    change (1 : G) * j * (r.toHom i)⁻¹ = k at hi
    simpa only [bot_el i, map_one, inv_one, one_mul, mul_one] using hi
  · intro j
    change Generator.mixedPair a b (a.toHom j * y.element * b.toHom j⁻¹) =
      Generator.mixedPair a b y.element
    change Generator.mixedPair a b (a.toHom j * y.element * a.toHom j⁻¹) = _
    rw [line_commutes _ _ ⟨j,rfl⟩ hy, map_inv, mul_assoc, mul_inv_cancel, mul_one]

end CaseTwoAudit
