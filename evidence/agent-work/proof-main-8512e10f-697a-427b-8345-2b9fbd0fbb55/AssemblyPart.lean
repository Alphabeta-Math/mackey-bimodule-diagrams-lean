import CanonicalPart

namespace CaseTwoAudit
open MackeyDiagrams

theorem elem_nontrivial : (τ : A) ≠ 1 := by
  intro h
  have he := congrArg (fun x : A => x.val.right) h
  exact (by decide : swap ≠ 1) he

theorem rhs_probe_one : eval rhs (basisVector 1) unitOut = 1 := by
  classical
  rw [right_sum, LinearMap.add_apply, Finsupp.add_apply, transfer_probe, transfer_probe]
  simp only [if_true, ite_eq_right elem_nontrivial, add_zero]

theorem rhs_probe_swap : eval rhs (basisVector τ) unitOut = 1 := by
  classical
  rw [right_sum, LinearMap.add_apply, Finsupp.add_apply, transfer_probe, transfer_probe]
  simp only [if_true, ite_eq_right (Ne.symm elem_nontrivial), zero_add]

theorem eval_add (x y : Drawing) : eval (LabelledDrawing.add x y) = eval x + eval y := by
  ext v out
  change (mergeTop.interpret.eval.toLinearMap
    ((x.interpret.eval.toLinearMap + y.interpret.eval.toLinearMap)
      (splitBottom.interpret.eval.toLinearMap (Finsupp.single v 1)))) out = _
  simp only [LinearMap.add_apply, map_add, Finsupp.add_apply]
  rfl

private theorem eval_zero :
    eval (LabelledDrawing.ordinary (Diagram.zero bottom top)) = 0 := by
  ext v out
  change (mergeTop.interpret.eval.toLinearMap (0 : Finsupp _ Complex)) out = _
  simp

private theorem member_swap_coset_reverse {x z : A}
    (h : z ∈ DoubleCoset.doubleCoset x (line : Set A) (line : Set A)) :
    x ∈ DoubleCoset.doubleCoset z (line : Set A) (line : Set A) := by
  obtain ⟨l,hl,r,hr,he⟩ := DoubleCoset.mem_doubleCoset.mp h
  apply DoubleCoset.mem_doubleCoset.mpr
  exact ⟨l⁻¹, line.inv_mem hl, r⁻¹, line.inv_mem hr, by rw [he]; group⟩

private theorem sum_drawings_zero_at (drawings : List Drawing) (q : A)
    (hall : ∀ x ∈ drawings, eval x (basisVector q) unitOut = 0) :
    eval (sumDrawings drawings) (basisVector q) unitOut = 0 := by
  have fold_zero (ds : List Drawing) :
      ∀ (s : Drawing), eval s (basisVector q) unitOut = 0 →
        (∀ x ∈ ds, eval x (basisVector q) unitOut = 0) →
        eval (ds.foldl LabelledDrawing.add s) (basisVector q) unitOut = 0 := by
    induction ds with
    | nil => exact fun _ h _ => h
    | cons d rest ih =>
      intro s hs h
      apply ih
      · rw [eval_add, LinearMap.add_apply, Finsupp.add_apply, hs, h d List.mem_cons_self, add_zero]
      · exact fun x hx => h x (List.mem_cons_of_mem d hx)
  cases drawings with
  | nil =>
    change eval (LabelledDrawing.ordinary (Diagram.zero bottom top)) (basisVector q) unitOut = _
    rw [eval_zero]
    rfl
  | cons d ds =>
    exact fold_zero ds d (hall d List.mem_cons_self) (fun x hx => hall x (List.mem_cons_of_mem d hx))

end CaseTwoAudit

namespace CaseTwoAudit
open MackeyDiagrams

private theorem candidate_zero (allowed : Set A) (drawing : Drawing)
    (hd : IsLeftWith allowed drawing) (q : A)
    (hq : ∀ x ∈ allowed, x ∉ DoubleCoset.doubleCoset q (line : Set A) (line : Set A)) :
    eval drawing (basisVector q) unitOut = 0 := by
  obtain ⟨_, r, s, t, xs, ys, zs, ha, rfl⟩ := hd
  exact canonical_zero r s t xs ys zs q (fun x hx hh =>
    hq x.dot.element (ha x hx) (member_swap_coset_reverse hh))

theorem allowed_crossings (allowed : Set A) (drawings : List Drawing)
    (hd : ∀ drawing ∈ drawings, IsLeftWith allowed drawing)
    (he : eval (sumDrawings drawings) = eval rhs) :
    (∃ x ∈ allowed, x ∈ line) ∧ (∃ x ∈ allowed, x ∈ swapCoset) := by
  constructor
  · by_contra! h
    have hz := sum_drawings_zero_at drawings 1 (fun d hd' =>
      candidate_zero allowed d (hd d hd') 1 (by
        rw [subset_self_coset 1 line.one_mem]
        exact h))
    rw [he, rhs_probe_one] at hz
    exact one_ne_zero hz
  · by_contra! h
    have hz := sum_drawings_zero_at drawings τ (fun d hd' =>
      candidate_zero allowed d (hd d hd') τ h)
    rw [he, rhs_probe_swap] at hz
    exact one_ne_zero hz

theorem two_left_drawings :
    ∃ l₁ lτ, IsLeftWith (line : Set A) l₁ ∧ IsLeftWith swapCoset lτ ∧
      eval l₁ = Qstar (overall 1) ∧ eval lτ = Qstar (overall τ) ∧
      eval (MackeyDiagrams.LabelledDrawing.add l₁ lτ) = eval rhs := by
  obtain ⟨l₁, h₁, hval₁⟩ := left_transfer (overall 1) line line.one_mem
  obtain ⟨lτ, hτ, hvalτ⟩ := left_transfer (overall τ) swapCoset
    (DoubleCoset.mem_doubleCoset_self line line τ)
  exact ⟨l₁,lτ,h₁,hτ,hval₁,hvalτ,by rw [eval_add, hval₁, hvalτ, right_sum]⟩

theorem canonical_ne {B : Subgroup U}
    (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding T B)
    (xs : Finsupp (ProjectionLabel a b r s) Complex)
    (ys : Finsupp (ProjectionLabel s c t f) Complex)
    (zs : DotLabel Complex (comp r t) de) :
    eval (left r s t xs ys zs) ≠ eval rhs := by
  intro he
  let allowed := {q : A | ∃ x ∈ xs.support, (x : ProjectionLabel a b r s).dot.element = q}
  have ha : IsLeftWith allowed (left r s t xs ys zs) :=
    ⟨B, r,s,t,xs,ys,zs,fun x hx => ⟨x,hx,rfl⟩,rfl⟩
  have hh := allowed_crossings allowed [left r s t xs ys zs] (by simpa) he
  obtain ⟨_, ⟨x, _, rfl⟩, hx⟩ := hh.1
  obtain ⟨_, ⟨y, _, rfl⟩, hy⟩ := hh.2
  exact parameters_incompatible r s x y hx hy

end CaseTwoAudit
