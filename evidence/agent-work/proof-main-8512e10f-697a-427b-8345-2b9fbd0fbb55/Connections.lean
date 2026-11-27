import Fibers
import ShapePart

namespace CaseTwoAudit
open MackeyDiagrams

private theorem one_in_line : (1 : A) ∈ line := line.one_mem
private theorem tau_in_swapCoset : τ ∈ swapCoset := DoubleCoset.mem_doubleCoset_self line line τ

theorem subset_self_coset (p : A) (hp : p ∈ line) :
    DoubleCoset.doubleCoset p (line : Set A) (line : Set A) = line := by
  ext x
  constructor
  · rintro h
    obtain ⟨k,hk,l,hl,rfl⟩ := DoubleCoset.mem_doubleCoset.mp h
    exact line.mul_mem (line.mul_mem hk hp) hl
  · intro hx
    apply DoubleCoset.mem_doubleCoset.mpr
    exact ⟨x * p⁻¹, line.mul_mem hx (line.inv_mem hp), 1, line.one_mem, by group⟩

theorem parameters_incompatible {B : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (x y : ProjectionLabel a b r s) :
    x.dot.element ∈ line → y.dot.element ∈ swapCoset → False := by
  intro hx hy
  have hB := forced_bot r s y.dot hy
  subst B
  exact unbounded_line_fiber r s x.dot hx (x.finite _)

private theorem singletonTerms {X : Type} (x : X) :
    terms (Finsupp.single x (1 : Complex)) = [((1 : Complex), x)] := by
  classical
  have hs : (Finsupp.single x (1 : Complex)).support = {x} := by simp
  unfold terms
  rw [hs]
  simp

-- Theorem 6.4(2), first assertion. This uses the full intersection
-- construction term by term. Its common-region specialization needs an
-- additional finite-index hypothesis that the example does not supply.
theorem left_transfer (p : ProjectionLabel a bc de f) (allowed : Set A)
    (hp : p.dot.element ∈ allowed) :
    ∃ l, IsLeftWith allowed l ∧ eval l = Qstar p := by
  classical
  obtain ⟨l, hw, hval⟩ := (CaseTwoLeftProjectionConstruction a b c d e f).1 p
  obtain ⟨r,s,t,_,_,_,_,x,y,z,hx,_,_,_,_,hl⟩ := hw
  refine ⟨l, ⟨_, r, s, t, Finsupp.single x 1, Finsupp.single y 1,
    Finsupp.single z 1, ?_, ?_⟩, hval⟩
  · intro q hq
    have he : q = x := ((Finsupp.mem_support_single q x (1 : Complex)).mp hq).1
    subst q
    exact hx.symm ▸ hp
  · rw [hl]
    dsimp only [left]
    change _ = LabelledDrawing.vertical
      (LabelledDrawing.horizontal (LabelledDrawing.compactProjection a b r s
        (terms (Finsupp.single x 1))) (drawId (up c)))
      (LabelledDrawing.vertical
        (atRight (up r) (LabelledDrawing.compactProjection s c t f
          (terms (Finsupp.single y 1))))
        (LabelledDrawing.horizontal (LabelledDrawing.parallelUp r t d e
          (terms (Finsupp.single z 1))) (drawId (down f))))
    rw [singletonTerms, singletonTerms, singletonTerms]

end CaseTwoAudit
