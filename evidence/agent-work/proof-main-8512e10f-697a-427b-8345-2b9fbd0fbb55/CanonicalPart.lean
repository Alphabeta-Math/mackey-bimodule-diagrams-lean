import RightPart

namespace CaseTwoAudit
open MackeyDiagrams
open private leftDot pulls_left leftDrawing ev atLeft
  weighted weighted_compact weighted_parallel weighted_atLeft weighted_atRight weighted_stack_mem preapply
  from Proofs.EvaluationForTwoProjections

private abbrev EvalMap :=
  ((Word.basis mergedBottom).carrier →₀ Complex) →ₗ[Complex]
    ((Word.basis mergedTop).carrier →₀ Complex)

private noncomputable abbrev probe (q : A) : EvalMap →ₗ[Complex] Complex :=
  (Finsupp.lapply unitOut).comp (preapply (basisVector q))

private theorem atom_zero {B : Subgroup U}
    {r : ConjEmbedding B G} {s : ConjEmbedding B D} {t : ConjEmbedding T B}
    (x : ProjectionLabel a b r s) (y : ProjectionLabel s c t f)
    (z : Dot (comp r t) de) (q : A)
    (hq : q ∉ DoubleCoset.doubleCoset x.dot.element (line : Set A) (line : Set A)) :
    probe q (eval (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)])) = 0 := by
  classical
  have hp := pulls_left a b c d e f x y z (1 : G) (1 : F) (basisVector q)
  have hne : q ≠ a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element := by
    intro he
    exact hq (DoubleCoset.mem_doubleCoset.mpr
      ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, he⟩)
  change probe q (eval (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)])) =
    basisVector q (Generator.mixedPair a bc (a.toHom 1 * (leftDot a b c d e f x y z).element * bc.toHom 1)) at hp
  rw [hp, map_one, map_one, one_mul, mul_one]
  change Finsupp.single (Generator.mixedPair a bc q) (1 : Complex)
    (Generator.mixedPair a bc (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element)) = _
  have hne' : Generator.mixedPair a bc q ≠
      Generator.mixedPair a bc (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element) :=
    fun eq => hne ((Generator.mixedEquiv a bc).symm.injective eq)
  rw [Finsupp.single_apply, ite_eq_right hne']

theorem canonical_zero {B : Subgroup U}
    (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding T B)
    (xs : Finsupp (ProjectionLabel a b r s) Complex)
    (ys : Finsupp (ProjectionLabel s c t f) Complex)
    (zs : DotLabel Complex (comp r t) de) (q : A)
    (hq : ∀ x ∈ xs.support, q ∉ DoubleCoset.doubleCoset x.dot.element (line : Set A) (line : Set A)) :
    probe q (eval (left r s t xs ys zs)) = 0 := by
  classical
  let S := {x // x ∈ xs.support}
  let xs' : List (Complex × S) := xs.support.attach.toList.map (fun x => (xs x.val, x))
  let X (x : ProjectionLabel a b r s) :=
    atLeft (LabelledDrawing.compactProjection a b r s [(1,x)]) (up c)
  let Y (y : ProjectionLabel s c t f) :=
    atRight (up r) (LabelledDrawing.compactProjection s c t f [(1,y)])
  let Z (z : Dot (comp r t) de) :=
    atLeft (LabelledDrawing.parallelUp r t d e [(1,z)]) (down f)
  let Xsum := atLeft (LabelledDrawing.compactProjection a b r s (terms xs)) (up c)
  let Ysum := atRight (up r) (LabelledDrawing.compactProjection s c t f (terms ys))
  let Zsum := atLeft (LabelledDrawing.parallelUp r t d e (DotLabel.terms zs)) (down f)
  have hx : ev Xsum = weighted (fun x => ev (X x)) (terms xs) :=
    weighted_atLeft _ _ _ (weighted_compact a b r s (terms xs))
  have hy : ev Ysum = weighted (fun y => ev (Y y)) (terms ys) :=
    weighted_atRight _ _ _ _ (weighted_compact s c t f (terms ys))
  have hz : ev Zsum = weighted (fun z => ev (Z z)) (DotLabel.terms zs) :=
    weighted_atLeft _ _ _ (weighted_parallel r t d e (DotLabel.terms zs))
  have hx' : ev Xsum = weighted (fun x : S => ev (X x.val)) xs' := by
    rw [hx]
    unfold weighted xs' terms
    simp only [List.map_map, Function.comp_def]
    rw [Finset.sum_map_toList, Finset.sum_map_toList]
    exact (Finset.sum_attach xs.support (fun x => xs x • ev (X x))).symm
  change (ev mergeTop).comp ((ev Zsum).comp ((ev Ysum).comp ((ev Xsum).comp (ev splitBottom)))) ∈
    LinearMap.ker (probe q)
  rw [hx', hy, hz]
  refine weighted_stack_mem _ _ _ _ _ _ xs' (terms ys) (DotLabel.terms zs) ?_
  intro x y z
  exact atom_zero x.val y z q (hq x.val x.property)

end CaseTwoAudit
