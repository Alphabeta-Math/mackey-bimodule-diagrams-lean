import Defs

namespace CaseFiveInfiniteAux
open MackeyDiagrams

-- Example 6.6 and (6.3)–(6.4), archived p. 27, published 28 November
-- revision p. 29. The column calculations use the actual balanced basis.
theorem bot_forced (Q : Subgroup U) (e : ConjEmbedding Q T) : Q = T := by
  apply le_antisymm _ bot_le
  intro x hx
  have he : e.toHom ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
  have hinj := e.injective (he.trans (map_one _).symm)
  exact (congrArg Subtype.val hinj : x = 1)

theorem input_surj (v : X.carrier) : ∃ g x : P, inputPair g x = v := by
  refine Quotient.inductionOn v (fun gy => ?_)
  exact ⟨gy.1, Generator.mixedProduct a a gy.2,
    congrArg ((Biset.induction a).pair _ gy.1) (Generator.mixedPair_mixedProduct a a gy.2)⟩

theorem output_mul (g x : P) : outputPair g x = outputPair (g * x) 1 := by
  have h := (Biset.induction p).pair_balance (Word.basis (tensor ce ef))
    x g (Generator.mixedPair p a 1)
  rw [show (Biset.induction p).act (1, x⁻¹) g = g * x by
    change 1 * g * (p.toHom (x⁻¹))⁻¹ = _
    simp [ConjEmbedding.id]] at h
  change outputPair (g * x) 1 =
    (Biset.induction p).pair _ g
      ((Word.basis (tensor ce ef)).act (x,1) (Generator.mixedPair p a 1)) at h
  rw [show (Word.basis (tensor ce ef)).act (x,1) (Generator.mixedPair p a 1) =
      Generator.mixedPair p a x by
    unfold Generator.mixedPair
    rw [Biset.act_pair]
    change (Biset.restriction p).pair (Biset.induction a)
      (p.toHom x * 1 * (1 : P)⁻¹) (1 * 1 * (a.toHom 1)⁻¹) = _
    simp [ConjEmbedding.id]] at h
  exact h.symm

theorem target_identification :
    ∃ identify : Y.carrier ≃ P, ∀ h y : P, identify (outputPair h y) = h * y := by
  let pr := Biset.leftUnitBasis (Word.basis (tensor ce ef))
  let prod := fun z : Y.carrier => Generator.mixedProduct p a (pr z)
  have pr_mul (g x : P) : prod (outputPair g x) = g * x := by
    unfold prod pr outputPair
    change Generator.mixedProduct p a
      ((Word.basis (tensor ce ef)).act (g,1) (Generator.mixedPair p a x)) = _
    unfold Generator.mixedPair
    rw [Biset.act_pair]
    change (p.toHom g * x * (1 : P)⁻¹) * (1 * 1 * (a.toHom 1)⁻¹) = _
    simp [ConjEmbedding.id]
  refine ⟨⟨prod, (outputPair · 1), ?_, ?_⟩, pr_mul⟩
  · intro z
    refine Quotient.inductionOn z (fun gy => ?_)
    change outputPair (prod ((Biset.induction p).pair _ gy.1 gy.2)) 1 =
      (Biset.induction p).pair _ gy.1 gy.2
    rw [← Generator.mixedPair_mixedProduct p a gy.2] at *
    -- Keep the inner quotient representative independent of its normal form.
    change outputPair (prod (outputPair gy.1 (Generator.mixedProduct p a gy.2))) 1 =
      outputPair gy.1 (Generator.mixedProduct p a gy.2)
    rw [pr_mul, output_mul gy.1 (Generator.mixedProduct p a gy.2)]
  · intro z
    rw [pr_mul, mul_one]

theorem terms_single {S K : Subgroup U} {b c : ConjEmbedding S K} (d : Dot b c) :
    DotLabel.terms (Finsupp.single d (1 : Complex)) = [(1, d)] := by
  classical
  simp [DotLabel.terms]

theorem right_fiber (d : Dot (comp a i) (comp a i)) (x : P) :
    {w | Generator.mixedProduct a a (Generator.mixedMultiplicationBasis a a i i d w) = x} =
      if x = d.element then
        {Biset.pair (Biset.induction i) (Biset.restriction i) 1 1} else ∅ := by
  classical
  have all (w : (Word.basis (tensor ai fj)).carrier) :
      w = Biset.pair (Biset.induction i) (Biset.restriction i) 1 1 := by
    refine Quotient.inductionOn w (fun xy => ?_)
    have he : xy = (1, 1) := Subsingleton.elim _ _
    rw [he]
    rfl
  ext w
  rw [all w]
  change Generator.mixedProduct a a (Generator.mixedPair a a
    (a.toHom 1 * d.element * a.toHom 1)) = x ↔ _
  rw [Generator.mixedProduct_mixedPair, map_one, one_mul, mul_one]
  by_cases h : x = d.element <;> simp [h, eq_comm]

-- Step 1 of the checked right-hand calculation uses the finite transfer
-- fiber. The middle and upper steps use its actual basis representatives.
theorem right_column (r g x : P) :
    eval (rightTerm r) (input g x) = if x = r then output (g*x) else 0 := by
  classical
  let lower := dot (comp a i) (comp a i) r
  let middle := dot (comp a i) (comp p a) r
  let upper := dot (comp p a) (comp a i) 1
  have hf (z : P) : Set.Finite {w | Generator.mixedProduct a a
      (Generator.mixedMultiplicationBasis a a i i lower w) = z} := by
    rw [right_fiber]
    split <;> simp
  have h := ((EvaluationWithOneProjection a a a p p a).2 T i i a).1 lower hf middle upper g x
  -- The two proofs of finiteness on the same mixed-product fiber are
  -- definitionally interchangeable by proof irrelevance.
  unfold rightTerm right
  simp only [terms_single, List.map_cons, List.map_nil]
  refine h.trans ?_
  symm
  -- The displayed term has support at the one admissible second coordinate.
  let w₀ := Biset.pair (Biset.induction i) (Biset.restriction i) 1 1
  change (if x = r then output (g*x) else 0) =
    (hf x).toFinset.sum (fun w =>
      Finsupp.single (outputPair (g * a.toHom (Quotient.out w).1 * r)
        ((1 : P) * a.toHom (Quotient.out w).2)) 1)
  have value (w : (Word.basis (tensor ai fj)).carrier) :
      Finsupp.single (outputPair (g * a.toHom (Quotient.out w).1 * r)
        ((1 : P) * a.toHom (Quotient.out w).2)) (1 : Complex) = output (g*r) := by
    rw [show (Quotient.out w).1 = (1 : T) from Subsingleton.elim _ _,
      show (Quotient.out w).2 = (1 : T) from Subsingleton.elim _ _]
    simp [output]
  by_cases hx : x = r
  · have ht : (hf x).toFinset = {w₀} := by
      ext w
      rw [Set.Finite.mem_toFinset, right_fiber]
      simp [hx, lower, w₀]
    rw [ite_eq_left hx, ht, Finset.sum_singleton, value, hx]
  · have ht : (hf x).toFinset = ∅ := by
      ext w
      rw [Set.Finite.mem_toFinset, right_fiber]
      simp [hx, lower]
    rw [ite_eq_right hx, ht, Finset.sum_empty]



theorem capPair (v w : P) :
    (Biset.induction p).pair (Biset.restriction p) v w =
      (Biset.induction p).pair (Biset.restriction p) (v*w) 1 := by
  have h := (Biset.induction p).pair_balance (Biset.restriction p) w v 1
  change (Biset.induction p).pair (Biset.restriction p)
    (1 * v * (p.toHom w⁻¹)⁻¹) 1 =
    (Biset.induction p).pair (Biset.restriction p) v (p.toHom w * 1 * (1:P)⁻¹) at h
  simpa [ConjEmbedding.id] using h.symm

theorem left_fiber (z : P) :
    {w | Generator.mixedProduct p p (Generator.mixedMultiplicationBasis p p p p leftDot w) = z} =
      {(Biset.induction p).pair (Biset.restriction p) z 1} := by
  ext w
  refine Quotient.inductionOn w (fun xy => ?_)
  change Generator.mixedProduct p p (Generator.mixedPair p p (xy.1 * 1 * xy.2)) = z ↔
    (Biset.induction p).pair (Biset.restriction p) xy.1 xy.2 =
      (Biset.induction p).pair (Biset.restriction p) z 1
  rw [Generator.mixedProduct_mixedPair, mul_one, capPair]
  constructor
  · exact fun h => congrArg (fun v => (Biset.induction p).pair (Biset.restriction p) v 1) h
  · intro h
    have he := congrArg (Generator.multiplicationCapBasis p) h
    change (xy.1 * xy.2) * 1 = z * 1 at he
    simpa using he

noncomputable def leftNative :
    LabelledDrawing Complex (tensor (tensor ga ad) df) (tensor (tensor gc ce) ef) :=
  stack (beside leftMixed (drawId df))
    (stack (plain (Diagram.associate ce gc df))
      (stack (beside (drawId ce) leftParallel)
        (stack (plain (Diagram.unassociate ce gc ef))
          (beside leftProject (drawId ef)))))

-- Steps 1–3 of the checked Case 5 left-shape evaluation apply locally.
-- The two structural isomorphisms below align its native parentheses with
-- Example 6.6. The fiber proof uses the full-range inclusion p.
theorem left_column (g x : P) : eval left (input g x) = output (g*x) := by
  classical
  let q := fun z : P => {w | Generator.mixedProduct p p
      (Generator.mixedMultiplicationBasis p p p p leftDot w) = z}
  have hf (z : P) : (q z).Finite := by
    change Set.Finite {w | Generator.mixedProduct p p
      (Generator.mixedMultiplicationBasis p p p p leftDot w) = z}
    rw [left_fiber]
    exact Set.finite_singleton _
  let nativeIn := (Biset.induction a).pair (Biset.restriction a) g x
  have h := ((EvaluationWithOneProjection a a a p p a).1 p p p).1
    (Dot.id (comp p a)) (Dot.id (comp p a)) leftDot hf g x
  have hNative :
      leftNative.interpret.eval.toLinearMap
        (Finsupp.single ((Word.basis (tensor ga ad)).pair (Biset.induction a) nativeIn 1) 1) =
      (hf (g*x)).toFinset.sum (fun w =>
        Finsupp.single ((Word.basis (tensor gc ce)).pair (Biset.induction a) w 1) 1) := by
    have hh : p.toHom g * (Dot.id (comp p a)).element * p.toHom x *
        (Dot.id (comp p a)).element = g*x := by
      change g * 1 * x * 1 = _
      simp
    dsimp only at h
    rw [hh] at h
    exact h
  let w₀ := (Biset.induction p).pair (Biset.restriction p) (g*x) 1
  have hff : (hf (g*x)).toFinset = {w₀} := by
    ext w
    rw [Set.Finite.mem_toFinset]
    change w ∈ {w | Generator.mixedProduct p p
      (Generator.mixedMultiplicationBasis p p p p leftDot w) = g*x} ↔ _
    rw [left_fiber]
    simp [w₀]
  rw [hff, Finset.sum_singleton] at hNative
  have htail : (Biset.associate (Word.basis gc) (Word.basis ce) (Word.basis ef) Complex).toLinearMap
      (leftNative.interpret.eval.toLinearMap
        (Finsupp.single ((Word.basis (tensor ga ad)).pair (Biset.induction a) nativeIn 1) 1)) =
      output (g*x) := by
    rw [hNative]
    exact Diagram.eval_associate_single (R := Complex) gc ce ef (g*x) 1 1 1
  have h_split :
      eval left (input g x) =
      (Biset.associate (Word.basis gc) (Word.basis ce) (Word.basis ef) Complex).toLinearMap
        (leftNative.interpret.eval.toLinearMap
          ((Biset.unassociate (Word.basis ga) (Word.basis ad) (Word.basis df) Complex).toLinearMap
            (input g x))) := by
    -- Change only the association of the vertical composite.
    have e : left.interpret.eval =
        ((Diagram.unassociate (R := Complex) ga ad df).eval.vertical leftNative.interpret.eval).vertical
        (Diagram.associate (R := Complex) gc ce ef).eval := by
      unfold leftNative
      simp only [LabelledDrawing.interpret, ScopedDiagram.eval, Biset.Hom.vertical_assoc]
    exact congrArg (fun m : Biset.Hom Complex X Y => m.toLinearMap (input g x)) e
  rw [h_split]
  change (Biset.associate (Word.basis gc) (Word.basis ce) (Word.basis ef) Complex).toLinearMap
    (leftNative.interpret.eval.toLinearMap
      ((Diagram.unassociate (R := Complex) ga ad df).eval.toLinearMap
        (Finsupp.single ((Word.basis ga).pair (Word.basis (tensor ad df)) g
          ((Word.basis ad).pair (Word.basis df) x 1)) 1))) = _
  rw [Diagram.eval_unassociate_single]
  exact htail

end CaseFiveInfiniteAux
