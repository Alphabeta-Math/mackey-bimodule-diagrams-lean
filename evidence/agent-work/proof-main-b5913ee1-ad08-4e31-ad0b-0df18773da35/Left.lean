import Columns

set_option maxHeartbeats 2000000

namespace CaseSixTrivialAux
open MackeyDiagrams
open scoped BigOperators
noncomputable section

def mass : (word.basis.carrier →₀ Complex) →ₗ[Complex] Complex :=
  Finsupp.lsum Complex (fun _ => LinearMap.id)

theorem mass_apply (z : word.basis.carrier →₀ Complex) : mass z = z.sum (fun _ c => c) := rfl

@[simp] theorem mass_single (p : word.basis.carrier) : mass (Finsupp.single p 1) = 1 := by
  rw [mass_apply, Finsupp.sum_single_index]
  rfl

abbrev upperFunction {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) := Generator.mixedMultiplicationBasis u w a b s.dot

abbrev pairAB (g : A) (x : D) := (up a).basis.pair (down b).basis g x

theorem pairAB_move (g : A) (x : D) : pairAB g x = pairAB 1 (b.toHom g * x) := by
  have eq := (up a).basis.pair_balance (down b).basis g 1 x
  change pairAB (1 * 1 * (g⁻¹)⁻¹) x = pairAB 1 (b.toHom g * x * (1 : D)⁻¹) at eq
  simpa only [inv_inv, mul_one, one_mul, inv_one] using eq

theorem upperFunction_pair {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (y : D) :
    upperFunction u w s (pairAB 1 y) = Generator.mixedPair u w (s.dot.element * w.toHom y) := by
  change Generator.mixedPair u w (u.toHom 1 * s.dot.element * w.toHom y) = _
  rw [map_one, one_mul]

theorem upperFunction_injective {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) : Function.Injective (upperFunction u w s) := by
  intro p q
  refine Quotient.inductionOn₂ p q (fun ⟨g,x⟩ ⟨h,y⟩ => ?_)
  change upperFunction u w s (pairAB g x) = upperFunction u w s (pairAB h y) → _
  have hg := pairAB_move g x
  have hh := pairAB_move h y
  change upperFunction u w s (pairAB g x) = upperFunction u w s (pairAB h y) →
    pairAB g x = pairAB h y
  rw [hg, hh, upperFunction_pair, upperFunction_pair]
  intro eq
  have hprod := (Generator.mixedEquiv u w).symm.injective eq
  rw [mul_right_inj] at hprod
  exact congrArg (pairAB 1) (w.injective hprod)

abbrev upperFiber {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (z : B) := (s.finite (Generator.mixedPair u w z)).toFinset

theorem upperFiber_mass {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (z : B) :
    mass (ev (atLeft (up d) (.compactProjection u w a b [(1, s)]))
      (Finsupp.single (mid u w z) 1)) = (upperFiber u w s z).card := by
  have eq := atLeft_pair (up d) (.compactProjection u w a b [(1, s)]) z 1 1
  change ev (atLeft (up d) (.compactProjection u w a b [(1, s)]))
    (Finsupp.single (mid u w z) 1) = _ at eq
  rw [eq]
  let act := (Diagram.associate (R := Complex) (up a) (down b) (up d)).eval.toLinearMap.comp
    ((Biset.pairLinear Complex (tensor (up a) (down b)).basis (up d).basis).flip (Finsupp.single 1 1))
  let p := Generator.mixedPair u w z
  let f := (Diagram.mixedProjection (R := Complex) u w a b s.dot s.finite).eval.toLinearMap
  change mass (act ((ScopedDiagram.linearCombination [(1, .ordinary
    (Diagram.mixedProjection u w a b s.dot s.finite))]).eval.toLinearMap (Finsupp.single p 1))) = _
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul]
  change mass (act (f (Finsupp.single p 1))) = _
  have hcol : f (Finsupp.single p 1) =
      ∑ v ∈ upperFiber u w s z, Finsupp.single v 1 := by
    change (Generator.mixedProjection u w a b s.dot Complex s.finite).toLinearMap
      (Finsupp.single p 1) = _
    rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul,
      Biset.Hom.transferBasis_sum]
  rw [hcol, map_sum, map_sum]
  have hmass (v : (tensor (up a) (down b)).basis.carrier) :
      mass (act (Finsupp.single v 1)) = 1 := by
    refine Quotient.inductionOn v (fun ⟨g,y⟩ => ?_)
    change mass (act (Finsupp.single (pairAB g y) 1)) = _
    simp only [act, LinearMap.comp_apply, LinearMap.flip_apply]
    rw [Biset.pairLinear_single, one_mul, Diagram.eval_associate_single (up a) (down b) (up d), mass_single]
  simp only [hmass, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem upper_mass {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (ss : List (Complex × SDot u w)) (z : B) :
    mass (ev (atLeft (up d) (.compactProjection u w a b ss))
      (Finsupp.single (mid u w z) 1)) =
      (ss.map fun (c,s) => c * (upperFiber u w s z).card).sum := by
  let act := mass.comp ((Diagram.associate (R := Complex) (up a) (down b) (up d)).eval.toLinearMap.comp
    ((Biset.pairLinear Complex (tensor (up a) (down b)).basis (up d).basis).flip (Finsupp.single 1 1)))
  let p := Generator.mixedPair u w z
  have apply_terms (labels : List (Complex × SDot u w)) :
      mass (ev (atLeft (up d) (.compactProjection u w a b labels))
        (Finsupp.single (mid u w z) 1)) =
      act ((ScopedDiagram.linearCombination (labels.map fun (c,s) =>
        (c, .ordinary (Diagram.mixedProjection u w a b s.dot s.finite)))).eval.toLinearMap
          (Finsupp.single p 1)) := by
    rw [atLeft_pair (up d) (.compactProjection u w a b labels) z 1 1]
    rfl
  rw [apply_terms, ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨c,s⟩ _
  simp only [Function.comp_apply, map_smul, smul_eq_mul]
  congr 1
  have h := upperFiber_mass u w s z
  rw [apply_terms, ScopedDiagram.eval_linearCombination_apply] at h
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] using h

theorem fiber_card_of_exists {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (z : B) :
    ((∃ y : D, s.dot.element * w.toHom y = z) → (upperFiber u w s z).card = 1) ∧
    ((¬ ∃ y : D, s.dot.element * w.toHom y = z) → (upperFiber u w s z).card = 0) := by
  classical
  have mem (p : (tensor (up a) (down b)).basis.carrier) :
      p ∈ upperFiber u w s z ↔ upperFunction u w s p = Generator.mixedPair u w z :=
    Set.Finite.mem_toFinset _
  constructor
  · rintro ⟨y, hy⟩
    have hp : pairAB 1 y ∈ upperFiber u w s z := by
      rw [mem, upperFunction_pair, hy]
    apply Finset.card_eq_one.mpr
    refine ⟨pairAB 1 y, ?_⟩
    ext p
    rw [Finset.mem_singleton]
    exact ⟨fun hin => upperFunction_injective u w s ((mem p).1 hin |>.trans ((mem _).1 hp).symm),
      fun e => e ▸ hp⟩
  · intro h
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p
    refine Quotient.inductionOn p (fun ⟨g,y⟩ => ?_)
    change pairAB g y ∉ upperFiber u w s z
    rw [pairAB_move, mem, upperFunction_pair]
    exact fun eq => h ⟨_, (Generator.mixedEquiv u w).symm.injective eq⟩

-- Step 4 of Example 8.6. The upper fiber has one element precisely when
-- the relative translation belongs to the common subgroup.
theorem fiber_card_constant {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (r : RDot u v) (t : TDot v w) (s : SDot u w) (x y : D) :
    (upperFiber u w s (r.element * v.toHom x * t.element)).card =
    (upperFiber u w s (r.element * v.toHom y * t.element)).card := by
  classical
  let R := MulAut.conj r.element
  let S := MulAut.conj s.dot.element
  let offset := r.element * t.element * s.dot.element⁻¹
  let H := Subgroup.map (R.toMonoidHom.comp v.toHom) ⊤
  have hrange : (fun x : D => r.element * v.toHom x * r.element⁻¹) '' (Set.univ : Set D) =
      (H : Set B) := by
    ext z
    change (∃ x : D, x ∈ (Set.univ : Set D) ∧ R (v.toHom x) = z) ↔
      (∃ x : D, x ∈ (⊤ : Subgroup D) ∧ R (v.toHom x) = z)
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, Subgroup.mem_top _, hx⟩,
      fun ⟨x, _, hx⟩ => ⟨x, Set.mem_univ _, hx⟩⟩
  have hs (z : B) : (∃ k : D, S (w.toHom k) = z) ↔ z ∈ H := by
    rw [← show z ∈ (H : Set B) ↔ z ∈ H from Iff.rfl, ← hrange, ranges_eq u v w r s.dot]
    simp [S]
  have translate (x : D) :
      (∃ k : D, s.dot.element * w.toHom k = r.element * v.toHom x * t.element) ↔ offset ∈ H := by
    have hx : R (v.toHom x) ∈ H := ⟨x, Subgroup.mem_top _, rfl⟩
    have eq (k : D) :
        s.dot.element * w.toHom k = r.element * v.toHom x * t.element ↔
          S (w.toHom k) = R (v.toHom x) * offset := by
      change _ ↔ s.dot.element * w.toHom k * s.dot.element⁻¹ =
        (r.element * v.toHom x * r.element⁻¹) * (r.element * t.element * s.dot.element⁻¹)
      rw [show (r.element * v.toHom x * r.element⁻¹) *
          (r.element * t.element * s.dot.element⁻¹) =
            r.element * v.toHom x * t.element * s.dot.element⁻¹ by group, mul_left_inj]
    simp only [eq]
    rw [hs]
    exact ⟨fun h => by simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hx) h,
      H.mul_mem hx⟩
  by_cases h : offset ∈ H
  · exact ((fiber_card_of_exists u w s _).1 ((translate x).2 h)).trans
      ((fiber_card_of_exists u w s _).1 ((translate y).2 h)).symm
  · exact ((fiber_card_of_exists u w s _).2 (fun hx => h ((translate x).1 hx))).trans
      ((fiber_card_of_exists u w s _).2 (fun hy => h ((translate y).1 hy))).symm

-- Step 5. Distribute over the actual three finite lists. Empty lists,
-- repeated labels and vanishing coefficients are all covered.
theorem left_mass {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (rs : List (Complex × RDot u v)) (ts : List (Complex × TDot v w))
    (ss : List (Complex × SDot u w)) (x y : D) :
    mass (ev (left u v w rs ts ss) (vector x)) = mass (ev (left u v w rs ts ss) (vector y)) := by
  let next := ev (horizontal (straight (down u)) (.parallelUp v d w d ts))
  let last := mass.comp (ev (atLeft (up d) (.compactProjection u w a b ss)))
  have expand (x : D) : mass (ev (left u v w rs ts ss) (vector x)) =
      (rs.map fun (cr,r) => cr • (ts.map fun (ct,t) => ct •
        (ss.map fun (cs,s) => cs * (upperFiber u w s (r.element * v.toHom x * t.element)).card).sum).sum).sum := by
    change last (next (ev (atLeft (up d) (.mixedMultiplication u v a b rs)) (vector x))) = _
    rw [lower_column, map_list_sum, map_list_sum]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ⟨cr,r⟩ _
    simp only [Function.comp_apply, map_smul]
    congr 1
    change last (ev (horizontal (straight (down u)) (.parallelUp v d w d ts))
      (Finsupp.single (mid u v (r.element * v.toHom x)) 1)) = _
    rw [middle_column, map_list_sum]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ⟨ct,t⟩ _
    simp only [Function.comp_apply, map_smul, last, LinearMap.comp_apply]
    rw [upper_mass]
  rw [expand x, expand y]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cr,r⟩ _
  apply congrArg (cr • ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨ct,t⟩ _
  apply congrArg (ct • ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cs,s⟩ _
  exact congrArg (fun n : Nat => cs * (n : Complex)) (fiber_card_constant u v w r t s x y)

end
end CaseSixTrivialAux
