import Columns

set_option maxHeartbeats 2000000

namespace CaseSixTrivialAux
open MackeyDiagrams
open scoped BigOperators
noncomputable section

abbrev endDot : Dot (b.comp i) (d.comp j) :=
  ⟨1, fun x => by rw [F_eq_one x]; simp only [map_one, mul_one]⟩

abbrev right
    (lower : List (Complex × ProjectionDot.Mixed b d i j))
    (middle : List (Complex × Dot (a.comp i) (a.comp i)))
    (upper : List (Complex × Dot (b.comp i) (d.comp j))) :=
  vertical (horizontal (straight (up a)) (.compactProjection b d i j lower))
    (vertical (atLeft (down j) (.parallelUp a i a i middle))
      (horizontal (straight (up a)) (.mixedMultiplication b d i j upper)))

abbrev fiberWord := tensor (up i) (down j)
abbrev fiberBasis := fiberWord.basis.carrier
abbrev fiberPair (g : A) : fiberBasis := (up i).basis.pair (down j).basis g 1

abbrev rightFunction :=
  Generator.mixedMultiplicationBasis b d i j endDot

abbrev rightProduct (w : fiberBasis) : D := Generator.mixedProduct b d (rightFunction w)

theorem rightProduct_pair (g : A) : rightProduct (fiberPair g) = b.toHom g := by
  change Generator.mixedProduct b d
    (Generator.mixedPair b d (b.toHom g * (1 : D) * d.toHom 1)) = _
  rw [Generator.mixedProduct_mixedPair, map_one, mul_one, mul_one]

theorem fiberPair_out (w : fiberBasis) : fiberPair (Quotient.out w).1 = w := by
  have hw := Quotient.out_eq w
  change (up i).basis.pair (down j).basis (Quotient.out w).1 (Quotient.out w).2 = w at hw
  rw [F_eq_one (Quotient.out w).2] at hw
  exact hw

theorem rightProduct_injective : Function.Injective rightProduct := by
  intro p q h
  have h' : rightProduct (fiberPair (Quotient.out p).1) =
      rightProduct (fiberPair (Quotient.out q).1) := by rw [fiberPair_out, fiberPair_out, h]
  rw [rightProduct_pair, rightProduct_pair] at h'
  exact (fiberPair_out p).symm.trans ((congrArg fiberPair (b.injective h')).trans (fiberPair_out q))

theorem rightGroupFinite (x : D) : Set.Finite {w | rightProduct w = x} := by
  classical
  by_cases h : ∃ w, rightProduct w = x
  · obtain ⟨w, hw⟩ := h
    apply (Set.finite_singleton w).subset
    exact fun v hv => Set.mem_singleton_iff.mpr (rightProduct_injective (hv.trans hw.symm))
  · exact Set.finite_empty.subset (fun w hw => (h ⟨w, hw⟩).elim)

theorem rightFinite (z : ad.basis.carrier) : Set.Finite {w | rightFunction w = z} :=
  (rightGroupFinite (Generator.mixedProduct b d z)).subset
    (fun _ hw => congrArg (Generator.mixedProduct b d) hw)

abbrev rightEval := ev
  (right [(1, ⟨endDot, rightFinite⟩)] [(1, Dot.id (a.comp i))] [(1, endDot)])

-- Step 1 of Example 8.6 and Lemma 6.6, equation (6.4), steps 1–4.
-- Use the registered singleton formula at B' = F. Its finiteness
-- hypothesis holds by injectivity of the lower product on the quotient.
theorem right_formula (x : D) :
    rightEval (vector x) =
      ∑ w ∈ (rightGroupFinite x).toFinset, Finsupp.single (coordinate (Quotient.out w).1 1) 1 := by
  have he := ((EvaluationWithOneProjection a b d a b d).2 F i j i).1
    endDot rightGroupFinite (Dot.id (a.comp i)) endDot 1 x
  change rightEval (vector x) = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro w _
  change Finsupp.single
      (coordinate (1 * a.toHom (Quotient.out w).1 * (1 : A)) (1 * d.toHom (Quotient.out w).2)) 1 = _
  have hm : a.toHom (Quotient.out w).1 = (Quotient.out w).1 := rfl
  rw [hm, F_eq_one (Quotient.out w).2, map_one, one_mul, mul_one, mul_one]

theorem right_action (x : D) :
    ((x : U) ∈ A → rightEval (vector x) = vector x) ∧
    ((x : U) ∉ A → rightEval (vector x) = 0) := by
  classical
  have mem (w : fiberBasis) : w ∈ (rightGroupFinite x).toFinset ↔ rightProduct w = x :=
    Set.Finite.mem_toFinset _
  rw [right_formula]
  constructor
  · intro hx
    let g : A := ⟨x, hx⟩
    have hg : b.toHom g = x := rfl
    have hf : (rightGroupFinite x).toFinset = {fiberPair g} := by
      ext w
      rw [mem, Finset.mem_singleton, ← hg, ← rightProduct_pair g]
      exact rightProduct_injective.eq_iff
    rw [hf, Finset.sum_singleton, coordinate_move, ← vector, ← rightProduct_pair,
      fiberPair_out, rightProduct_pair, hg, mul_one]
  · intro hx
    have hf : (rightGroupFinite x).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hw' := (mem w).1 hw
      rw [← fiberPair_out w, rightProduct_pair] at hw'
      have hproperty := (Quotient.out w).1.property
      exact hx ((congrArg (fun y : D => (y : U)) hw') ▸ hproperty)
    rw [hf, Finset.sum_empty]

end
end CaseSixTrivialAux
