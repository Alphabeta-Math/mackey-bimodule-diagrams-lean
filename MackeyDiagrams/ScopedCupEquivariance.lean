import MackeyDiagrams.ScopedCup

/-! Equivariance of trace-scoped reverse cups by reindexing the cup fiber. -/

namespace MackeyDiagrams.Biset

universe u v
variable {K H : Type u} [Group K] [Group H]

theorem actLinear_injective (X : Biset K H) (R : Type v) [CommSemiring R] (g : K × H) :
    Function.Injective (X.actLinear R g) :=
  (Finsupp.mapDomain.linearEquiv R R (X.actEquiv g)).injective

end MackeyDiagrams.Biset

namespace MackeyDiagrams.RightCupTrace

universe u v
noncomputable section

variable {U : Type u} [Group U] {A B K : Subgroup U}
variable {R : Type v} [CommSemiring R]
variable {p q : Word K B} {a : ConjEmbedding A B}

private theorem cap_act (a : ConjEmbedding A B) (g : B × B)
    (w : (reverseCupWord a).basis.carrier) :
    Generator.multiplicationCapBasis a ((reverseCupWord a).basis.act g w) =
      g.1 * Generator.multiplicationCapBasis a w * g.2⁻¹ := by
  refine Quotient.inductionOn w (fun x => ?_)
  change (g.1 * x.1 * (a.toHom 1)⁻¹) * (a.toHom 1 * x.2 * g.2⁻¹) =
    g.1 * (x.1 * x.2) * g.2⁻¹
  simp [mul_assoc]

private def fiberAct (h : B) (w : reverseCupUnitFiber a) : reverseCupUnitFiber a :=
  ⟨(reverseCupWord a).basis.act (h,h) w.val, by
    rw [cap_act, w.property, mul_one, mul_inv_cancel]⟩

private def fiberConj (h : B) : reverseCupUnitFiber a ≃ reverseCupUnitFiber a where
  toFun := fiberAct h
  invFun := fiberAct h⁻¹
  left_inv w := by
    apply Subtype.ext
    change (reverseCupWord a).basis.act (h⁻¹,h⁻¹)
      ((reverseCupWord a).basis.act (h,h) w.val) = w.val
    rw [← (reverseCupWord a).basis.mul_act, Prod.mk_mul_mk, inv_mul_cancel]
    exact (reverseCupWord a).basis.one_act w.val
  right_inv w := by
    apply Subtype.ext
    change (reverseCupWord a).basis.act (h,h)
      ((reverseCupWord a).basis.act (h⁻¹,h⁻¹) w.val) = w.val
    rw [← (reverseCupWord a).basis.mul_act, Prod.mk_mul_mk, mul_inv_cancel]
    exact (reverseCupWord a).basis.one_act w.val

private theorem term_shift (tail : Diagram R (p.tensor (reverseCupWord a)) q)
    (g : K × B) (x : p.basis.carrier) (w : reverseCupUnitFiber a) :
    term tail (p.basis.act g x) w =
      q.basis.actLinear R g (term tail x (fiberConj g.2⁻¹ w)) := by
  rcases g with ⟨k,h⟩
  unfold term
  rw [← tail.eval.commutes, Biset.actLinear_single]
  apply congrArg (fun y => tail.eval.toLinearMap (Finsupp.single y 1))
  let C := (reverseCupWord a).basis
  change p.basis.pair C (p.basis.act (k,h) x) w.val =
    (p.basis.tensor C).act (k,h) (p.basis.pair C x (C.act (h⁻¹,h⁻¹) w.val))
  rw [Biset.act_pair, ← C.mul_act]
  have hc : (1,h) * (h⁻¹,h⁻¹) = ((h⁻¹,1) : B × B) := by simp
  rw [hc]
  have he := p.basis.pair_balance C h⁻¹ (p.basis.act (k,1) x) w.val
  rw [inv_inv, ← p.basis.mul_act] at he
  have hg : (1,h) * (k,1) = ((k,h) : K × B) := by simp
  rw [hg] at he
  exact he

theorem basisSum_equivariant (tail : Diagram R (p.tensor (reverseCupWord a)) q)
    (finiteAfter : FiniteAfter tail) (g : K × B) (x : p.basis.carrier) :
    basisSum tail finiteAfter (p.basis.act g x) =
      q.basis.actLinear R g (basisSum tail finiteAfter x) := by
  classical
  let e : reverseCupUnitFiber a ≃ reverseCupUnitFiber a := fiberConj g.2⁻¹
  have hs (i : reverseCupUnitFiber a) :
      term tail (p.basis.act g x) i = q.basis.actLinear R g (term tail x (e i)) :=
    term_shift tail g x i
  have hne (i : reverseCupUnitFiber a) :
      term tail (p.basis.act g x) i ≠ 0 ↔ term tail x (e i) ≠ 0 := by
    rw [hs]
    constructor
    · intro h hz
      apply h
      exact (q.basis.actLinear R g).map_eq_zero_iff (q.basis.actLinear_injective R g) |>.mpr hz
    · intro h hz
      apply h
      exact (q.basis.actLinear R g).map_eq_zero_iff (q.basis.actLinear_injective R g) |>.mp hz
  unfold basisSum
  rw [map_sum]
  refine Finset.sum_bij (fun i _ => e i) ?_ ?_ ?_ ?_
  · intro i hi
    exact (Set.Finite.mem_toFinset _).mpr ((hne i).mp ((Set.Finite.mem_toFinset _).mp hi))
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, (Set.Finite.mem_toFinset _).mpr ?_, e.apply_symm_apply j⟩
    apply (hne _).mpr
    rw [e.apply_symm_apply]
    exact (Set.Finite.mem_toFinset _).mp hj
  · intro i _
    exact hs i

/-- Local finiteness after the typed tail suffices to construct the whole scoped cup. -/
def ofFiniteAfter (tail : Diagram R (p.tensor (reverseCupWord a)) q)
    (finiteAfter : FiniteAfter tail) : RightCupTrace R p q a where
  tail := tail
  finiteAfter := finiteAfter
  equivariant := basisSum_equivariant tail finiteAfter

end
end MackeyDiagrams.RightCupTrace
