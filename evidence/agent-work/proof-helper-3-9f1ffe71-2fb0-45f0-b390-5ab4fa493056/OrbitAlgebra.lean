import MackeyDiagrams.Linear
import Mathlib.Basic.Finite.Prod
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Span

open MackeyDiagrams

noncomputable section
namespace OrbitAlgebra

universe u v
variable {G F : Type u} [Group G] [Group F] (X Y : Biset G F)
variable (R : Type v) [CommRing R]

abbrev Pair := X.carrier × Y.carrier

instance pairAction : MulAction (G × F) (Pair X Y) where
  smul q z := (X.act q z.1, Y.act q z.2)
  one_smul z := Prod.ext (X.one_act z.1) (Y.one_act z.2)
  mul_smul q q' z := Prod.ext (X.mul_act q q' z.1) (Y.mul_act q q' z.2)

abbrev orbit := MulAction.orbit (G × F) (α := Pair X Y)
abbrev Orbits := Set.range (orbit X Y)

def rep (O : Orbits X Y) : Pair X Y := Classical.choose O.property

theorem orbit_rep (O : Orbits X Y) : orbit X Y (rep X Y O) = O.val :=
  Classical.choose_spec O.property

def which (z : Pair X Y) : Orbits X Y := ⟨orbit X Y z, ⟨z, rfl⟩⟩

theorem which_eq {z : Pair X Y} {O : Orbits X Y} :
    which X Y z = O ↔ z ∈ O.val := by
  refine Subtype.ext_iff.trans ?_
  change orbit X Y z = O.val ↔ z ∈ O.val
  rw [← orbit_rep X Y O]
  exact MulAction.orbit_eq_iff

def maps : Submodule R ((X.carrier →₀ R) →ₗ[R] Y.carrier →₀ R) where
  carrier := {m | ∀ q x, m (X.actLinear R q x) = Y.actLinear R q (m x)}
  zero_mem' := by simp
  add_mem' := by
    intro m n hm hn q x
    simp only [LinearMap.add_apply, map_add, hm q x, hn q x]
  smul_mem' := by
    intro r m hm q x
    simp only [LinearMap.smul_apply, map_smul, hm q x]

def coeff (m : maps X Y R) (z : Pair X Y) : R :=
  m.val (Finsupp.single z.1 1) z.2

theorem act_apply (B : Biset G F) (q : G × F) (m : B.carrier →₀ R) (x : B.carrier) :
    B.actLinear R q m (B.act q x) = m x := by
  change Finsupp.mapDomain (B.act q) m (B.act q x) = m x
  apply Finsupp.mapDomain_apply_of_injective
  intro x y h
  have he := congrArg (B.act q⁻¹) h
  simpa only [← B.mul_act, inv_mul_cancel, B.one_act] using he

theorem coeff_smul (m : maps X Y R) (q : G × F) (z : Pair X Y) :
    coeff X Y R m (q • z) = coeff X Y R m z := by
  change m.val (Finsupp.single (X.act q z.1) 1) (Y.act q z.2) = _
  rw [← X.actLinear_single R q z.1 1, m.property q, act_apply]
  rfl

theorem coeff_orbit (m : maps X Y R) {z z' : Pair X Y} (h : z' ∈ orbit X Y z) :
    coeff X Y R m z' = coeff X Y R m z := by
  obtain ⟨q, rfl⟩ := h
  exact coeff_smul X Y R m q z

theorem coeff_injective : Function.Injective (coeff X Y R) := by
  intro m n h
  apply Subtype.ext
  apply Finsupp.lhom_ext
  intro x r
  rw [← Finsupp.smul_single_one x r, map_smul, map_smul]
  congr 1
  exact DFunLike.ext _ _ fun y => congrFun h (x,y)

variable [Finite Y.carrier]

def column (c : Orbits X Y → R) (x : X.carrier) : Y.carrier →₀ R :=
  Finsupp.equivFunOnFinite.symm fun y => c (which X Y (x,y))

theorem column_apply (c : Orbits X Y → R) (x : X.carrier) (y : Y.carrier) :
    column X Y R c x y = c (which X Y (x,y)) := by
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (fun y : Y.carrier => c (which X Y (x,y)))) y

def reconstruct (c : Orbits X Y → R) : maps X Y R := by
  let h := Biset.Hom.ofBasis (R := R) (X := X) (Y := Y) (column X Y R c) (by
    intro q x
    ext y
    have he : Y.act q (Y.act q⁻¹ y) = y := by
      rw [← Y.mul_act, mul_inv_cancel, Y.one_act]
    conv_lhs => rw [← he]
    conv_rhs => rw [← he]
    rw [act_apply, column_apply, column_apply]
    congr 1
    apply (which_eq X Y).2
    exact ⟨q, rfl⟩)
  exact ⟨h.toLinearMap, h.commutes⟩

theorem coeff_reconstruct (c : Orbits X Y → R) (z : Pair X Y) :
    coeff X Y R (reconstruct X Y R c) z = c (which X Y z) := by
  change freeLift R (column X Y R c) (Finsupp.single z.1 1) z.2 = _
  rw [freeLift_single, one_smul, column_apply]

def coordinates : maps X Y R ≃ₗ[R] (Orbits X Y → R) where
  toFun m O := coeff X Y R m (rep X Y O)
  invFun := reconstruct X Y R
  left_inv m := by
    apply coeff_injective
    funext z
    rw [coeff_reconstruct]
    symm
    apply coeff_orbit
    rw [orbit_rep]
    exact MulAction.mem_orbit_self z
  right_inv c := by
    funext O
    change coeff X Y R (reconstruct X Y R c) (rep X Y O) = c O
    rw [coeff_reconstruct, (which_eq X Y).2]
    rw [← orbit_rep X Y O]
    exact MulAction.mem_orbit_self _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def basis [Finite X.carrier] : Module.Basis (Orbits X Y) R (maps X Y R) := by
  letI : Finite (Pair X Y) := inferInstanceAs (Finite (X.carrier × Y.carrier))
  letI : Finite (Orbits X Y) := Finite.Set.finite_range _
  exact Module.Basis.ofRepr ((coordinates X Y R).trans
    (Finsupp.linearEquivFunOnFinite R R (Orbits X Y)).symm)

theorem basis_coeff [Finite X.carrier] (O : Orbits X Y) (z : Pair X Y) :
    coeff X Y R (basis X Y R O) z = @ite R (z ∈ O.val) (Classical.propDecidable _) 1 0 := by
  classical
  letI : Finite (Pair X Y) := inferInstanceAs (Finite (X.carrier × Y.carrier))
  letI : Finite (Orbits X Y) := Finite.Set.finite_range _
  change coeff X Y R (reconstruct X Y R (Finsupp.single O 1)) z = _
  rw [coeff_reconstruct, Finsupp.single_apply]
  by_cases hz : z ∈ O.val
  · simp only [if_pos hz, if_pos ((which_eq X Y).2 hz).symm]
  · have hne : O ≠ which X Y z := fun h => hz ((which_eq X Y).1 h.symm)
    simp only [if_neg hz, if_neg hne]

end OrbitAlgebra

namespace OrbitAlgebra
section Span
variable {R : Type*} [CommRing R]
variable {ι : Type*} {M : Type*} [AddCommGroup M] [Module R M] [Fintype ι]

theorem span_iff_ideal (b : Module.Basis ι R M) (n : ι → R) (S : Set M)
    (upper : ∀ m ∈ S, ∀ i, b.repr m i ∈ Ideal.span ({n i} : Set R))
    (lower : ∀ i, n i • b i ∈ Submodule.span R S) (m : M) :
    m ∈ Submodule.span R S ↔ ∀ i, b.repr m i ∈ Ideal.span ({n i} : Set R) := by
  constructor
  · intro hm i
    let J := Ideal.span ({n i} : Set R)
    let f := b.coord i
    exact (Submodule.span_le.mpr (fun x hx => upper x hx i) :
      Submodule.span R S ≤ J.comap f) hm
  · intro hm
    rw [← b.sum_repr m]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hm i)
    rw [← hr, ← smul_smul]
    exact Submodule.smul_mem _ r (lower i)

theorem ideal_of_singleton (b : Module.Basis ι R M) (n : ι → Nat)
    (j : ι) (count : Nat) (hd : n j ∣ count) (i : ι) :
    b.repr ((count : R) • b j) i ∈ Ideal.span ({(n i : R)} : Set R) := by
  classical
  by_cases h : j = i
  · subst j
    obtain ⟨k, hk⟩ := hd
    simpa [Module.Basis.repr_self, hk, Nat.cast_mul] using
      (Ideal.mem_span_singleton.mpr (dvd_mul_right (n i : R) (k : R)) :
        (n i : R) * (k : R) ∈ Ideal.span ({(n i : R)} : Set R))
  · simp [Module.Basis.repr_self, Finsupp.single_apply, h]
end Span
end OrbitAlgebra

#print axioms OrbitAlgebra.basis_coeff
#print axioms OrbitAlgebra.span_iff_ideal
#print axioms OrbitAlgebra.ideal_of_singleton
