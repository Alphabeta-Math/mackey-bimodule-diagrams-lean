import MackeyDiagrams.MackeySummand

/-! Transfer along an injective basis map returns the unique preimage on
its image and zero elsewhere. -/

namespace MackeyDiagrams.Biset.Hom

universe u v w

variable {K H : Type u} [Group K] [Group H]
variable {R : Type v} [CommSemiring R]
variable {X Y : Biset K H}

theorem transfer_injective_single (f : X.carrier → Y.carrier)
    (equivariant : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) (injective : Function.Injective f)
    (x : X.carrier) (r : R) :
    (transfer R f equivariant finite).toLinearMap (Finsupp.single (f x) r) =
      Finsupp.single x r := by
  classical
  rw [transfer_single, transferBasis_sum]
  have hs : (finite (f x)).toFinset = {x} := by
    ext z
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact injective.eq_iff
  rw [hs, Finset.sum_singleton, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem transfer_outside_single (f : X.carrier → Y.carrier)
    (equivariant : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) {y : Y.carrier}
    (outside : y ∉ Set.range f) (r : R) :
    (transfer R f equivariant finite).toLinearMap (Finsupp.single y r) = 0 := by
  rw [transfer_single, transferBasis_sum]
  have hs : (finite y).toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact outside ⟨x, (finite y).mem_toFinset.mp hx⟩
  rw [hs, Finset.sum_empty, smul_zero]

theorem inclusion_projection (f : X.carrier → Y.carrier)
    (equivariant : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) (injective : Function.Injective f) :
    ((ofFunction f equivariant : Hom R X Y).vertical (transfer R f equivariant finite)) =
      id X := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  change (transfer R f equivariant finite).toLinearMap
    ((ofFunction f equivariant : Hom R X Y).toLinearMap (Finsupp.single x r)) = Finsupp.single x r
  rw [ofFunction_single, transfer_injective_single f equivariant finite injective]

theorem projection_between_disjoint (f : X.carrier → Y.carrier)
    (equivariant : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) {Z : Biset K H}
    (g : Z.carrier → Y.carrier)
    (equivariantG : ∀ s z, g (Z.act s z) = Y.act s (g z))
    (disjoint : Disjoint (Set.range f) (Set.range g)) :
    ((ofFunction g equivariantG : Hom R Z Y).vertical (transfer R f equivariant finite)) =
      zero := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  change (transfer R f equivariant finite).toLinearMap
    ((ofFunction g equivariantG : Hom R Z Y).toLinearMap (Finsupp.single z r)) = 0
  rw [ofFunction_single]
  exact transfer_outside_single f equivariant finite
    (fun h => Set.disjoint_left.mp disjoint h ⟨z,rfl⟩) r

end MackeyDiagrams.Biset.Hom

namespace MackeyDiagrams.Biset.Hom

universe u v w

variable {K H : Type u} [Group K] [Group H] {R : Type v} [CommSemiring R]
variable {Y : Biset K H} {J : Type w}
variable (X : J → Biset K H)
variable (f : ∀ i, (X i).carrier → Y.carrier)
variable (equivariant : ∀ i g z, f i ((X i).act g z) = Y.act g (f i z))
variable (finite : ∀ i y, Set.Finite {z | f i z = y})

/-- The identity is the pointwise finite sum of the projectors of a partition of the basis. -/
theorem sum_partition_projections
    (injective : ∀ i, Function.Injective (f i))
    (partition : ∀ y, ∃! i, y ∈ Set.range (f i)) (x : Y.carrier →₀ R) :
    let term := fun i : J =>
      ((transfer R (f i) (equivariant i) (finite i)).vertical
        (ofFunction (f i) (equivariant i))).toLinearMap x
    ∃ h : Set.Finite (Function.support term), x = ∑ i ∈ h.toFinset, term i := by
  classical
  let term (i : J) := (transfer R (f i) (equivariant i) (finite i)).vertical
    (ofFunction (f i) (equivariant i))
  let index (y : Y.carrier) : J := (partition y).choose
  have eval (y : Y.carrier) (r : R) (i : J) :
      (term i).toLinearMap (Finsupp.single y r) =
        if i = index y then Finsupp.single y r else 0 := by
    have hh := (partition y).choose_spec
    by_cases hi : i = index y
    · have hin : y ∈ Set.range (f i) := hi ▸ hh.1
      obtain ⟨z,hz⟩ := hin
      change (ofFunction (f i) (equivariant i) : Hom R (X i) Y).toLinearMap
        ((transfer R (f i) (equivariant i) (finite i)).toLinearMap (Finsupp.single y r)) =
          if i = index y then Finsupp.single y r else 0
      rw [if_pos hi, ← hz,
        transfer_injective_single (f i) (equivariant i) (finite i) (injective i),
        ofFunction_single]
    · have hout : y ∉ Set.range (f i) := fun h => hi (hh.2 i h)
      change (ofFunction (f i) (equivariant i) : Hom R (X i) Y).toLinearMap
        ((transfer R (f i) (equivariant i) (finite i)).toLinearMap (Finsupp.single y r)) =
          if i = index y then Finsupp.single y r else 0
      rw [if_neg hi, transfer_outside_single (f i) (equivariant i) (finite i) hout, map_zero]
  let active := x.support.image index
  have hx : ∑ y ∈ x.support, Finsupp.single y (x y) = x := Finsupp.sum_single x
  have emptyTerm (i : J) (hi : i ∉ active) : (term i).toLinearMap x = 0 := by
    rw [← hx, map_sum]
    apply Finset.sum_eq_zero
    intro y hy
    rw [eval, if_neg]
    exact fun h => hi (Finset.mem_image.mpr ⟨y,hy,h.symm⟩)
  have covered : Function.support (fun i : J => (term i).toLinearMap x) ⊆ (active : Set J) := by
    intro i hi
    by_contra hn
    exact hi (emptyTerm i hn)
  have finiteSupport : Set.Finite (Function.support (fun i : J => (term i).toLinearMap x)) :=
    active.finite_toSet.subset covered
  refine ⟨finiteSupport, ?_⟩
  change x = ∑ i ∈ finiteSupport.toFinset, (term i).toLinearMap x
  have hactive : ∑ i ∈ active, (term i).toLinearMap x = x := by
    conv_lhs =>
      arg 2
      intro i
      rw [← hx, map_sum]
    rw [Finset.sum_comm]
    calc
      ∑ y ∈ x.support, ∑ i ∈ active, (term i).toLinearMap (Finsupp.single y (x y)) =
          ∑ y ∈ x.support, Finsupp.single y (x y) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp_rw [eval]
        have hmem : index y ∈ active := Finset.mem_image.mpr ⟨y, hy, rfl⟩
        simp [Finset.sum_ite_eq', hmem]
      _ = x := hx
  refine hactive.symm.trans ?_
  symm
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    exact covered (finiteSupport.mem_toFinset.mp hi)
  · intro i _ hi
    by_contra hne
    exact hi (finiteSupport.mem_toFinset.mpr hne)

end MackeyDiagrams.Biset.Hom
