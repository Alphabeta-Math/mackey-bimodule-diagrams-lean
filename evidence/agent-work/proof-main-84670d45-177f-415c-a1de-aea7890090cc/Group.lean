import Mathlib.GroupTheory.Perm.Cycle.Type
import Proofs.ParabolicRightOrbitMultiplicity

namespace CaseSixCharThree
open MackeyDiagrams

private abbrev finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (S : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
private abbrev parabolic (H : Subgroup finitary) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H.map finitary.subtype = iSup (fun i => blockSym (blocks i))
private abbrev points : Finset Nat := {1, 2, 3}
private abbrev S₃ := Subgroup.comap finitary.subtype (blockSym points)
private abbrev extendBlock (S : Finset Nat) := Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S)

private theorem extend_mem (σ : Equiv.Perm ↥points) : extendBlock points σ ∈ finitary := by
  apply _root_.mem_closure_isSwap'.2
  apply (Finset.finite_toSet points).subset
  intro n moved
  by_contra outside
  exact moved (MulAction.mem_fixedBy.mpr (Equiv.Perm.ofSubtype_apply_of_not_mem σ outside))

private def extend (σ : Equiv.Perm ↥points) : S₃ :=
  ⟨⟨extendBlock points σ, extend_mem σ⟩, ⟨σ, rfl⟩⟩

private theorem extend_surj : Function.Surjective extend := by
  intro ⟨⟨σ, _⟩, h⟩
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, Subtype.ext (Subtype.ext hρ)⟩

private instance : Finite S₃ := Finite.of_surjective extend extend_surj

private def extendHom : Equiv.Perm ↥points →* S₃ where
  toFun := extend
  map_one' := Subtype.ext (Subtype.ext (map_one (extendBlock points)))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul (extendBlock points) x y))

private theorem extend_inj : Function.Injective extendHom := by
  intro x y h
  have he := congrArg (fun u : S₃ => ((u : finitary) : Equiv.Perm Nat)) h
  exact Equiv.Perm.ofSubtype_injective he

private abbrev label₁ : ↥points := ⟨1, by decide⟩
private abbrev label₂ : ↥points := ⟨2, by decide⟩
private abbrev label₃ : ↥points := ⟨3, by decide⟩
private def c₀ := Equiv.swap label₁ label₂ * Equiv.swap label₂ label₃
private abbrev cycle := extendHom c₀
private abbrev transposition := extendHom (Equiv.swap label₁ label₂)

-- Step 1 of Example 8.5 (unnumbered in the portal): do the finite calculation
-- on the three actual points. These decidable computations are kernel-checked.
private theorem small_pow : c₀ ^ 3 = 1 := by decide
private theorem small_ne : c₀ ≠ 1 := by decide
private theorem small_symm_ne : c₀ ≠ c₀⁻¹ := by decide
private theorem small_flip : Equiv.swap label₁ label₂ * c₀ * (Equiv.swap label₁ label₂)⁻¹ =
    c₀⁻¹ := by decide
private theorem small_conj (g : Equiv.Perm ↥points) :
    g * c₀ * g⁻¹ = c₀ ∨ g * c₀ * g⁻¹ = c₀⁻¹ := by
  revert g
  decide

private theorem cycle_ne : cycle ≠ cycle⁻¹ := by
  intro h
  apply small_symm_ne
  exact extend_inj (h.trans (map_inv extendHom c₀).symm)

private theorem cycle_order : orderOf cycle = 3 := by
  rw [orderOf_injective _ extend_inj]
  exact orderOf_eq_prime small_pow small_ne

private theorem cycle_card : Nat.card (Subgroup.zpowers cycle) = 3 := by
  classical
  letI := Fintype.ofFinite (Subgroup.zpowers cycle)
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, cycle_order]

private theorem cycle_flip : transposition * cycle * transposition⁻¹ = cycle⁻¹ := by
  simpa only [map_mul, map_inv] using congrArg extendHom small_flip

private theorem cycle_conj (g : S₃) :
    g * cycle * g⁻¹ = cycle ∨ g * cycle * g⁻¹ = cycle⁻¹ := by
  obtain ⟨g, rfl⟩ := extend_surj g
  change extendHom g * cycle * (extendHom g)⁻¹ = cycle ∨
    extendHom g * cycle * (extendHom g)⁻¹ = cycle⁻¹
  rcases small_conj g with h | h
  · left
    simpa only [map_mul, map_inv] using congrArg extendHom h
  · right
    simpa only [map_mul, map_inv] using congrArg extendHom h

private theorem S₃_parabolic : parabolic S₃ := by
  refine ⟨1, fun _ => points, fun _ => ⟨1, show 1 ∈ points by decide⟩, ?_, ?_⟩
  · intro i j h
    exact (h (Subsingleton.elim i j)).elim
  · change (Subgroup.comap finitary.subtype (blockSym points)).map finitary.subtype =
      ⨆ _ : Fin 1, blockSym points
    rw [iSup_const]
    apply Subgroup.map_comap_eq_self
    rintro _ ⟨σ, rfl⟩
    exact ⟨⟨extendBlock points σ, extend_mem σ⟩, rfl⟩

private theorem swap_order {σ : Equiv.Perm Nat} (hs : σ.IsSwap) : orderOf σ = 2 := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  apply orderOf_eq_prime
  · rw [pow_two, Equiv.swap_mul_self]
  · exact Equiv.swap_ne_one hab

private theorem small_centralizer (g : Equiv.Perm ↥points) :
    g * c₀ = c₀ * g → g = 1 ∨ g = c₀ ∨ g = c₀⁻¹ := by
  revert g
  decide

private theorem cycle_centralizer {g : S₃} (h : g * cycle = cycle * g) :
    g ∈ Subgroup.zpowers cycle := by
  obtain ⟨g, rfl⟩ := extend_surj g
  change extendHom g * extendHom c₀ = extendHom c₀ * extendHom g at h
  rw [← map_mul, ← map_mul] at h
  rcases small_centralizer g (extend_inj h) with h | h | h
  · rw [h]
    change extendHom 1 ∈ Subgroup.zpowers cycle
    rw [map_one]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers _
  · rw [h]
    change extendHom c₀⁻¹ ∈ Subgroup.zpowers cycle
    rw [map_inv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

section IdentityBoundary

variable {W : Type*} [Group W] (H : Subgroup W)

private abbrev identity := ConjEmbedding.id H
private abbrev Up := Word.up (identity H)
private abbrev Down := Word.down (identity H)
private abbrev Mixed := (Down H).tensor (Up H)
private abbrev Boundary := (Up H).tensor (Mixed H)
private abbrev Basis := (Boundary H).basis.carrier
private abbrev PairBasis := Basis H × Basis H
private abbrev point (g x : H) : Basis H :=
  (Up H).basis.pair (Mixed H).basis g (Generator.mixedPair (identity H) (identity H) x)
private abbrev regularBasis (x : H) := point H x 1
private abbrev onBasis : MulAction (H × H) (Basis H) where
  smul := (Boundary H).basis.act
  one_smul := (Boundary H).basis.one_act
  mul_smul := (Boundary H).basis.mul_act
private abbrev onPairs : MulAction (H × H) (PairBasis H) where
  smul q z := ((Boundary H).basis.act q z.1, (Boundary H).basis.act q z.2)
  one_smul z := Prod.ext ((Boundary H).basis.one_act z.1) ((Boundary H).basis.one_act z.2)
  mul_smul q q' z := Prod.ext ((Boundary H).basis.mul_act q q' z.1)
    ((Boundary H).basis.mul_act q q' z.2)
private abbrev pairOrbit (z : PairBasis H) := @MulAction.orbit (H × H) _ _ (onPairs H) z
private abbrev projectBasis (z : Basis H) :=
  (@MulAction.stabilizer (H × H) _ _ (onBasis H) z).map (MonoidHom.snd H H)
private abbrev projectPair (z : PairBasis H) :=
  (@MulAction.stabilizer (H × H) _ _ (onPairs H) z).map (MonoidHom.snd H H)
private abbrev ambientProject (z : PairBasis H) := (projectPair H z).map H.subtype

private theorem point_normal (g x : H) : point H g x = regularBasis H (g * x) := by
  apply Quotient.sound
  refine ⟨x⁻¹, ?_, ?_⟩
  · change 1 * g * (x⁻¹)⁻¹ = g * x
    rw [one_mul, inv_inv]
  · apply (Generator.mixedEquiv (identity H) (identity H)).injective
    change (x⁻¹ * x * (1 : H)⁻¹) * (1 * 1 * (1 : H)⁻¹) =
      Generator.mixedProduct (identity H) (identity H)
        (Generator.mixedPair (identity H) (identity H) 1)
    simp

private theorem regular_bijective : Function.Bijective (regularBasis H) := by
  constructor
  · intro x y hxy
    obtain ⟨h, hh, hb⟩ := Quotient.exact hxy
    have h₁ : 1 * x * h⁻¹ = y := hh
    have h₂ := congrArg (Generator.mixedProduct (identity H) (identity H)) hb
    change (h * 1 * (1 : H)⁻¹) * (1 * 1 * (1 : H)⁻¹) =
      Generator.mixedProduct (identity H) (identity H)
        (Generator.mixedPair (identity H) (identity H) 1) at h₂
    have he : h = 1 := by simpa using h₂
    simpa [he] using h₁
  · intro z
    obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
    obtain ⟨x, rfl⟩ := (Generator.mixedEquiv (identity H) (identity H)).symm.surjective y
    exact ⟨g * x, (point_normal H g x).symm⟩

private theorem act_regular (q : H × H) (x : H) :
    (Boundary H).basis.act q (regularBasis H x) = regularBasis H (q.1 * x * q.2⁻¹) := by
  have he : (Boundary H).basis.act q (regularBasis H x) = point H (q.1 * x) q.2⁻¹ := by
    change (Up H).basis.pair (Mixed H).basis
      (q.1 * x * (1 : H)⁻¹)
      ((Down H).basis.pair (Up H).basis
        ((1 : H) * 1 * (1 : H)⁻¹) ((1 : H) * 1 * q.2⁻¹)) = _
    simp only [inv_one, mul_one, one_mul]
    change (Up H).basis.pair (Mixed H).basis (q.1 * x)
      ((Down H).basis.pair (Up H).basis 1 q.2⁻¹) = _
    congr 1
    apply (Generator.mixedEquiv (identity H) (identity H)).injective
    change 1 * q.2⁻¹ = Generator.mixedProduct (identity H) (identity H)
      (Generator.mixedPair (identity H) (identity H) q.2⁻¹)
    simp
  rw [he, point_normal]

private theorem project_basis_top (x : H) : projectBasis H (regularBasis H x) = ⊤ := by
  apply top_unique
  intro h _
  refine ⟨(x * h * x⁻¹, h), ?_, rfl⟩
  change (Boundary H).basis.act _ (regularBasis H x) = _
  rw [act_regular]
  congr 1
  group

private theorem ambient_project_conj (q : H × H) (z : PairBasis H) :
    letI := onPairs H
    ambientProject H (q • z) =
      (projectPair H z).map (H.subtype.comp (MulAut.conj q.2).toMonoidHom) := by
  intro inst
  change (projectPair H (q • z)).map H.subtype = _
  unfold projectPair
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext x
  rfl

end IdentityBoundary

private abbrev representative : PairBasis S₃ := (regularBasis S₃ 1, regularBasis S₃ cycle)

private theorem project_representative : projectPair S₃ representative = Subgroup.zpowers cycle := by
  classical
  letI := onPairs S₃
  have fixes (g h : S₃) :
      (g, h) • representative = representative ↔ g = h ∧ h * cycle = cycle * h := by
    change ((Boundary S₃).basis.act (g, h) (regularBasis S₃ 1),
      (Boundary S₃).basis.act (g, h) (regularBasis S₃ cycle)) = _ ↔ _
    rw [act_regular, act_regular, Prod.mk.injEq]
    simp only [(regular_bijective S₃).injective.eq_iff, mul_one]
    rw [mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h⟩
  constructor
  · rintro h ⟨⟨g, g'⟩, hfix, rfl⟩
    exact cycle_centralizer ((fixes g g').mp hfix).2
  · apply Subgroup.zpowers_le.mpr
    exact ⟨(cycle, cycle), (fixes cycle cycle).mpr ⟨rfl, rfl⟩, rfl⟩

private theorem orbit_iff (x y : S₃) :
    (regularBasis S₃ x, regularBasis S₃ y) ∈ pairOrbit S₃ representative ↔
      y = x * cycle ∨ y = x * cycle⁻¹ := by
  letI := onPairs S₃
  have acts (g h : S₃) :
      (g, h) • representative =
        (regularBasis S₃ (g * h⁻¹), regularBasis S₃ (g * cycle * h⁻¹)) := by
    change ((Boundary S₃).basis.act (g, h) (regularBasis S₃ 1),
      (Boundary S₃).basis.act (g, h) (regularBasis S₃ cycle)) = _
    rw [act_regular, act_regular, mul_one]
  constructor
  · rintro ⟨⟨g, h⟩, hh⟩
    change (g, h) • representative = _ at hh
    rw [acts, Prod.mk.injEq] at hh
    rcases hh with ⟨hg, hy⟩
    apply (regular_bijective S₃).injective at hg hy
    have he : y = x * (h * cycle * h⁻¹) := by rw [← hg, ← hy]; group
    rw [he]
    rcases cycle_conj h with h' | h' <;> simp [h']
  · rintro (rfl | rfl)
    · refine ⟨(x, 1), ?_⟩
      change (x, (1 : S₃)) • representative = _
      rw [acts, inv_one, mul_one, mul_one]
    · refine ⟨(x * transposition, transposition), ?_⟩
      change (x * transposition, transposition) • representative = _
      rw [acts, mul_inv_cancel_right, mul_assoc x transposition cycle, mul_assoc x, cycle_flip]

end CaseSixCharThree
