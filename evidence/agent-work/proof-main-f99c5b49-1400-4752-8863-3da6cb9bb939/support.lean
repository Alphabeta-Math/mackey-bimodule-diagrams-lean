open private crossingFiberSize from Proofs.ParabolicCaseTwoProjectionFiberIndices
open private leftBound conj conj_one finite_mixed from Proofs.ParabolicExtremalOutsideRestrictionRegions

namespace SmallerParabolicProjectionAux

open MackeyDiagrams

private def inclusion {U : Type*} [Group U] {H K : Subgroup U} (h : H ≤ K) :
    ConjEmbedding H K :=
  ⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩

private theorem mappedInclusionRange {U : Type*} [Group U] {H K : Subgroup U} (h : H ≤ K) :
    ((inclusion h).toHom.range).map K.subtype = H := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact y.property
  · intro hx
    exact ⟨(inclusion h).toHom ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩

private theorem inclusionFiber {U : Type*} [Group U] {A G B C : Subgroup U}
    [Finite G] [Finite B] (hGA : G ≤ A) (hBA : B ≤ A) (hCG : C ≤ G) (hCB : C ≤ B)
    (m : Dot ((inclusion hGA).comp (inclusion hCG)) ((inclusion hBA).comp (inclusion hCB)))
    (hm : m.element = 1) :
    let q := Generator.mixedMultiplicationBasis (inclusion hGA) (inclusion hBA)
      (inclusion hCG) (inclusion hCB) m
    ∀ z ∈ Set.range q, Nat.card {x // q x = z} = C.relIndex (G ⊓ B) := by
  intro q z hz
  -- The registered Case 2 proof uses Lemma 6.3 and equation (6.1) for one
  -- crossing. Its local calculation applies to this Case 1 middle crossing:
  -- the domain is a quotient of G × B, so all fibers are finite.
  let hp : ProjectionDot.Mixed (inclusion hGA) (inclusion hBA)
      (inclusion hCG) (inclusion hCB) :=
    ⟨m, finite_mixed _ _ _ _ m⟩
  have hc :
      ((inclusion hGA).comp (inclusion hCG)).toHom = (inclusion (hCG.trans hGA)).toHom := by
    ext x
    rfl
  have h := crossingFiberSize _ _ _ _ hp z hz
  change _ = ((inclusion hGA).comp (inclusion hCG)).toHom.range.relIndex
    (leftBound (inclusion hGA) (inclusion hBA) m.element) at h
  rw [h, hc]
  change ((inclusion (hCG.trans hGA)).toHom.range).relIndex
    ((inclusion hGA).toHom.range ⊓ conj m.element (inclusion hBA).toHom.range) = _
  rw [hm, conj_one,
    ← Subgroup.relIndex_map_map_of_injective _ _ A.subtype_injective,
    Subgroup.map_inf _ _ _ A.subtype_injective,
    mappedInclusionRange, mappedInclusionRange, mappedInclusionRange]

private theorem mem_of_blockSwaps {X : Type*} [Finite X] [DecidableEq X]
    (H : Subgroup (Equiv.Perm X)) (block : X → Prop) [DecidablePred block]
    (hswap : ∀ x y, block x → block y → x ≠ y → Equiv.swap x y ∈ H)
    (σ : Equiv.Perm X) (hfix : ∀ x, ¬ block x → σ x = x) : σ ∈ H := by
  have hmove (x : X) (hx : σ x ≠ x) : block x := by
    by_contra hn
    exact hx (hfix x hn)
  have hpres (x : X) : block (σ x) ↔ block x := by
    constructor
    · intro hx
      by_contra hn
      exact hn (hfix x hn ▸ hx)
    · intro hx
      by_contra hn
      have he := σ.injective (hfix (σ x) hn)
      apply hn
      rw [he]
      exact hx
  rw [← Equiv.Perm.ofSubtype_subtypePerm hpres hmove]
  induction σ.subtypePerm hpres using Equiv.Perm.swap_induction_on with
  | one => simpa only [map_one] using H.one_mem
  | swap_mul τ x y hxy ih =>
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq]
    exact H.mul_mem (hswap x y x.property y.property (fun h => hxy (Subtype.ext h))) ih

private abbrev Point := ↥({1, 2, 3, 4} : Finset Nat)
private abbrev p1 : Point := ⟨1, by decide⟩
private abbrev p2 : Point := ⟨2, by decide⟩
private abbrev p3 : Point := ⟨3, by decide⟩
private abbrev p4 : Point := ⟨4, by decide⟩
private abbrev Perm := Equiv.Perm Point
private abbrev G : Subgroup Perm := MulAction.stabilizer Perm p3
private abbrev P : Subgroup Perm := MulAction.stabilizer Perm p4
private abbrev C : Subgroup Perm := Subgroup.closure {Equiv.swap p1 p2}
private abbrev D : Subgroup Perm := Subgroup.closure {Equiv.swap p2 p3}

private theorem pointCases (x : Point) : x = p1 ∨ x = p2 ∨ x = p3 ∨ x = p4 := by
  have h := x.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  simpa only [Subtype.ext_iff] using h

private theorem leastRegion :
    IsLeast {B : Subgroup Perm | C ≤ B ∧ D ≤ B} P := by
  have hfix (x y : Point) (hx : p4 ≠ x) (hy : p4 ≠ y) : Equiv.swap x y ∈ P :=
    Equiv.swap_apply_of_ne_of_ne hx hy
  refine ⟨⟨(Subgroup.closure_le P).mpr (Set.singleton_subset_iff.mpr (hfix p1 p2 (by decide)
      (by decide))), (Subgroup.closure_le P).mpr (Set.singleton_subset_iff.mpr
      (hfix p2 p3 (by decide) (by decide)))⟩, ?_⟩
  intro H hH
  change C ≤ H ∧ D ≤ H at hH
  have h12 : Equiv.swap p1 p2 ∈ H := hH.1 (Subgroup.subset_closure (Set.mem_singleton _))
  have h23 : Equiv.swap p2 p3 ∈ H := hH.2 (Subgroup.subset_closure (Set.mem_singleton _))
  have h13 := SubmonoidClass.swap_mem_trans H h12 h23
  intro σ hσ
  refine mem_of_blockSwaps H (· ≠ p4) ?_ σ ?_
  · intro x y hx hy hxy
    rcases pointCases x with rfl | rfl | rfl | rfl <;>
      rcases pointCases y with rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hx rfl).elim
      | exact (hy rfl).elim
      | exact (hxy rfl).elim
      | exact h12
      | exact h23
      | exact h13
      | exact (Equiv.swap_comm p1 p2) ▸ h12
      | exact (Equiv.swap_comm p2 p3) ▸ h23
      | exact (Equiv.swap_comm p1 p3) ▸ h13
  · intro x hx
    rcases not_ne_iff.mp hx with rfl
    exact hσ

private theorem intersection : G ⊓ P = C := by
  apply le_antisymm
  · intro σ hσ
    have h3 : σ p3 = p3 := hσ.1
    have h4 : σ p4 = p4 := hσ.2
    refine mem_of_blockSwaps C (fun x => x ≠ p3 ∧ x ≠ p4) ?_ σ ?_
    · intro x y hx hy hxy
      have h12 : Equiv.swap p1 p2 ∈ C := Subgroup.subset_closure (Set.mem_singleton _)
      rcases pointCases x with rfl | rfl | rfl | rfl <;>
        rcases pointCases y with rfl | rfl | rfl | rfl
      all_goals
        first
        | exact (hx.1 rfl).elim
        | exact (hx.2 rfl).elim
        | exact (hy.1 rfl).elim
        | exact (hy.2 rfl).elim
        | exact (hxy rfl).elim
        | exact h12
        | exact (Equiv.swap_comm p1 p2) ▸ h12
    · intro x hx
      by_cases h : x = p3
      · simpa only [h] using h3
      · have h' : x = p4 := not_ne_iff.mp (fun hn => hx ⟨h, hn⟩)
        simpa only [h'] using h4
  · apply (Subgroup.closure_le _).mpr
    apply Set.singleton_subset_iff.mpr
    exact ⟨Equiv.swap_apply_of_ne_of_ne (by decide) (by decide),
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)⟩

private theorem ambientIndex : C.relIndex G = 3 := by
  have hstab : C.subgroupOf G = MulAction.stabilizer G p4 := by
    ext g
    change (g : Perm) ∈ C ↔ (g : Perm) p4 = p4
    rw [← intersection]
    exact ⟨And.right, fun hg => ⟨g.property, hg⟩⟩
  have horbit (x : Point) : x ∈ MulAction.orbit G p4 ↔ x ≠ p3 := by
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩ rfl
      have h : (g : Perm) p4 = p3 := hg
      have hg3 : (g : Perm) p3 = p3 := g.property
      exact (by decide : p4 ≠ p3) ((g : Perm).injective (h.trans hg3.symm))
    · intro hx
      refine ⟨⟨Equiv.swap p4 x, ?_⟩, Equiv.swap_apply_left _ _⟩
      exact Equiv.swap_apply_of_ne_of_ne (by decide) hx.symm
  let s : Finset Nat := {1, 2, 3, 4}
  have hmem (x : Point) : x ≠ p3 ↔ x.val ∈ s.erase 3 := by
    rw [Finset.mem_erase]
    exact ⟨fun hx => ⟨fun h => hx (Subtype.ext h), x.property⟩,
      fun hx h => hx.1 (congrArg Subtype.val h)⟩
  let orbitPoints : MulAction.orbit G p4 ≃ ↥(s.erase 3) :=
    { toFun := fun x => ⟨x.val.val, (hmem x.val).mp ((horbit x.val).mp x.property)⟩
      invFun := fun x =>
        let y : Point := ⟨x.val, Finset.mem_of_mem_erase x.property⟩
        ⟨y, (horbit y).mpr ((hmem y).mpr x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (C.subgroupOf G).index = 3
  rw [hstab, Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G p4),
    Nat.card_congr orbitPoints, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_erase_of_mem (by decide : 3 ∈ s)]
  rfl

end SmallerParabolicProjectionAux
