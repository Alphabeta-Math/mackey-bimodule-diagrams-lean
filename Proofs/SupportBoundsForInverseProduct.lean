import MackeyDiagrams
import Proofs.SupportBoundsUnderComposition

set_option maxHeartbeats 2000000

theorem SupportBoundsForInverseProduct : (
let A : Finset Nat := Finset.Icc 1 2
let B : Finset Nat := Finset.Icc 3 4
let C : Finset Nat := Finset.Icc 5 6
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun S => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let G := blockSym A ⊔ blockSym B ⊔ blockSym C
let H := blockSym A
let Ghat := blockSym (A ∪ B ∪ C)
let bound : Set (Equiv.Perm Nat) :=
  Set.image2 (fun x y => x * y) (Ghat : Set (Equiv.Perm Nat)) (H : Set (Equiv.Perm Nat))
let conjugate : Equiv.Perm Nat → Subgroup (Equiv.Perm Nat) → Subgroup (Equiv.Perm Nat) :=
  fun σ S => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj σ)) S
let α : Equiv.Perm Nat := Equiv.swap 1 3 * Equiv.swap 2 4
let β : Equiv.Perm Nat := Equiv.swap 4 5
let γ := β * α⁻¹
α ∈ bound ∧
  β ∈ bound ∧
  conjugate α H ≤ G ∧
  conjugate β H ≤ G ∧
  Finset.image γ A = ({3, 5} : Finset Nat) ∧
  ¬ (conjugate γ H ≤ G)
) :=
(by
  intro A B C blockSym G H Ghat bound conjugate α β γ
  -- Xiao, Example 3.7, archived PDF p. 11 and 28 November revision p. 13.
  -- Alphabeta Math, https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group,
  -- step 1.1 checks a product of swaps pointwise, with the rightmost factor first.
  -- The swaps are given here, so the finite-carrier decomposition in step 2.1
  -- is unnecessary. On Nat we check the complement of each finite block.
  -- SupportBoundsUnderComposition treats six-point blocks and β = 1.
  -- Its conclusion supplies no containment for these two-point blocks.
  have memA (x : Nat) : x ∈ A ↔ 1 ≤ x ∧ x ≤ 2 := Finset.mem_Icc
  have memB (x : Nat) : x ∈ B ↔ 3 ≤ x ∧ x ≤ 4 := Finset.mem_Icc
  have memC (x : Nat) : x ∈ C ↔ 5 ≤ x ∧ x ≤ 6 := Finset.mem_Icc
  have oneA := (memA 1).mpr (by decide)
  have twoA := (memA 2).mpr (by decide)
  have threeB := (memB 3).mpr (by decide)
  have fourB := (memB 4).mpr (by decide)
  have fiveC := (memC 5).mpr (by decide)
  have memPair (x : Nat) : x ∈ A ↔ x = 1 ∨ x = 2 := by
    rw [memA]
    omega
  have blockOfFix (S : Finset Nat) (p : Equiv.Perm Nat)
      (fix : ∀ x, x ∉ S → p x = x) : p ∈ blockSym S := by
    let e := Equiv.Perm.subtypeEquivSubtypePerm (fun x : Nat => x ∈ S)
    exact ⟨e.symm ⟨p, fix⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p, fix⟩)⟩
  have blockFix (S : Finset Nat) (p : Equiv.Perm Nat) (hp : p ∈ blockSym S)
      (x : Nat) (hx : x ∉ S) : p x = x := by
    obtain ⟨f, rfl⟩ := hp
    exact Equiv.Perm.ofSubtype_apply_of_not_mem f hx
  have swapFix {S : Finset Nat} {u v : Nat} (hu : u ∈ S) (hv : v ∈ S)
      (x : Nat) (hx : x ∉ S) : Equiv.swap u v x = x :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hx (h.symm ▸ hu)) (fun h => hx (h.symm ▸ hv))
  let U := A ∪ B ∪ C
  have oneU : 1 ∈ U := Finset.mem_union_left _ (Finset.mem_union_left _ oneA)
  have twoU : 2 ∈ U := Finset.mem_union_left _ (Finset.mem_union_left _ twoA)
  have threeU : 3 ∈ U := Finset.mem_union_left _ (Finset.mem_union_right _ threeB)
  have fourU : 4 ∈ U := Finset.mem_union_left _ (Finset.mem_union_right _ fourB)
  have fiveU : 5 ∈ U := Finset.mem_union_right _ fiveC
  have αhat : α ∈ Ghat := by
    apply blockOfFix U α
    intro x hx
    by_contra moved
    change (Equiv.swap 1 3 * Equiv.swap 2 4 : Equiv.Perm Nat) x ≠ x at moved
    rcases Equiv.Perm.set_support_mul_subset _ _ moved with h | h
    · exact h (swapFix oneU threeU x hx)
    · exact h (swapFix twoU fourU x hx)
  have βhat : β ∈ Ghat := blockOfFix U β (swapFix fourU fiveU)
  have boundOfHat (p : Equiv.Perm Nat) (hp : p ∈ Ghat) : p ∈ bound :=
    ⟨p, hp, 1, H.one_mem, mul_one p⟩
  have transport (σ : Equiv.Perm Nat) (T : Finset Nat)
      (maps : ∀ x ∈ A, σ x ∈ T) : conjugate σ H ≤ blockSym T := by
    rintro q ⟨p, hp, rfl⟩
    apply blockOfFix T
    intro x hx
    have outside : σ.symm x ∉ A :=
      fun h => hx (by simpa only [Equiv.apply_symm_apply] using maps (σ.symm x) h)
    change σ (p (σ.symm x)) = x
    rw [blockFix A p hp _ outside, Equiv.apply_symm_apply]
  have αone : α 1 = 3 := by
    simp [α, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have αtwo : α 2 = 4 := by
    simp [α, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have βone : β 1 = 1 := by
    simp [β, Equiv.swap_apply_def]
  have βtwo : β 2 = 2 := by
    simp [β, Equiv.swap_apply_def]
  have embα : conjugate α H ≤ G := by
    refine (transport α B ?_).trans (le_sup_of_le_left le_sup_right)
    intro x hx
    rcases (memPair x).mp hx with rfl | rfl
    · exact αone.symm ▸ threeB
    · exact αtwo.symm ▸ fourB
  have embβ : conjugate β H ≤ G := by
    refine (transport β A ?_).trans (le_sup_of_le_left le_sup_left)
    intro x hx
    rcases (memPair x).mp hx with rfl | rfl
    · exact βone.symm ▸ oneA
    · exact βtwo.symm ▸ twoA
  -- The inverse-support equality identifies the moved points of α⁻¹. To get
  -- the exact image under β * α⁻¹, compute the two inverse images via α's
  -- forward action and then apply β.
  have αinvOne : α.symm 1 = 3 := by
    apply α.injective
    rw [Equiv.apply_symm_apply]
    simp [α, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have αinvTwo : α.symm 2 = 4 := by
    apply α.injective
    rw [Equiv.apply_symm_apply]
    simp [α, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have γone : γ 1 = 3 := by
    change β (α.symm 1) = 3
    simp [αinvOne, β, Equiv.swap_apply_def]
  have γtwo : γ 2 = 5 := by
    change β (α.symm 2) = 5
    simp [αinvTwo, β]
  have image : Finset.image γ A = ({3, 5} : Finset Nat) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton, memPair]
    constructor
    · rintro ⟨y, rfl | rfl, h⟩
      · exact Or.inl (h.symm.trans γone)
      · exact Or.inr (h.symm.trans γtwo)
    · rintro (rfl | rfl)
      · exact ⟨1, Or.inl rfl, γone⟩
      · exact ⟨2, Or.inr rfl, γtwo⟩
  -- The target preserves B setwise. The conjugate of (1 2) takes 3 out of B.
  let preservesB : Subgroup (Equiv.Perm Nat) :=
    { carrier := {p | ∀ x, p x ∈ B ↔ x ∈ B}
      one_mem' := fun _ => Iff.rfl
      mul_mem' := fun hp hq x => (hp _).trans (hq x)
      inv_mem' := fun {p} hp x => by
        change p.symm x ∈ B ↔ x ∈ B
        simpa only [Equiv.apply_symm_apply] using (hp (p.symm x)).symm }
  have preserveOther (S : Finset Nat) (hd : Disjoint S B) : blockSym S ≤ preservesB := by
    intro p hp x
    by_cases hx : x ∈ S
    · obtain ⟨f, rfl⟩ := hp
      exact iff_of_false
        (Finset.disjoint_left.mp hd ((Equiv.Perm.ofSubtype_apply_mem_iff_mem f x).mpr hx))
        (Finset.disjoint_left.mp hd hx)
    · rw [blockFix S p hp x hx]
  have preserveOwn : blockSym B ≤ preservesB := by
    rintro p ⟨f, rfl⟩
    exact Equiv.Perm.ofSubtype_apply_mem_iff_mem f
  have disjointAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have := (memA x).mp hxA
    have := (memB x).mp hxB
    omega
  have disjointCB : Disjoint C B := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxB
    have := (memC x).mp hxC
    have := (memB x).mp hxB
    omega
  have preserveG : G ≤ preservesB :=
    sup_le (sup_le (preserveOther A disjointAB) preserveOwn) (preserveOther C disjointCB)
  refine ⟨boundOfHat α αhat, boundOfHat β βhat, embα, embβ, image, ?_⟩
  intro contained
  let τ : Equiv.Perm Nat := Equiv.swap 1 2
  have τH : τ ∈ H := blockOfFix A τ (swapFix oneA twoA)
  have swapIn : (Equiv.swap 3 5 : Equiv.Perm Nat) ∈ conjugate γ H := by
    refine ⟨τ, τH, ?_⟩
    change γ * Equiv.swap 1 2 * γ⁻¹ = Equiv.swap 3 5
    rw [← Equiv.swap_apply_apply, γone, γtwo]
  have h := preserveG (contained swapIn) 3
  rw [Equiv.swap_apply_left] at h
  have fiveNotB : 5 ∉ B := fun hx => (by decide : ¬ (5 ≤ 4)) ((memB 5).mp hx).2
  exact fiveNotB (h.mpr threeB)
)
