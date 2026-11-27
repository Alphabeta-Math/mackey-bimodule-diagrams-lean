import MackeyDiagrams
import Proofs.ConjugationEmbeddingCentralizerCoset
import Proofs.FiniteParabolicClosure
import Proofs.FiniteParabolicConjugateBlocks

set_option maxHeartbeats 2000000

namespace SupportBoundsUnderCompositionAux

private def blockExchange (xs : List Nat) : Equiv.Perm Nat :=
  (xs.map fun a => Equiv.swap a (a + 6)).prod

private theorem exchange_fixes (xs : List Nat) (x : Nat)
    (avoids : ∀ a ∈ xs, x ≠ a ∧ x ≠ a + 6) : blockExchange xs x = x := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_contra moved
      change (Equiv.swap a (a + 6) * blockExchange xs) x ≠ x at moved
      rcases Equiv.Perm.set_support_mul_subset _ _ moved with head | tail
      · obtain ⟨ha, ha'⟩ := avoids a (List.mem_cons_self)
        exact head (Equiv.swap_apply_of_ne_of_ne ha ha')
      · exact tail (ih (fun b hb => avoids b (List.mem_cons_of_mem _ hb)))

private theorem exchange_pair (xs : List Nat) (nodup : xs.Nodup)
    (within : ∀ a ∈ xs, 1 ≤ a ∧ a ≤ 6) (x : Nat) (hx : x ∈ xs) :
    blockExchange xs x = x + 6 ∧ blockExchange xs (x + 6) = x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      have tailWithin (b : Nat) (hb : b ∈ xs) : 1 ≤ b ∧ b ≤ 6 :=
        within b (List.mem_cons_of_mem _ hb)
      have ax := within a List.mem_cons_self
      have xx := within x hx
      have hnodup := List.nodup_cons.mp nodup
      change (Equiv.swap a (a + 6) * blockExchange xs) x = x + 6 ∧
        (Equiv.swap a (a + 6) * blockExchange xs) (x + 6) = x
      simp only [Equiv.Perm.mul_apply]
      rcases List.mem_cons.mp hx with eq | htail
      · subst x
        have avoid (b : Nat) (hb : b ∈ xs) : a ≠ b := fun eq =>
          hnodup.1 (eq ▸ hb)
        rw [exchange_fixes xs a (fun b hb => by
              have := tailWithin b hb
              exact ⟨avoid b hb, by omega⟩),
            exchange_fixes xs (a + 6) (fun b hb => by
              have := tailWithin b hb
              have := avoid b hb
              exact ⟨by omega, by omega⟩)]
        exact ⟨Equiv.swap_apply_left _ _, Equiv.swap_apply_right _ _⟩
      · have ne : x ≠ a := fun eq => hnodup.1 (eq ▸ htail)
        obtain ⟨left, right⟩ := ih hnodup.2 tailWithin htail
        rw [left, right, Equiv.swap_apply_of_ne_of_ne (by omega : x + 6 ≠ a)
          (by omega : x + 6 ≠ a + 6), Equiv.swap_apply_of_ne_of_ne ne (by omega : x ≠ a + 6)]
        exact ⟨rfl, rfl⟩
end SupportBoundsUnderCompositionAux

theorem SupportBoundsUnderComposition : (let A : Finset Nat := Finset.Icc 1 6
let B : Finset Nat := Finset.Icc 7 12
let supportK : Finset Nat := Finset.Icc 1 3
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun S => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let subgroupProduct : Subgroup (Equiv.Perm Nat) → Subgroup (Equiv.Perm Nat) →
    Set (Equiv.Perm Nat) :=
  fun S T => Set.image2 (fun x y => x * y) (S : Set (Equiv.Perm Nat))
    (T : Set (Equiv.Perm Nat))
let G := blockSym A ⊔ blockSym B
let H := G
let K := blockSym supportK
let Hhat := blockSym (A ∪ B)
let Khat := blockSym supportK
let β : Equiv.Perm Nat := 1
∃ (α : Equiv.Perm Nat)
    (hα : ∀ h : H, α * (h : Equiv.Perm Nat) * α⁻¹ ∈ G)
    (hβ : ∀ k : K, β * (k : Equiv.Perm Nat) * β⁻¹ ∈ H),
  Finset.image α A = B ∧
  Finset.image α B = A ∧
  α ∈ subgroupProduct G Hhat ∧
  β ∈ subgroupProduct H Khat ∧
  (∀ γ ∈ subgroupProduct G Khat, Finset.image γ A = A ∧ Finset.image γ B = B) ∧
  Set.MapsTo (⇑(α * β)) (supportK : Set Nat) (B : Set Nat) ∧
  α * β ∉ subgroupProduct G Khat ∧
  ¬ ∃ (γ : Equiv.Perm Nat) (_ : γ ∈ subgroupProduct G Khat)
      (hγ : ∀ k : K, γ * (k : Equiv.Perm Nat) * γ⁻¹ ∈ G),
    MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ =
      MackeyDiagrams.ConjEmbedding.comp
        (MackeyDiagrams.ConjEmbedding.ofConjugator α hα)
        (MackeyDiagrams.ConjEmbedding.ofConjugator β hβ)) :=
(by
  intro A B supportK blockSym subgroupProduct G H K Hhat Khat β
  -- Xiao, Example 3.6, project PDF p. 11 and published PDF p. 13.
  -- The downloaded PDF and project copy have different SHA-256 digests.
  -- The text of this example agrees in both versions.
  -- Alphabeta Math, https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group,
  -- step 1.1 suggests checking the action of a transposition product pointwise.
  -- Here the cycles are already disjoint transpositions. We give the six factors
  -- explicitly on Nat and verify their complement is fixed, taking the place of
  -- the finite-carrier cycle decomposition and concatenation in step 2.1.
  let xs : List Nat := [1, 2, 3, 4, 5, 6]
  let α := SupportBoundsUnderCompositionAux.blockExchange xs
  have memA (x : Nat) : x ∈ A ↔ 1 ≤ x ∧ x ≤ 6 := Finset.mem_Icc
  have memB (x : Nat) : x ∈ B ↔ 7 ≤ x ∧ x ≤ 12 := Finset.mem_Icc
  have memK (x : Nat) : x ∈ supportK ↔ 1 ≤ x ∧ x ≤ 3 := Finset.mem_Icc
  have listMem (x : Nat) : x ∈ xs ↔ x ∈ A := by
    rw [memA]
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have exchange (x : Nat) (hx : x ∈ A) : α x = x + 6 ∧ α (x + 6) = x :=
    SupportBoundsUnderCompositionAux.exchange_pair xs (by decide)
      (fun a ha => (memA a).mp ((listMem a).mp ha)) x ((listMem x).mpr hx)
  have shift (x : Nat) (hx : x ∈ A) : x + 6 ∈ B := by
    have := (memA x).mp hx
    exact (memB _).mpr (by omega)
  have unshift (x : Nat) (hx : x ∈ B) : x - 6 ∈ A := by
    have := (memB x).mp hx
    exact (memA _).mpr (by omega)
  have addBack (x : Nat) (hx : x ∈ B) : x - 6 + 6 = x := by
    have := (memB x).mp hx
    omega
  have imageA : Finset.image α A = B := by
    ext x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [(exchange y hy).1]
      exact shift y hy
    · intro hx
      have hy := unshift x hx
      exact ⟨x - 6, hy, (exchange _ hy).1.trans (addBack x hx)⟩
  have imageB : Finset.image α B = A := by
    ext x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e := (exchange _ (unshift y hy)).2
      rw [addBack y hy] at e
      rw [e]
      exact unshift y hy
    · intro hx
      exact ⟨x + 6, shift x hx, (exchange x hx).2⟩
  have αfix (x : Nat) (hx : x ∉ A ∪ B) : α x = x := by
    apply SupportBoundsUnderCompositionAux.exchange_fixes
    intro a ha
    have haA := (listMem a).mp ha
    exact ⟨fun eq => hx (Finset.mem_union_left _ (eq ▸ haA)),
      fun eq => hx (Finset.mem_union_right _ (eq ▸ shift a haA))⟩

  have blockOfFix (S : Finset Nat) (p : Equiv.Perm Nat)
      (fix : ∀ x, x ∉ S → p x = x) : p ∈ blockSym S := by
    let e := Equiv.Perm.subtypeEquivSubtypePerm (fun x : Nat => x ∈ S)
    exact ⟨e.symm ⟨p, fix⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p, fix⟩)⟩
  have KinsideA : supportK ⊆ A := by
    intro x hx
    have := (memK x).mp hx
    exact (memA x).mpr (by omega)
  have KleG : K ≤ G := by
    intro p hp
    apply le_sup_left (a := blockSym A) (b := blockSym B)
    apply blockOfFix A p
    obtain ⟨σ, rfl⟩ := hp
    exact fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem σ (fun hk => hx (KinsideA hk))

  -- Use the registered exact block formula, including its finitary, nonempty
  -- and disjoint hypotheses. FiniteParabolicClosure only asserts parabolicity.
  let blocks : Bool → Finset Nat := fun i => if i then A else B
  have supBlocks : (⨆ i, blockSym (blocks i)) = G := by
    rw [iSup_bool_eq]
  have disjointAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hA hB
    have := (memA x).mp hA
    have := (memB x).mp hB
    omega
  have nonempty : ∀ i, (blocks i).Nonempty := by
    intro i
    cases i
    · exact ⟨7, (memB 7).mpr (by decide)⟩
    · exact ⟨1, (memA 1).mpr (by decide)⟩
  have disjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)) := by
    intro i j ne
    cases i <;> cases j
    · exact (ne rfl).elim
    · exact disjointAB.symm
    · exact disjointAB
    · exact (ne rfl).elim
  have finitary : α ∈ Subgroup.closure {σ : Equiv.Perm Nat | σ.IsSwap} := by
    apply mem_closure_isSwap'.mpr
    refine (A ∪ B).finite_toSet.subset ?_
    intro x moved
    by_contra hx
    exact moved (show x ∈ MulAction.fixedBy Nat α from αfix x hx)
  have conjugates :
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) G = G := by
    have e := FiniteParabolicConjugateBlocks blocks nonempty disjoint ⟨α, finitary⟩
    change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α))
      (⨆ i, blockSym (blocks i)) = ⨆ i, blockSym ((blocks i).image α) at e
    rw [supBlocks, iSup_bool_eq] at e
    change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) G =
      blockSym (A.image α) ⊔ blockSym (B.image α) at e
    rw [imageA, imageB, sup_comm] at e
    exact e
  have hα (h : H) : α * (h : Equiv.Perm Nat) * α⁻¹ ∈ G := by
    rw [← conjugates]
    exact ⟨h, h.property, rfl⟩
  have hβ (k : K) : β * (k : Equiv.Perm Nat) * β⁻¹ ∈ H := by
    simpa only [β, inv_one, one_mul, mul_one] using KleG k.property

  have preserveG (p : Equiv.Perm Nat) (hp : p ∈ G) :
      (∀ x, p x ∈ A ↔ x ∈ A) ∧ (∀ x, p x ∈ B ↔ x ∈ B) := by
    rw [← supBlocks] at hp
    refine Subgroup.iSup_induction (fun i => blockSym (blocks i))
      (C := fun p => (∀ x, p x ∈ A ↔ x ∈ A) ∧ (∀ x, p x ∈ B ↔ x ∈ B)) hp ?_ ?_ ?_
    · intro i p hp
      obtain ⟨σ, rfl⟩ := hp
      have own := Equiv.Perm.ofSubtype_apply_mem_iff_mem σ
      have other (S : Finset Nat) (d : Disjoint (blocks i) S) (x : Nat) :
          Equiv.Perm.ofSubtype σ x ∈ S ↔ x ∈ S := by
        by_cases hx : x ∈ blocks i
        · exact iff_of_false
            (Finset.disjoint_left.mp d ((own x).mpr hx)) (Finset.disjoint_left.mp d hx)
        · rw [Equiv.Perm.ofSubtype_apply_of_not_mem σ hx]
      cases i
      · exact ⟨other A disjointAB.symm, own⟩
      · exact ⟨own, other B disjointAB⟩
    · exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    · rintro p q ⟨pA, pB⟩ ⟨qA, qB⟩
      exact ⟨fun x => (pA (q x)).trans (qA x), fun x => (pB (q x)).trans (qB x)⟩
  have preserveImage (p : Equiv.Perm Nat) (S : Finset Nat)
      (preserves : ∀ x, p x ∈ S ↔ x ∈ S) : S.image p = S := by
    ext x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (preserves y).mpr hy
    · intro hx
      obtain ⟨y, rfl⟩ := p.surjective x
      exact ⟨y, (preserves y).mp hx, rfl⟩
  have productInG (p : Equiv.Perm Nat) (hp : p ∈ subgroupProduct G Khat) : p ∈ G := by
    obtain ⟨g, hg, k, hk, rfl⟩ := hp
    exact G.mul_mem hg (KleG hk)
  have αin : α ∈ subgroupProduct G Hhat :=
    ⟨1, G.one_mem, α, blockOfFix _ _ αfix, one_mul α⟩
  have βin : β ∈ subgroupProduct H Khat :=
    ⟨1, H.one_mem, 1, Khat.one_mem, one_mul 1⟩
  have moveK : Set.MapsTo (⇑(α * β)) (supportK : Set Nat) (B : Set Nat) := by
    intro x hx
    have hxA := KinsideA hx
    change (α * β) x ∈ B
    simpa only [β, mul_one, (exchange x hxA).1] using shift x hxA
  have oneK : 1 ∈ supportK := (memK 1).mpr (by decide)
  have oneA := KinsideA oneK
  refine ⟨α, hα, hβ, imageA, imageB, αin, βin, ?_, moveK, ?_, ?_⟩
  · intro p hp
    obtain ⟨pA, pB⟩ := preserveG p (productInG p hp)
    exact ⟨preserveImage p A pA, preserveImage p B pB⟩
  · intro hp
    exact Finset.disjoint_left.mp disjointAB
      (((preserveG _ (productInG _ hp)).1 1).mpr oneA) (moveK oneK)
  · -- Test equality at the actual source element (1 2). The centralizer-coset
    -- supplier compares linearized maps of two conjugators. The endpoint uses
    -- equality of the typed embeddings themselves, so evaluate their toHom.
    rintro ⟨γ, hγProduct, hγ, same⟩
    have twoK : 2 ∈ supportK := (memK 2).mpr (by decide)
    let τ : Equiv.Perm Nat := Equiv.swap 1 2
    have τK : τ ∈ K :=
      ⟨Equiv.swap (⟨1, oneK⟩ : {x // x ∈ supportK}) ⟨2, twoK⟩,
        Equiv.Perm.ofSubtype_swap_eq _ _⟩
    let k : K := ⟨τ, τK⟩
    have sameAt := congrArg (fun e : MackeyDiagrams.ConjEmbedding K G =>
      (e.toHom k : Equiv.Perm Nat)) same
    simp only [MackeyDiagrams.ConjEmbedding.comp_apply,
      MackeyDiagrams.ConjEmbedding.ofConjugator_apply, β, inv_one, one_mul, mul_one] at sameAt
    change γ * Equiv.swap 1 2 * γ⁻¹ = α * Equiv.swap 1 2 * α⁻¹ at sameAt
    rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply] at sameAt
    have γA := (preserveG γ (productInG γ hγProduct)).1
    have αoneB : α 1 ∈ B := by
      rw [(exchange 1 oneA).1]
      exact shift 1 oneA
    have γfix : Equiv.swap (γ 1) (γ 2) (α 1) = α 1 :=
      Equiv.swap_apply_of_ne_of_ne
        (fun eq => Finset.disjoint_left.mp disjointAB ((γA 1).mpr oneA) (eq ▸ αoneB))
        (fun eq => Finset.disjoint_left.mp disjointAB ((γA 2).mpr (KinsideA twoK)) (eq ▸ αoneB))
    have atPoint := congrArg (fun p : Equiv.Perm Nat => p (α 1)) sameAt
    change Equiv.swap (γ 1) (γ 2) (α 1) = Equiv.swap (α 1) (α 2) (α 1) at atPoint
    rw [γfix, Equiv.swap_apply_left] at atPoint
    exact (by decide : (1 : Nat) ≠ 2) (α.injective atPoint))

#print axioms SupportBoundsUnderComposition
