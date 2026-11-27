import MackeyDiagrams
import Proofs.InductionBimoduleOrbitSumBasis
import Proofs.BlockwiseGroupElementDotCriterion
import Proofs.FiniteOrbitSumDiagram

set_option maxHeartbeats 2000000

namespace BlockSwapOrbitSumSupport

open MackeyDiagrams

private abbrev U : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}

private abbrev block (B : Set Nat) : Subgroup ↥U :=
  fixingSubgroup (↥U) Bᶜ

private theorem fixesOutside {B : Set Nat} {p : ↥U} (hp : p ∈ block B)
    {x : Nat} (hx : x ∉ B) : p.val x = x :=
  (mem_fixingSubgroup_iff _).mp hp x hx

private theorem mapsBlock {B : Set Nat} {p : ↥U} (hp : p ∈ block B) :
    Set.MapsTo p.val B B := by
  intro x hx
  by_contra hout
  exact hout ((p.val.injective (fixesOutside hp hout)).symm ▸ hx)

private theorem preservesBlocks {ι : Type*} (Y : ι → Set Nat)
    (hY : Pairwise (fun i j => Disjoint (Y i) (Y j))) (j : ι)
    {p : ↥U} (hp : p ∈ ⨆ i, block (Y i)) : Set.MapsTo p.val (Y j) (Y j) := by
  refine Subgroup.iSup_induction (fun i => block (Y i))
    (C := fun q => Set.MapsTo q.val (Y j) (Y j)) hp ?_ ?_ ?_
  · intro i q hq
    by_cases hij : i = j
    · subst i
      exact mapsBlock hq
    · intro x hx
      have hout : x ∉ Y i := fun hi => Set.disjoint_left.mp (hY hij) hi hx
      exact (fixesOutside hq hout).symm ▸ hx
  · exact fun _ hx => hx
  · exact fun _ _ hq hr _ hx => hq (hr hx)

private theorem conjugatesInto {ι κ : Type*} (X : ι → Set Nat) (Y : κ → Set Nat)
    (p : ↥U) (k : ι → κ) (hmaps : ∀ i, Set.MapsTo p.val (X i) (Y (k i)))
    (h : ↥(⨆ i, block (X i))) : p * h.val * p⁻¹ ∈ ⨆ j, block (Y j) := by
  let G : Subgroup ↥U := ⨆ j, block (Y j)
  have hle : (⨆ i, block (X i)) ≤ G.comap (MulAut.conj p).toMonoidHom := by
    refine iSup_le fun i q hq => ?_
    change p * q * p⁻¹ ∈ G
    refine Subgroup.mem_iSup_of_mem (k i) ?_
    apply (mem_fixingSubgroup_iff _).mpr
    intro x hx
    have hout : (p.val⁻¹ : Equiv.Perm Nat) x ∉ X i := by
      intro hmem
      apply hx
      simpa using hmaps i hmem
    change (p.val * q.val * p.val⁻¹) x = x
    simp only [Equiv.Perm.mul_apply]
    rw [fixesOutside hq hout]
    exact p.val.apply_symm_apply x
  exact hle h.property

private theorem finiteOfBound {H : Subgroup ↥U} {S : Set Nat}
    (hle : H ≤ block S) (hS : S.Finite) : Finite H := by
  classical
  let _ : Finite S := hS
  let restrict := (Equiv.Perm.subtypeEquivSubtypePerm (· ∈ S)).symm
  let asPerm : H → {p : Equiv.Perm Nat // ∀ x, x ∉ S → p x = x} :=
    fun p => ⟨p.val.val, fun _ hx => fixesOutside (hle p.property) hx⟩
  have hinj : Function.Injective asPerm := by
    intro p q hpq
    have hv := congrArg Subtype.val hpq
    exact Subtype.ext (Subtype.ext hv)
  exact Finite.of_injective (restrict ∘ asPerm) (restrict.injective.comp hinj)

private theorem swapInBlock {B : Set Nat} {i j : Nat} {p : ↥U}
    (hp : p.val = Equiv.swap i j) (hi : i ∈ B) (hj : j ∈ B) : p ∈ block B := by
  apply (mem_fixingSubgroup_iff _).mpr
  intro x hx
  change p.val x = x
  rw [hp]
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h.symm ▸ hi)) (fun h => hx (h.symm ▸ hj))

private theorem orbitDiagram {V : Type*} [Group V] (H G : Subgroup V) [Finite H]
    (α β : V) (hα : ∀ h : H, α * h.val * α⁻¹ ∈ G) (hβ : ∀ h : H, β * h.val * β⁻¹ ∈ G)
    (g : G) :
    let a := ConjEmbedding.ofConjugator α hα
    let b := ConjEmbedding.ofConjugator β hβ
    let orbit := Set.range (fun h : H => a.toHom h * g * (b.toHom h)⁻¹)
    ∃ s : Finset G, (s : Set G) = orbit ∧
      ∃ d : Diagram Complex (Word.up a) (Word.up b),
        ∀ x : MonoidAlgebra Complex G, d.eval.toLinearMap x.coeff =
          (x * ∑ z ∈ s, MonoidAlgebra.single z (1 : Complex)).coeff := by
  intro a b orbit
  obtain ⟨basis, hbasis, _, hdiagram⟩ := FiniteOrbitSumDiagram H G α β hα hβ
  -- Alphabeta Math, Orbit-stabiliser, steps 1.1, 2.1 and 3.1
  -- (https://alphabetamath.cc/item/thm-orbit-stabilizer). Step 2.1 uses the
  -- range description of the orbit. Finiteness here comes from the separate
  -- hypothesis Finite H. FiniteOrbitSumDiagram checks the twisted left action
  -- using the two homomorphisms and uses the coset equivalence in steps 1.1
  -- and 3.1 to count each fiber before dividing by the stabilizer order.
  have hfinite : orbit.Finite := Set.finite_range _
  have hscaled := (hdiagram g).2.2
  refine ⟨hfinite.toFinset, hfinite.coe_toFinset, _, fun x => (hscaled x).trans ?_⟩
  exact congrArg MonoidAlgebra.coeff (hbasis ⟨hfinite.toFinset, ⟨g, hfinite.coe_toFinset⟩⟩ x)

private theorem nonzeroAtIdentity {G : Type*} [Group G] (s : Finset G) (hs : 1 ∈ s) :
    (∑ z ∈ s, MonoidAlgebra.single z (1 : Complex)).coeff 1 = 1 := by
  classical
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, hs]

end BlockSwapOrbitSumSupport

theorem BlockSwapOrbitSumWithoutGroupDot : (
let B₁ : Set Nat := {1, 2, 3}
  let B₂ : Set Nat := {4, 5, 6}
  let B₃ : Set Nat := {7, 8, 9}
  let B₄ : Set Nat := {10, 11, 12}
  let X : Fin 4 → Set Nat := ![B₁, B₂, B₃, B₄]
  let Y : Fin 2 → Set Nat := ![B₁ ∪ B₂, B₃ ∪ B₄]
  let U := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
  let blockSym := fun B : Set Nat => _root_.fixingSubgroup (↥U) Bᶜ
  let H := iSup (fun i => blockSym (X i))
  let G := iSup (fun j => blockSym (Y j))
  let swap := fun (i j : Nat) (hij : i ≠ j) =>
    (⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩ : ↥U)
  let α := swap 4 7 (by decide) * swap 5 8 (by decide) * swap 6 9 (by decide)
  let β : ↥U := 1
  ∃ (hα : ∀ h : H, α * (h : ↥U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : ↥U) * β⁻¹ ∈ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
    let orbit := Set.range (fun h : H =>
      MackeyDiagrams.ConjEmbedding.toHom a h * (1 : G) *
        (MackeyDiagrams.ConjEmbedding.toHom b h)⁻¹)
    (∀ (g : G) (j : Fin 2), Set.MapsTo (⇑((g : ↥U) : Equiv.Perm Nat)) (Y j) (Y j)) ∧
    (∃ t : H,
      ((t : ↥U) : Equiv.Perm Nat) = Equiv.swap 4 5 ∧
      (((MackeyDiagrams.ConjEmbedding.toHom a t : G) : ↥U) : Equiv.Perm Nat) =
        Equiv.swap 7 8 ∧
      (((MackeyDiagrams.ConjEmbedding.toHom b t : G) : ↥U) : Equiv.Perm Nat) =
        Equiv.swap 4 5) ∧
    ¬ Nonempty (MackeyDiagrams.Dot a b) ∧
    ∃ s : Finset G, (s : Set G) = orbit ∧
      let B := MonoidAlgebra Complex G
      let orbitSum : B := Finset.sum s (fun g => MonoidAlgebra.single g (1 : Complex))
      ∃ d : MackeyDiagrams.Diagram Complex (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b),
        let f := MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval d)
        f ≠ 0 ∧ ∀ x : B, f (MonoidAlgebra.coeff x) = MonoidAlgebra.coeff (x * orbitSum)
) :=
(by
  open BlockSwapOrbitSumSupport MackeyDiagrams in
  intro B₁ B₂ B₃ B₄ X Y U blockSym H G swap α β
  classical
  -- Xiao, Example 3.3 and Proposition 3.3 in § 3.4, archived p. 10.
  -- In the 28 November 2026 revision the example is on p. 13 and the
  -- proposition and its proof are on p. 12.
  -- These locators refer to separate PDFs. The revision has SHA-256
  -- 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61.
  -- The example has no numbered Alphabeta Math counterpart in the task context.
  -- Check the block images first so both conjugation embeddings have target G.
  let kα : Fin 4 → Fin 2 := ![0, 1, 0, 1]
  let kβ : Fin 4 → Fin 2 := ![0, 0, 1, 1]
  have hαMaps (i : Fin 4) : Set.MapsTo α.val (X i) (Y (kα i)) := by
    fin_cases i <;> intro x hx <;> simp [X, B₁, B₂, B₃, B₄] at hx <;>
      rcases hx with rfl | rfl | rfl <;>
      simp [Y, kα, B₁, B₂, B₃, B₄, α, swap, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have hβMaps (i : Fin 4) : Set.MapsTo β.val (X i) (Y (kβ i)) := by
    fin_cases i <;> intro x hx <;>
      simp [X, Y, kβ, B₁, B₂, B₃, B₄, β] at hx ⊢ <;> omega
  have hα : ∀ h : H, α * h.val * α⁻¹ ∈ G := conjugatesInto X Y α kα hαMaps
  have hβ : ∀ h : H, β * h.val * β⁻¹ ∈ G := conjugatesInto X Y β kβ hβMaps
  refine ⟨hα, hβ, ?_⟩
  intro a b orbit
  -- Every target factor preserves both blocks because the blocks are disjoint.
  have hY : Pairwise (fun j k => Disjoint (Y j) (Y k)) := by
    intro j k hjk
    rw [Set.disjoint_left]
    fin_cases j <;> fin_cases k <;>
      intro x hx hy <;> simp [Y, B₁, B₂, B₃, B₄] at hx hy <;> omega
  have hpres (g : G) (j : Fin 2) : Set.MapsTo g.val.val (Y j) (Y j) :=
    preservesBlocks Y hY j g.property
  let t₀ := swap 4 5 (by decide)
  have ht₀ : t₀ ∈ blockSym (X 1) := by
    apply swapInBlock (i := 4) (j := 5) rfl <;> simp [X, B₂]
  let t : H := ⟨t₀, Subgroup.mem_iSup_of_mem 1 ht₀⟩
  have ha : (a.toHom t).val.val = Equiv.swap 7 8 := by
    change α.val * Equiv.swap 4 5 * α.val⁻¹ = Equiv.swap 7 8
    rw [← Equiv.swap_apply_apply]
    rfl
  have hb : (b.toHom t).val.val = Equiv.swap 4 5 := by
    change (1 : Equiv.Perm Nat) * Equiv.swap 4 5 * 1⁻¹ = Equiv.swap 4 5
    simp
  refine ⟨hpres, ?_, ?_, ?_⟩
  · exact ⟨t, rfl, ha, hb⟩
  · -- Use the named transposition from the example directly. The blockwise
    -- criterion also applies to these disjoint nonempty families. The single
    -- intertwining equation here uses the already computed images of t.
    rintro ⟨d⟩
    have hp : d.element.val.val 4 ∈ Y 0 := hpres d.element 0 (by simp [Y, B₁, B₂])
    have hn₇ : d.element.val.val 4 ≠ 7 := by
      intro h
      rw [h] at hp
      simp [Y, B₁, B₂] at hp
    have hn₈ : d.element.val.val 4 ≠ 8 := by
      intro h
      rw [h] at hp
      simp [Y, B₁, B₂] at hp
    have heq := congrArg (fun g : G => g.val.val 4) (d.intertwines t)
    change (a.toHom t).val.val (d.element.val.val 4) =
      d.element.val.val ((b.toHom t).val.val 4) at heq
    rw [ha, hb, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hn₇ hn₈] at heq
    exact (by decide : (4 : Nat) ≠ 5) (d.element.val.val.injective heq)
  · -- Finiteness of the source supplies the reverse cup for the trivial
    -- subgroup in FiniteOrbitSumDiagram. Its scaled composite realizes the
    -- distinct orbit sum, using the basis comparison inherited from
    -- InductionBimoduleOrbitSumBasis. The supplier gives pointwise evaluation
    -- on the whole group algebra. Diagram.eval_ext is unnecessary here.
    let S : Set Nat := (Finset.range 13 : Set Nat)
    have hbound : H ≤ blockSym S := by
      refine iSup_le fun i => fixingSubgroup_antitone (↥U) Nat (Set.compl_subset_compl.mpr ?_)
      intro x hx
      fin_cases i <;> simp [X, B₁, B₂, B₃, B₄, S] at hx ⊢ <;> omega
    let _ : Finite H := finiteOfBound hbound (Finset.range 13).finite_toSet
    obtain ⟨s, hs, d, hd⟩ := orbitDiagram H G α β hα hβ (1 : G)
    refine ⟨s, hs, d, ?_, hd⟩
    have hmem : (1 : G) ∈ (s : Set G) := by
      rw [hs]
      exact ⟨1, by simp⟩
    -- The identity occurs once in the distinct orbit sum. Evaluating at the
    -- algebra unit and reading the identity coefficient gives 1.
    intro hz
    have hx := hd (1 : MonoidAlgebra Complex G)
    rw [hz, LinearMap.zero_apply, one_mul] at hx
    have hcoeff := congrArg (fun f : G →₀ Complex => f 1) hx
    rw [Finsupp.zero_apply, nonzeroAtIdentity s hmem] at hcoeff
    exact zero_ne_one hcoeff)

#print axioms BlockSwapOrbitSumWithoutGroupDot
