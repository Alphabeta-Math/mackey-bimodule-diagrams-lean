import MackeyDiagrams
import Proofs.InductionBimoduleOrbitSumBasis
import Proofs.BlockwiseGroupElementDotCriterion
import Proofs.FiniteOrbitSumDiagram
namespace BlockSwapOrbitSumSupport

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
    rw [show (p.val.symm : Nat → Nat) x = (p.val⁻¹ : Equiv.Perm Nat) x from rfl,
      fixesOutside hq hout]
    exact p.val.apply_symm_apply x
  exact hle h.property

private theorem finiteOfBound {H : Subgroup ↥U} {S : Set Nat}
    (hle : H ≤ block S) (hS : S.Finite) : Finite H := by
  let _ : Finite S := hS
  let restrict : H → S → S := fun p x => ⟨p.val.val x, mapsBlock (hle p.property) x.property⟩
  refine Finite.of_injective restrict (fun p q h => ?_)
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ S
  · exact congrArg (fun f : S → S => (f ⟨x, hx⟩ : Nat)) h
  · exact (fixesOutside (hle p.property) hx).trans (fixesOutside (hle q.property) hx).symm

private theorem swapInBlock {B : Set Nat} {i j : Nat} {p : ↥U}
    (hp : p.val = Equiv.swap i j) (hi : i ∈ B) (hj : j ∈ B) : p ∈ block B := by
  apply (mem_fixingSubgroup_iff _).mpr
  intro x hx
  change p.val x = x
  rw [hp]
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h.symm ▸ hi)) (fun h => hx (h.symm ▸ hj))

end BlockSwapOrbitSumSupport

namespace BlockSwapOrbitSumSupport

open MackeyDiagrams

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
  have hfinite : orbit.Finite := Set.finite_range _
  let i := ⟨hfinite.toFinset, ⟨g, hfinite.coe_toFinset⟩⟩
  have hscaled := (hdiagram g).2.2
  refine ⟨hfinite.toFinset, hfinite.coe_toFinset, _, fun x => (hscaled x).trans ?_⟩
  exact congrArg MonoidAlgebra.coeff (hbasis i x)

private theorem nonzeroAtIdentity {G : Type*} [Group G] (s : Finset G) (hs : 1 ∈ s) :
    (∑ z ∈ s, MonoidAlgebra.single z (1 : Complex)).coeff 1 = 1 := by
  classical
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  simp [MonoidAlgebra.coeff_single_apply, hs, eq_comm]

end BlockSwapOrbitSumSupport
