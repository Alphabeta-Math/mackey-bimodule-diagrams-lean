import MackeyDiagrams
import Proofs.CaseFiveLeftShapeEvaluation
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks

namespace SupportedLeftOrbitAux

open MackeyDiagrams

private abbrev finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (S : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
private abbrev ParabolicPerm (H : Subgroup (Equiv.Perm Nat)) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat), (∀ i, (blocks i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧ H = ⨆ i, blockSym (blocks i)
private abbrev Parabolic (H : Subgroup finitary) := ParabolicPerm (H.map finitary.subtype)

private theorem parabolic_of_family {ι : Type} [Finite ι] (blocks : ι → Finset Nat)
    (hne : ∀ i, (blocks i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) :
    ParabolicPerm (⨆ i, blockSym (blocks i)) := by
  letI := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  exact ⟨_, blocks ∘ e, fun i => hne (e i),
    fun i j hij => hdisj (fun h => hij (e.injective h)),
    (e.iSup_comp (g := fun i => blockSym (blocks i))).symm⟩

private theorem parabolic_conj {H : Subgroup (Equiv.Perm Nat)} (hH : ParabolicPerm H)
    (z : finitary) : ParabolicPerm (H.map (MulAut.conj (z : Equiv.Perm Nat)).toMonoidHom) := by
  classical
  obtain ⟨n, A, hA, hdisj, rfl⟩ := hH
  rw [FiniteParabolicConjugateBlocks A hA hdisj z]
  refine parabolic_of_family _ (fun i => (hA i).image _) ?_
  intro i j hij
  simpa only [Finset.map_eq_image] using
    (Finset.disjoint_map (z : Equiv.Perm Nat).toEmbedding).mpr (hdisj hij)

private theorem parabolic_inf_perm {H K : Subgroup (Equiv.Perm Nat)}
    (hH : ParabolicPerm H) (hK : ParabolicPerm K) : ParabolicPerm (H ⊓ K) := by
  classical
  obtain ⟨n, A, hA, hdA, rfl⟩ := hH
  obtain ⟨m, B, hB, hdB, rfl⟩ := hK
  let X := (Finset.univ.biUnion A) ∪ (Finset.univ.biUnion B)
  -- Prop. 7.1 uses two partitions of one finite set. Singleton padding
  -- adds trivial factors and supplies exactly the common-carrier hypotheses.
  have pad {ι : Type} [Fintype ι] (D : ι → Finset Nat)
      (hne : ∀ i, (D i).Nonempty)
      (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
      (hsub : Finset.univ.biUnion D ⊆ X) :
      let blocks : ι ⊕ ↥(X \ Finset.univ.biUnion D) → Finset Nat :=
        Sum.elim D (fun y => {y.val})
      (∀ i, (blocks i).Nonempty) ∧
        Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
        (∀ x, x ∈ X ↔ ∃ i, x ∈ blocks i) ∧
        (⨆ i, blockSym (blocks i)) = ⨆ i, blockSym (D i) := by
    intro blocks
    have memUnion (x : Nat) : x ∈ Finset.univ.biUnion D ↔ ∃ i, x ∈ D i := by
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (i | y)
      · exact hne i
      · exact Finset.singleton_nonempty _
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro x hx hy
      cases i with
      | inl i =>
        cases j with
        | inl j => exact Finset.disjoint_left.mp (hd (fun h => hij (congrArg Sum.inl h))) hx hy
        | inr y =>
          exact (Finset.mem_sdiff.mp y.property).2
            ((Finset.mem_singleton.mp hy) ▸ (memUnion x).mpr ⟨i, hx⟩)
      | inr y =>
        cases j with
        | inl j =>
          exact (Finset.mem_sdiff.mp y.property).2
            ((Finset.mem_singleton.mp hx) ▸ (memUnion x).mpr ⟨j, hy⟩)
        | inr w =>
          exact hij (congrArg Sum.inr (Subtype.ext
            ((Finset.mem_singleton.mp hx).symm.trans (Finset.mem_singleton.mp hy))))
    · intro x
      constructor
      · intro hx
        by_cases h : x ∈ Finset.univ.biUnion D
        · obtain ⟨i, hi⟩ := (memUnion x).mp h
          exact ⟨Sum.inl i, hi⟩
        · exact ⟨Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨hx, h⟩⟩, Finset.mem_singleton_self x⟩
      · rintro ⟨i | y, hx⟩
        · exact hsub ((memUnion x).mpr ⟨i, hx⟩)
        · exact (Finset.mem_singleton.mp hx).symm ▸ (Finset.mem_sdiff.mp y.property).1
    · rw [iSup_sum]
      change (⨆ i, blockSym (D i)) ⊔ (⨆ j : ↥(X \ Finset.univ.biUnion D), blockSym {j.val}) = _
      have singletonSym (x : Nat) : blockSym {x} = ⊥ := by
        refine le_antisymm ?_ bot_le
        rintro σ ⟨τ, rfl⟩
        have hτ : τ = 1 := by
          apply Equiv.ext
          intro y
          apply Subtype.ext
          exact (Finset.mem_singleton.mp (τ y).property).trans
            (Finset.mem_singleton.mp y.property).symm
        rw [hτ, map_one]
        exact Subgroup.one_mem _
      simp only [singletonSym, iSup_bot, sup_bot_eq]
  let A' : Fin n ⊕ ↥(X \ Finset.univ.biUnion A) → Finset Nat :=
    Sum.elim A (fun y => {y.val})
  let B' : Fin m ⊕ ↥(X \ Finset.univ.biUnion B) → Finset Nat :=
    Sum.elim B (fun y => {y.val})
  obtain ⟨ha, da, ca, ea⟩ := pad A hA hdA Finset.subset_union_left
  obtain ⟨hb, db, cb, eb⟩ := pad B hB hdB Finset.subset_union_right
  change (⨆ i, blockSym (A' i)) = _ at ea
  change (⨆ i, blockSym (B' i)) = _ at eb
  rw [← ea, ← eb, FiniteParabolicIntersectionBlocks X A' B' ha hb da db ca cb]
  let Cell := {ij : _ × _ // (A' ij.1 ∩ B' ij.2).Nonempty}
  let cell (ij : Cell) := A' ij.val.1 ∩ B' ij.val.2
  have omitEmpty : (⨆ i, ⨆ j, blockSym (A' i ∩ B' j)) = ⨆ ij, blockSym (cell ij) := by
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun j => ?_
      by_cases h : (A' i ∩ B' j).Nonempty
      · exact le_iSup (fun ij => blockSym (cell ij)) (⟨(i, j), h⟩ : Cell)
      · rintro σ ⟨τ, rfl⟩
        have hone : Equiv.Perm.ofSubtype τ = (1 : Equiv.Perm Nat) := by
          apply Equiv.ext
          intro x
          exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun hx => h ⟨x, hx⟩)
        rw [hone]
        exact Subgroup.one_mem _
    · refine iSup_le fun ij => ?_
      exact (le_iSup (fun j => blockSym (A' ij.val.1 ∩ B' j)) ij.val.2).trans
        (le_iSup (fun i => ⨆ j, blockSym (A' i ∩ B' j)) ij.val.1)
  rw [omitEmpty]
  refine parabolic_of_family cell (fun ij => ij.property) ?_
  intro ij kl hne
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
  obtain ⟨hk, hl⟩ := Finset.mem_inter.mp hy
  have hik : ij.val.1 = kl.val.1 := by
    by_contra h
    exact Finset.disjoint_left.mp (da h) hi hk
  have hjl : ij.val.2 = kl.val.2 := by
    by_contra h
    exact Finset.disjoint_left.mp (db h) hj hl
  exact hne (Subtype.ext (Prod.ext hik hjl))

private theorem parabolic_inf {H K : Subgroup finitary}
    (hH : Parabolic H) (hK : Parabolic K) : Parabolic (H ⊓ K) := by
  change ParabolicPerm ((H ⊓ K).map finitary.subtype)
  rw [Subgroup.map_inf _ _ _ finitary.subtype_injective]
  exact parabolic_inf_perm hH hK

private theorem projected_parabolic {A D F : Subgroup finitary} (hA : Parabolic A)
    (hF : Parabolic F) (b : ConjEmbedding A D) (d : ConjEmbedding F D) (x : D) :
    Parabolic (((MonoidHom.range b.toHom).map (MulAut.conj x⁻¹).toMonoidHom).comap
      d.toHom |>.map F.subtype) := by
  obtain ⟨β, hβ⟩ := b.hasRepresentative
  obtain ⟨δ, hδ⟩ := d.hasRepresentative
  let z : finitary := δ⁻¹ * (x : finitary)⁻¹ * β
  let projected := (((MonoidHom.range b.toHom).map (MulAut.conj x⁻¹).toMonoidHom).comap
    d.toHom).map F.subtype
  have hproj : projected.map finitary.subtype =
      F.map finitary.subtype ⊓ (A.map finitary.subtype).map
        (MulAut.conj (z : Equiv.Perm Nat)).toMonoidHom := by
    ext σ
    constructor
    · rintro ⟨_, ⟨k, ⟨_, ⟨α, rfl⟩, hk⟩, rfl⟩, rfl⟩
      refine ⟨⟨(k : finitary), k.property, rfl⟩, _, ⟨(α : finitary), α.property, rfl⟩, ?_⟩
      change ((z * (α : finitary) * z⁻¹ : finitary) : Equiv.Perm Nat) =
        ((k : finitary) : Equiv.Perm Nat)
      apply Subtype.val_injective.congr_arg
      have hk' := congrArg (fun y : D => (y : finitary)) hk
      change (x : finitary)⁻¹ * (b.toHom α : finitary) * ((x⁻¹ : D) : finitary)⁻¹ =
        (d.toHom k : finitary) at hk'
      rw [hβ, hδ] at hk'
      change (x : finitary)⁻¹ * (β * (α : finitary) * β⁻¹) *
        ((x : finitary)⁻¹)⁻¹ = δ * (k : finitary) * δ⁻¹ at hk'
      calc
        z * (α : finitary) * z⁻¹ =
            δ⁻¹ * ((x : finitary)⁻¹ * (β * (α : finitary) * β⁻¹) *
              ((x : finitary)⁻¹)⁻¹) * δ := by dsimp only [z]; group
        _ = k := by rw [hk']; group
    · rintro ⟨⟨k, hk, rfl⟩, _, ⟨α, hα, rfl⟩, h⟩
      change ((z * α * z⁻¹ : finitary) : Equiv.Perm Nat) = (k : Equiv.Perm Nat) at h
      have hz : z * α * z⁻¹ = k := Subtype.ext h
      refine ⟨k, ⟨⟨k, hk⟩, ⟨b.toHom ⟨α, hα⟩, ⟨⟨α, hα⟩, rfl⟩, ?_⟩, rfl⟩, rfl⟩
      apply Subtype.ext
      change (x : finitary)⁻¹ * (b.toHom ⟨α, hα⟩ : finitary) *
        ((x⁻¹ : D) : finitary)⁻¹ = (d.toHom ⟨k, hk⟩ : finitary)
      rw [hβ, hδ, ← hz]
      change (x : finitary)⁻¹ * (β * α * β⁻¹) * ((x : finitary)⁻¹)⁻¹ =
        δ * (z * α * z⁻¹) * δ⁻¹
      dsimp only [z]
      group
  show ParabolicPerm (projected.map finitary.subtype)
  rw [hproj]
  exact parabolic_inf_perm hF (parabolic_conj hA z)

private theorem parabolic_finite {H : Subgroup finitary} (hH : Parabolic H) : Finite H := by
  classical
  obtain ⟨n, A, _, _, hA⟩ := hH
  let X := Finset.univ.biUnion A
  have hsub : H.map finitary.subtype ≤ blockSym X := by
    rw [hA]
    refine iSup_le fun i σ hs => ?_
    have h := Equiv.Perm.mem_range_ofSubtype_iff.mp hs
    refine Equiv.Perm.mem_range_ofSubtype_iff.mpr fun x hx => ?_
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h hx⟩
  letI : Finite (blockSym X) :=
    (Set.finite_range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))).to_subtype
  exact Finite.of_injective
    (fun h : H => (⟨(h.val : Equiv.Perm Nat), hsub ⟨h.val, h.property, rfl⟩⟩ : blockSym X))
    (fun _ _ hh => Subtype.ext (Subtype.ext (congrArg Subtype.val hh)))

end SupportedLeftOrbitAux

