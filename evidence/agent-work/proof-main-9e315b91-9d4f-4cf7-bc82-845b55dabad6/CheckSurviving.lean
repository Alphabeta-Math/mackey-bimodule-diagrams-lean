import Mathlib.GroupTheory.DoubleCoset
import MackeyDiagrams
import Proofs.ConjugationEmbeddingCentralizerCoset

set_option maxHeartbeats 2000000

theorem SurvivingCosetRepresentative : (∀ {U : Type*} [Group U] (K H G : Subgroup U) (α β : U),
  let Kα := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K
  let Hβ := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj β)) H
  Kα ≤ G → Hβ ≤ G →
  let A := Subgroup.comap (Subgroup.subtype G) Kα
  let B := Subgroup.comap (Subgroup.subtype G) Hβ
  let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
  ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
    let L := fun j : J =>
      Kα ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H
    let C := fun j : J =>
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (β⁻¹ * (σ j : U)⁻¹))) (L j)
    ∀ (I : J → Type*) (hRep : ∀ j : J, I j → H)
      (_ : ∀ (j : J) (h : H), ∃! u : I j, (h : U) * (hRep j u : U)⁻¹ ∈ C j)
      (j : J) (g : G),
      let surviving : Set (I j) :=
        {u | α⁻¹ * (g : U) * β * (hRep j u : U)⁻¹ * β⁻¹ * (σ j : U)⁻¹ * α ∈ K}
      (DoubleCoset.mk A B g = j → ∃! u : I j, u ∈ surviving) ∧
        (DoubleCoset.mk A B g ≠ j → surviving = ∅)) :=
(by
  intro U _ K H G α β Kα Hβ hK hH A B J σ hσ L C I hRep hTrans j g surviving
  let s : U := (σ j : U)

  /- Ian Xiao, Lemma 2.3 (project PDF p. 6, published PDF p. 7).
     The article page gives the same proof and numbers the data in (2.1),
     (2.2), and (2.4). It has no separately numbered proof steps.
     ConjugationEmbeddingCentralizerCoset characterizes equality of strand
     labels. The membership calculations here use the given subgroup images. -/
  have mem_conjugate (S : Subgroup U) (a x : U) :
      x ∈ S.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ S := by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

  -- For (2.1), DoubleCoset.eq gives the product in G. The hypothesis hσ
  -- supplies the representative, so no choice of Quotient.out is needed.
  have factor :
      DoubleCoset.mk A B g = j ↔
        ∃ k ∈ Kα, ∃ h : H, (g : U) = k * s * (β * (h : U) * β⁻¹) := by
    rw [← hσ j, eq_comm (a := DoubleCoset.mk A B g), DoubleCoset.eq]
    constructor
    · rintro ⟨a, ha, b, hb, hg⟩
      change (a : U) ∈ Kα at ha
      change (b : U) ∈ Hβ at hb
      obtain ⟨h, hh, eh⟩ := Subgroup.mem_map.mp hb
      change β * h * β⁻¹ = (b : U) at eh
      refine ⟨(a : U), ha, ⟨h, hh⟩, ?_⟩
      change (g : U) = (a : U) * s * (β * h * β⁻¹)
      rw [eh]
      exact congrArg Subtype.val hg
    · rintro ⟨k, hk, h, hg⟩
      have hb : β * (h : U) * β⁻¹ ∈ Hβ := ⟨h, h.property, rfl⟩
      exact ⟨⟨k, hK hk⟩, hk, ⟨_, hH hb⟩, hb, Subtype.ext hg⟩

  have surviving_iff (u : I j) :
      u ∈ surviving ↔ (g : U) * β * (hRep j u : U)⁻¹ * β⁻¹ * s⁻¹ ∈ Kα := by
    let x : U := (g : U) * β * (hRep j u : U)⁻¹ * β⁻¹ * s⁻¹
    change α⁻¹ * (g : U) * β * (hRep j u : U)⁻¹ * β⁻¹ * s⁻¹ * α ∈ K ↔
      x ∈ K.map (MulAut.conj α).toMonoidHom
    rw [mem_conjugate]
    have he : α⁻¹ * x * α =
        α⁻¹ * (g : U) * β * (hRep j u : U)⁻¹ * β⁻¹ * s⁻¹ * α := by
      dsimp only [x]
      group
    rw [he]

  -- The conjugated term already belongs to the H side of (2.2).
  have transversal_iff (h : H) (u : I j) :
      (h : U) * (hRep j u : U)⁻¹ ∈ C j ↔
        (s * β) * ((h : U) * (hRep j u : U)⁻¹) * (s * β)⁻¹ ∈ Kα := by
    let x : U := (h : U) * (hRep j u : U)⁻¹
    let y : U := (s * β) * x * (s * β)⁻¹
    change x ∈ (L j).map (MulAut.conj (β⁻¹ * s⁻¹)).toMonoidHom ↔ y ∈ Kα
    rw [mem_conjugate, show (β⁻¹ * s⁻¹)⁻¹ * x * (β⁻¹ * s⁻¹) = y by
      dsimp only [y]
      group]
    change (y ∈ Kα ∧ y ∈ H.map (MulAut.conj (s * β)).toMonoidHom) ↔ y ∈ Kα
    have hx : x ∈ H := H.mul_mem h.property (H.inv_mem (hRep j u).property)
    have hy : y ∈ H.map (MulAut.conj (s * β)).toMonoidHom := ⟨x, hx, rfl⟩
    simp only [hy, and_true]

  constructor
  · intro hg
    obtain ⟨k, hk, h, hg⟩ := factor.mp hg
    -- Cancel the left factor inside Kα, then use the unique index in (2.4).
    have tests_agree (u : I j) :
        u ∈ surviving ↔ (h : U) * (hRep j u : U)⁻¹ ∈ C j := by
      rw [surviving_iff, transversal_iff, hg]
      let y : U := (s * β) * ((h : U) * (hRep j u : U)⁻¹) * (s * β)⁻¹
      have he : k * s * (β * (h : U) * β⁻¹) * β * (hRep j u : U)⁻¹ *
          β⁻¹ * s⁻¹ = k * y := by
        dsimp only [y]
        group
      rw [he]
      change k * y ∈ Kα ↔ y ∈ Kα
      refine ⟨?_, Kα.mul_mem hk⟩
      intro hky
      simpa only [inv_mul_cancel_left] using Kα.mul_mem (Kα.inv_mem hk) hky
    obtain ⟨u, hu, unique⟩ := hTrans j h
    exact ⟨u, (tests_agree u).mpr hu, fun v hv => unique v ((tests_agree v).mp hv)⟩
  · intro hne
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    -- A surviving index yields a factorization in (2.1).
    exact hne (factor.mpr ⟨_, (surviving_iff u).mp hu, hRep j u, by group⟩))

#print axioms SurvivingCosetRepresentative

#check DoubleCoset.Quotient
#check DoubleCoset.eq
#check DoubleCoset.out_eq'
#check ConjugationEmbeddingCentralizerCoset
#check MackeyDiagrams.ConjEmbedding.ofConjugator_apply
#check MackeyDiagrams.ConjEmbedding.injective
