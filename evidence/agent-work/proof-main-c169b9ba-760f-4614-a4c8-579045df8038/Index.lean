import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention
import Proofs.MixedCrossingFiberMaps
namespace EvaluationForTwoProjectionsAux

open MackeyDiagrams

universe u
noncomputable section
set_option maxHeartbeats 2500000

section Index
variable {U : Type u} [Group U] {K H P L : Subgroup U}
variable (a : ConjEmbedding K P) (b : ConjEmbedding H P)
variable (d : ConjEmbedding L K) (e : ConjEmbedding L H)
variable (p : Dot (a.comp d) (b.comp e))

private abbrev intersection :=
  a.toHom.range ⊓ Subgroup.map (MulAut.conj p.element).toMonoidHom b.toHom.range

private abbrev q := Generator.mixedMultiplicationBasis a b d e p

private theorem lower_le : (a.comp d).toHom.range ≤ intersection a b d e p := by
  rintro _ ⟨l, rfl⟩
  refine ⟨⟨d.toHom l, rfl⟩, b.toHom (e.toHom l), ⟨e.toHom l, rfl⟩, ?_⟩
  change p.element * b.toHom (e.toHom l) * p.element⁻¹ = a.toHom (d.toHom l)
  have h := p.intertwines l
  change a.toHom (d.toHom l) * p.element = p.element * b.toHom (e.toHom l) at h
  rw [← h, mul_inv_cancel_right]

private abbrev HasIndexFormula : Prop :=
    ((∀ z, Set.Finite {w | q a b d e p w = z}) ↔
      ((a.comp d).toHom.range.subgroupOf (intersection a b d e p)).FiniteIndex) ∧
    (∀ z : P, z ∈ Set.range (Generator.mixedProduct a b ∘ q a b d e p) →
      (∀ z, Set.Finite {w | q a b d e p w = z}) →
      Nat.card {w // Generator.mixedProduct a b (q a b d e p w) = z} =
        (a.comp d).toHom.range.relIndex (intersection a b d e p))

private theorem embedding_eq_of_rep {A B : Subgroup U} (i : ConjEmbedding A B) (s : U)
    (hi : ∀ x : A, (i.toHom x : U) = s * (x : U) * s⁻¹) :
    i = ConjEmbedding.ofConjugator s (fun x => hi x ▸ (i.toHom x).property) :=
  ConjEmbedding.ext (MonoidHom.ext (fun x => Subtype.ext (hi x)))

-- Lemma 6.3, equation (6.1). Proposition 5.1 is supplied for representative
-- conjugators. As in the registered finite-fiber convention, choose the
-- inner-left representative to realize the actual typed dot and use the
-- quotient's representative section. Then transport the relative index back
-- along the injective inclusion of the outer group.
private theorem index_formula : HasIndexFormula a b d e p := by
  classical
  obtain ⟨α, hα⟩ := a.hasRepresentative
  obtain ⟨β, hβ⟩ := b.hasRepresentative
  obtain ⟨ε, hε⟩ := e.hasRepresentative
  let δ : U := α⁻¹ * (p.element : U) * (β * ε)
  have hδ (l : L) : (d.toHom l : U) = δ * (l : U) * δ⁻¹ := by
    have h := congrArg (fun x : P => (x : U)) (p.intertwines l)
    change (a.toHom (d.toHom l) : U) * (p.element : U) =
      (p.element : U) * (b.toHom (e.toHom l) : U) at h
    rw [hα, hβ, hε] at h
    calc
      (d.toHom l : U) =
          α⁻¹ * ((α * (d.toHom l : U) * α⁻¹) * (p.element : U)) *
            (p.element : U)⁻¹ * α := by group
      _ = α⁻¹ * ((p.element : U) * (β * (ε * (l : U) * ε⁻¹) * β⁻¹)) *
            (p.element : U)⁻¹ * α := by rw [h]
      _ = δ * (l : U) * δ⁻¹ := by dsimp [δ]; group
  have hquot : (α * δ) * (β * ε)⁻¹ = (p.element : U) := by dsimp [δ]; group
  have ha (k : K) : α * (k : U) * α⁻¹ ∈ P := hα k ▸ (a.toHom k).property
  have hb (h : H) : β * (h : U) * β⁻¹ ∈ P := hβ h ▸ (b.toHom h).property
  have hd (l : L) : δ * (l : U) * δ⁻¹ ∈ K := hδ l ▸ (d.toHom l).property
  have he (l : L) : ε * (l : U) * ε⁻¹ ∈ H := hε l ▸ (e.toHom l).property
  have hp : (α * δ) * (β * ε)⁻¹ ∈ P := hquot ▸ p.element.property
  let a' := ConjEmbedding.ofConjugator α ha
  let b' := ConjEmbedding.ofConjugator β hb
  let d' := ConjEmbedding.ofConjugator δ hd
  let e' := ConjEmbedding.ofConjugator ε he
  let p' : Dot (a'.comp d') (b'.comp e') :=
    Dot.ofRepresentatives (α * δ) (β * ε)
      (by intro x; change α * (δ * (x : U) * δ⁻¹) * α⁻¹ = _; group)
      (by intro x; change β * (ε * (x : U) * ε⁻¹) * β⁻¹ = _; group) hp
  have move
      (a₁ : ConjEmbedding K P) (b₁ : ConjEmbedding H P) (d₁ : ConjEmbedding L K)
      (e₁ : ConjEmbedding L H) (p₁ : Dot (a₁.comp d₁) (b₁.comp e₁))
      (ha₁ : a = a₁) (hb₁ : b = b₁) (hd₁ : d = d₁) (he₁ : e = e₁)
      (hp₁ : (p₁.element : U) = (p.element : U))
      (result : HasIndexFormula a₁ b₁ d₁ e₁ p₁) : HasIndexFormula a b d e p := by
    cases ha₁
    cases hb₁
    cases hd₁
    cases he₁
    have hh : p₁ = p := Dot.ext (Subtype.ext hp₁)
    subst p₁
    exact result
  refine move a' b' d' e' p' (embedding_eq_of_rep a α hα) (embedding_eq_of_rep b β hβ)
    (embedding_eq_of_rep d δ hδ) (embedding_eq_of_rep e ε hε) hquot ?_
  let lower := (a'.comp d').toHom.range
  let upper := intersection a' b' d' e' p'
  let lowerU := Subgroup.map (MulAut.conj (α * δ)).toMonoidHom L
  let upperU := Subgroup.map (MulAut.conj α).toMonoidHom K ⊓
    Subgroup.map (MulAut.conj ((p'.element : U) * β)).toMonoidHom H
  have hlo : lower.map P.subtype = lowerU := by
    rw [MonoidHom.map_range]
    ext x
    change (∃ l : L, α * (δ * (l : U) * δ⁻¹) * α⁻¹ = x) ↔
      ∃ y ∈ L, (α * δ) * y * (α * δ)⁻¹ = x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, l.property, by group⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, by group⟩
  have hup : upper.map P.subtype = upperU := by
    rw [show upper = a'.toHom.range ⊓ Subgroup.map (MulAut.conj p'.element).toMonoidHom
      b'.toHom.range from rfl, Subgroup.map_inf _ _ _ Subtype.val_injective,
      MonoidHom.map_range, Subgroup.map_map, MonoidHom.map_range]
    congr 1
    · ext x
      change (∃ k : K, α * (k : U) * α⁻¹ = x) ↔ ∃ y ∈ K, α * y * α⁻¹ = x
      exact ⟨fun ⟨k, hk⟩ => ⟨k, k.property, hk⟩, fun ⟨k, hk, hx⟩ => ⟨⟨k, hk⟩, hx⟩⟩
    · ext x
      change (∃ h : H, (p'.element : U) * (β * (h : U) * β⁻¹) * (p'.element : U)⁻¹ = x) ↔
        ∃ y ∈ H, ((p'.element : U) * β) * y * ((p'.element : U) * β)⁻¹ = x
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨h, h.property, by group⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨⟨h, hh⟩, by group⟩
  have hi := Subgroup.relIndex_map_map_of_injective lower upper
    (f := P.subtype) Subtype.val_injective
  rw [hlo, hup] at hi
  have hfi : lowerU.IsFiniteRelIndex upperU ↔ (lower.subgroupOf upper).FiniteIndex := by
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Subgroup.finiteIndex_iff, hi]
    rfl
  have supplier := MixedCrossingFiberMaps K H P L α β δ ε ha hb hd he hp
    (fun j => j.out) DoubleCoset.out_eq'
  obtain ⟨_, _, _, hrange, hcard, hfinite, _⟩ := supplier
  refine ⟨hfinite.trans hfi, ?_⟩
  intro z hz hf
  have hc := hcard z (hrange ▸ hz) (hfinite.mp hf)
  exact hc.trans hi

end Index
end
end EvaluationForTwoProjectionsAux
