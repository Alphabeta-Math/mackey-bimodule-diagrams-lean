import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

theorem ParallelInductionProductDotAdmissibility : (∀ {U : Type*} [Group U] (G K H B H' : Subgroup U)
    (α β γ δ α' β' : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hβ : ∀ k : K, β * (k : U) * β⁻¹ ∈ H)
    (hγ : ∀ b : B, γ * (b : U) * γ⁻¹ ∈ G)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ B)
    (hα' : ∀ h : H', α' * (h : U) * (α')⁻¹ ∈ G)
    (hβ' : ∀ k : K, β' * (k : U) * (β')⁻¹ ∈ H'),
  let u := α * β
  let v := γ * δ
  let w := α' * β'
  let bottom := MackeyDiagrams.ConjEmbedding.comp
    (MackeyDiagrams.ConjEmbedding.ofConjugator α hα)
    (MackeyDiagrams.ConjEmbedding.ofConjugator β hβ)
  let middle := MackeyDiagrams.ConjEmbedding.comp
    (MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ)
    (MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ)
  let top := MackeyDiagrams.ConjEmbedding.comp
    (MackeyDiagrams.ConjEmbedding.ofConjugator α' hα')
    (MackeyDiagrams.ConjEmbedding.ofConjugator β' hβ')
  let C := Subgroup.centralizer (K : Set U)
  (∀ (d : MackeyDiagrams.Dot bottom middle) (e : MackeyDiagrams.Dot middle top),
    let de := MackeyDiagrams.Dot.element d * MackeyDiagrams.Dot.element e
    (∃ p : MackeyDiagrams.Dot bottom top, MackeyDiagrams.Dot.element p = de) ∧
    u⁻¹ * (de : U) * w ∈ C ∧
    (de = 1 → bottom = top)) ∧
  (∀ d : MackeyDiagrams.Dot bottom middle,
    ∃ r : MackeyDiagrams.Dot middle bottom,
      MackeyDiagrams.Dot.element r = (MackeyDiagrams.Dot.element d)⁻¹ ∧
      v⁻¹ * (MackeyDiagrams.Dot.element r : U) * u ∈ C ∧
      MackeyDiagrams.Dot.vertical d r = MackeyDiagrams.Dot.id bottom ∧
      MackeyDiagrams.Dot.vertical r d = MackeyDiagrams.Dot.id middle)) :=
(by
  intro U inst G K H B H' α β γ δ α' β' hα hβ hγ hδ hα' hβ'
    u v w bottom middle top C
  have composedRepresentative {L : Subgroup U} (a b : U)
      (ha : ∀ l : L, a * (l : U) * a⁻¹ ∈ G)
      (hb : ∀ k : K, b * (k : U) * b⁻¹ ∈ L) (k : K) :
      ((((MackeyDiagrams.ConjEmbedding.ofConjugator a ha).comp
        (MackeyDiagrams.ConjEmbedding.ofConjugator b hb)).toHom k : G) : U) =
        (a * b) * (k : U) * (a * b)⁻¹ := by
    simp only [MackeyDiagrams.ConjEmbedding.comp_apply,
      MackeyDiagrams.ConjEmbedding.ofConjugator_apply]
    group
  have centralizes {a b : MackeyDiagrams.ConjEmbedding K G} {p q : U}
      (ha : ∀ k : K, (a.toHom k : U) = p * (k : U) * p⁻¹)
      (hb : ∀ k : K, (b.toHom k : U) = q * (k : U) * q⁻¹)
      (d : MackeyDiagrams.Dot a b) :
      p⁻¹ * (d.element : U) * q ∈ C := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    have commute := congrArg (fun g : G => (g : U)) (d.intertwines ⟨k, hk⟩)
    change (a.toHom ⟨k, hk⟩ : U) * (d.element : U) =
      (d.element : U) * (b.toHom ⟨k, hk⟩ : U) at commute
    rw [ha, hb] at commute
    calc
      k * (p⁻¹ * (d.element : U) * q) =
          p⁻¹ * ((p * k * p⁻¹) * (d.element : U)) * q := by group
      _ = p⁻¹ * ((d.element : U) * (q * k * q⁻¹)) * q := by rw [commute]
      _ = (p⁻¹ * (d.element : U) * q) * k := by group
  constructor
  · intro d e
    let product := d.vertical e
    refine ⟨⟨product, rfl⟩,
      centralizes (composedRepresentative α β hα hβ)
        (composedRepresentative α' β' hα' hβ') product, ?_⟩
    intro unit
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro k
    have commute := product.intertwines k
    change bottom.toHom k * (d.element * e.element) =
      (d.element * e.element) * top.toHom k at commute
    simpa only [unit, mul_one, one_mul] using commute
  · intro d
    exact ⟨d.inverse, rfl, centralizes (composedRepresentative γ δ hγ hδ)
      (composedRepresentative α β hα hβ) d.inverse,
      MackeyDiagrams.Dot.then_inverse d, MackeyDiagrams.Dot.inverse_then d⟩)
