import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
namespace CaseTwoLeftProjectionConstructionAux

open MackeyDiagrams
universe u
noncomputable section

variable {U : Type u} [Group U]

private abbrev crossingIntersection {K H P : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P) (p : P) : Subgroup P :=
  a.toHom.range ⊓ Subgroup.map (MulAut.conj p).toMonoidHom b.toHom.range

private abbrev FiberSize {X Y : Type u} (q : X → Y) (n : Nat) :=
  ∀ z ∈ Set.range q, Nat.card {w : X // q w = z} = n

section FiberIndex

variable {K H P L : Subgroup U}
variable (a : ConjEmbedding K P) (b : ConjEmbedding H P)
  (d : ConjEmbedding L K) (e : ConjEmbedding L H)

-- Lemma 6.3 and (6.1). Insert identity embeddings to use the registered
-- calculation for a single crossing. mixedEquiv changes only its target
-- coordinates, so the fiber subtypes have the same cardinality.
private theorem crossingIndex (p : Dot (a.comp d) (b.comp e)) :
    (a.comp d).toHom.range ≤ crossingIntersection a b p.element ∧
      ((∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b d e p w = z}) ↔
        ((a.comp d).toHom.range.subgroupOf (crossingIntersection a b p.element)).FiniteIndex) := by
  have h := (EvaluationForTwoProjections a b (ConjEmbedding.id H) d (ConjEmbedding.id L) e).1 p
  exact ⟨h.1, h.2.1⟩

private theorem crossingFiberSize (p : ProjectionDot.Mixed a b d e) :
    FiberSize (Generator.mixedMultiplicationBasis a b d e p.dot)
      ((a.comp d).toHom.range.relIndex (crossingIntersection a b p.dot.element)) := by
  intro z hz
  have hinj := (Generator.mixedEquiv a b).injective
  have h := (EvaluationForTwoProjections a b (ConjEmbedding.id H) d (ConjEmbedding.id L) e).2.1 p
    (Generator.mixedProduct a b z) |>.2 (by obtain ⟨w, rfl⟩ := hz; exact ⟨w, rfl⟩)
  refine (Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))).trans h
  exact ⟨congrArg (Generator.mixedProduct a b), fun he => hinj he⟩

private theorem crossingCardBound (p : ProjectionDot.Mixed a b d e) (n : Nat)
    (h : (a.comp d).toHom.range.relIndex (crossingIntersection a b p.dot.element) ≤ n) :
    ∀ z, Nat.card {w // Generator.mixedMultiplicationBasis a b d e p.dot w = z} ≤ n := by
  intro z
  by_cases hz : z ∈ Set.range (Generator.mixedMultiplicationBasis a b d e p.dot)
  · rw [crossingFiberSize a b d e p z hz]
    exact h
  · have empty : IsEmpty {w // Generator.mixedMultiplicationBasis a b d e p.dot w = z} :=
      ⟨fun w => hz ⟨w.1, w.2⟩⟩
    exact (Nat.card_eq_zero.mpr (Or.inl empty)).le.trans (Nat.zero_le n)

end FiberIndex

private theorem rangeComp_le {K H P : Subgroup U} (a : ConjEmbedding H P)
    (b : ConjEmbedding K H) : (a.comp b).toHom.range ≤ a.toHom.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨b.toHom x, rfl⟩

private theorem compId (a : ConjEmbedding U₁ U₂) : a.comp (ConjEmbedding.id U₁) = a := by
  apply ConjEmbedding.ext
  exact MonoidHom.ext fun _ => rfl

private def unitDot {K H : Subgroup U} {a b : ConjEmbedding K H} (h : a = b) : Dot a b where
  element := 1
  intertwines x := by subst b; simp

section FullIntersection

variable {G A D F E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (de : ConjEmbedding E G) (f : ConjEmbedding E F)

private abbrev internalGroup (p : A) :=
  (Subgroup.comap a.toHom (crossingIntersection a b p)).map G.subtype

-- Theorem 6.4(2), full-intersection construction. B is a subgroup of the
-- ambient group in the drawing syntax, so transport the comap along G.subtype.
private theorem transportedEmbeddings (p : Dot (a.comp de) ((b.comp c).comp f)) :
    let B := internalGroup a b p.element
    ∃ (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B),
      (∀ v : B, (r.toHom v : U) = (v : U)) ∧
      (∀ v : B, b.toHom (s.toHom v) = p.element⁻¹ * a.toHom (r.toHom v) * p.element) ∧
      r.comp t = de ∧ s.comp t = c.comp f ∧
      (a.comp r).toHom.range = crossingIntersection a b p.element := by
  let I := crossingIntersection a b p.element
  let J := I.comap a.toHom
  let B := J.map G.subtype
  have hBG : B ≤ G := by
    rintro _ ⟨v, _, rfl⟩
    exact v.property
  let r : ConjEmbedding B G :=
    ⟨Subgroup.inclusion hBG, ⟨1, fun _ => by simp⟩⟩
  have hr (v : B) : a.toHom (r.toHom v) ∈ I := by
    obtain ⟨w, hw, hval⟩ := v.property
    have eq : r.toHom v = w := Subtype.ext hval.symm
    rw [eq]
    exact hw
  obtain ⟨α, hα⟩ := a.hasRepresentative
  obtain ⟨β, hβ⟩ := b.hasRepresentative
  let σ : U := β⁻¹ * (p.element : U)⁻¹ * α
  have candidate (v : B) :
      ∃ w : D, (w : U) = σ * (v : U) * σ⁻¹ ∧
        b.toHom w = p.element⁻¹ * a.toHom (r.toHom v) * p.element := by
    obtain ⟨y, ⟨w, rfl⟩, hy⟩ := (hr v).2
    change p.element * b.toHom w * p.element⁻¹ = a.toHom (r.toHom v) at hy
    have hw : b.toHom w = p.element⁻¹ * a.toHom (r.toHom v) * p.element := by rw [← hy]; group
    refine ⟨w, ?_, hw⟩
    have he := congrArg (fun x : A => (x : U)) hw
    change (b.toHom w : U) = (p.element : U)⁻¹ * (a.toHom (r.toHom v) : U) * (p.element : U) at he
    rw [hβ, hα] at he
    change β * (w : U) * β⁻¹ =
      (p.element : U)⁻¹ * (α * (v : U) * α⁻¹) * (p.element : U) at he
    calc
      (w : U) = β⁻¹ * (β * (w : U) * β⁻¹) * β := by group
      _ = σ * (v : U) * σ⁻¹ := by rw [he]; dsimp [σ]; group
  let s : ConjEmbedding B D := ConjEmbedding.ofConjugator σ (fun v => by
    obtain ⟨w, hw, _⟩ := candidate v
    exact hw ▸ w.property)
  have hs (v : B) : b.toHom (s.toHom v) = p.element⁻¹ * a.toHom (r.toHom v) * p.element := by
    obtain ⟨w, hw, he⟩ := candidate v
    have eq : s.toHom v = w := Subtype.ext hw.symm
    rw [eq, he]
  have hlo := (crossingIndex a (b.comp c) de f p).1
  have hI : crossingIntersection a (b.comp c) p.element ≤ I :=
    inf_le_inf_left _ (Subgroup.map_mono (rangeComp_le b c))
  have ht (v : E) : (de.toHom v : U) ∈ B :=
    ⟨de.toHom v, hI (hlo ⟨v, rfl⟩), rfl⟩
  let t : ConjEmbedding E B := ⟨(G.subtype.comp de.toHom).codRestrict B ht, de.hasRepresentative⟩
  have hrt : r.comp t = de := ConjEmbedding.ext (MonoidHom.ext fun _ => rfl)
  have hst : s.comp t = c.comp f := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro v
    apply b.injective
    change b.toHom (s.toHom (t.toHom v)) = b.toHom (c.toHom (f.toHom v))
    rw [hs]
    change p.element⁻¹ * a.toHom (de.toHom v) * p.element = _
    have hp := p.intertwines v
    change a.toHom (de.toHom v) * p.element = p.element * b.toHom (c.toHom (f.toHom v)) at hp
    rw [mul_assoc, hp, inv_mul_cancel_left]
  refine ⟨r, s, t, fun _ => rfl, hs, hrt, hst, ?_⟩
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact hr v
  · intro x hx
    obtain ⟨v, hv⟩ := hx.1
    refine ⟨⟨v, ⟨v, hv ▸ hx, rfl⟩⟩, hv⟩

private theorem transportedIndex (p : Dot (a.comp de) ((b.comp c).comp f))
    {B : Subgroup U} (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
    (hs : ∀ v : B, b.toHom (s.toHom v) = p.element⁻¹ * a.toHom (r.toHom v) * p.element)
    (hrt : r.comp t = de) (hI : (a.comp r).toHom.range = crossingIntersection a b p.element) :
    (s.comp t).toHom.range.relIndex (s.toHom.range ⊓ c.toHom.range) =
      (a.comp de).toHom.range.relIndex (crossingIntersection a (b.comp c) p.element) := by
  let φ : D →* A := (MulAut.conj p.element).toMonoidHom.comp b.toHom
  have hφ : Function.Injective φ := (MulAut.conj p.element).injective.comp b.injective
  have hrs (v : B) : φ (s.toHom v) = a.toHom (r.toHom v) := by
    change p.element * b.toHom (s.toHom v) * p.element⁻¹ = _
    rw [hs]
    group
  have hsMap : s.toHom.range.map φ = (a.comp r).toHom.range := by
    rw [← MonoidHom.range_comp]
    congr 1
    exact MonoidHom.ext hrs
  have htMap : (s.comp t).toHom.range.map φ = (a.comp de).toHom.range := by
    rw [← MonoidHom.range_comp, ← hrt]
    congr 1
    exact MonoidHom.ext fun v => hrs (t.toHom v)
  have hcMap : c.toHom.range.map φ =
      (b.comp c).toHom.range.map (MulAut.conj p.element).toMonoidHom := by
    rw [← Subgroup.map_map, ← MonoidHom.range_comp]
    rfl
  have hcLe := Subgroup.map_mono (f := (MulAut.conj p.element).toMonoidHom) (rangeComp_le b c)
  have upperMap : (s.toHom.range ⊓ c.toHom.range).map φ =
      crossingIntersection a (b.comp c) p.element := by
    rw [Subgroup.map_inf _ _ _ hφ, hsMap, hI, hcMap]
    change (_ ⊓ _) ⊓ _ = a.toHom.range ⊓ _
    rw [inf_assoc, inf_eq_right.mpr hcLe]
  rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, htMap, upperMap]

end FullIntersection

end
end CaseTwoLeftProjectionConstructionAux
