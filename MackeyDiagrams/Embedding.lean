import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Conjugation-labelled strands

Fix an ambient group. Strand labels are stored as homomorphisms together with
existence of a conjugating representative. Dots retain their group elements.
-/

namespace MackeyDiagrams

variable {U : Type*} [Group U]

structure ConjEmbedding (H G : Subgroup U) where
  toHom : H →* G
  hasRepresentative : ∃ a : U, ∀ h : H, (toHom h : U) = a * (h : U) * a⁻¹

namespace ConjEmbedding

variable {H G K : Subgroup U}

@[ext] theorem ext {a b : ConjEmbedding H G} (h : a.toHom = b.toHom) : a = b := by
  cases a
  cases b
  cases h
  rfl

def ofConjugator (a : U) (ha : ∀ h : H, a * (h : U) * a⁻¹ ∈ G) :
    ConjEmbedding H G where
  toHom :=
    { toFun := fun h => ⟨a * (h : U) * a⁻¹, ha h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro h k
        apply Subtype.ext
        change a * ((h : U) * (k : U)) * a⁻¹ =
          (a * (h : U) * a⁻¹) * (a * (k : U) * a⁻¹)
        group }
  hasRepresentative := ⟨a, fun _ => rfl⟩

@[simp] theorem ofConjugator_apply (a : U) (ha : ∀ h : H, a * (h : U) * a⁻¹ ∈ G)
    (h : H) : ((ofConjugator a ha).toHom h : U) = a * (h : U) * a⁻¹ := rfl

/-- Two conjugators label the same strand exactly when their left cosets agree. -/
theorem ofConjugator_eq_iff (a b : U)
    (ha : ∀ h : H, a * (h : U) * a⁻¹ ∈ G)
    (hb : ∀ h : H, b * (h : U) * b⁻¹ ∈ G) :
    ofConjugator a ha = ofConjugator b hb ↔
      a⁻¹ * b ∈ Subgroup.centralizer (H : Set U) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro heq h hh
    have hconj : a * h * a⁻¹ = b * h * b⁻¹ :=
      congrArg (fun e : ConjEmbedding H G => (e.toHom ⟨h, hh⟩ : U)) heq
    calc
      h * (a⁻¹ * b) = a⁻¹ * (a * h * a⁻¹) * b := by group
      _ = a⁻¹ * (b * h * b⁻¹) * b := by rw [hconj]
      _ = (a⁻¹ * b) * h := by group
  · intro hcomm
    apply ext
    apply MonoidHom.ext
    intro h
    apply Subtype.ext
    change a * (h : U) * a⁻¹ = b * (h : U) * b⁻¹
    calc
      a * (h : U) * a⁻¹ = a * ((h : U) * (a⁻¹ * b)) * b⁻¹ := by group
      _ = a * ((a⁻¹ * b) * (h : U)) * b⁻¹ := by rw [hcomm _ h.property]
      _ = b * (h : U) * b⁻¹ := by group

def id (H : Subgroup U) : ConjEmbedding H H where
  toHom := MonoidHom.id H
  hasRepresentative := ⟨1, fun _ => by simp⟩

def comp (b : ConjEmbedding G K) (a : ConjEmbedding H G) : ConjEmbedding H K where
  toHom := b.toHom.comp a.toHom
  hasRepresentative := by
    obtain ⟨x, hx⟩ := a.hasRepresentative
    obtain ⟨y, hy⟩ := b.hasRepresentative
    refine ⟨y * x, fun h => ?_⟩
    change (b.toHom (a.toHom h) : U) = _
    rw [hy, hx]
    group

@[simp] theorem comp_apply (b : ConjEmbedding G K) (a : ConjEmbedding H G) (h : H) :
    (b.comp a).toHom h = b.toHom (a.toHom h) := rfl

theorem injective (a : ConjEmbedding H G) : Function.Injective a.toHom := by
  obtain ⟨x, hx⟩ := a.hasRepresentative
  intro h k heq
  apply Subtype.ext
  have hconj : x * (h : U) * x⁻¹ = x * (k : U) * x⁻¹ := by
    rw [← hx h, ← hx k, heq]
  calc
    (h : U) = x⁻¹ * (x * (h : U) * x⁻¹) * x := by group
    _ = x⁻¹ * (x * (k : U) * x⁻¹) * x := by rw [hconj]
    _ = (k : U) := by group

end ConjEmbedding

end MackeyDiagrams

