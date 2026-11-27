import MackeyDiagrams
import Proofs.ThreeInductionCrossingMultipliers
import Proofs.ThreeInductionReidemeisterThree
namespace AlternativeThreeInductionProof

open MackeyDiagrams

variable {U : Type*} [Group U] {H K L : Subgroup U}

private abbrev Represents (a : ConjEmbedding H K) (s : U) : Prop :=
  ∀ h : H, (a.toHom h : U) = s * (h : U) * s⁻¹

private theorem repEq {a b : ConjEmbedding H K} {s : U}
    (ha : Represents a s) (hb : Represents b s) : a = b :=
  ConjEmbedding.ext (MonoidHom.ext fun h => Subtype.ext ((ha h).trans (hb h).symm))

private theorem repComp {a : ConjEmbedding K L} {b : ConjEmbedding H K} {s t : U}
    (ha : Represents a s) (hb : Represents b t) : Represents (a.comp b) (s * t) := by
  intro h
  rw [ConjEmbedding.comp_apply, ha, hb]
  group

private theorem asConjugator (a : ConjEmbedding H K) :
    ∃ s : U, ∃ hs : ∀ h : H, s * (h : U) * s⁻¹ ∈ K,
      a = ConjEmbedding.ofConjugator s hs := by
  obtain ⟨s, hs⟩ := a.hasRepresentative
  exact ⟨s, fun h => hs h ▸ (a.toHom h).property,
    repEq hs (fun _ => rfl)⟩

private theorem repDotLeft {a b : ConjEmbedding H K} (d : Dot a b) {s : U}
    (hb : Represents b s) : Represents a ((d.element : U) * s) := by
  intro h
  have he := congrArg (fun k : K => (k : U)) (d.intertwines h)
  simp only [Subgroup.coe_mul, hb h] at he
  calc
    (a.toHom h : U) = ((a.toHom h : U) * (d.element : U)) * (d.element : U)⁻¹ := by group
    _ = ((d.element : U) * s) * (h : U) * ((d.element : U) * s)⁻¹ := by rw [he]; group

private theorem repDotRight {a b : ConjEmbedding H K} (d : Dot a b) {s : U}
    (ha : Represents a s) : Represents b ((d.element : U)⁻¹ * s) :=
  repDotLeft d.inverse ha

private theorem repFactorRight {a : ConjEmbedding K L} {b : ConjEmbedding H K} {s t : U}
    (ha : Represents a s) (hab : Represents (a.comp b) t) :
    Represents b (s⁻¹ * t) := by
  intro h
  have he := hab h
  rw [ConjEmbedding.comp_apply, ha] at he
  calc
    (b.toHom h : U) = s⁻¹ * (s * (b.toHom h : U) * s⁻¹) * s := by group
    _ = (s⁻¹ * t) * (h : U) * (s⁻¹ * t)⁻¹ := by rw [he]; group

private def restrictTarget (a : ConjEmbedding H K) (L : Subgroup U)
    (ha : ∀ h : H, (a.toHom h : U) ∈ L) : ConjEmbedding H L where
  toHom :=
    { toFun := fun h => ⟨a.toHom h, ha h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' x y := Subtype.ext (by simp) }
  hasRepresentative := a.hasRepresentative

private theorem idDotOfEq {a b : ConjEmbedding H K} (h : a = b) :
    ∃ d : Dot a b, d.element = 1 := by
  subst b
  exact ⟨Dot.id a, rfl⟩

private theorem liftSupported {B G F : Subgroup U} (hBG : B ≤ G)
    {a b : ConjEmbedding F B} (m : MonoidAlgebra Complex G)
    (hB : ∀ p ∈ m.coeff.support, (p : U) ∈ B)
    (hDot : ∀ p ∈ m.coeff.support, ∀ f : F,
      (a.toHom f : U) * (p : U) = (p : U) * (b.toHom f : U)) :
    ∃ x : DotLabel Complex a b,
      MonoidAlgebra.mapDomainAlgHom Complex Complex (Subgroup.inclusion hBG)
        (MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element x)) = m := by
  classical
  let inc := Subgroup.inclusion hBG
  let key : Dot a b → G := fun d => inc d.element
  have injective : Function.Injective key :=
    fun _ _ heq => Dot.ext (Subtype.ext (congrArg Subtype.val heq))
  have hRange : ↑m.coeff.support ⊆ Set.range key := by
    intro p hp
    let bp : B := ⟨p, hB p hp⟩
    let d : Dot a b := ⟨bp, fun f => Subtype.ext (hDot p hp f)⟩
    exact ⟨d, Subtype.ext rfl⟩
  refine ⟨Finsupp.comapDomain key m.coeff injective.injOn, ?_⟩
  apply MonoidAlgebra.coeff_injective
  change Finsupp.mapDomain inc (Finsupp.mapDomain Dot.element _) = _
  rw [Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_comapDomain key injective m.coeff hRange

private theorem singletonValue {a b : ConjEmbedding H K} (d : Dot a b) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (Finsupp.single d (1 : Complex))) =
      MonoidAlgebra.single d.element 1 := by
  rw [Finsupp.mapDomain_single]
  rfl

private abbrev conjugate (s : U) (H : Subgroup U) : Subgroup U :=
  H.map (MulAut.conj s).toMonoidHom

private theorem mem_conjugate {s z : U} :
    z ∈ conjugate s H ↔ s⁻¹ * z * s ∈ H := by
  change (∃ x ∈ H, s * x * s⁻¹ = z) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hz
    exact ⟨_, hz, by group⟩

end AlternativeThreeInductionProof
