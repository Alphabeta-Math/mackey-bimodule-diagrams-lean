import MackeyDiagrams
import Proofs.CaseFiveLeftShapeEvaluation
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks

namespace SupportedLeftOrbitAux

open MackeyDiagrams

section Basis

variable {U : Type*} [Group U] {G A D F B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)

private abbrev word := (Word.up a).tensor ((Word.down b).tensor (.up d))
private abbrev point (g : G) (x : D) : (word a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis g (Generator.mixedPair b d x)

private theorem point_surjective (z : (word a b d).basis.carrier) :
    ∃ (g : G) (x : D), point a b d g x = z := by
  refine Quotient.inductionOn z fun ⟨g, y⟩ => ?_
  exact ⟨g, Generator.mixedProduct b d y, by rw [point, Generator.mixedPair_mixedProduct]; rfl⟩

private theorem point_eq (g' g : G) (x' x : D) :
    point a b d g' x' = point a b d g x ↔
      ∃ α : A, g' = g * a.toHom α ∧ x = b.toHom α * x' := by
  constructor
  · intro h
    obtain ⟨α, hg, hx⟩ := Quotient.exact h
    change 1 * g' * (a.toHom α)⁻¹ = g at hg
    have hx' := congrArg (Generator.mixedProduct b d) hx
    change (b.toHom α * x' * (1 : D)⁻¹) * (1 * 1 * (d.toHom 1)⁻¹) =
      Generator.mixedProduct b d (Generator.mixedPair b d x) at hx'
    exact ⟨α, mul_inv_eq_iff_eq_mul.mp (by simpa using hg), by simpa using hx'.symm⟩
  · rintro ⟨α, rfl, rfl⟩
    apply Quotient.sound
    refine ⟨α, ?_, ?_⟩
    · change 1 * (g * a.toHom α) * (a.toHom α)⁻¹ = g
      simp
    · change (Biset.restriction b).pair (Biset.induction d)
        (b.toHom α * x' * (1 : D)⁻¹) (1 * 1 * (d.toHom 1)⁻¹) = _
      simp [Generator.mixedPair]

private theorem act_point (q : G × F) (g : G) (x : D) :
    (word a b d).basis.act q (point a b d g x) =
      point a b d (q.1 * g) (x * (d.toHom q.2)⁻¹) := by
  change (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    (q.1 * g * (a.toHom 1)⁻¹)
    ((Biset.restriction b).pair (Biset.induction d)
      (b.toHom 1 * x * (1 : D)⁻¹) (1 * 1 * (d.toHom q.2)⁻¹)) = _
  simp only [map_one, inv_one, mul_one, one_mul, point]
  congr 1
  apply (Generator.mixedEquiv b d).injective
  change x * (d.toHom q.2)⁻¹ =
    Generator.mixedProduct b d (Generator.mixedPair b d (x * (d.toHom q.2)⁻¹))
  simp

private abbrev action {X : Biset G F} : MulAction (G × F) X.carrier where
  smul := X.act
  one_smul := X.one_act
  mul_smul := X.mul_act

private theorem projection_formula (g : G) (x : D) :
    letI := action (X := (word a b d).basis)
    (MulAction.stabilizer (G × F) (point a b d g x)).map (MonoidHom.snd G F) =
      ((MonoidHom.range b.toHom).map (MulAut.conj x⁻¹).toMonoidHom).comap d.toHom := by
  intro inst
  ext k
  change (∃ q : G × F, (word a b d).basis.act q (point a b d g x) = point a b d g x ∧
    q.2 = k) ↔ ∃ z : D, (∃ α : A, b.toHom α = z) ∧ x⁻¹ * z * (x⁻¹)⁻¹ = d.toHom k
  constructor
  · rintro ⟨⟨q, k'⟩, h, rfl⟩
    rw [act_point, point_eq] at h
    obtain ⟨α, _, h⟩ := h
    change x = b.toHom α * (x * (d.toHom k')⁻¹) at h
    refine ⟨b.toHom α, ⟨α, rfl⟩, ?_⟩
    have he : x * d.toHom k' = b.toHom α * x := by
      apply eq_mul_inv_iff_mul_eq.mp
      simpa only [mul_assoc] using h
    simpa only [inv_inv] using (show x⁻¹ * b.toHom α * x = d.toHom k' from calc
      _ = x⁻¹ * (b.toHom α * x) := mul_assoc _ _ _
      _ = _ := by rw [← he, inv_mul_cancel_left])
  · rintro ⟨_, ⟨α, rfl⟩, h⟩
    refine ⟨(g * a.toHom α * g⁻¹, k), ?_, rfl⟩
    rw [act_point, point_eq]
    refine ⟨α, by dsimp; group, ?_⟩
    change x = b.toHom α * (x * (d.toHom k)⁻¹)
    rw [← h]
    group

private noncomputable def ambientMap (u : ConjEmbedding G B) (v : ConjEmbedding D B)
    (r : Dot (u.comp a) (v.comp b)) (t : B) : (word a b d).basis.carrier → B :=
  Quotient.lift
    (fun p : G × ((Word.down b).tensor (.up d)).basis.carrier =>
      u.toHom p.1 * r.element * v.toHom (Generator.mixedProduct b d p.2) * t)
    (by
      intro p p' h
      let x := Generator.mixedProduct b d p.2
      let x' := Generator.mixedProduct b d p'.2
      have hp : point a b d p.1 x = point a b d p'.1 x' := by
        simpa only [point, x, x', Generator.mixedPair_mixedProduct] using
          (Quotient.sound h : (⟦p⟧ : (word a b d).basis.carrier) = ⟦p'⟧)
      obtain ⟨α, hg, hx⟩ := (point_eq a b d p.1 p'.1 x x').mp hp
      change u.toHom p.1 * r.element * v.toHom x * t =
        u.toHom p'.1 * r.element * v.toHom x' * t
      have hr := r.intertwines α
      change u.toHom (a.toHom α) * r.element = r.element * v.toHom (b.toHom α) at hr
      simp only [hg, hx, map_mul, mul_assoc]
      rw [← mul_assoc (u.toHom (a.toHom α)) r.element, hr, mul_assoc])

private theorem ambientMap_point (u : ConjEmbedding G B) (v : ConjEmbedding D B)
    (r : Dot (u.comp a) (v.comp b)) (t : B) (g : G) (x : D) :
    ambientMap a b d u v r t (point a b d g x) =
      u.toHom g * r.element * v.toHom x * t := by
  change u.toHom g * r.element * v.toHom (Generator.mixedProduct b d (Generator.mixedPair b d x)) * t = _
  rw [Generator.mixedProduct_mixedPair]

private theorem ambientMap_act (u : ConjEmbedding G B) (v : ConjEmbedding D B)
    (r : Dot (u.comp a) (v.comp b)) (t : B) (right : F →* B)
    (ht : ∀ k, v.toHom (d.toHom k) * t = t * right k)
    (q : G × F) (p : (word a b d).basis.carrier) :
    ambientMap a b d u v r t ((word a b d).basis.act q p) =
      u.toHom q.1 * ambientMap a b d u v r t p * (right q.2)⁻¹ := by
  obtain ⟨g, x, rfl⟩ := point_surjective a b d p
  rw [act_point, ambientMap_point, ambientMap_point]
  simp only [map_mul, map_inv]
  have hk : (v.toHom (d.toHom q.2))⁻¹ * t = t * (right q.2)⁻¹ := by
    calc
      _ = (v.toHom (d.toHom q.2))⁻¹ *
          (v.toHom (d.toHom q.2) * t) * (right q.2)⁻¹ := by group
      _ = _ := by rw [ht]; group
  conv_lhs =>
    rw [mul_assoc (u.toHom q.1 * u.toHom g * r.element), mul_assoc (v.toHom x), hk]
  group

end Basis

end SupportedLeftOrbitAux

