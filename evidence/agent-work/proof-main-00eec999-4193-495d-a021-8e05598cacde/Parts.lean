import Mathlib.GroupTheory.Perm.Finite
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
  let := Fintype.ofFinite ι
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
  have hmap (S : Finset Nat) : S.map (z : Equiv.Perm Nat).toEmbedding =
      S.image (z : Equiv.Perm Nat) := Finset.map_eq_image _ _
  rw [← hmap, ← hmap]
  exact (Finset.disjoint_map _).mpr (hdisj hij)

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
      apply congrArg (fun g : finitary => (g : Equiv.Perm Nat))
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
      rw [hβ, hδ]
      change (x : finitary)⁻¹ * (β * α * β⁻¹) * ((x : finitary)⁻¹)⁻¹ =
        δ * k * δ⁻¹
      rw [← hz]
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
  let : Finite (blockSym X) :=
    (Set.finite_range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))).to_subtype
  exact Finite.of_injective
    (fun h : H => (⟨(h.val : Equiv.Perm Nat), hsub ⟨h.val, h.property, rfl⟩⟩ : blockSym X))
    (fun _ _ hh => Subtype.ext (Subtype.ext (congrArg (fun y : blockSym X => y.val) hh)))

end SupportedLeftOrbitAux

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
        simp only [point, x, x', Generator.mixedPair_mixedProduct]
        obtain ⟨g, y⟩ := p
        obtain ⟨g', y'⟩ := p'
        exact Quotient.sound h
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
    simpa only [map_inv] using ht q.2⁻¹
  conv_lhs =>
    rw [mul_assoc (u.toHom q.1 * u.toHom g * r.element), mul_assoc (v.toHom x), hk]
  group

end Basis

end SupportedLeftOrbitAux

namespace SupportedLeftOrbitAux

open MackeyDiagrams

section Evaluation

variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (u : ConjEmbedding G B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
variable (r : Dot (u.comp a) (v.comp b)) (t : Dot (v.comp d) (w.comp f))
variable (s : Dot (u.comp c) (w.comp e))

private abbrev upBasis := ((Word.up c).tensor (.down e)).basis
private abbrev upperMap := Generator.mixedMultiplicationBasis u w c e s

private noncomputable abbrev leftInner
    (finite : ∀ z, Set.Finite {p | upperMap c e u w s p = z}) :
    LabelledDrawing Complex (((Word.up a).tensor (.down b)).tensor (.up d))
      (((Word.up c).tensor (.down e)).tensor (.up f)) :=
  .vertical
    (.horizontal (.mixedMultiplication u v a b [(1, r)]) (.ordinary (.id (.up d))))
    (.vertical (.ordinary (.associate (.down u) (.up v) (.up d)))
      (.vertical (.horizontal (.ordinary (.id (.down u))) (.parallelUp v d w f [(1, t)]))
        (.vertical (.ordinary (.unassociate (.down u) (.up w) (.up f)))
          (.horizontal (.compactProjection u w c e [(1, ⟨s, finite⟩)])
            (.ordinary (.id (.up f)))))))

private noncomputable abbrev leftDrawing
    (finite : ∀ z, Set.Finite {p | upperMap c e u w s p = z}) :
    LabelledDrawing Complex (word a b d) (word c e f) :=
  .vertical (.ordinary (.unassociate (.up a) (.down b) (.up d)))
    (.vertical (leftInner a b d c e f u v w r t s finite)
      (.ordinary (.associate (.up c) (.down e) (.up f))))

private noncomputable abbrev coefficient {K H : Subgroup U} {p q : Word K H}
    (drawing : LabelledDrawing Complex p q) (z : p.basis.carrier × q.basis.carrier) :=
  drawing.interpret.eval.toLinearMap (Finsupp.single z.1 1) z.2

private def appendUnit (p : (upBasis c e).carrier) : (word c e f).basis.carrier :=
  Biset.associateBasis (Biset.induction c) (Biset.restriction e) (Biset.induction f)
    ((upBasis c e).pair (Biset.induction f) p 1)

private theorem appendUnit_injective : Function.Injective (appendUnit c e f) := by
  intro p p' h
  have h' := (Biset.associateBasisEquiv (Biset.induction c) (Biset.restriction e)
    (Biset.induction f)).injective h
  obtain ⟨k, hp, hk⟩ := Quotient.exact h'
  change k * 1 * (f.toHom 1)⁻¹ = (1 : E) at hk
  have he : k = 1 := by simpa only [map_one, inv_one, mul_one] using hk
  change (upBasis c e).act (1, k) p = p' at hp
  rw [he, (upBasis c e).one_act] at hp
  exact hp

private theorem appendUnit_pair (p : (upBasis c e).carrier) :
    (Diagram.associate (R := Complex) (.up c) (.down e) (.up f)).eval.toLinearMap
      (Finsupp.single ((upBasis c e).pair (Biset.induction f) p 1) 1) =
    Finsupp.single (appendUnit c e f p) 1 := by
  change (Biset.associate (Biset.induction c) (Biset.restriction e) (Biset.induction f) Complex
    ).toLinearMap _ = _
  rw [Biset.associate, Biset.Hom.ofFunction_single]
  rfl

private theorem coefficient_on_points
    (finite : ∀ z, Set.Finite {p | upperMap c e u w s p = z})
    (g : G) (x : D) (h : G) (y : E) :
    coefficient (leftDrawing a b d c e f u v w r t s finite)
      (point a b d g x, point c e f h y) =
      (if u.toHom g * r.element * v.toHom x * t.element =
          u.toHom h * s.element * w.toHom y then 1 else 0) := by
  classical
  let L := Generator.mixedProduct u w ∘ upperMap c e u w s
  let z := u.toHom g * r.element * v.toHom x * t.element
  have fibers (q : B) : Set.Finite {p | L p = q} := by
    refine (finite (Generator.mixedPair u w q)).subset ?_
    intro p hp
    change Generator.mixedProduct u w (upperMap c e u w s p) = q at hp
    rw [← hp, Generator.mixedPair_mixedProduct]
  let p₀ := (Biset.induction c).pair (Biset.restriction e) h y
  have hp₀ : L p₀ = u.toHom h * s.element * w.toHom y :=
    Generator.mixedProduct_mixedPair u w _
  let inLeft := ((Word.up a).tensor (.down b)).basis.pair (Biset.induction d)
    ((Biset.induction a).pair (Biset.restriction b) g x) 1
  let outer := Diagram.associate (R := Complex) (.up c) (.down e) (.up f)
  -- Lemma 6.6, equation (6.3) is stated on left-associated bases.
  -- The exterior associators only rebracket the same balanced classes.
  have hInner : (leftInner a b d c e f u v w r t s finite).interpret.eval.toLinearMap
      (Finsupp.single inLeft 1) =
      ∑ p ∈ (fibers z).toFinset,
        Finsupp.single ((upBasis c e).pair (Biset.induction f) p 1) (1 : Complex) :=
    (CaseFiveLeftShapeEvaluation a b d c e f u v w).1 r t s fibers g x
  change (outer.eval.toLinearMap
    ((leftInner a b d c e f u v w r t s finite).interpret.eval.toLinearMap
      ((Diagram.unassociate (R := Complex) (.up a) (.down b) (.up d)).eval.toLinearMap
        (Finsupp.single (point a b d g x) 1)))) (point c e f h y) = _
  rw [show (Diagram.unassociate (R := Complex) (.up a) (.down b) (.up d)).eval.toLinearMap
      (Finsupp.single (point a b d g x) 1) = Finsupp.single inLeft 1 from
      Diagram.eval_unassociate_single _ _ _ g x 1 1,
    hInner, map_sum, Finsupp.finset_sum_apply]
  have hout : point c e f h y = appendUnit c e f p₀ := rfl
  simp only [appendUnit_pair, hout, Finsupp.single_apply, (appendUnit_injective c e f).eq_iff,
    Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_setOf_eq, hp₀, eq_comm (a := z)]

end Evaluation

end SupportedLeftOrbitAux

