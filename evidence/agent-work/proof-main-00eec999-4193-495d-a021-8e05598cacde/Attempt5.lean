import MackeyDiagrams
import Proofs.CaseFiveLeftShapeEvaluation
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks

set_option maxHeartbeats 2000000

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
    obtain ⟨τ, rfl⟩ := hs
    let σ : Equiv.Perm Nat := Equiv.Perm.ofSubtype τ
    have moved_mem (x : Nat) (hx : σ x ≠ x) : x ∈ X := by
      by_contra hn
      have hi : x ∉ A i := fun hx' => hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx'⟩)
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem τ hi)
    have preserves (x : Nat) : σ x ∈ X ↔ x ∈ X := by
      by_cases h : σ x = x
      · rw [h]
      · have hy : σ (σ x) ≠ σ x := fun hh => h (σ.injective hh)
        exact iff_of_true (moved_mem (σ x) hy) (moved_mem x h)
    exact ⟨σ.subtypePerm preserves, Equiv.Perm.ofSubtype_subtypePerm preserves moved_mem⟩
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
  let assoc := Biset.associateBasisEquiv (Biset.induction c) (Biset.restriction e) (Biset.induction f)
  have h' : (upBasis c e).pair (Biset.induction f) p 1 =
      (upBasis c e).pair (Biset.induction f) p' 1 := by
    apply assoc.injective
    exact h
  obtain ⟨k, hp, hk⟩ := Quotient.exact h'
  change k * 1 * (f.toHom 1)⁻¹ = (1 : E) at hk
  have he : k = 1 := by simpa only [map_one, inv_one, mul_one] using hk
  change (upBasis c e).act (1, k) p = p' at hp
  rw [he] at hp
  change (upBasis c e).act 1 p = p' at hp
  exact ((upBasis c e).one_act p).symm.trans hp

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
      @ite Complex (u.toHom g * r.element * v.toHom x * t.element =
          u.toHom h * s.element * w.toHom y) (Classical.propDecidable _) 1 0 := by
  classical
  let L := Generator.mixedProduct u w ∘ upperMap c e u w s
  let z := u.toHom g * r.element * v.toHom x * t.element
  have fibers (q : B) : Set.Finite {p | L p = q} := by
    refine (finite (Generator.mixedPair u w q)).subset ?_
    intro p hp
    change Generator.mixedProduct u w (upperMap c e u w s p) = q at hp
    change upperMap c e u w s p = Generator.mixedPair u w q
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
      Diagram.eval_unassociate_single (.up a) (.down b) (.up d) g x 1 1,
    hInner, map_sum, Finset.sum_apply']
  have hout : point c e f h y = appendUnit c e f p₀ := rfl
  rw [hout]
  have hterm (p : (upBasis c e).carrier) :
      (outer.eval.toLinearMap (Finsupp.single ((upBasis c e).pair (Biset.induction f) p 1) 1))
        (appendUnit c e f p₀) = (if p = p₀ then (1 : Complex) else 0) := by
    have hassoc := congrArg
      (fun col : (word c e f).basis.carrier →₀ Complex => col (appendUnit c e f p₀))
      (appendUnit_pair c e f p)
    refine hassoc.trans ?_
    by_cases hp : p = p₀
    · simp [hp]
    · have hne : appendUnit c e f p ≠ appendUnit c e f p₀ :=
        fun he => hp (appendUnit_injective c e f he)
      simp [Finsupp.single_apply, hp, hne]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  simp only [Finset.sum_ite_eq', Set.Finite.mem_toFinset]
  change (if L p₀ = z then (1 : Complex) else 0) =
    @ite Complex (z = u.toHom h * s.element * w.toHom y) (Classical.propDecidable _) 1 0
  rw [hp₀]
  by_cases hz : z = u.toHom h * s.element * w.toHom y
  · simp [hz]
  · simp [hz, Ne.symm hz]


end Evaluation

end SupportedLeftOrbitAux


open MackeyDiagrams SupportedLeftOrbitAux


theorem SupportedLeftOrbitProjectedStabilizer : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (S : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
∀ {G A D F C E B : Subgroup U},
  parabolic G → parabolic A → parabolic D → parabolic F →
  parabolic C → parabolic E → parabolic B →
  ∀ (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E)
    (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
    (w : MackeyDiagrams.ConjEmbedding E B),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  ∀ (r : MackeyDiagrams.Dot (comp u a) (comp v b))
    (t : MackeyDiagrams.Dot (comp v d) (comp w f))
    (s : MackeyDiagrams.Dot (comp u c) (comp w e)),
  let upperProduct := MackeyDiagrams.Generator.mixedMultiplicationBasis u w c e s
  ∃ (leftFinite : ∀ z, Set.Finite {p | upperProduct p = z}),
    let ga := up a
    let ad := down b
    let df := up d
    let gc := up c
    let ce := down e
    let ef := up f
    let du := down u
    let uv := up v
    let uw := up w
    let bottom := tensor ga (tensor ad df)
    let top := tensor gc (tensor ce ef)
    let X := MackeyDiagrams.Word.basis bottom
    let Y := MackeyDiagrams.Word.basis top
    let input := fun (g : G) (x : D) =>
      MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
        (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
    let output := fun (h : G) (y : E) =>
      MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
        (MackeyDiagrams.Word.basis (tensor ce ef)) h (MackeyDiagrams.Generator.mixedPair e f y)
    let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
    let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
    let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
    let first : MackeyDiagrams.LabelledDrawing Complex (tensor (tensor ga ad) df) (tensor (tensor du uv) df) :=
      juxtapose (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b [(1, r)])
        (ordinary (MackeyDiagrams.Diagram.id df))
    let middle : MackeyDiagrams.LabelledDrawing Complex (tensor uv df) (tensor uw ef) :=
      MackeyDiagrams.LabelledDrawing.parallelUp v d w f [(1, t)]
    let last : MackeyDiagrams.LabelledDrawing Complex (tensor (tensor du uw) ef) (tensor (tensor gc ce) ef) :=
      juxtapose (MackeyDiagrams.LabelledDrawing.compactProjection u w c e [(1, ⟨s, leftFinite⟩)])
        (ordinary (MackeyDiagrams.Diagram.id ef))
    let leftDiagram : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      stack (ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
        (stack first
          (stack (ordinary (MackeyDiagrams.Diagram.associate du uv df))
            (stack (juxtapose (ordinary (MackeyDiagrams.Diagram.id du)) middle)
              (stack (ordinary (MackeyDiagrams.Diagram.unassociate du uw ef))
                (stack last (ordinary (MackeyDiagrams.Diagram.associate gc ce ef)))))))
    letI : MulAction (G × F) X.carrier :=
      { smul := MackeyDiagrams.Biset.act X
        one_smul := MackeyDiagrams.Biset.one_act X
        mul_smul := MackeyDiagrams.Biset.mul_act X }
    letI : MulAction (G × F) Y.carrier :=
      { smul := MackeyDiagrams.Biset.act Y
        one_smul := MackeyDiagrams.Biset.one_act Y
        mul_smul := MackeyDiagrams.Biset.mul_act Y }
    let Pair := X.carrier × Y.carrier
    let orbit : Pair → Set Pair := MulAction.orbit (G × F)
    let stabilizer : Pair → Subgroup (G × F) := MulAction.stabilizer (G × F)
    let project := Subgroup.map (MonoidHom.snd G F)
    let inAmbient := Subgroup.map (Subgroup.subtype F)
    let projectedSource := fun (p : X.carrier) => project (MulAction.stabilizer (G × F) p)
    let projectedTarget := fun (p : Y.carrier) => project (MulAction.stabilizer (G × F) p)
    let projectedPair := fun (p : Pair) => project (stabilizer p)
    let coefficient := fun (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top) (z : Pair) =>
      MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret diagram))
        (Finsupp.single z.1 (1 : Complex)) z.2
    let actB := fun (q : G × F) (z : B) =>
      MackeyDiagrams.ConjEmbedding.toHom u q.1 * z *
        (MackeyDiagrams.ConjEmbedding.toHom w (MackeyDiagrams.ConjEmbedding.toHom f q.2))⁻¹
    ∃ (sourceMap : X.carrier → B) (targetMap : Y.carrier → B),
      (∀ (g : G) (x : D), sourceMap (input g x) =
        MackeyDiagrams.ConjEmbedding.toHom u g * MackeyDiagrams.Dot.element r *
          MackeyDiagrams.ConjEmbedding.toHom v x * MackeyDiagrams.Dot.element t) ∧
      (∀ (h : G) (y : E), targetMap (output h y) =
        MackeyDiagrams.ConjEmbedding.toHom u h * MackeyDiagrams.Dot.element s *
          MackeyDiagrams.ConjEmbedding.toHom w y) ∧
      (∀ (q : G × F) (p : X.carrier),
        sourceMap (MackeyDiagrams.Biset.act X q p) = actB q (sourceMap p)) ∧
      (∀ (q : G × F) (p : Y.carrier),
        targetMap (MackeyDiagrams.Biset.act Y q p) = actB q (targetMap p)) ∧
      (∀ z : Pair, coefficient leftDiagram z ≠ 0 ↔ sourceMap z.1 = targetMap z.2) ∧
      (∀ z : Pair, coefficient leftDiagram z ≠ 0 →
        projectedPair z = projectedSource z.1 ⊓ projectedTarget z.2 ∧
        parabolic (inAmbient (projectedSource z.1)) ∧
        parabolic (inAmbient (projectedTarget z.2)) ∧
        parabolic (inAmbient (projectedPair z)) ∧
        coefficient leftDiagram z = 1) ∧
      (∀ (x : D) (h : G) (y : E),
        let z₀ : Pair := (input 1 x, output h y)
        coefficient leftDiagram z₀ ≠ 0 →
        projectedSource z₀.1 =
          Subgroup.comap (MackeyDiagrams.ConjEmbedding.toHom d)
            (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x⁻¹))
              (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b))) ∧
        projectedTarget z₀.2 =
          Subgroup.comap (MackeyDiagrams.ConjEmbedding.toHom f)
            (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj y⁻¹))
              (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom e))) ∧
        let P := inAmbient (projectedPair z₀)
        ∃ (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
          (k : MackeyDiagrams.ConjEmbedding P C)
          (r' : MackeyDiagrams.Dot (comp b i) (comp d j))
          (t' : MackeyDiagrams.Dot (comp a i) (comp c k))
          (s' : MackeyDiagrams.Dot (comp e k) (comp f j)),
          (∀ p : P, (MackeyDiagrams.ConjEmbedding.toHom j p : U) = (p : U)) ∧
          MackeyDiagrams.Dot.element r' = x ∧
          MackeyDiagrams.Dot.element t' = h ∧
          MackeyDiagrams.Dot.element s' = y ∧
          ∃ (rightFinite : ∀ z, Set.Finite
            {p | MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r' p = z}),
            let ai := up i
            let fj := down j
            let ck := up k
            let lower := MackeyDiagrams.LabelledDrawing.compactProjection b d i j [(1, ⟨r', rightFinite⟩)]
            let center := MackeyDiagrams.LabelledDrawing.parallelUp a i c k [(1, t')]
            let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j [(1, s')]
            let rightDiagram : MackeyDiagrams.LabelledDrawing Complex bottom top :=
              stack (juxtapose (ordinary (MackeyDiagrams.Diagram.id ga)) lower)
                (stack (ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
                  (stack (juxtapose center (ordinary (MackeyDiagrams.Diagram.id fj)))
                    (stack (ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
                      (juxtapose (ordinary (MackeyDiagrams.Diagram.id gc)) upper))))
            ∀ z : Pair, coefficient rightDiagram z =
              @ite Complex (z ∈ orbit z₀) (Classical.propDecidable (z ∈ orbit z₀)) 1 0)
) :=
(by
  classical
  intro finitary U blockSym parabolic G A D F C E B hG hA hD hF hC hE hB
    a b d c e f u v w up down tensor comp r t s upperProduct
  -- Xiao, Prop. 8.7, first proof paragraph (archived pp. 39–40,
  -- revised published pp. 41–42). The online proof uses paragraphs.
  -- Steps 1–4 below follow its coefficient, equivariance, stabilizer
  -- and right-orbit arguments. Equation (6.3) is on archived p. 25
  -- and revised published p. 27. Theorem 6.7 is on pp. 26 and 28.
  -- The saved source note's byte-identity claim is stale: the archived
  -- source/mackey-bimodules.pdf hashes to bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2.
  -- The revised published PDF hashes to 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e.
  -- The cited argument agrees on the verified pages of both copies.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  have hfinite : ∀ z, Set.Finite {p | upperProduct p = z} := by
    let : Finite G := parabolic_finite hG
    let : Finite E := parabolic_finite hE
    let : Finite (upBasis c e).carrier :=
      Finite.of_surjective (fun p : G × E => (Biset.induction c).pair (Biset.restriction e) p.1 p.2)
        (fun p => Quotient.inductionOn p (fun q => ⟨q, rfl⟩))
    exact fun _ => Set.toFinite _
  refine ⟨hfinite, ?_⟩
  intro ga ad df gc ce ef du uv uw bottom top X Y input output stack juxtapose ordinary
    first middle last leftDiagram Pair orbit stabilizer project inAmbient
    projectedSource projectedTarget projectedPair coefficient actB
  let sourceMap := ambientMap a b d u v r t.element
  let targetMap := ambientMap c e f u w s 1
  have hsRep (g : G) (x : D) : sourceMap (input g x) =
      u.toHom g * r.element * v.toHom x * t.element :=
    ambientMap_point a b d u v r t.element g x
  have htRep (h : G) (y : E) : targetMap (output h y) = u.toHom h * s.element * w.toHom y := by
    simpa only [mul_one] using ambientMap_point c e f u w s 1 h y
  -- Step 1. The group-element singleton crosses the projection fiber once.
  have hentry (z : Pair) :
      coefficient leftDiagram z =
        @ite Complex (sourceMap z.1 = targetMap z.2) (Classical.propDecidable _) 1 0 := by
    obtain ⟨p, q⟩ := z
    obtain ⟨g, x, rfl⟩ := point_surjective a b d p
    obtain ⟨h, y, rfl⟩ := point_surjective c e f q
    show coefficient leftDiagram (input g x, output h y) = _
    rw [show sourceMap (input g x, output h y).1 = _ from hsRep g x,
      show targetMap (input g x, output h y).2 = _ from htRep h y]
    exact coefficient_on_points a b d c e f u v w r t s hfinite g x h y
  -- Step 2. The crossing labels give quotient descent and equivariance,
  -- including v(d(k)) * t = t * w(f(k)) for the middle crossing.
  have hsAct (q : G × F) (p : X.carrier) :
      sourceMap (Biset.act X q p) = actB q (sourceMap p) :=
    ambientMap_act a b d u v r t.element (w.toHom.comp f.toHom) t.intertwines q p
  have htAct (q : G × F) (p : Y.carrier) :
      targetMap (Biset.act Y q p) = actB q (targetMap p) :=
    ambientMap_act c e f u w s 1 (w.toHom.comp f.toHom) (fun k => by simp) q p
  have hsupport (z : Pair) :
      coefficient leftDiagram z ≠ 0 ↔ sourceMap z.1 = targetMap z.2 := by
    rw [hentry]
    by_cases h : sourceMap z.1 = targetMap z.2 <;> simp [h]
  refine ⟨sourceMap, targetMap, hsRep, htRep, hsAct, htAct, hsupport, ?_, ?_⟩
  · intro z hz
    have himage := (hsupport z).mp hz
    -- Step 3. Fixing the shared image pins down the same first component
    -- for both lifts of any k in the intersection of projections.
    have hpair : projectedPair z = projectedSource z.1 ⊓ projectedTarget z.2 := by
      ext k
      change (∃ q : G × F, (X.act q z.1, Y.act q z.2) = z ∧ q.2 = k) ↔
        (∃ q : G × F, X.act q z.1 = z.1 ∧ q.2 = k) ∧
        (∃ q : G × F, Y.act q z.2 = z.2 ∧ q.2 = k)
      constructor
      · rintro ⟨q, hq, hk⟩
        exact ⟨⟨q, congrArg Prod.fst hq, hk⟩, ⟨q, congrArg Prod.snd hq, hk⟩⟩
      · rintro ⟨⟨⟨q₁, k₁⟩, h₁, rfl⟩, ⟨⟨q₂, k₂⟩, h₂, hk⟩⟩
        change k₂ = k₁ at hk
        subst k₂
        have hleft := hsAct (q₁, k₁) z.1
        have hright := htAct (q₂, k₁) z.2
        rw [h₁] at hleft
        rw [h₂, ← himage] at hright
        have he : q₁ = q₂ := u.injective (mul_right_cancel (mul_right_cancel
          (hleft.symm.trans hright)))
        exact ⟨(q₁, k₁), Prod.ext h₁ (he.symm ▸ h₂), rfl⟩
    have hsPar : parabolic (inAmbient (projectedSource z.1)) := by
      obtain ⟨g, x, hx⟩ := SupportedLeftOrbitAux.point_surjective a b d z.1
      change input g x = z.1 at hx
      rw [← hx]
      rw [show projectedSource (input g x) = _ from
        SupportedLeftOrbitAux.projection_formula a b d g x]
      exact SupportedLeftOrbitAux.projected_parabolic hA hF b d x
    have htPar : parabolic (inAmbient (projectedTarget z.2)) := by
      obtain ⟨h, y, hy⟩ := SupportedLeftOrbitAux.point_surjective c e f z.2
      change output h y = z.2 at hy
      rw [← hy]
      rw [show projectedTarget (output h y) = _ from
        SupportedLeftOrbitAux.projection_formula c e f h y]
      exact SupportedLeftOrbitAux.projected_parabolic hC hF e f y
    refine ⟨hpair, hsPar, htPar, ?_, by rw [hentry, ite_eq_left himage]⟩
    rw [hpair]
    change parabolic ((projectedSource z.1 ⊓ projectedTarget z.2).map F.subtype)
    rw [Subgroup.map_inf _ _ _ F.subtype_injective]
    exact SupportedLeftOrbitAux.parabolic_inf hsPar htPar
  · intro x h y z₀ hz
    refine ⟨SupportedLeftOrbitAux.projection_formula a b d 1 x,
      SupportedLeftOrbitAux.projection_formula c e f h y, ?_⟩
    -- Step 4. Theorem 6.7 requires a nonzero entry of an equivariant
    -- finitely supported column. Use the evaluated left drawing itself.
    intro P
    have hP : P = (stabilizer z₀).map (F.subtype.comp (MonoidHom.snd G F)) :=
      Subgroup.map_map (stabilizer z₀) F.subtype (MonoidHom.snd G F)
    rw [hP]
    have hR := ((RightOrbitDiagramFromProjectedStabilizer G A D F C E a b d c e f
      ).2.2.1 x h y).2.2.2
    obtain ⟨i, j, k, r', t', s', hj, hr, ht, hs, _, _, horbit⟩ := hR
    obtain ⟨_, finite, heval⟩ := horbit leftDiagram.interpret.eval hz
    exact ⟨i, j, k, r', t', s', hj, hr, ht, hs, finite, heval⟩)

#print axioms SupportedLeftOrbitProjectedStabilizer
