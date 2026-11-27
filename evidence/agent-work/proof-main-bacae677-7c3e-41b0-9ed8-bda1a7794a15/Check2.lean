import MackeyDiagrams
import Proofs.CaseSixRightShapeEvaluation
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.ExtremalParabolicsOfFiniteGroup
import Proofs.FiniteParabolicClosure
import Proofs.SupportedLeftOrbitProjectedStabilizer
set_option maxHeartbeats 3000000 in
private theorem orbitMultiplicityFinite {W : Type*} [Group W]
    {H K : Subgroup W} [Finite K] : H.relIndex K ≠ 0 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_ne_zero

namespace OrbitMultiplicity

open MackeyDiagrams

private abbrev Sinf := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
private abbrev ParabolicPerm (H : Subgroup (Equiv.Perm Nat)) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    H = ⨆ l, blockSym (blocks l)
private abbrev Parabolic (H : Subgroup Sinf) := ParabolicPerm (H.map Sinf.subtype)
private abbrev swaps (P : Subgroup Sinf) :=
  Subgroup.closure {σ : Sinf | σ ∈ P ∧ Equiv.Perm.IsSwap (σ : Equiv.Perm Nat)}

private theorem parabolic_finite {H : Subgroup Sinf} (hH : Parabolic H) : Finite H := by
  classical
  obtain ⟨n, blocks, _, _, hblocks⟩ := hH
  let X := Finset.univ.biUnion blocks
  have hsub : H.map Sinf.subtype ≤ blockSym X := by
    rw [hblocks]
    refine iSup_le fun i σ hs => ?_
    obtain ⟨τ, rfl⟩ := hs
    let σ : Equiv.Perm Nat := Equiv.Perm.ofSubtype τ
    have moved_mem (x : Nat) (hx : σ x ≠ x) : x ∈ X := by
      by_contra hn
      have hi : x ∉ blocks i := fun hx' => hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx'⟩)
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

private theorem parabolic_extremal (P : Subgroup Sinf) [Finite P] :
    IsGreatest {K : Subgroup Sinf | Parabolic K ∧ K ≤ P} (swaps P) := by
  classical
  let Q := P.map Sinf.subtype
  haveI : Finite Q := (Set.finite_range (Sinf.subtype.comp P.subtype)).to_subtype
  have hQ : Q ≤ Sinf := fun _ ⟨p, _, hp⟩ => hp ▸ p.property
  have unionWitness (H : Subgroup (Equiv.Perm Nat)) :
      ParabolicPerm H ↔ ∃ X : Finset Nat, ∃ (n : Nat) (blocks : Fin n → Finset Nat),
        (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
        (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ H = ⨆ l, blockSym (blocks l) := by
    constructor
    · rintro ⟨n, blocks, hn, hd, he⟩
      exact ⟨Finset.univ.biUnion blocks, n, blocks, hn, hd, by simp, he⟩
    · rintro ⟨_, n, blocks, hn, hd, _, he⟩
      exact ⟨n, blocks, hn, hd, he⟩
  have hmap : (swaps P).map Sinf.subtype =
      Subgroup.closure {σ | σ ∈ Q ∧ Equiv.Perm.IsSwap σ} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext σ
    constructor
    · rintro ⟨p, ⟨hp, hs⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hs⟩
    · rintro ⟨⟨p, hp, rfl⟩, hs⟩
      exact ⟨p, ⟨hp, hs⟩, rfl⟩
  have h := (ExtremalParabolicsOfFiniteGroup Q hQ).1
  rw [← hmap] at h
  refine ⟨⟨(unionWitness _).mpr h.1.1, ?_⟩, ?_⟩
  · exact (Subgroup.map_le_map_iff_of_injective Sinf.subtype_injective).mp h.1.2
  · intro K hK
    exact (Subgroup.map_le_map_iff_of_injective Sinf.subtype_injective).mp
      (h.2 ⟨(unionWitness _).mp hK.1, Subgroup.map_mono hK.2⟩)

private theorem conjugate_parabolic {B F : Subgroup Sinf} (j : ConjEmbedding B F)
    (hB : Parabolic B) : Parabolic ((F.subtype.comp j.toHom).range) := by
  classical
  obtain ⟨q, hq⟩ := j.hasRepresentative
  let conj := (MulAut.conj (q : Equiv.Perm Nat)).toMonoidHom
  have hmap : ((F.subtype.comp j.toHom).range).map Sinf.subtype =
      (B.map Sinf.subtype).map conj := by
    ext σ
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨p.val.val, ⟨p.val, p.property, rfl⟩, (congrArg Subtype.val (hq p)).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨j.toHom ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, congrArg Subtype.val (hq ⟨p, hp⟩)⟩
  have hcarrier : ∃ X : Finset Nat, ∃ (n : Nat) (blocks : Fin n → Finset Nat),
      (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
      (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ B.map Sinf.subtype = ⨆ l, blockSym (blocks l) := by
    obtain ⟨n, blocks, hn, hd, he⟩ := hB
    exact ⟨Finset.univ.biUnion blocks, n, blocks, hn, hd, by simp, he⟩
  obtain ⟨_, n, blocks, hn, hd, _, he⟩ := FiniteParabolicClosure.1 (B.map Sinf.subtype) hcarrier q
  exact ⟨n, blocks, hn, hd, hmap.trans he⟩

section Geometry

variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)

private abbrev word := (Word.up a).tensor ((Word.down b).tensor (.up d))
private abbrev point (g : G) (x : D) : (word a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b |>.tensor (.up d)).basis) g (Generator.mixedPair b d x)
private abbrev Pair := (word a b d).basis.carrier × (word c e f).basis.carrier
private abbrev action : MulAction (G × F) (Pair a b d c e f) where
  smul q z := ((word a b d).basis.act q z.1, (word c e f).basis.act q z.2)
  one_smul z := Prod.ext ((word a b d).basis.one_act z.1) ((word c e f).basis.one_act z.2)
  mul_smul q q' z := Prod.ext ((word a b d).basis.mul_act q q' z.1)
    ((word c e f).basis.mul_act q q' z.2)

private abbrev orbit (z : Pair a b d c e f) :=
  @MulAction.orbit (G × F) _ _ (action a b d c e f) z
private abbrev stabilizer (z : Pair a b d c e f) :=
  @MulAction.stabilizer (G × F) _ _ (action a b d c e f) z
private abbrev projectHom (G F : Subgroup U) := F.subtype.comp (MonoidHom.snd G F)
private abbrev projected (z : Pair a b d c e f) :=
  (stabilizer a b d c e f z).map (projectHom G F)
private abbrev base (r : D) (t : G) (s : E) : Pair a b d c e f :=
  (point a b d 1 r, point c e f t s)

private theorem point_surjective (z : (word a b d).basis.carrier) :
    ∃ g x, point a b d g x = z := by
  obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective y
  exact ⟨g, x, rfl⟩

private abbrev coefficient (M : Biset.Hom Complex (word a b d).basis (word c e f).basis)
    (z : Pair a b d c e f) : Complex := M.toLinearMap (Finsupp.single z.1 1) z.2
private noncomputable abbrev matrix (O : Set (Pair a b d c e f)) (n : Nat)
    (z : Pair a b d c e f) : Complex := @ite _ (z ∈ O) (Classical.propDecidable _) n 0
private abbrev eval (drawing : LabelledDrawing Complex (word a b d) (word c e f)) :=
  drawing.interpret.eval
private abbrev fiber (i : ConjEmbedding B A) (j : ConjEmbedding B F) :=
  ((Word.up i).tensor (.down j)).basis.carrier
private abbrev innerPoint (i : ConjEmbedding B A) (j : ConjEmbedding B F) (v : A × F) :
    fiber i j := (Biset.induction i).pair (Biset.restriction j) v.1 v.2
private abbrev lowerMap (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (r : Dot (b.comp i) (d.comp j)) := Generator.mixedMultiplicationBasis b d i j r
private abbrev outputOf (g : G) (t : G) (s : E) (v : A × F) :=
  point c e f (g * a.toHom v.1 * t) (s * f.toHom v.2)
private abbrev FiniteFibers (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (r : Dot (b.comp i) (d.comp j)) := ∀ z, Set.Finite {w | lowerMap b d i j r w = z}
private noncomputable abbrev hits (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (r : Dot (b.comp i) (d.comp j)) (t : G) (s : E) (g : G) (x : D)
    (y : (word c e f).basis.carrier) : Set (fiber i j) :=
  {w | lowerMap b d i j r w = Generator.mixedPair b d x ∧
    outputOf a c e f g t s (Quotient.out w) = y}

private theorem finite_of_bases [Finite A] [Finite F]
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) : Finite (fiber i j) :=
  Finite.of_surjective (innerPoint i j) (Quotient.exists_rep)

private theorem finiteFibers_of_bases [Finite A] [Finite F]
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (r : Dot (b.comp i) (d.comp j)) :
    FiniteFibers b d i j r := by
  letI := finite_of_bases i j
  exact fun _ => Set.toFinite _

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

private abbrev diagonal (i : ConjEmbedding B A) (j : ConjEmbedding B F) :
    B →* A × F := i.toHom.prod j.toHom
private abbrev phi : A × F →* G × F :=
  a.toHom.prodMap (MonoidHom.id F)

private theorem inner_eq (i : ConjEmbedding B A) (j : ConjEmbedding B F) (v w : A × F) :
    innerPoint i j (v.1, v.2⁻¹) = innerPoint i j (w.1, w.2⁻¹) ↔
      v⁻¹ * w ∈ (diagonal i j).range := by
  constructor
  · intro h
    obtain ⟨p, hp, hq⟩ := Quotient.exact h
    change 1 * v.1 * (i.toHom p)⁻¹ = w.1 at hp
    change j.toHom p * v.2⁻¹ * (1 : F)⁻¹ = w.2⁻¹ at hq
    refine ⟨p⁻¹, Prod.ext ?_ ?_⟩
    · change i.toHom p⁻¹ = v.1⁻¹ * w.1
      simp only [one_mul] at hp
      rw [← hp, map_inv, inv_mul_cancel_left]
    · change j.toHom p⁻¹ = v.2⁻¹ * w.2
      simp only [inv_one, mul_one] at hq
      rw [map_inv, ← inv_inv w.2, ← hq, mul_inv_rev, inv_inv, inv_mul_cancel_left]
  · rintro ⟨p, hp⟩
    apply Quotient.sound
    have hv : w = v * diagonal i j p := by rw [hp, mul_inv_cancel_left]
    refine ⟨p⁻¹, ?_, ?_⟩
    · change 1 * v.1 * (i.toHom p⁻¹)⁻¹ = w.1
      rw [hv]
      simp [diagonal]
    · change j.toHom p⁻¹ * v.2⁻¹ * (1 : F)⁻¹ = w.2⁻¹
      rw [hv]
      simp [diagonal, mul_inv_rev]

private noncomputable def innerEquiv (i : ConjEmbedding B A) (j : ConjEmbedding B F) :
    (A × F) ⧸ (diagonal i j).range ≃ fiber i j :=
  Equiv.ofBijective (Quotient.lift (fun v : A × F => innerPoint i j (v.1, v.2⁻¹))
    fun v w hv => (inner_eq i j v w).mpr ((QuotientGroup.leftRel_apply).mp hv)) ⟨
    fun v w => Quotient.inductionOn₂ v w (fun v w h =>
      Quotient.sound ((QuotientGroup.leftRel_apply).mpr ((inner_eq i j v w).mp h))),
    fun w => by
      obtain ⟨⟨p,q⟩, hw⟩ := Quotient.exists_rep w
      exact ⟨QuotientGroup.mk (p,q⁻¹), by simpa [innerPoint] using hw⟩⟩

private theorem count_tower {H : Type*} [Group H] {K P : Subgroup H} (h : K ≤ P)
    (base : H) :
    Nat.card {w : H ⧸ K // (Subgroup.quotientEquivProdOfLE h w).1 = QuotientGroup.mk base} =
      K.relIndex P := by
  let E := Subgroup.quotientEquivProdOfLE h
  apply (Nat.card_congr (Equiv.mk
    (fun w => (E w.1).2)
    (fun q => ⟨E.symm (QuotientGroup.mk base, q), by simp [E]⟩)
    (fun w => Subtype.ext (E.injective (by simpa [E] using Prod.ext w.property.symm
      (rfl : (E w.1).2 = (E w.1).2))))
    (fun q => by simp [E]))).trans
  exact (Subgroup.index_eq_card _).symm

private theorem hit_eq_parameters
    (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (tDot : Dot (a.comp i) (c.comp k))
    (sDot : Dot (e.comp k) (f.comp j)) (g : G) (x : D)
    (y : (word c e f).basis.carrier)
    (input_eq : ∀ (g g' : G) (x : D) (h : F),
      point a b d g' (r.element * d.toHom h) = point a b d g x ↔
        ∃ α : A, g' = g * a.toHom α ∧ x = b.toHom α * r.element * d.toHom h)
    (v : A × F) :
    let t := tDot.element
    let s := sDot.element
    letI := action a b d c e f
    innerPoint i j (v.1, v.2⁻¹) ∈ hits a b d c e f i j r t s g x y ↔
      ((g, 1) * phi (F := F) a v) • base a b d c e f r.element t s =
        (point a b d g x, y) := by
  letI := action a b d c e f
  let t := tDot.element
  let s := sDot.element
  let w := innerPoint i j (v.1, v.2⁻¹)
  let u : A × F := Quotient.out w
  have hbalance : innerPoint i j u = w := Quotient.out_eq' w
  have hx : lowerMap b d i j r w = Generator.mixedPair b d x ↔
      b.toHom v.1 * r.element * d.toHom v.2⁻¹ = x :=
    (Generator.mixedEquiv b d).symm.injective.eq_iff
  have hy : outputOf a c e f g t s u = outputOf a c e f g t s (v.1,v.2⁻¹) := by
    obtain ⟨p, h₁, h₂⟩ := Quotient.exact hbalance
    change 1 * u.1 * (i.toHom p)⁻¹ = v.1 at h₁
    change j.toHom p * u.2 * (1 : F)⁻¹ = v.2⁻¹ at h₂
    simp only [one_mul, mul_one, inv_one] at h₁ h₂
    apply Quotient.sound
    refine ⟨k.toHom p, ?_, ?_⟩
    · change 1 * (g * a.toHom u.1 * t) * (c.toHom (k.toHom p))⁻¹ =
        g * a.toHom v.1 * t
      have ht : a.toHom (i.toHom p) * t = t * c.toHom (k.toHom p) :=
        tDot.intertwines p
      rw [← h₁, map_mul, map_inv, one_mul]
      have ht' : t * (c.toHom (k.toHom p))⁻¹ = (a.toHom (i.toHom p))⁻¹ * t := by
        calc
          _ = (a.toHom (i.toHom p))⁻¹ * (t * c.toHom (k.toHom p)) *
            (c.toHom (k.toHom p))⁻¹ := by rw [← ht]; group
          _ = _ := by group
      rw [mul_assoc (g * a.toHom u.1) t _, ht']
      group
    · change (Biset.restriction e).pair (Biset.induction f)
        (e.toHom (k.toHom p) * (s * f.toHom u.2) * (1 : E)⁻¹)
        (1 * 1 * (f.toHom 1)⁻¹) = _
      have hs : e.toHom (k.toHom p) * s = s * f.toHom (j.toHom p) :=
        sDot.intertwines p
      simp only [inv_one, map_one, mul_one, one_mul]
      rw [← mul_assoc, hs, mul_assoc, ← map_mul, h₂]
      rfl
  change (lowerMap b d i j r w = _ ∧ outputOf a c e f g t s u = y) ↔ _
  rw [hx, hy]
  change (_ ∧ _) ↔ ((word a b d).basis.act _ _, (word c e f).basis.act _ _) = _
  rw [act_point, act_point, Prod.mk.injEq]
  change (_ ∧ _) ↔
    point a b d (g * a.toHom v.1 * 1) (r.element * (d.toHom (1 * v.2))⁻¹) = point a b d g x ∧ _
  simp only [mul_one, one_mul, ← map_inv, input_eq]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨⟨v.1, rfl, hx.symm⟩, hy⟩
  · rintro ⟨⟨α, hα, hx⟩, hy⟩
    have he : v.1 = α := a.injective (mul_left_cancel hα)
    exact ⟨by simpa only [he] using hx.symm, hy⟩

end Geometry
end OrbitMultiplicity
