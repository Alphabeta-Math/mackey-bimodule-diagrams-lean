import MackeyDiagrams
import Proofs.CaseSixRightShapeEvaluation
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.ExtremalParabolicsOfFiniteGroup
import Proofs.FiniteParabolicClosure
import Proofs.SupportedLeftOrbitProjectedStabilizer

set_option maxHeartbeats 2000000

private theorem orbitMultiplicityFinite {W : Type*} [Group W]
    {H K : Subgroup W} [Finite K] : H.relIndex K ≠ 0 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

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
  letI : Finite Q := Finite.of_surjective (fun p : P => (⟨p.val.val, ⟨p.val, p.property, rfl⟩⟩ : Q))
    (by rintro ⟨_, i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩)
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
  letI := action a b d c e f
  MulAction.orbit (G × F) z
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

private noncomputable abbrev coefficient (M : Biset.Hom Complex (word a b d).basis (word c e f).basis)
    (z : Pair a b d c e f) : Complex := M.toLinearMap (Finsupp.single z.1 1) z.2
private noncomputable abbrev matrix (O : Set (Pair a b d c e f)) (n : Nat)
    (z : Pair a b d c e f) : Complex := @ite _ (z ∈ O) (Classical.propDecidable _) n 0
private noncomputable abbrev eval (drawing : LabelledDrawing Complex (word a b d) (word c e f)) :=
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
      refine ⟨QuotientGroup.mk (p,q⁻¹), ?_⟩
      change innerPoint i j (p, (q⁻¹)⁻¹) = w
      rw [inv_inv]
      exact hw⟩

private theorem count_tower {H : Type*} [Group H] {K P : Subgroup H} (h : K ≤ P)
    (base : H) :
    Nat.card {w : H ⧸ K // (Subgroup.quotientEquivProdOfLE h w).1 = QuotientGroup.mk base} =
      K.relIndex P := by
  let E := Subgroup.quotientEquivProdOfLE h
  let E' : {w : H ⧸ K // (E w).1 = QuotientGroup.mk base} ≃ (P ⧸ K.subgroupOf P) :=
    { toFun := fun w => (E w.1).2
      invFun := fun q => ⟨E.symm (QuotientGroup.mk base, q), by simp⟩
      left_inv := fun w => Subtype.ext (E.injective (by
        rw [Equiv.apply_symm_apply]
        exact Prod.ext w.property.symm rfl))
      right_inv := fun q => congrArg Prod.snd (E.apply_symm_apply (QuotientGroup.mk base, q)) }
  exact (Nat.card_congr E').trans (Subgroup.index_eq_card _).symm

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
    letI := action a b d c e f
    innerPoint i j (v.1, v.2⁻¹) ∈ hits a b d c e f i j r tDot.element sDot.element g x y ↔
      ((g, 1) * phi (F := F) a v) • base a b d c e f r.element tDot.element sDot.element =
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
    point a b d (g * a.toHom v.1 * 1) (r.element * (d.toHom (1 * v.2))⁻¹) =
      point a b d g x ∧
    point c e f (g * a.toHom v.1 * t) (s * (f.toHom (1 * v.2))⁻¹) = y
  simp only [mul_one, one_mul, ← map_inv, input_eq, outputOf]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨⟨v.1, rfl, hx.symm⟩, hy⟩
  · rintro ⟨⟨α, hα, hx⟩, hy⟩
    have he : v.1 = α := a.injective (mul_left_cancel hα)
    exact ⟨by simpa only [he] using hx.symm, hy⟩

private theorem count_of_lift
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) (g : G) (x : D) (y : (word c e f).basis.carrier)
    (input_eq : ∀ (g g' : G) (x : D) (h : F),
      point a b d g' (r.element * d.toHom h) = point a b d g x ↔
        ∃ α : A, g' = g * a.toHom α ∧ x = b.toHom α * r.element * d.toHom h)
    (v₀ : A × F)
    (lift : letI := action a b d c e f
      ((g, 1) * phi (F := F) a v₀) • base a b d c e f r.element t.element s.element =
        (point a b d g x, y)) :
    let S := (stabilizer a b d c e f (base a b d c e f r.element t.element s.element)).comap (phi a)
    let T := (diagonal i j).range
    (T ≤ S) → Nat.card (hits a b d c e f i j r t.element s.element g x y) = T.relIndex S := by
  letI := action a b d c e f
  intro S T hTS
  let E := innerEquiv i j
  let z := base a b d c e f r.element t.element s.element
  have eq_act (v : A × F) :
      ((g, 1) * phi (F := F) a v) • z = (point a b d g x, y) ↔ v₀⁻¹ * v ∈ S := by
    rw [← lift]
    change _ ↔ phi a (v₀⁻¹ * v) • z = z
    rw [map_mul, map_inv, mul_smul, mul_smul, smul_left_cancel_iff]
    rw [mul_smul, inv_smul_eq_iff]
  have eq_mem (q : (A × F) ⧸ T) :
      E q ∈ hits a b d c e f i j r t.element s.element g x y ↔
        (Subgroup.quotientEquivProdOfLE hTS q).1 = QuotientGroup.mk v₀ := by
    refine Quotient.inductionOn q fun v => ?_
    change innerPoint i j (v.1, v.2⁻¹) ∈ _ ↔ QuotientGroup.mk v = QuotientGroup.mk v₀
    rw [hit_eq_parameters a b d c e f i j k r t s g x y input_eq, eq_act, eq_comm,
      QuotientGroup.eq]
  exact (Nat.card_congr (E.subtypeEquiv (fun q => (eq_mem q).symm)).symm).trans (count_tower hTS v₀)

private theorem index_on_range {W V : Type*} [Group W] [Group V] {S T : Subgroup W}
    (hTS : T ≤ S) (m : W →* V) (hm : Function.Injective (m.comp S.subtype)) :
    (T.map m).relIndex (S.map m) = T.relIndex S := by
  have h := Subgroup.relIndex_map_map_of_injective (T.subgroupOf S) (⊤ : Subgroup S) hm
  rwa [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hTS, ← Subgroup.map_map,
    Subgroup.map_top, S.range_subtype, Subgroup.relIndex_top_right] at h

private theorem right_count
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) :
    let z := base a b d c e f r.element t.element s.element
    let P := projected a b d c e f z
    let K := (F.subtype.comp j.toHom).range
    K ≤ P ∧ ∀ (g : G) (x : D) (y : (word c e f).basis.carrier),
      Nat.card (hits a b d c e f i j r t.element s.element g x y) =
        @ite Nat ((point a b d g x, y) ∈ orbit a b d c e f z)
          (Classical.propDecidable _) (K.relIndex P) 0 := by
  classical
  letI := action a b d c e f
  intro z P K
  obtain ⟨_, orbit_range, input_eq, iP, jP, _, _, _, _, _, _, _, _, graph, _, _⟩ :=
    (RightOrbitDiagramFromProjectedStabilizer G A D F C E a b d c e f).2.2.1
      r.element t.element s.element
  let S := (stabilizer a b d c e f z).comap (phi a)
  let T := (diagonal i j).range
  let m := F.subtype.comp (MonoidHom.snd A F)
  have hS : S = (diagonal iP jP).range := by
    ext v
    change phi a v ∈ stabilizer a b d c e f z ↔ _
    rw [graph]
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p, Prod.ext (a.injective ?_) ?_⟩
      · exact (congrArg Prod.fst hp).symm
      · exact (congrArg Prod.snd hp).symm
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
  have hTS : T ≤ S := by
    intro v hv
    let L := hit_eq_parameters a b d c e f i j k r t s 1 r.element
      (point c e f t.element s.element) input_eq
    have h := (L 1).mpr (by
      change (((1 : G), (1 : F)) * phi a 1) • z = z
      rw [map_one, mul_one]
      exact one_smul _ _)
    have he := (inner_eq i j 1 v).mpr (by simpa only [inv_one, one_mul] using hv)
    rw [he] at h
    have hh := (L v).mp h
    change (1 * phi a v) • z = z at hh
    change phi a v • z = z
    simpa only [one_mul] using hh
  have hmapT : T.map m = K := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨diagonal i j p, ⟨p, rfl⟩, rfl⟩
  have hmapS : S.map m = P := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨phi a v, hv, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨p, rfl⟩ := (graph q).mp hq
      exact ⟨diagonal iP jP p, (graph _).mpr ⟨p, rfl⟩, rfl⟩
  have hm : Function.Injective (m.comp S.subtype) := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    rw [hS] at hv hw
    obtain ⟨p, rfl⟩ := hv
    obtain ⟨q, rfl⟩ := hw
    have hp : p = q := jP.injective (Subtype.ext h)
    exact Subtype.ext (congrArg (diagonal iP jP) hp)
  have hindex : K.relIndex P = T.relIndex S := by
    simpa only [hmapT, hmapS] using index_on_range hTS m hm
  have hKP : K ≤ P := by
    rw [← hmapT, ← hmapS]
    exact Subgroup.map_mono hTS
  refine ⟨hKP, fun g x y => ?_⟩
  by_cases hy : (point a b d g x, y) ∈ orbit a b d c e f z
  · change orbit a b d c e f z = _ at orbit_range
    have hr := hy
    rw [orbit_range] at hr
    obtain ⟨⟨g', h⟩, he⟩ := hr
    obtain ⟨α, hα, hx⟩ := (input_eq g g' x h).mp (congrArg Prod.fst he)
    let v₀ : A × F := (α, h⁻¹)
    have lift : ((g, 1) * phi (F := F) a v₀) • z = (point a b d g x, y) := by
      change ((word a b d).basis.act _ _, (word c e f).basis.act _ _) = _
      rw [act_point, act_point]
      change (point a b d ((g * a.toHom α) * 1) (r.element * (d.toHom (1 * h⁻¹))⁻¹),
        point c e f ((g * a.toHom α) * t.element) (s.element * (f.toHom (1 * h⁻¹))⁻¹)) = _
      simpa only [one_mul, mul_one, map_inv, inv_inv, ← hα] using he
    rw [if_pos hy, hindex]
    exact count_of_lift a b d c e f i j k r t s g x y input_eq v₀ lift hTS
  · rw [if_neg hy]
    haveI : IsEmpty (hits a b d c e f i j r t.element s.element g x y) := ⟨fun w => by
      obtain ⟨⟨u,v⟩, huv⟩ := Quotient.exists_rep w.val
      have hw : innerPoint i j (u,(v⁻¹)⁻¹) = w.val := by
        rw [inv_inv]
        exact huv
      have h := (hit_eq_parameters a b d c e f i j k r t s g x y input_eq (u,v⁻¹)).mp
        (hw ▸ w.property)
      exact hy ⟨_, h⟩⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private abbrev drawId {A F : Subgroup U} (p : Word A F) :=
  LabelledDrawing.ordinary (Diagram.id (R := Complex) p)

private noncomputable abbrev drawing
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) (fin : FiniteFibers b d i j r) :
    LabelledDrawing Complex (word a b d) (word c e f) :=
  let ga := Word.up a
  let gc := Word.up c
  let ai := Word.up i
  let fj := Word.down j
  let ck := Word.up k
  let lower := LabelledDrawing.compactProjection (R := Complex) b d i j [(1, ⟨r, fin⟩)]
  let center := LabelledDrawing.parallelUp (R := Complex) a i c k [(1, t)]
  let upper := LabelledDrawing.mixedMultiplication (R := Complex) e f k j [(1, s)]
  LabelledDrawing.vertical
    (LabelledDrawing.horizontal (drawId ga) lower)
    (LabelledDrawing.vertical
      (LabelledDrawing.ordinary (Diagram.unassociate ga ai fj))
      (LabelledDrawing.vertical
        (LabelledDrawing.horizontal center (drawId fj))
        (LabelledDrawing.vertical
          (LabelledDrawing.ordinary (Diagram.associate gc ck fj))
          (LabelledDrawing.horizontal (drawId gc) upper))))

private theorem drawing_count
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) (fin : FiniteFibers b d i j r)
    (g : G) (x : D) (y : (word c e f).basis.carrier) :
    coefficient a b d c e f (eval a b d c e f (drawing a b d c e f i j k r t s fin))
        (point a b d g x, y) =
      (Nat.card (hits a b d c e f i j r t.element s.element g x y) : Complex) := by
  classical
  have eq (x' : D) (w : fiber i j) :
      Generator.mixedProduct b d (lowerMap b d i j r w) = x' ↔
        lowerMap b d i j r w = Generator.mixedPair b d x' := by
    constructor
    · intro he
      apply (Generator.mixedEquiv b d).injective
      exact he.trans (Generator.mixedProduct_mixedPair b d x').symm
    · intro he
      rw [he, Generator.mixedProduct_mixedPair]
  have h (x' : D) : Set.Finite {w | Generator.mixedProduct b d (lowerMap b d i j r w) = x'} :=
    (fin (Generator.mixedPair b d x')).subset (fun w hw => (eq x' w).mp hw)
  have hset : (h x).toFinset = (fin (Generator.mixedPair b d x)).toFinset := by
    ext w
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using eq x w
  let target : fiber i j → (word c e f).basis.carrier := fun w =>
    outputOf a c e f g t.element s.element (Quotient.out w)
  let column : Finset (fiber i j) := (fin (Generator.mixedPair b d x)).toFinset
  let H := hits a b d c e f i j r t.element s.element g x y
  have hf : H.Finite := (fin (Generator.mixedPair b d x)).subset fun _ hw => hw.1
  have hfilter : column.filter (fun w => target w = y) = hf.toFinset := by
    apply Finset.ext
    intro w
    simp only [Finset.mem_filter, column, Set.Finite.mem_toFinset] <;> rfl
  have supplied := (CaseSixRightShapeEvaluation G A D F C E B a b d c e f i j k).1 r h t s g x
  change (drawing a b d c e f i j k r t s fin).interpret.eval.toLinearMap
    (Finsupp.single (point a b d g x) 1) =
      ∑ w ∈ (h x).toFinset, Finsupp.single (target w) 1 at supplied
  rw [hset] at supplied
  change (drawing a b d c e f i j k r t s fin).interpret.eval.toLinearMap
    (Finsupp.single (point a b d g x) 1) y = (Nat.card H : Complex)
  rw [supplied, Finset.sum_apply']
  simp only [Finsupp.single_apply, ← Finset.sum_filter]
  change (∑ w ∈ column.filter (fun w => target w = y), (1 : Complex)) = _
  letI := hf.fintype
  rw [hfilter, Finset.sum_const, nsmul_eq_mul, mul_one, Set.Finite.card_toFinset hf]
  exact congrArg (Nat.cast : Nat → Complex) (Nat.card_eq_fintype_card (α := H)).symm

private theorem right_eval [Finite A] [Finite F]
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) :
    let z := base a b d c e f r.element t.element s.element
    let P := projected a b d c e f z
    let K := (F.subtype.comp j.toHom).range
    K ≤ P ∧
    (∃ fin : FiniteFibers b d i j r, ∀ z',
      coefficient a b d c e f (eval a b d c e f (drawing a b d c e f i j k r t s fin)) z' =
        matrix a b d c e f (orbit a b d c e f z) (K.relIndex P) z') ∧
    ∀ g x y, Nat.card (hits a b d c e f i j r t.element s.element g x y) =
      @ite Nat ((point a b d g x, y) ∈ orbit a b d c e f z)
        (Classical.propDecidable _) (K.relIndex P) 0 := by
  classical
  intro z P K
  obtain ⟨hKP, hcount⟩ := right_count a b d c e f i j k r t s
  let fin := finiteFibers_of_bases b d i j r
  refine ⟨hKP, ⟨fin, ?_⟩, hcount⟩
  rintro ⟨x, y⟩
  obtain ⟨g, x, rfl⟩ := point_surjective a b d x
  change coefficient a b d c e f (eval a b d c e f (drawing a b d c e f i j k r t s fin))
    (point a b d g x, y) = matrix a b d c e f (orbit a b d c e f z) (K.relIndex P) (point a b d g x, y)
  have h := hcount g x y
  change Nat.card (hits a b d c e f i j r t.element s.element g x y) =
      @ite Nat ((point a b d g x, y) ∈ orbit a b d c e f z) (Classical.propDecidable _) (K.relIndex P) 0 at h
  rw [drawing_count, h]
  by_cases hy : (point a b d g x, y) ∈ orbit a b d c e f z <;>
    simp only [matrix, hy, if_true, if_false, Nat.cast_zero]

end Geometry
private theorem swaps_map_conj (q : Sinf) (P : Subgroup Sinf) :
    swaps (P.map (MulAut.conj q).toMonoidHom) =
      (swaps P).map (MulAut.conj q).toMonoidHom := by
  rw [swaps, swaps, MonoidHom.map_closure]
  congr 1
  have transposition (σ : Sinf) :
      Equiv.Perm.IsSwap ((MulAut.conj q σ : Sinf) : Equiv.Perm Nat) ↔
        Equiv.Perm.IsSwap (σ : Equiv.Perm Nat) := by
    have forward (g σ : Equiv.Perm Nat) (h : Equiv.Perm.IsSwap σ) :
        Equiv.Perm.IsSwap (g * σ * g⁻¹) := by
      obtain ⟨x, y, hxy, rfl⟩ := h
      exact ⟨g x, g y, fun h => hxy (g.injective h), Equiv.swap_apply_apply g x y |>.symm⟩
    change Equiv.Perm.IsSwap ((q : Equiv.Perm Nat) * σ.val * (q : Equiv.Perm Nat)⁻¹) ↔ _
    exact ⟨fun h => by simpa [mul_assoc] using forward (q : Equiv.Perm Nat)⁻¹ _ h,
      forward q.val σ.val⟩
  ext σ
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hs⟩
    exact ⟨x, ⟨hx, (transposition x).mp hs⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (transposition x).mpr hs⟩

private def restrictEmbedding {W : Type*} [Group W] {P K A : Subgroup W}
    (hK : K ≤ P) (i : ConjEmbedding P A) : ConjEmbedding K A :=
  ⟨i.toHom.comp (Subgroup.inclusion hK), by
    obtain ⟨q, hq⟩ := i.hasRepresentative
    exact ⟨q, fun k => hq (Subgroup.inclusion hK k)⟩⟩

private def restrictDot {W : Type*} [Group W] {P K A F D : Subgroup W}
    (hK : K ≤ P) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (i : ConjEmbedding P A) (j : ConjEmbedding P F) (r : Dot (b.comp i) (d.comp j)) :
    Dot (b.comp (restrictEmbedding hK i)) (d.comp (restrictEmbedding hK j)) :=
  ⟨r.element, fun k => r.intertwines (Subgroup.inclusion hK k)⟩

private theorem finite_word_of_groups {W : Type*} [Group W] {G A D F : Subgroup W}
    [Finite G] [Finite D]
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :
    Finite (word a b d).basis.carrier :=
  Finite.of_surjective (fun p : G × D => point a b d p.1 p.2) (by
    intro x
    obtain ⟨g, x', h⟩ := point_surjective a b d x
    exact ⟨(g, x'), h⟩)

private theorem projected_finite {W : Type*} [Group W] {G A D F C E : Subgroup W}
    [Finite F] (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
    (z : Pair a b d c e f) : Finite (projected a b d c e f z) := by
  let P := projected a b d c e f z
  have hPF : P ≤ F := by
    rintro x ⟨q, _, rfl⟩
    exact q.2.property
  exact Finite.of_injective (Subgroup.inclusion hPF) (Subgroup.inclusion_injective hPF)

private theorem orbit_index_transport {G A D F C E : Subgroup Sinf}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
    (z z' : Pair a b d c e f) (hz' : z' ∈ orbit a b d c e f z) :
    (swaps (projected a b d c e f z')).relIndex (projected a b d c e f z') =
      (swaps (projected a b d c e f z)).relIndex (projected a b d c e f z) := by
  letI := action a b d c e f
  obtain ⟨q, rfl⟩ := hz'
  let qF : Sinf := q.2
  let J := (MulAut.conj qF).toMonoidHom
  have conj_proj : (projectHom G F).comp (MulAut.conj q).toMonoidHom =
      J.comp (projectHom G F) := by ext v; rfl
  have he : projected a b d c e f (q • z) = (projected a b d c e f z).map J := by
    unfold projected stabilizer
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, conj_proj,
      Subgroup.map_map]
  rw [he, swaps_map_conj]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj qF).injective

private theorem indexed_expansion {W : Type*} [Group W] {G A D F C E : Subgroup W}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
    [Finite (Pair a b d c e f)]
    (M : Biset.Hom Complex (word a b d).basis (word c e f).basis)
    (invariant : ∀ z z', z' ∈ orbit a b d c e f z →
      coefficient a b d c e f M z' = coefficient a b d c e f M z)
    (oneOn : ∀ z, coefficient a b d c e f M z ≠ 0 → coefficient a b d c e f M z = 1)
    (valid : Set (Pair a b d c e f) → LabelledDrawing Complex (word a b d) (word c e f) → Prop) :
    let S : Set (Set (Pair a b d c e f)) :=
      {O | ∃ z, O = orbit a b d c e f z ∧ coefficient a b d c e f M z ≠ 0}
    (∀ O : ↥S, ∃ D, valid O.val D ∧ ∀ z',
      coefficient a b d c e f (eval a b d c e f D) z' =
        matrix a b d c e f O.val 1 z') →
    ∃ expansion : IndexedDrawing Complex (word a b d) (word c e f) ↥S,
      (∀ O : ↥S, O ∈ expansion.indices) ∧
      (∀ O : ↥S, valid O.val (expansion.summand O) ∧ ∀ z',
        coefficient a b d c e f (eval a b d c e f (expansion.summand O)) z' =
          matrix a b d c e f O.val 1 z') ∧
      M.toLinearMap = expansion.eval := by
  classical
  letI := action a b d c e f
  intro S terms
  choose D hD using terms
  letI : Fintype ↥S := Fintype.ofFinite _
  let expansion : IndexedDrawing Complex (word a b d) (word c e f) ↥S :=
    ⟨Finset.univ, D⟩
  refine ⟨expansion, fun O => Finset.mem_univ O, hD, ?_⟩
  apply Finsupp.lhom_ext
  intro x q
  rw [← Finsupp.smul_single_one x q, map_smul, map_smul]
  congr 1
  ext y
  let z : Pair a b d c e f := (x,y)
  let coef := coefficient a b d c e f M
  let I := matrix a b d c e f
  change coef z = (expansion.eval (Finsupp.single x 1)) y
  rw [IndexedDrawing.eval_apply, Finset.sum_apply']
  change coef z = ∑ O : ↥S, coefficient a b d c e f (eval a b d c e f (D O)) z
  simp_rw [fun O => (hD O).2 z]
  change coef z = ∑ O : ↥S, I O.val 1 z
  by_cases h : coef z = 0
  · rw [h, Finset.sum_eq_zero]
    intro O _
    apply if_neg
    intro hz
    obtain ⟨z', hO, hz'⟩ := O.property
    rw [hO] at hz
    exact hz' ((invariant z' z hz).symm.trans h)
  · let O : ↥S := ⟨orbit a b d c e f z, ⟨z,rfl,h⟩⟩
    rw [Finset.sum_eq_single O]
    · have hz : z ∈ orbit a b d c e f z := MulAction.mem_orbit_self z
      change coef z = @ite Complex (z ∈ orbit a b d c e f z)
        (Classical.propDecidable _) ((1 : Nat) : Complex) 0
      rw [if_pos hz, Nat.cast_one]
      exact oneOn z h
    · intro O' _ hne
      apply if_neg
      intro hz
      obtain ⟨z', hO', _⟩ := O'.property
      rw [hO'] at hz
      exact hne (Subtype.ext (hO'.trans (MulAction.orbit_eq_iff.mpr hz).symm))
    · simp

end OrbitMultiplicity

theorem ParabolicRightOrbitMultiplicity : (
let Sinf : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ | Equiv.Perm.IsSwap σ}
let U := ↥Sinf
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun X => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
let parabolic : Subgroup U → Prop :=
  fun H => ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, Finset.Nonempty (blocks l)) ∧
    Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    Subgroup.map (Subgroup.subtype Sinf) H = iSup (fun l => blockSym (blocks l))
∀ (G A D F C E : Subgroup U),
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  ∀ (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let ga := up a
  let ad := down b
  let df := up d
  let gc := up c
  let ce := down e
  let ef := up f
  let bottom := tensor ga (tensor ad df)
  let top := tensor gc (tensor ce ef)
  let X := MackeyDiagrams.Word.basis bottom
  let Y := MackeyDiagrams.Word.basis top
  let Pair := X.carrier × Y.carrier
  let input := fun (g : G) (x : D) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis ga)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis gc)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  let pair := fun (r : D) (t : G) (s : E) => (input 1 r, output t s)
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let orbit : Pair → Set Pair := MulAction.orbit (G × F)
  let stabilizer : Pair → Subgroup (G × F) := MulAction.stabilizer (G × F)
  let projected := fun z : Pair =>
    Subgroup.map (MonoidHom.comp (Subgroup.subtype F) (MonoidHom.snd G F)) (stabilizer z)
  let swaps := fun P : Subgroup U =>
    Subgroup.closure {σ : U | σ ∈ P ∧ Equiv.Perm.IsSwap (σ : Equiv.Perm Nat)}
  let coefficient := fun (M : MackeyDiagrams.Biset.Hom Complex X Y) (z : Pair) =>
    MackeyDiagrams.Biset.Hom.toLinearMap M (Finsupp.single z.1 (1 : Complex)) z.2
  let matrix := fun (O : Set Pair) (n : Nat) (z : Pair) =>
    @ite Complex (z ∈ O) (Classical.propDecidable (z ∈ O)) (n : Complex) 0
  let RightData := fun B' : Subgroup U =>
    Σ (i : MackeyDiagrams.ConjEmbedding B' A)
      (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C),
      MackeyDiagrams.Dot (comp b i) (comp d j) ×
      MackeyDiagrams.Dot (comp a i) (comp c k) ×
      MackeyDiagrams.Dot (comp e k) (comp f j)
  let labels : {B' : Subgroup U} → RightData B' → D × G × E :=
    fun ⟨_, _, _, r, t, s⟩ =>
      (MackeyDiagrams.Dot.element r, MackeyDiagrams.Dot.element t, MackeyDiagrams.Dot.element s)
  let representative := fun {B'} (data : RightData B') =>
    let (r, t, s) := labels data
    pair r t s
  let toA : {B' : Subgroup U} → RightData B' → (B' →* A) :=
    fun ⟨i, _, _, _, _, _⟩ => MackeyDiagrams.ConjEmbedding.toHom i
  let toF : {B' : Subgroup U} → RightData B' → (B' →* F) :=
    fun ⟨_, j, _, _, _, _⟩ => MackeyDiagrams.ConjEmbedding.toHom j
  let toC : {B' : Subgroup U} → RightData B' → (B' →* C) :=
    fun ⟨_, _, k, _, _, _⟩ => MackeyDiagrams.ConjEmbedding.toHom k
  let restricts := fun {P K : Subgroup U}
      (term : RightData K) (full : RightData P) (hK : K ≤ P) =>
    labels term = labels full ∧
    toA term = MonoidHom.comp (toA full) (Subgroup.inclusion hK) ∧
    toF term = MonoidHom.comp (toF full) (Subgroup.inclusion hK) ∧
    toC term = MonoidHom.comp (toC full) (Subgroup.inclusion hK)
  let image := fun {B'} (data : RightData B') =>
    MonoidHom.range (MonoidHom.comp (Subgroup.subtype F) (toF data))
  let isInclusion := fun {B'} (data : RightData B') =>
    ∀ h : B', (toF data h : U) = (h : U)
  let Fiber : {B' : Subgroup U} → RightData B' → Type :=
    fun ⟨i, j, _, _, _, _⟩ => (MackeyDiagrams.Word.basis (tensor (up i) (down j))).carrier
  let lowerMap : {B' : Subgroup U} → (data : RightData B') → Fiber data →
      (MackeyDiagrams.Word.basis (tensor ad df)).carrier :=
    fun ⟨i, j, _, r, _, _⟩ => MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r
  let finiteFibers := fun {B'} (data : RightData B') =>
    ∀ z, Set.Finite {w : Fiber data | lowerMap data w = z}
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let rightDiagram : {B' : Subgroup U} → (data : RightData B') → finiteFibers data →
      MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨i, j, k, r, t, s⟩ finite =>
      let ai := up i
      let fj := down j
      let ck := up k
      let lower := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex) b d i j [(1, ⟨r, finite⟩)]
      let middle := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex) a i c k [(1, t)]
      let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex) e f k j [(1, s)]
      MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId ga) lower)
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal middle (drawId fj))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
              (MackeyDiagrams.LabelledDrawing.horizontal (drawId gc) upper))))
  let rightCount := fun {B'} (data : RightData B') (g : G) (x : D) (y : Y.carrier) =>
    let (_, t, s) := labels data
    Nat.card {w : Fiber data //
      lowerMap data w = MackeyDiagrams.Generator.mixedPair b d x ∧
      (let v : A × F := Quotient.out w
       output (g * MackeyDiagrams.ConjEmbedding.toHom a v.1 * t)
         (s * MackeyDiagrams.ConjEmbedding.toHom f v.2)) = y}
  let realizes := fun {B'} (data : RightData B') (O : Set Pair) (n : Nat) =>
    orbit (representative data) = O ∧
      ∃ finite : finiteFibers data, ∀ z : Pair,
        coefficient (eval (rightDiagram data finite)) z = matrix O n z
  let LeftUpperFiber := fun {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (w : MackeyDiagrams.ConjEmbedding E B)
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) =>
    ∀ z, Set.Finite {p | MackeyDiagrams.Generator.mixedMultiplicationBasis u w c e s p = z}
  let leftDiagram := fun {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (r : MackeyDiagrams.Dot (comp u a) (comp v b))
      (t : MackeyDiagrams.Dot (comp v d) (comp w f))
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) (finite : LeftUpperFiber u w s) =>
    let lower := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex) u v a b [(1, r)]
    let middle := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex) v d w f [(1, t)]
    let upper := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex) u w c e [(1, ⟨s, finite⟩)]
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal lower (drawId df))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate (down u) (up v) df))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down u)) middle)
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate (down u) (up w) ef))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.horizontal upper (drawId ef))
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ce ef)))))))
  (∀ (M : MackeyDiagrams.Biset.Hom Complex X Y) (z z' : Pair),
    z' ∈ orbit z → coefficient M z' = coefficient M z) ∧
  (∀ z : Pair, ∃ (r : D) (t : G) (s : E), z ∈ orbit (pair r t s)) ∧
  (∀ (r : D) (t : G) (s : E),
    let z := pair r t s
    let P := projected z
    let L := swaps P
    (∀ h : F, (h : U) ∈ P ↔ ∃ (α : A) (κ : C),
      r * MackeyDiagrams.ConjEmbedding.toHom d h * r⁻¹ = MackeyDiagrams.ConjEmbedding.toHom b α ∧
      s * MackeyDiagrams.ConjEmbedding.toHom f h * s⁻¹ = MackeyDiagrams.ConjEmbedding.toHom e κ ∧
      MackeyDiagrams.ConjEmbedding.toHom a α = t * MackeyDiagrams.ConjEmbedding.toHom c κ * t⁻¹) ∧
    (∃ full : RightData P,
      labels full = (r, t, s) ∧ isInclusion full ∧
      (∀ q : G × F, q ∈ stabilizer z ↔ ∃ h : P,
        q = (MackeyDiagrams.ConjEmbedding.toHom a (toA full h), toF full h)) ∧
      (∀ (K : Subgroup U) (hK : K ≤ P), parabolic K →
        ∃ term : RightData K,
          restricts term full hK ∧ realizes term (orbit z) (Subgroup.relIndex K P)) ∧
      (∃ (hL : L ≤ P) (term : RightData L),
        parabolic L ∧ restricts term full hL ∧ isInclusion term ∧
        realizes term (orbit z) (Subgroup.relIndex L P)))) ∧
  (∀ (B' : Subgroup U), parabolic B' → ∀ data : RightData B',
    let z := representative data
    let P := projected z
    let K := image data
    let n := Subgroup.relIndex K P
    K ≤ P ∧ realizes data (orbit z) n ∧
      ∀ (g : G) (x : D) (y : Y.carrier),
        rightCount data g x y =
          @ite Nat ((input g x, y) ∈ orbit z)
            (Classical.propDecidable ((input g x, y) ∈ orbit z)) n 0) ∧
  (∀ z : Pair,
    let P := projected z
    let n := Subgroup.relIndex (swaps P) P
    IsLeast {m : Nat | ∃ (B' : Subgroup U) (term : RightData B'),
      parabolic B' ∧ realizes term (orbit z) m} n ∧
    (n = 1 ↔ parabolic P) ∧
    (∀ z' : Pair, z' ∈ orbit z → Subgroup.relIndex (swaps (projected z')) (projected z') = n)) ∧
  (∀ (B : Subgroup U), parabolic B →
    ∀ (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (r : MackeyDiagrams.Dot (comp u a) (comp v b))
      (t : MackeyDiagrams.Dot (comp v d) (comp w f))
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) (finite : LeftUpperFiber u w s),
    let M := eval (leftDiagram u v w r t s finite)
    let S : Set (Set Pair) := {O | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0}
    ∃ expansion : MackeyDiagrams.IndexedDrawing Complex bottom top ↥S,
      (∀ O : ↥S, O ∈ MackeyDiagrams.IndexedDrawing.indices expansion) ∧
      (∀ O : ↥S,
        ∃ (r₀ : D) (t₀ : G) (s₀ : E),
          let z := pair r₀ t₀ s₀
          let P := projected z
          O.val = orbit z ∧ parabolic P ∧
          ∃ (data : RightData P) (fiberProof : finiteFibers data),
            labels data = (r₀, t₀, s₀) ∧ isInclusion data ∧
            MackeyDiagrams.IndexedDrawing.summand expansion O = rightDiagram data fiberProof ∧
            ∀ z' : Pair,
              coefficient (eval (MackeyDiagrams.IndexedDrawing.summand expansion O)) z' =
                matrix O.val 1 z') ∧
      MackeyDiagrams.Biset.Hom.toLinearMap M = MackeyDiagrams.IndexedDrawing.eval expansion)

) :=
(by
  classical
  intro Sinf U blockSym parabolic G A D F C E hG hA hD hF hC hE a b d c e f
    up down tensor comp ga ad df gc ce ef bottom top X Y Pair input output pair
    orbit stabilizer projected swaps coefficient matrix RightData labels representative
    toA toF toC restricts image isInclusion Fiber lowerMap finiteFibers drawId eval
    rightDiagram rightCount realizes LeftUpperFiber leftDiagram
  letI : MulAction (G × F) Pair := OrbitMultiplicity.action a b d c e f
  haveI : Finite A := OrbitMultiplicity.parabolic_finite hA
  haveI : Finite F := OrbitMultiplicity.parabolic_finite hF
  let supplier := RightOrbitDiagramFromProjectedStabilizer G A D F C E a b d c e f
  have invariant (M : MackeyDiagrams.Biset.Hom Complex X Y) (z z' : Pair) :
      z' ∈ orbit z → coefficient M z' = coefficient M z :=
    supplier.1 M z z'
  have normalized (z : Pair) : ∃ r t s, z ∈ orbit (pair r t s) := supplier.2.1 z
  have orbit_eq {z z' : Pair} (hz : z ∈ orbit z') : orbit z = orbit z' :=
    MulAction.orbit_eq_iff.mpr hz
  have orbit_self (z : Pair) : z ∈ orbit z := MulAction.mem_orbit_self z
  have extremal (z : Pair) : IsGreatest
      {K : Subgroup U | parabolic K ∧ K ≤ projected z} (swaps (projected z)) := by
    letI := OrbitMultiplicity.projected_finite a b d c e f z
    exact OrbitMultiplicity.parabolic_extremal (projected z)
  -- Ian Xiao, Proposition 8.7 and proof, archived source/mackey-bimodules.pdf
  -- pp. 39–40 and revised published PDF pp. 41–42.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:parabolic-three-unscaled
  -- The portal presents the proof in paragraphs. Steps 1–6 refer to its
  -- normalization, vertex, fiber, minimization, and expansion arguments,
  -- with the expansion checked last because its Lean statement uses the
  -- typed indexed drawing and the coefficient formula.
  -- Steps 1–3 of § 8.3. Use the normalized representative and the graph from
  -- Theorem 6.7. Finite boundary groups make every lower projection finite.
  -- Step 4. Identify the exact hits in the right drawing with a coset-tower
  -- fiber. The inverse in the F coordinate reconciles the two action conventions.
  have arbitrary (B' : Subgroup U) (data : RightData B') :
      image data ≤ projected (representative data) ∧
      realizes data (orbit (representative data))
        ((image data).relIndex (projected (representative data))) ∧
      ∀ g x y, rightCount data g x y =
        @ite Nat ((input g x, y) ∈ orbit (representative data))
          (Classical.propDecidable _) ((image data).relIndex (projected (representative data))) 0 := by
    rcases data with ⟨i,j,k,r,t,s⟩
    obtain ⟨hle, ⟨fin, hc⟩, hcount⟩ := OrbitMultiplicity.right_eval a b d c e f i j k r t s
    exact ⟨hle, ⟨rfl, fin, hc⟩, hcount⟩
  have restrictRealizes {P K : Subgroup U} (hK : K ≤ P) (full : RightData P)
      (hj : isInclusion full) (z : Pair) (hz : representative full = z)
      (hP : P = projected z) :
      ∃ term : RightData K, restricts term full hK ∧ isInclusion term ∧
        realizes term (orbit z) (K.relIndex P) := by
    rcases full with ⟨i,j,k,r,t,s⟩
    let i' := OrbitMultiplicity.restrictEmbedding hK i
    let j' := OrbitMultiplicity.restrictEmbedding hK j
    let k' := OrbitMultiplicity.restrictEmbedding hK k
    let r' := OrbitMultiplicity.restrictDot hK b d i j r
    let t' := OrbitMultiplicity.restrictDot hK a c i k t
    let s' := OrbitMultiplicity.restrictDot hK e f k j s
    let term : RightData K := ⟨i',j',k',r',t',s'⟩
    have hInc : isInclusion term := fun p => hj (Subgroup.inclusion hK p)
    have hImage : image term = K := by
      ext p
      constructor
      · rintro ⟨k, rfl⟩
        change (toF term k : U) ∈ K
        rw [hInc k]
        exact k.property
      · intro hp
        exact ⟨⟨p,hp⟩, hInc ⟨p,hp⟩⟩
    have hrep : representative term = z := hz
    have ht := (arbitrary K term).2.1
    rw [hrep, hImage, ← hP] at ht
    exact ⟨term, ⟨rfl,rfl,rfl,rfl⟩, hInc, ht⟩
  refine ⟨invariant, normalized, ?_, fun B' _ data => arbitrary B' data, ?_, ?_⟩
  · intro r t s z P L
    obtain ⟨equations, _, _, i, j, k, rd, td, sd, hj, hr, ht, hs, graph, _, _⟩ :=
      supplier.2.2.1 r t s
    let full : RightData P := ⟨i,j,k,rd,td,sd⟩
    have he : labels full = (r,t,s) := Prod.ext hr (Prod.ext ht hs)
    have hrep : representative full = z := by
      change pair (labels full).1 (labels full).2.1 (labels full).2.2 = pair r t s
      rw [he]
    have hL := (extremal z).1
    refine ⟨equations, full, he, hj, graph, ?_, ?_⟩
    · intro K hK _
      obtain ⟨term, hrest, _, hreal⟩ := restrictRealizes hK full hj z hrep rfl
      exact ⟨term, hrest, hreal⟩
    · obtain ⟨term, hrest, hinc, hreal⟩ := restrictRealizes hL.2 full hj z hrep rfl
      exact ⟨hL.2, term, hL.1, hrest, hinc, hreal⟩
  · -- Step 5. Lemma 7.2 supplies the greatest parabolic subgroup.
    -- Since the projected stabilizer is finite, the relative indices are
    -- positive ordinary natural numbers. One orbit entry recovers the integer.
    intro z P n
    letI : Finite P := OrbitMultiplicity.projected_finite a b d c e f z
    have hL := extremal z
    refine ⟨⟨?_, ?_⟩, ?_, fun z' hz' =>
      OrbitMultiplicity.orbit_index_transport a b d c e f z z' hz'⟩
    · obtain ⟨r,t,s,hz⟩ := normalized z
      let z₀ := pair r t s
      have ho : orbit z₀ = orbit z := (orbit_eq hz).symm
      obtain ⟨_, _, _, i, j, k, rd, td, sd, hj, hr, ht, hs, _, _, _⟩ :=
        supplier.2.2.1 r t s
      let full : RightData (projected z₀) := ⟨i,j,k,rd,td,sd⟩
      have he : labels full = (r,t,s) := Prod.ext hr (Prod.ext ht hs)
      have hrep : representative full = z₀ := by
        change pair (labels full).1 (labels full).2.1 (labels full).2.2 = pair r t s
        rw [he]
      have hL₀ := (extremal z₀).1
      obtain ⟨term, _, _, hreal⟩ := restrictRealizes hL₀.2 full hj z₀ hrep rfl
      have hi := OrbitMultiplicity.orbit_index_transport a b d c e f z₀ z hz
      change n = (swaps (projected z₀)).relIndex (projected z₀) at hi
      rw [ho, ← hi] at hreal
      exact ⟨swaps (projected z₀), term, hL₀.1, hreal⟩
    · rintro m ⟨B', term, hp, ho, finite, hm⟩
      let z₀ := representative term
      let P₀ := projected z₀
      let K := image term
      letI : Finite P₀ := OrbitMultiplicity.projected_finite a b d c e f z₀
      letI : Finite (swaps P₀) :=
        Finite.of_injective (Subgroup.inclusion (extremal z₀).1.2)
          (Subgroup.inclusion_injective (extremal z₀).1.2)
      obtain ⟨hKP, ⟨_, fin', he⟩, _⟩ := arbitrary B' term
      have hpK : parabolic K := OrbitMultiplicity.conjugate_parabolic (by
        rcases term with ⟨i,j,k,r,t,s⟩
        exact j) hp
      have hz₀ : z₀ ∈ orbit z := ho ▸ orbit_self z₀
      have hme : m = K.relIndex P₀ := by
        have h := (hm z₀).symm.trans (he z₀)
        change matrix (orbit z) m z₀ = matrix (orbit z₀) (K.relIndex P₀) z₀ at h
        have h' : (m : Complex) = (K.relIndex P₀ : Complex) := by
          simpa only [matrix, if_pos hz₀, if_pos (orbit_self z₀)] using h
        exact Nat.cast_injective h'
      have hKL : K ≤ swaps P₀ := (extremal z₀).2 ⟨hpK, hKP⟩
      have hi := OrbitMultiplicity.orbit_index_transport a b d c e f z z₀ hz₀
      change (swaps P₀).relIndex P₀ = n at hi
      change n ≤ m
      rw [hme, ← hi, ← Subgroup.relIndex_mul_relIndex K (swaps P₀) P₀ hKL (extremal z₀).1.2]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero orbitMultiplicityFinite)
    · change (swaps P).relIndex P = 1 ↔ parabolic P
      rw [Subgroup.relIndex_eq_one]
      exact ⟨fun h => le_antisymm h hL.1.2 ▸ hL.1.1,
        fun hP => hL.2 ⟨hP, le_rfl⟩⟩
  · -- Step 6. Use the Case 5 supplier on the actual left drawing. Its
    -- finite-fiber witness and the endpoint witness are proof-irrelevant.
    -- The index set is the finite set of supported orbits of the pair basis.
    intro B hB u v w r t s finite M S
    haveI : Finite G := OrbitMultiplicity.parabolic_finite hG
    haveI : Finite D := OrbitMultiplicity.parabolic_finite hD
    haveI : Finite E := OrbitMultiplicity.parabolic_finite hE
    letI : Finite X.carrier := OrbitMultiplicity.finite_word_of_groups a b d
    letI : Finite Y.carrier := OrbitMultiplicity.finite_word_of_groups c e f
    obtain ⟨fin', sourceMap, targetMap, _, _, _, _, _, supported, _⟩ :=
      SupportedLeftOrbitProjectedStabilizer hG hA hD hF hC hE hB a b d c e f u v w r t s
    have oneOn (z : Pair) (hz : coefficient M z ≠ 0) : coefficient M z = 1 :=
      (supported z hz).2.2.2.2
    let valid (O : Set Pair) (Dg : MackeyDiagrams.LabelledDrawing Complex bottom top) :=
      ∃ (r₀ : D) (t₀ : G) (s₀ : E),
        let z := pair r₀ t₀ s₀
        let P := projected z
        O = orbit z ∧ parabolic P ∧
        ∃ (data : RightData P) (fiberProof : finiteFibers data),
          labels data = (r₀, t₀, s₀) ∧ isInclusion data ∧ Dg = rightDiagram data fiberProof
    have terms (O : ↥S) :
        ∃ Dg, valid O.val Dg ∧ ∀ z',
          coefficient (eval Dg) z' = matrix O.val 1 z' := by
      obtain ⟨z, hO, hz⟩ := O.property
      obtain ⟨r₀,t₀,s₀,hnorm⟩ := normalized z
      let z₀ := pair r₀ t₀ s₀
      have hO' : O.val = orbit z₀ := hO.trans (orbit_eq hnorm)
      have hz₀ : coefficient M z₀ ≠ 0 := by
        rw [← invariant M z₀ z hnorm]
        exact hz
      have hpar := (supported z₀ hz₀).2.2.2.1
      change OrbitMultiplicity.Parabolic ((Subgroup.map (MonoidHom.snd G F) (stabilizer z₀)).map F.subtype) at hpar
      rw [Subgroup.map_map] at hpar
      obtain ⟨_, _, _, i, j, k, rd, td, sd, hj, hr, ht, hs, _, _, fullEval⟩ :=
        supplier.2.2.1 r₀ t₀ s₀
      obtain ⟨_, fin, hcoef⟩ := fullEval M hz₀
      let data : RightData (projected z₀) := ⟨i,j,k,rd,td,sd⟩
      refine ⟨rightDiagram data fin, ⟨r₀,t₀,s₀,hO',hpar,data,fin,
        Prod.ext hr (Prod.ext ht hs),hj,rfl⟩, ?_⟩
      intro z'
      rw [hO']
      simpa only [matrix, Nat.cast_one] using hcoef z'
    obtain ⟨expansion, hall, hvalid, heval⟩ :=
      OrbitMultiplicity.indexed_expansion a b d c e f M (invariant M) oneOn valid terms
    refine ⟨expansion, hall, ?_, heval⟩
    intro O
    obtain ⟨hO, hc⟩ := hvalid O
    obtain ⟨x, g, y, horbit, hpar, dat, fin, hlab, hinc, hdraw⟩ := hO
    exact ⟨x,g,y,horbit,hpar,dat,fin,hlab,hinc,hdraw,hc⟩
)
#print axioms ParabolicRightOrbitMultiplicity
