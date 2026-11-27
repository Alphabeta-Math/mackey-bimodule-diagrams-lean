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
    rw [map_mul, map_inv]
    constructor
    · intro h
      have he := congrArg (fun w : Pair a b d c e f => (((g, 1) * phi (F := F) a v₀)⁻¹) • w) h
      simpa [← mul_smul, mul_inv_rev, mul_assoc] using he
    · intro h
      have he := congrArg (fun w : Pair a b d c e f => ((g, 1) * phi (F := F) a v₀) • w) h
      simpa [← mul_smul, mul_assoc] using he
  have eq_mem (q : (A × F) ⧸ T) :
      E q ∈ hits a b d c e f i j r t.element s.element g x y ↔
        (Subgroup.quotientEquivProdOfLE hTS q).1 = QuotientGroup.mk v₀ := by
    refine Quotient.inductionOn q fun v => ?_
    change innerPoint i j (v.1, v.2⁻¹) ∈ _ ↔ QuotientGroup.mk v = QuotientGroup.mk v₀
    rw [hit_eq_parameters a b d c e f i j k r t s g x y input_eq, eq_act, eq_comm,
      QuotientGroup.eq]
  exact (Nat.card_congr (E.subtypeEquiv eq_mem).symm).trans (count_tower hTS v₀)

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
  obtain ⟨_, orbit_range, input_eq, iP, jP, _, _, _, _, _, _, graph, _, _⟩ :=
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
    have h := (L 1).mpr (by change (1 : G × F) • z = z; exact one_smul _ _)
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
  refine ⟨hmapT ▸ hmapS ▸ Subgroup.map_mono hTS, fun g x y => ?_⟩
  by_cases hy : (point a b d g x, y) ∈ orbit a b d c e f z
  · have hr := hy
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
      have hw : innerPoint i j (u,(v⁻¹)⁻¹) = w.val := by simpa only [inv_inv] using huv
      have h := (hit_eq_parameters a b d c e f i j k r t s g x y input_eq (u,v⁻¹)).mp
        (hw ▸ w.property)
      exact hy ⟨_, h⟩⟩
    exact Nat.card_eq_zero_of_isEmpty _

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
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using eq x w
  have supplied := (CaseSixRightShapeEvaluation G A D F C E B a b d c e f i j k).1 r h t s g x
  change (drawing a b d c e f i j k r t s fin).interpret.eval.toLinearMap
    (Finsupp.single (point a b d g x) 1) =
      ∑ w ∈ (h x).toFinset, Finsupp.single (outputOf a c e f g t.element s.element (Quotient.out w)) 1
    at supplied
  rw [hset] at supplied
  unfold coefficient eval
  rw [supplied, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, ← Finset.sum_filter]
  let H := hits a b d c e f i j r t.element s.element g x y
  have hf : H.Finite := (fin (Generator.mixedPair b d x)).subset fun _ hw => hw.1
  have he : ((fin (Generator.mixedPair b d x)).toFinset.filter
      (fun w => outputOf a c e f g t.element s.element (Quotient.out w) = y)) = hf.toFinset := by
    ext w
    simp [H, hits]
  rw [he, Finset.sum_const, nsmul_eq_mul, mul_one, ← Set.Finite.card_toFinset hf]

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
  rw [drawing_count, hcount g x y]
  by_cases hy : (point a b d g x, y) ∈ orbit a b d c e f z <;> simp [matrix, hy]

end Geometry
end OrbitMultiplicity
