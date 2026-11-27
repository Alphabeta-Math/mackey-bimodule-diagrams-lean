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

end Geometry
end OrbitMultiplicity
