import MackeyDiagrams
import Proofs.FiniteParabolicJoinOfFamily
import Proofs.ParabolicExtremalOutsideRestrictionRegions
import Proofs.ExtremalParabolicsOfFiniteGroup
import Proofs.EvaluationForTwoProjections
import Proofs.ReplacementForTwoMultiplications
import Proofs.FiniteParabolicClosure

set_option maxHeartbeats 2000000

-- Xiao, Lemma 6.3 and Theorem 6.5 (Cases 1 and 3). Adapt the project's
-- checked singleton coefficient and column calculations from
-- Proofs.ParabolicExtremalOutsideRestrictionRegions to these marked diagrams.
-- The public replacement statements give an existential normalization or
-- replacement, so the local calculations identify the particular parameter.
namespace CommonRightRegionAux
open MackeyDiagrams

private abbrev conj {V : Type*} [Group V] (p : V) (H : Subgroup V) :=
  H.map (MulAut.conj p).toMonoidHom

section
variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev leftParameter {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :=
  a.toHom z.element⁻¹ * x.element * b.toHom y.element

private abbrev rightParameter {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :=
  m.element * j.toHom n.element * ell.element⁻¹

end
section
variable {U : Type*} [Group U]

private def inclusion {K : Subgroup U} (S : Subgroup K) : ConjEmbedding (S.map K.subtype) K :=
  ⟨Subgroup.inclusion (Subgroup.map_subtype_le S), ⟨1, fun _ => by simp⟩⟩

private theorem inclusion_mem {K : Subgroup U} (S : Subgroup K) (v : S.map K.subtype) :
    (inclusion S).toHom v ∈ S := by
  obtain ⟨x, hx, he⟩ := v.property
  exact (Subtype.ext he : x = (inclusion S).toHom v) ▸ hx

private theorem inclusion_range {K : Subgroup U} (S : Subgroup K) :
    (inclusion S).toHom.range = S := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact inclusion_mem S v
  · intro v hv
    exact ⟨⟨(v : U), ⟨v, hv, rfl⟩⟩, rfl⟩

private def restrictTo {K L : Subgroup U} (a : ConjEmbedding K L) (S : Subgroup L)
    (h : a.toHom.range ≤ S) : ConjEmbedding K (S.map L.subtype) :=
  ⟨(L.subtype.comp a.toHom).codRestrict _ (fun x => ⟨a.toHom x, h ⟨x, rfl⟩, rfl⟩),
    a.hasRepresentative⟩

private def conjugated {K L : Subgroup U} (a : ConjEmbedding K L) (p : L) :
    ConjEmbedding K L :=
  ⟨(MulAut.conj p).toMonoidHom.comp a.toHom, by
    obtain ⟨s, hs⟩ := a.hasRepresentative
    refine ⟨(p : U) * s, fun x => ?_⟩
    change (p : U) * (a.toHom x : U) * (p : U)⁻¹ = _
    rw [hs]
    group⟩

private theorem conjugated_range {K L : Subgroup U} (a : ConjEmbedding K L) (p : L) :
    (conjugated a p).toHom.range = conj p a.toHom.range :=
  (MonoidHom.map_range _ _).symm


end
end CommonRightRegionAux
namespace CommonRightRegionAux

private abbrev Perm := Equiv.Perm Nat
private abbrev Finitary := Subgroup.closure {σ : Perm | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) : Subgroup Perm :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X))

private abbrev ParabolicPerm (H : Subgroup Perm) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H = ⨆ i, blockSym (blocks i)

private abbrev Parabolic (H : Subgroup Finitary) := ParabolicPerm (H.map Finitary.subtype)

private theorem parabolicPerm_iff (H : Subgroup Perm) : ParabolicPerm H ↔
    ∃ X : Finset Nat, ∃ (k : Nat) (blocks : Fin k → Finset Nat),
      (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
      (∀ m, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ H = iSup (fun i => blockSym (blocks i)) := by
  constructor
  · rintro ⟨k, blocks, hn, hd, he⟩
    exact ⟨Finset.univ.biUnion blocks, k, blocks, hn, hd, fun m => by simp, he⟩
  · rintro ⟨_, k, blocks, hn, hd, _, he⟩
    exact ⟨k, blocks, hn, hd, he⟩

private theorem commonRegion_parabolic_conj {H : Subgroup Perm} (hH : ParabolicPerm H)
    (q : Finitary) : ParabolicPerm (conj (q : Perm) H) :=
  (parabolicPerm_iff _).2 (FiniteParabolicClosure.1 H ((parabolicPerm_iff H).1 hH) q)

private theorem parabolic_finite {H : Subgroup Finitary} (hH : Parabolic H) : Finite H := by
  classical
  obtain ⟨n, blocks, _, _, hblocks⟩ := hH
  let X := Finset.univ.biUnion blocks
  have hsub : H.map Finitary.subtype ≤ blockSym X := by
    rw [hblocks]
    refine iSup_le fun i σ hs => ?_
    obtain ⟨τ, rfl⟩ := hs
    let σ : Perm := Equiv.Perm.ofSubtype τ
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
  let _ : Finite (blockSym X) :=
    (Set.finite_range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))).to_subtype
  exact Finite.of_injective
    (fun h : H => (⟨(h.val : Perm), hsub ⟨h.val, h.property, rfl⟩⟩ : blockSym X))
    (fun _ _ hh => Subtype.ext (Subtype.ext (congrArg (fun y : blockSym X => y.val) hh)))

open MackeyDiagrams

private theorem parabolic_embedding {H K : Subgroup Finitary}
    (i : ConjEmbedding H K) (hH : Parabolic H) : Parabolic (i.toHom.range.map K.subtype) := by
  obtain ⟨q, hq⟩ := i.hasRepresentative
  have hr : (i.toHom.range.map K.subtype).map Finitary.subtype =
      conj (q : Perm) (H.map Finitary.subtype) := by
    ext x
    constructor
    · rintro ⟨_, ⟨_, ⟨y, rfl⟩, rfl⟩, rfl⟩
      exact ⟨y.val, ⟨y.val, y.property, rfl⟩, congrArg Finitary.subtype (hq y).symm⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      let x : H := ⟨y, hy⟩
      exact ⟨(i.toHom x : Finitary), ⟨i.toHom x, ⟨x, rfl⟩, rfl⟩, congrArg Finitary.subtype (hq x)⟩
  show ParabolicPerm _
  rw [hr]
  exact commonRegion_parabolic_conj hH q


end CommonRightRegionAux
namespace CommonRightRegionAux
open MackeyDiagrams

-- The registered Lemma 6.3 proves existence and uniqueness of the merged
-- projection parameter. Its internal coefficient computation also identifies
-- that parameter. Keep the coefficient calculation local so the bounds can
-- use the actual product of the three marked labels.
universe u
noncomputable section
set_option maxHeartbeats 1500000

private abbrev Vec (X : Type*) := X →₀ Complex

-- A contravariant basis map acts by precomposition on coefficients.
private def Pulls {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X) : Prop :=
  ∀ v, L v y = v x

private theorem pulls_single {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X)
    (h : ∀ i : X, L (Finsupp.single i 1) y = Finsupp.single i (1 : Complex) x) :
    Pulls L y x := by
  let l := (Finsupp.lapply y : Vec Y →ₗ[Complex] Complex).comp L
  have he : l = (Finsupp.lapply x : Vec X →ₗ[Complex] Complex) := by
    apply Finsupp.lhom_ext
    intro i w
    have hs : Finsupp.single i w = w • Finsupp.single i (1 : Complex) := by
      simp [Finsupp.smul_single]
    rw [hs, map_smul, map_smul]
    exact congrArg (w • ·) (h i)
  exact fun v => LinearMap.congr_fun he v

private theorem pulls_of_single {X Y : Type*} {L : Vec X →ₗ[Complex] Vec Y}
    {forward : X → Y} {x : X} {y : Y} (inv : ∀ i, forward i = y ↔ i = x)
    (h : ∀ i : X, L (Finsupp.single i 1) = Finsupp.single (forward i) 1) :
    Pulls L y x := by
  classical
  apply pulls_single
  intro i
  rw [h i]
  simp only [Finsupp.single_apply, inv]

private theorem pulls_mixed {U : Type u} [Group U] {K H P L : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (d : ConjEmbedding L K) (e : ConjEmbedding L H)
    (p : ProjectionDot.Mixed a b d e)
    (y : ((Word.up d).tensor (.down e)).basis.carrier) :
    Pulls (Diagram.mixedProjection (R := Complex) a b d e p.dot p.finite).eval.toLinearMap
      y (Generator.mixedMultiplicationBasis a b d e p.dot y) := by
  classical
  apply pulls_single
  intro i
  change (Biset.Hom.transfer Complex (Generator.mixedMultiplicationBasis a b d e p.dot)
    (Generator.mixedMultiplication_equivariant a b d e p.dot) p.finite).toLinearMap
      (Finsupp.single i 1) y = _
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_apply, Finsupp.single_apply]
  by_cases h : i = Generator.mixedMultiplicationBasis a b d e p.dot y
  · simp [h]
  · simp [h, Ne.symm h]

section Balanced
variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {X X' : Biset K H} {Y Y' : Biset H J}

-- The unchanged strand makes the balancing parameter unique at a fixed output
-- representative. Thus no orbit multiplicity is introduced by tensoring a pullback.
private theorem pulls_horizontal_right (L : Biset.Hom Complex X X')
    (free : ∀ (s : Y.carrier) (h : H), Y.act (h, 1) s = s → h = 1)
    {x' : X'.carrier} {x : X.carrier} (hx : Pulls L.toLinearMap x' x) (s : Y.carrier) :
    Pulls (L.horizontal (Biset.Hom.id Y)).toLinearMap (X'.pair Y x' s) (X.pair Y x s) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨i,t⟩ => ?_)
  change (L.horizontal (Biset.Hom.id Y)).toLinearMap (Finsupp.single (X.pair Y i t) 1)
    (X'.pair Y x' s) = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
    (Finsupp.single t 1) (X'.pair Y x' s) = Finsupp.single (X.pair Y i t) 1 (X.pair Y x s)
  by_cases ht : ∃ h : H, Y.act (h, 1) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y i t = X.pair Y (X.act (1,h) i) s := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single s 1) (X'.pair Y x' s) = v x' := by
      apply pulls_single ((Biset.pairLinear Complex X' Y).flip (Finsupp.single s 1))
      intro j
      change Biset.pairLinear Complex X' Y (Finsupp.single j 1) (Finsupp.single s 1)
        (X'.pair Y x' s) = _
      rw [Biset.pairLinear_single, mul_one]
      have hi : X'.pair Y j s = X'.pair Y x' s ↔ j = x' := by
        constructor
        · intro hp
          obtain ⟨k, hk, hs⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (X'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    -- Rechoose the input representative before using the horizontal basis formula.
    have hre := congrArg (fun w => (L.horizontal (Biset.Hom.id Y)).toLinearMap
      (Finsupp.single w 1) (X'.pair Y x' s)) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
      (Finsupp.single t 1) (X'.pair Y x' s) =
      Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single (X.act (1,h) i) 1))
      (Finsupp.single s 1) (X'.pair Y x' s) at hre
    rw [hre, heval, hx _ , he]
    have hi : X.pair Y (X.act (1,h) i) s = X.pair Y x s ↔ X.act (1,h) i = x := by
      constructor
      · intro hp
        obtain ⟨k, hk, hs⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (X.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single t 1) (X'.pair Y x' s) = 0 := by
      have he : (Finsupp.lapply (X'.pair Y x' s) : Vec (X'.tensor Y).carrier →ₗ[Complex] Complex).comp
          ((Biset.pairLinear Complex X' Y).flip (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X' Y (Finsupp.single j r) (Finsupp.single t 1)
          (X'.pair Y x' s) = 0
        rw [Biset.pairLinear_single, mul_one, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, _, hk⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, _, hk⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

private theorem pulls_horizontal_left (L : Biset.Hom Complex Y Y')
    (free : ∀ (s : X.carrier) (h : H), X.act (1, h) s = s → h = 1)
    {y' : Y'.carrier} {y : Y.carrier} (hy : Pulls L.toLinearMap y' y) (s : X.carrier) :
    Pulls ((Biset.Hom.id X).horizontal L).toLinearMap (X.pair Y' s y') (X.pair Y s y) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨t,i⟩ => ?_)
  change ((Biset.Hom.id X).horizontal L).toLinearMap (Finsupp.single (X.pair Y t i) 1)
    (X.pair Y' s y') = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
    (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') = Finsupp.single (X.pair Y t i) 1 (X.pair Y s y)
  by_cases ht : ∃ h : H, X.act (1, h) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y t i = X.pair Y s (Y.act (h,1) i) := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single s 1) v (X.pair Y' s y') = v y' := by
      apply pulls_single (Biset.pairLinear Complex X Y' (Finsupp.single s 1))
      intro j
      rw [Biset.pairLinear_single, one_mul]
      have hi : X.pair Y' s j = X.pair Y' s y' ↔ j = y' := by
        constructor
        · intro hp
          obtain ⟨k, hs, hk⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (Y'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    have hre := congrArg (fun w => ((Biset.Hom.id X).horizontal L).toLinearMap
      (Finsupp.single w 1) (X.pair Y' s y')) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
      (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') =
      Biset.pairLinear Complex X Y' (Finsupp.single s 1)
      (L.toLinearMap (Finsupp.single (Y.act (h,1) i) 1)) (X.pair Y' s y') at hre
    rw [hre, heval, hy _ , he]
    have hi : X.pair Y s (Y.act (h,1) i) = X.pair Y s y ↔ Y.act (h,1) i = y := by
      constructor
      · intro hp
        obtain ⟨k, hs, hk⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (Y.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single t 1) v (X.pair Y' s y') = 0 := by
      have he : (Finsupp.lapply (X.pair Y' s y') : Vec (X.tensor Y').carrier →ₗ[Complex] Complex).comp
          (Biset.pairLinear Complex X Y' (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X Y' (Finsupp.single t 1) (Finsupp.single j r)
          (X.pair Y' s y') = 0
        rw [Biset.pairLinear_single, one_mul, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, hk, _⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, hk, _⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

end Balanced

end

noncomputable section
set_option maxHeartbeats 2000000

variable {U : Type u} [Group U]
variable {K H J L M : Subgroup U}

private abbrev ev {p q : Word K H} (d : LabelledDrawing Complex p q) := d.interpret.eval.toLinearMap

private abbrev drawId (p : Word K H) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private abbrev before {p q r : Word K H} (d : LabelledDrawing Complex p q)
    (e : LabelledDrawing Complex q r) := LabelledDrawing.vertical d e

private abbrev atLeft {p q : Word K H} (d : LabelledDrawing Complex p q)
    (r : Word H J) := LabelledDrawing.horizontal d (drawId r)

private abbrev atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :=
  before (.ordinary (.associate p q r))
    (before (.horizontal (drawId p) d) (.ordinary (.unassociate p q' r')))

private abbrev pair (p : Word K H) (q : Word H J) := p.basis.pair q.basis

private abbrev triple (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :=
  pair (p.tensor q) r (pair p q x y) z

private theorem pulls_before {p q r : Word K H}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex q r}
    {z : r.basis.carrier} {y : q.basis.carrier} {x : p.basis.carrier}
    (he : Pulls (ev e) z y) (hd : Pulls (ev d) y x) : Pulls (ev (before d e)) z x := by
  intro v
  change ev e (ev d v) z = _
  rw [he _, hd _]

private theorem pulls_assoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.associate p q r))) (pair p (q.tensor r) x (pair q r y z))
      (triple p q r x y z) := by
  let i := Biset.associateBasisEquiv p.basis q.basis r.basis
  have hi : ∀ v : _, i v = i (triple p q r x y z) ↔ v = triple p q r x y z :=
    fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨xy,t⟩ => ?_)
  exact Quotient.inductionOn xy (fun ⟨s,w⟩ => Diagram.eval_associate_single p q r s w t 1)

private theorem pulls_unassoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.unassociate p q r))) (triple p q r x y z)
      (pair p (q.tensor r) x (pair q r y z)) := by
  let i := (Biset.associateBasisEquiv p.basis q.basis r.basis).symm
  have hi : ∀ v : _, i v = i (pair p (q.tensor r) x (pair q r y z)) ↔
      v = pair p (q.tensor r) x (pair q r y z) := fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨s,yz⟩ => ?_)
  exact Quotient.inductionOn yz (fun ⟨w,t⟩ => Diagram.eval_unassociate_single p q r s w t 1)

private theorem pulls_atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    {d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')}
    (free : ∀ (s : p.basis.carrier) (h : H), p.basis.act (1, h) s = s → h = 1)
    (s : p.basis.carrier) {x : q'.basis.carrier} {y : r'.basis.carrier}
    {x' : q.basis.carrier} {y' : r.basis.carrier}
    (hd : Pulls (ev d) (pair q' r' x y) (pair q r x' y')) :
    Pulls (ev (atRight p d)) (triple p q' r' s x y) (triple p q r s x' y') := by
  apply pulls_before (pulls_before (pulls_unassoc p q' r' s x y) ?_)
    (pulls_assoc p q r s x' y')
  exact pulls_horizontal_left d.interpret.eval free hd s

private theorem free_up_left (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.induction a).act (h, 1) s = s) : h = 1 := by
  change h * s * (a.toHom 1)⁻¹ = s at eq
  simpa using mul_right_cancel (show h * s = 1 * s by simpa using eq)

private theorem free_up_right (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.induction a).act (1, h) s = s) : h = 1 := by
  change 1 * s * (a.toHom h)⁻¹ = s at eq
  apply a.injective
  have he : (a.toHom h)⁻¹ = 1 :=
    mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_right (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.restriction a).act (1, h) s = s) : h = 1 := by
  change a.toHom 1 * s * h⁻¹ = s at eq
  have he : h⁻¹ = 1 := mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_left (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.restriction a).act (h, 1) s = s) : h = 1 := by
  change a.toHom h * s * (1 : K)⁻¹ = s at eq
  apply a.injective
  exact mul_right_cancel (show a.toHom h * s = a.toHom 1 * s by simpa using eq)

private theorem up_balance (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    pair (Word.up a) (Word.up b) (x * a.toHom y) 1 = pair (Word.up a) (Word.up b) x y := by
  simpa [pair, Word.basis, Biset.induction] using
    (Biset.induction a).pair_balance (Biset.induction b) y x 1

private theorem pulls_merge (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) :
    Pulls (ev (.trivalent (.mergeUp a b))) x (pair (Word.up a) (Word.up b) x 1) := by
  have hi (w : ((Word.up a).tensor (.up b)).basis.carrier) (z : K) :
      Generator.mergeUpBasis a b w = z ↔ w = pair (Word.up a) (Word.up b) z 1 := by
    refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
    change s * a.toHom t = z ↔ pair (Word.up a) (Word.up b) s t = _
    constructor
    · rintro rfl
      exact (up_balance a b s t).symm
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom t = z * a.toHom 1 at eq
      simpa using eq
  apply pulls_of_single (fun w => hi w x)
  intro w
  refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
  exact Diagram.eval_mergeUp_single a b s t 1

private theorem pulls_split (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    Pulls (ev (.trivalent (.splitUp a b))) (pair (Word.up a) (Word.up b) x y) (x * a.toHom y) := by
  apply pulls_single
  intro s
  change (Diagram.splitUp (R := Complex) a b).eval.toLinearMap (Finsupp.single s 1)
    (pair (Word.up a) (Word.up b) x y) = _
  rw [Diagram.eval_splitUp_single]
  classical
  have hi : pair (Word.up a) (Word.up b) s 1 = pair (Word.up a) (Word.up b) x y ↔
      s = x * a.toHom y := by
    constructor
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom 1 = x * a.toHom y at eq
      simpa using eq
    · rintro rfl
      exact up_balance a b x y
  simp only [Finsupp.single_apply, hi]

private theorem sum_eval (p q : Word K H) (xs : List (Complex × Diagram Complex p q)) :
    (ScopedDiagram.linearCombination (xs.map fun (c,d) => (c, ScopedDiagram.ordinary d))).eval.toLinearMap =
      (xs.map fun (c,d) => c • d.eval.toLinearMap).sum := by
  apply LinearMap.ext
  intro v
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c,d⟩
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply]
    rw [ih]
    rfl

private theorem singleton_mixed (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d) :
    ev (.compactProjection a b c d [(1,p)]) =
      (Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem singleton_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) :
    ev (.parallelUp a b c d [(1,p)]) =
      (Diagram.parallelUp (R := Complex) a b c d p).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.parallelUp (R := Complex) a b c d p)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem pulls_compact (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d)
    (x : K) (y : J) :
    Pulls (ev (.compactProjection a b c d [(1,p)])) (pair (Word.up c) (Word.down d) x y)
      (Generator.mixedPair a b (a.toHom x * p.dot.element * b.toHom y)) := by
  rw [singleton_mixed]
  exact pulls_mixed a b c d p _

private theorem pulls_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) (x : K) (y : J) :
    Pulls (ev (.parallelUp a b c d [(1,p)])) (pair (Word.up c) (Word.up d) x y)
      (pair (Word.up a) (Word.up b) (x * c.toHom y * p.element⁻¹) 1) := by
  rw [singleton_parallel]
  intro v
  change ev (.trivalent (.splitUp c d))
    ((Diagram.upDot (R := Complex) p).eval.toLinearMap (ev (.trivalent (.mergeUp a b)) v))
    (pair (Word.up c) (Word.up d) x y) = _
  rw [pulls_split c d x y _]
  have he : Pulls (Diagram.upDot (R := Complex) p).eval.toLinearMap
      (x * c.toHom y) (x * c.toHom y * p.element⁻¹) := by
    refine pulls_of_single (forward := fun z : K => z * p.element)
      ?_ (fun z => Diagram.eval_upDot_single p z 1)
    intro s
    exact eq_mul_inv_iff_mul_eq.symm
  rw [he _, pulls_merge a b _ _]

end

noncomputable section
set_option maxHeartbeats 2400000

variable {U : Type u} [Group U] {G A D F C E B B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A)
  (c : ConjEmbedding F D) (d : ConjEmbedding C G)
  (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev bottom := ((Word.down a).tensor (.up b)).tensor (.up c)
private abbrev top := ((Word.up d).tensor (.up e)).tensor (.down f)
private abbrev mergedBottom := (Word.down a).tensor (.up (b.comp c))
private abbrev mergedTop := (Word.up (d.comp e)).tensor (.down f)

private abbrev splitBottom : LabelledDrawing Complex (mergedBottom a b c) (bottom a b c) :=
  before (.horizontal (drawId (.down a)) (.trivalent (.splitUp b c)))
    (.ordinary (.unassociate (.down a) (.up b) (.up c)))

private abbrev mergeTop : LabelledDrawing Complex (top d e f) (mergedTop d e f) :=
  .horizontal (.trivalent (.mergeUp d e)) (drawId (.down f))

private abbrev mergedEval (drawing : LabelledDrawing Complex (bottom a b c) (top d e f)) :=
  ev (before (splitBottom a b c) (before drawing (mergeTop d e f)))

private abbrev leftDrawing (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B)
    (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × Dot (r.comp t) (d.comp e))) :=
  before (atLeft (.compactProjection a b r s xs) (.up c))
    (before (atRight (.up r) (.compactProjection s c t f ys))
      (atLeft (.parallelUp r t d e zs) (.down f)))

private abbrev rightDrawing (u' : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B')
    (ells : List (Complex × Dot (b.comp c) (u'.comp w)))
    (ms : List (Complex × ProjectionDot.Mixed a u' d v))
    (ns : List (Complex × ProjectionDot.Mixed v w e f)) :=
  before (atRight (.down a) (.parallelUp b c u' w ells))
    (before (atLeft (.compactProjection a u' d v ms) (.up w))
      (atRight (.up d) (.compactProjection v w e f ns)))

private theorem pulls_splitBottom (x y : A) (z : D) :
    Pulls (ev (splitBottom a b c)) (triple (.down a) (.up b) (.up c) x y z)
      (pair (.down a) (.up (b.comp c)) x (y * b.toHom z)) := by
  apply pulls_before (pulls_unassoc (.down a) (.up b) (.up c) x y z)
  exact pulls_horizontal_left (X := Biset.restriction a) (Diagram.splitUp (R := Complex) b c).eval (free_down_right a)
    (pulls_split b c y z) x

private theorem pulls_mergeTop (g : G) (h : F) :
    Pulls (ev (mergeTop d e f)) (pair (.up (d.comp e)) (.down f) g h)
      (triple (.up d) (.up e) (.down f) g 1 h) := by
  exact pulls_horizontal_right (Y := Biset.restriction f) (Diagram.mergeUp (R := Complex) d e).eval
    (free_down_left f) (pulls_merge d e g) h

private theorem mixedPair_coord {K H P : Subgroup U}
    (α : ConjEmbedding K P) (β : ConjEmbedding H P) (x y : P) :
    pair (.down α) (.up β) x y = Generator.mixedPair α β (x * y) := by
  apply (Generator.mixedEquiv α β).injective
  change x * y = Generator.mixedProduct α β (Generator.mixedPair α β (x * y))
  rw [Generator.mixedProduct_mixedPair]

-- Lemma 6.3, left backward calculation. At each stage the linear coefficient
-- is evaluated at its unique backwards coordinate. The fixed strands act
-- freely at the balancing interfaces, so rebracketing retains the fiber sum.
private theorem pulls_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedPair a (b.comp c)
        (a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h)) := by
  let g' := g * z.element⁻¹
  let y' := y.dot.element * c.toHom h
  let x' := a.toHom g' * x.dot.element * b.toHom y'
  have step₃ : Pulls (ev (atLeft (.parallelUp r t d e [(1,z)]) (.down f)))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up r) (.up t) (.down f) g' 1 h) := by
    have hp := pulls_parallel r t d e z g 1
    simp only [map_one, mul_one] at hp
    exact pulls_horizontal_right (Y := Biset.restriction f) _ (free_down_left f) hp h
  have step₂ : Pulls (ev (atRight (.up r) (.compactProjection s c t f [(1,y)])))
      (triple (.up r) (.up t) (.down f) g' 1 h) (triple (.up r) (.down s) (.up c) g' y' 1) := by
    apply pulls_atRight (.up r) (free_up_right r) g'
    have hp := pulls_compact s c t f y 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₁ : Pulls (ev (atLeft (.compactProjection a b r s [(1,x)]) (.up c)))
      (triple (.up r) (.down s) (.up c) g' y' 1) (triple (.down a) (.up b) (.up c) x' 1 1) :=
    pulls_horizontal_right _ (free_up_left c) (pulls_compact a b r s x g' y') _
  have step₀ := pulls_splitBottom a b c x' 1 1
  simp only [map_one, mul_one] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h))
  have hc : x' = a.toHom g * leftParameter a b c d e f x.dot y.dot z * (b.comp c).toHom h := by
    simp only [x', g', y', leftParameter, ConjEmbedding.comp_apply, map_mul, mul_assoc]
  rw [← hc]
  exact out

-- Lemma 6.3, right backward calculation. The parallel vertex contributes
-- right multiplication by ell⁻¹. Its reversed intertwining equation
-- moves that factor through the right boundary action.
private theorem pulls_right {u' : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (u'.comp w))
    (m : ProjectionDot.Mixed a u' d v) (n : ProjectionDot.Mixed v w e f)
    (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (rightDrawing a b c d e f u' v w [(1,ell)] [(1,m)] [(1,n)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedPair a (b.comp c)
        (a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h)) := by
  let n' := n.dot.element * w.toHom h
  let m' := a.toHom g * m.dot.element * u'.toHom n'
  have step₃ : Pulls (ev (atRight (.up d) (.compactProjection v w e f [(1,n)])))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up d) (.down v) (.up w) g n' 1) := by
    apply pulls_atRight (.up d) (free_up_right d) g
    have hp := pulls_compact v w e f n 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₂ : Pulls (ev (atLeft (.compactProjection a u' d v [(1,m)]) (.up w)))
      (triple (.up d) (.down v) (.up w) g n' 1) (triple (.down a) (.up u') (.up w) m' 1 1) :=
    pulls_horizontal_right _ (free_up_left w) (pulls_compact a u' d v m g n') _
  have step₁ : Pulls (ev (atRight (.down a) (.parallelUp b c u' w [(1,ell)])))
      (triple (.down a) (.up u') (.up w) m' 1 1)
      (triple (.down a) (.up b) (.up c) m' ell.element⁻¹ 1) := by
    apply pulls_atRight (.down a) (free_down_right a) m'
    simpa only [map_one, mul_one, one_mul] using pulls_parallel b c u' w ell 1 1
  have step₀ := pulls_splitBottom a b c m' ell.element⁻¹ 1
  simp only [map_one, mul_one] at step₀
  rw [mixedPair_coord a (b.comp c) m' ell.element⁻¹] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h))
  have hel := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at hel
  have hc : m' * ell.element⁻¹ =
      a.toHom g * rightParameter a b c d e f ell m.dot n.dot * (b.comp c).toHom h := by
    simp only [m', n', rightParameter, ConjEmbedding.comp_apply, map_mul, mul_assoc, hel]
  rw [← hc]
  exact out

end
end CommonRightRegionAux
namespace CommonRightRegionAux
open MackeyDiagrams

noncomputable section
variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)
variable (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)

private abbrev mergeBottom : LabelledDrawing Complex (bottom a b c) (mergedBottom a b c) :=
  before (.ordinary (.associate (.down a) (.up b) (.up c)))
    (.horizontal (drawId (.down a)) (.trivalent (.mergeUp b c)))

private abbrev splitTop : LabelledDrawing Complex (mergedTop d e f) (top d e f) :=
  .horizontal (.trivalent (.splitUp d e)) (drawId (.down f))

private abbrev targetProjection :=
  before (mergeBottom a b c)
    (before (.compactProjection a (b.comp c) (d.comp e) f [(1,p)]) (splitTop d e f))

private abbrev targetMultiplication :=
  before (mergeTop d e f)
    (before (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) (splitBottom a b c))

-- The boundary frames come in inverse pairs, by the typed trivalent
-- and reassociation identities. This bridges merged coordinates and the
-- full three-strand equality used in the endpoint.
private theorem cancel_splitBottom_mergeBottom :
    (splitBottom a b c).interpret.eval.vertical (mergeBottom a b c).interpret.eval =
      Biset.Hom.id (mergedBottom a b c).basis := by
  let X := (Word.down a).basis
  let Y := (Word.up b).basis
  let Z := (Word.up c).basis
  let S := (Diagram.id (R := Complex) (.down a)).eval.horizontal (Diagram.splitUp b c).eval
  let M := (Diagram.id (R := Complex) (.down a)).eval.horizontal (Diagram.mergeUp b c).eval
  change (S.vertical (Biset.unassociate X Y Z Complex)).vertical
    ((Biset.associate X Y Z Complex).vertical M) = _
  refine Biset.Hom.cancel_middle _ _ _ _ Biset.unassociate_associate ?_
  change ((Biset.Hom.id (R := Complex) X).horizontal (Diagram.splitUp b c).eval).vertical
    ((Biset.Hom.id X).horizontal (Diagram.mergeUp b c).eval) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id X).horizontal
    (((Diagram.splitUp (R := Complex) b c).vertical (Diagram.mergeUp b c)).eval) = _
  rw [Diagram.splitUp_mergeUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_mergeBottom_splitBottom :
    (mergeBottom a b c).interpret.eval.vertical (splitBottom a b c).interpret.eval =
      Biset.Hom.id (bottom a b c).basis := by
  change ((Biset.associate (Word.down a).basis (Word.up b).basis (Word.up c).basis
      Complex).vertical
      ((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.mergeUp b c).eval)).vertical
    (((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.splitUp b c).eval).vertical
      (Biset.unassociate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex)) = _
  refine Biset.Hom.cancel_middle _ _ _ _ ?_ Biset.associate_unassociate
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id (Word.down a).basis).horizontal
    ((Diagram.mergeUp (R := Complex) b c).vertical (Diagram.splitUp b c)).eval = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_splitTop_mergeTop :
    (splitTop d e f).interpret.eval.vertical (mergeTop d e f).interpret.eval =
      Biset.Hom.id (mergedTop d e f).basis := by
  change ((Diagram.splitUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)).vertical
      ((Diagram.mergeUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.splitUp (R := Complex) d e).vertical (Diagram.mergeUp d e)).eval.horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.splitUp_mergeUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_mergeTop_splitTop :
    (mergeTop d e f).interpret.eval.vertical (splitTop d e f).interpret.eval =
      Biset.Hom.id (top d e f).basis := by
  change ((Diagram.mergeUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)).vertical
      ((Diagram.splitUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.mergeUp (R := Complex) d e).vertical (Diagram.splitUp d e)).eval.horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem frame_eq {U : Type*} [Group U] {K H : Subgroup U}
    {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (preInv : LabelledDrawing Complex p p₀) (postInv : LabelledDrawing Complex q₀ q)
    (hp : preInv.interpret.eval.vertical pre.interpret.eval = Biset.Hom.id p.basis)
    (hq : post.interpret.eval.vertical postInv.interpret.eval = Biset.Hom.id q.basis)
    (x y : LabelledDrawing Complex p q) :
    ev (before pre (before x post)) = ev (before pre (before y post)) ↔
      x.interpret.eval = y.interpret.eval := by
  constructor
  · intro h
    have he : pre.interpret.eval.vertical (x.interpret.eval.vertical post.interpret.eval) =
        pre.interpret.eval.vertical (y.interpret.eval.vertical post.interpret.eval) :=
      Biset.Hom.ext h
    have undo (z : LabelledDrawing Complex p q) :
        (preInv.interpret.eval.vertical (pre.interpret.eval.vertical
          (z.interpret.eval.vertical post.interpret.eval))).vertical postInv.interpret.eval =
        z.interpret.eval := by
      rw [← Biset.Hom.vertical_assoc preInv.interpret.eval, hp, Biset.Hom.id_vertical,
        Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]
    have h' := congrArg (fun z => (preInv.interpret.eval.vertical z).vertical postInv.interpret.eval) he
    exact (undo x).symm.trans (h'.trans (undo y))
  · intro h
    exact congrArg (fun z : Biset.Hom Complex p.basis q.basis =>
      (pre.interpret.eval.vertical (z.vertical post.interpret.eval)).toLinearMap) h

private theorem framed_target {U : Type*} [Group U] {K H : Subgroup U}
    {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (preInv : LabelledDrawing Complex p p₀) (postInv : LabelledDrawing Complex q₀ q)
    (hp : pre.interpret.eval.vertical preInv.interpret.eval = Biset.Hom.id p₀.basis)
    (hq : postInv.interpret.eval.vertical post.interpret.eval = Biset.Hom.id q₀.basis)
    (target : LabelledDrawing Complex p₀ q₀) :
    ev (before pre (before (before preInv (before target postInv)) post)) = ev target := by
  change (pre.interpret.eval.vertical
    ((preInv.interpret.eval.vertical (target.interpret.eval.vertical postInv.interpret.eval)).vertical
      post.interpret.eval)).toLinearMap = _
  rw [Biset.Hom.vertical_assoc preInv.interpret.eval,
    ← Biset.Hom.vertical_assoc pre.interpret.eval, hp, Biset.Hom.id_vertical,
    Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]

private theorem projection_comparison
    (drawing : LabelledDrawing Complex (bottom a b c) (top d e f)) (q : A)
    (h : ∀ (g : G) (k : F), Pulls (mergedEval a b c d e f drawing)
      (pair (.up (d.comp e)) (.down f) g k)
      (Generator.mixedPair a (b.comp c) (a.toHom g * q * (b.comp c).toHom k))) :
    drawing.interpret.eval = (targetProjection a b c d e f p).interpret.eval ↔ q = p.dot.element := by
  classical
  have htarget : mergedEval a b c d e f (targetProjection a b c d e f p) =
      ev (.compactProjection a (b.comp c) (d.comp e) f [(1, p)]) :=
    framed_target (splitBottom a b c) (mergeTop d e f) (mergeBottom a b c) (splitTop d e f)
      (cancel_splitBottom_mergeBottom a b c) (cancel_splitTop_mergeTop d e f) _
  rw [← frame_eq (splitBottom a b c) (mergeTop d e f) (mergeBottom a b c) (splitTop d e f)
    (cancel_mergeBottom_splitBottom a b c) (cancel_mergeTop_splitTop d e f)]
  change (mergedEval a b c d e f drawing =
    mergedEval a b c d e f (targetProjection a b c d e f p)) ↔ _
  rw [htarget]
  constructor
  · intro he
    have hq := h 1 1 (Finsupp.single (Generator.mixedPair a (b.comp c) q) 1)
    rw [he] at hq
    rw [pulls_compact a (b.comp c) (d.comp e) f p 1 1 _] at hq
    simp only [map_one, one_mul, mul_one, Finsupp.single_eq_same] at hq
    by_contra hne
    have hne' : Generator.mixedPair a (b.comp c) (p.dot.element) ≠
        Generator.mixedPair a (b.comp c) q :=
      fun h => hne ((Generator.mixedEquiv a (b.comp c)).symm.injective h.symm)
    rw [Finsupp.single_eq_of_ne hne'] at hq
    exact zero_ne_one hq
  · rintro rfl
    apply LinearMap.ext
    intro input
    apply Finsupp.ext
    intro output
    refine Quotient.inductionOn output (fun ⟨g,k⟩ => ?_)
    exact (h g k input).trans (pulls_compact a (b.comp c) (d.comp e) f p g k input).symm

private theorem left_project_eval {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) :
    (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]).interpret.eval =
      (targetProjection a b c d e f p).interpret.eval ↔ leftParameter a b c d e f x.dot y.dot z = p.dot.element :=
  projection_comparison a b c d e f p _ _ (pulls_left a b c d e f x y z)

private theorem right_project_eval {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f) :
    (rightDrawing a b c d e f j v w [(1,ell)] [(1,m)] [(1,n)]).interpret.eval =
      (targetProjection a b c d e f p).interpret.eval ↔ rightParameter a b c d e f ell m.dot n.dot = p.dot.element :=
  projection_comparison a b c d e f p _ _ (pulls_right a b c d e f ell m n)

end
end CommonRightRegionAux
namespace CommonRightRegionAux
open MackeyDiagrams
noncomputable section

variable {U : Type*} [Group U] {K H J L M G A D F C E B : Subgroup U}

private abbrev col {X : Type*} (x : X) : Vec X :=
  Finsupp.single x 1

private theorem push_before {p q r : Word K H}
    (D : LabelledDrawing Complex p q) (E : LabelledDrawing Complex q r)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier)
    (hd : ev D (col x) = col y) (he : ev E (col y) = col z) :
    ev (before D E) (col x) = col z := by
  change ev E (ev D (col x)) = _
  rw [hd, he]

private theorem push_atLeft {p p' : Word K H} {q : Word H J}
    (D : LabelledDrawing Complex p p') (x : p.basis.carrier) (y : q.basis.carrier)
    (x' : p'.basis.carrier) (hd : ev D (col x) = col x') :
    ev (atLeft D q) (col (pair p q x y)) = col (pair p' q x' y) := by
  change (D.interpret.eval.horizontal (Diagram.id q).eval).toLinearMap _ = _
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply, hd,
    Biset.pairLinear_single, one_mul]

private theorem push_atRight {p : Word K H} {q : Word H J} {s : Word J L}
    {q' : Word H M} {s' : Word M L}
    (D : LabelledDrawing Complex (q.tensor s) (q'.tensor s'))
    (x : p.basis.carrier) (y : q.basis.carrier) (z : s.basis.carrier)
    (y' : q'.basis.carrier) (z' : s'.basis.carrier)
    (hd : ev D (col (pair q s y z)) = col (pair q' s' y' z')) :
    ev (atRight p D) (col (triple p q s x y z)) = col (triple p q' s' x y' z') := by
  change (Diagram.unassociate (R := Complex) p q' s').eval.toLinearMap
    (((Diagram.id p).eval.horizontal D.interpret.eval).toLinearMap
      ((Diagram.associate (R := Complex) p q s).eval.toLinearMap (col (triple p q s x y z)))) = _
  rw [Diagram.eval_associate_single, Biset.Hom.horizontal_single, one_smul,
    Diagram.eval_id_apply, hd, Biset.pairLinear_single, one_mul, Diagram.eval_unassociate_single]

private theorem push_mixed (a : ConjEmbedding K A) (b : ConjEmbedding H A)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (x : Dot (a.comp l) (b.comp r)) (g : K) (h : H) :
    ev (.mixedMultiplication a b l r [(1,x)]) (col (pair (.up l) (.down r) g h)) =
      col (pair (.down a) (.up b) (a.toHom g * x.element * b.toHom h) 1) := by
  let label : DotLabel Complex (a.comp l) (b.comp r) := Finsupp.single x 1
  have hterms : label.terms = [(1,x)] := by
    classical
    simp [label, DotLabel.terms]
  rw [← hterms]
  have hcol := ((MixedCrossingFiniteFiberConvention (U := U)).2.2.1 a b l r label).1
    (pair (.up l) (.down r) g h)
  rw [hterms] at hcol
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] at hcol
  exact hcol

private theorem push_parallel (a : ConjEmbedding H A) (b : ConjEmbedding L H)
    (j : ConjEmbedding J A) (w : ConjEmbedding L J)
    (x : Dot (a.comp b) (j.comp w)) (g : A) (h : H) :
    ev (.parallelUp a b j w [(1,x)]) (col (pair (.up a) (.up b) g h)) =
      col (pair (.up j) (.up w) (g * a.toHom h * x.element) 1) := by
  rw [singleton_parallel]
  change (Diagram.splitUp (R := Complex) j w).eval.toLinearMap
    ((Diagram.upDot x).eval.toLinearMap ((Diagram.mergeUp a b).eval.toLinearMap
      (col (pair (.up a) (.up b) g h)))) = _
  rw [Diagram.eval_mergeUp_single, Diagram.eval_upDot_single, Diagram.eval_splitUp_single]

variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev framedMul (drawing : LabelledDrawing Complex (top d e f) (bottom a b c)) :=
  before (splitTop d e f) (before drawing (mergeBottom a b c))

private theorem push_splitTop (g : G) (h : F) :
    ev (splitTop d e f) (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (triple (.up d) (.up e) (.down f) g 1 h) := by
  change (Diagram.horizontal (R := Complex) (Diagram.splitUp d e) (Diagram.id (.down f))).eval.toLinearMap _ = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_splitUp_single,
    Diagram.eval_id_apply, Biset.pairLinear_single, one_mul]

private theorem push_mergeBottom (x y : A) (z : D) :
    ev (mergeBottom a b c) (col (triple (.down a) (.up b) (.up c) x y z)) =
      col (Generator.mixedPair a (b.comp c) (x * (y * b.toHom z))) := by
  change (Diagram.horizontal (R := Complex) (Diagram.id (.down a)) (Diagram.mergeUp b c)).eval.toLinearMap
    ((Diagram.associate (.down a) (.up b) (.up c)).eval.toLinearMap
      (col (triple (.down a) (.up b) (.up c) x y z))) = _
  rw [Diagram.eval_associate_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, Diagram.eval_mergeUp_single, Biset.pairLinear_single, one_mul]
  exact congrArg col (mixedPair_coord a (b.comp c) x (y * b.toHom z))

private abbrev leftMulDrawing (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B) (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :=
  before (atLeft (.parallelUp d e r t [(1,z.inverse)]) (.down f))
    (before (atRight (.up r) (.mixedMultiplication s c t f [(1,y)]))
      (atLeft (.mixedMultiplication a b r s [(1,x)]) (.up c)))

private abbrev rightMulDrawing (j : ConjEmbedding B A) (v : ConjEmbedding C B)
    (w : ConjEmbedding F B) (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :=
  before (atRight (.up d) (.mixedMultiplication v w e f [(1,n)]))
    (before (atLeft (.mixedMultiplication a j d v [(1,m)]) (.up w))
      (atRight (.down a) (.parallelUp j w b c [(1,ell.inverse)])))

-- The forward columns of Xiao's Theorem 6.5 specialize to the same
-- parameter products as the backward coefficient calculation of Lemma 6.3.
private theorem push_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    ev (framedMul a b c d e f (leftMulDrawing a b c d e f r s t x y z))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * leftParameter a b c d e f x y z * (b.comp c).toHom h)) := by
  let g' := g * z.element⁻¹
  let t' := y.element * c.toHom h
  let q := a.toHom g' * x.element * b.toHom t'
  have h₁ := push_atLeft (.parallelUp d e r t [(1,z.inverse)])
    (q := .down f) (pair (.up d) (.up e) g 1) h (pair (.up r) (.up t) g' 1) (by
      simpa only [g', map_one, mul_one, Dot.inverse] using push_parallel d e r t z.inverse g 1)
  have h₂ := push_atRight (p := Word.up r) (.mixedMultiplication s c t f [(1,y)])
    g' 1 h t' 1 (by simpa only [t', map_one, one_mul] using push_mixed s c t f y 1 h)
  have h₃ := push_atLeft (.mixedMultiplication a b r s [(1,x)])
    (q := .up c) (pair (.up r) (.down s) g' t') 1
    (pair (.down a) (.up b) q 1) (push_mixed a b r s x g' t')
  have h₄ := push_mergeBottom a b c q 1 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  simpa only [q, g', t', leftParameter, map_one, one_mul, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc] using hEval

private theorem push_right {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) (g : G) (h : F) :
    ev (framedMul a b c d e f (rightMulDrawing a b c d e f j v w ell m n))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * rightParameter a b c d e f ell m n * (b.comp c).toHom h)) := by
  let n' := n.element * w.toHom h
  let q := a.toHom g * m.element * j.toHom n'
  have h₁ := push_atRight (p := Word.up d) (.mixedMultiplication v w e f [(1,n)])
    g 1 h n' 1 (by simpa only [n', map_one, one_mul] using push_mixed v w e f n 1 h)
  have h₂ := push_atLeft (.mixedMultiplication a j d v [(1,m)])
    (q := .up w) (pair (.up d) (.down v) g n') 1
    (pair (.down a) (.up j) q 1) (push_mixed a j d v m g n')
  have h₃ := push_atRight (p := Word.down a) (.parallelUp j w b c [(1,ell.inverse)])
    q 1 1 ell.element⁻¹ 1 (by
      simpa only [map_one, mul_one, one_mul, Dot.inverse] using push_parallel j w b c ell.inverse 1 1)
  have h₄ := push_mergeBottom a b c q ell.element⁻¹ 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  have he := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at he
  simpa only [q, n', rightParameter, map_one, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc, he] using hEval

private theorem multiplication_comparison
    (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (drawing : LabelledDrawing Complex (top d e f) (bottom a b c)) (q : A)
    (h : ∀ (g : G) (k : F), ev (framedMul a b c d e f drawing)
      (col (pair (.up (d.comp e)) (.down f) g k)) =
      col (Generator.mixedPair a (b.comp c) (a.toHom g * q * (b.comp c).toHom k))) :
    drawing.interpret.eval = (targetMultiplication a b c d e f p).interpret.eval ↔ q = p.dot.element := by
  classical
  have htarget : ev (framedMul a b c d e f (targetMultiplication a b c d e f p)) =
      ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) :=
    framed_target (splitTop d e f) (mergeBottom a b c) (mergeTop d e f) (splitBottom a b c)
      (cancel_splitTop_mergeTop d e f) (cancel_splitBottom_mergeBottom a b c) _
  have col_target (g : G) (k : F) :
      ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)])
        (col (pair (.up (d.comp e)) (.down f) g k)) =
        col (Generator.mixedPair a (b.comp c) (a.toHom g * p.dot.element * (b.comp c).toHom k)) := by
    refine (push_mixed a (b.comp c) (d.comp e) f p.dot g k).trans ?_
    apply congrArg col
    exact (mixedPair_coord a (b.comp c) _ 1).trans (congrArg _ (mul_one _))
  rw [← frame_eq (splitTop d e f) (mergeBottom a b c) (mergeTop d e f) (splitBottom a b c)
    (cancel_mergeTop_splitTop d e f) (cancel_mergeBottom_splitBottom a b c)]
  change (ev (framedMul a b c d e f drawing) =
    ev (framedMul a b c d e f (targetMultiplication a b c d e f p))) ↔ _
  rw [htarget]
  constructor
  · intro he
    have eq := h 1 1
    rw [he, col_target] at eq
    simp only [map_one, one_mul, mul_one] at eq
    apply (Generator.mixedEquiv a (b.comp c)).symm.injective
    exact Finsupp.single_left_injective one_ne_zero eq.symm
  · rintro rfl
    apply Finsupp.lhom_ext
    intro z k
    have hc (z : (mergedTop d e f).basis.carrier) :
        ev (framedMul a b c d e f drawing) (col z) =
        ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) (col z) :=
      Quotient.inductionOn z fun ⟨g,h'⟩ => (h g h').trans (col_target g h').symm
    rw [show Finsupp.single z k = k • col z by simp [col, Finsupp.smul_single],
      map_smul, map_smul, hc]

private theorem left_mul_eval {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (x : Dot (a.comp r) (b.comp s)) (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :
    (leftMulDrawing a b c d e f r s t x y z).interpret.eval =
      (targetMultiplication a b c d e f p).interpret.eval ↔ leftParameter a b c d e f x y z = p.dot.element :=
  multiplication_comparison a b c d e f p _ _ (push_left a b c d e f x y z)

private theorem right_mul_eval {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (ell : Dot (b.comp c) (j.comp w)) (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :
    (rightMulDrawing a b c d e f j v w ell m n).interpret.eval =
      (targetMultiplication a b c d e f p).interpret.eval ↔ rightParameter a b c d e f ell m n = p.dot.element :=
  multiplication_comparison a b c d e f p _ _ (push_right a b c d e f ell m n)

end
end CommonRightRegionAux
namespace CommonRightRegionAux
open MackeyDiagrams

section
variable {U : Type*} [Group U] {G A D F C E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private theorem finite_mixed {K H P L : Subgroup U} [Finite K] [Finite H]
    (α : ConjEmbedding K P) (β : ConjEmbedding H P)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (x : Dot (α.comp l) (β.comp r)) :
    ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis α β l r x w = z} := by
  let _ : Finite ((Word.up l).tensor (.down r)).basis.carrier :=
    Finite.of_surjective (fun p : K × H => (Biset.induction l).pair (Biset.restriction r) p.1 p.2)
      (fun w => Quotient.exists_rep w)
  exact fun _ => Set.toFinite _


end
end CommonRightRegionAux

namespace CommonRightRegionAux
open MackeyDiagrams

noncomputable section

-- A weighted mark is linear in its list of eligible group elements. The
-- surrounding diagram remains fixed, including when the list is empty.

private def weighted {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (s : I → M) (xs : List (Complex × I)) : M :=
  (xs.map fun x => x.1 • s x.2).sum

private theorem map_weighted {I M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (L : M →ₗ[Complex] N) (s : I → M) (xs : List (Complex × I)) :
    L (weighted s xs) = weighted (fun i => L (s i)) xs := by
  unfold weighted
  rw [map_list_sum, List.map_map]
  simp only [Function.comp_def, map_smul]

private def preapply {M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (x : M) : (M →ₗ[Complex] N) →ₗ[Complex] N where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def composeAround
    {M N P Q : Type*} [AddCommMonoid M] [Module Complex M] [AddCommMonoid N] [Module Complex N]
    [AddCommMonoid P] [Module Complex P] [AddCommMonoid Q] [Module Complex Q]
    (pre : M →ₗ[Complex] N) (post : P →ₗ[Complex] Q) :
    (N →ₗ[Complex] P) →ₗ[Complex] (M →ₗ[Complex] Q) where
  toFun f := post.comp (f.comp pre)
  map_add' g h := by
    change post.comp ((g + h).comp pre) = post.comp (g.comp pre) + post.comp (h.comp pre)
    rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r g := by
    change post.comp ((r • g).comp pre) = r • post.comp (g.comp pre)
    rw [LinearMap.smul_comp, LinearMap.comp_smul]

section WeightedCrossings
variable {U : Type u} [Group U] {K H J L M : Subgroup U}
private theorem weighted_compact (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (xs : List (Complex × ProjectionDot.Mixed a b c d)) :
    ev (.compactProjection a b c d xs) =
      weighted (fun p => ev (.compactProjection a b c d [(1,p)])) xs := by
  have hs := sum_eval ((Word.down a).tensor (.up b)) ((Word.up c).tensor (.down d))
    (xs.map fun t => (t.1, Diagram.mixedProjection (R := Complex) a b c d t.2.dot t.2.finite))
  simp only [List.map_map] at hs
  rw [show weighted (fun p => ev (.compactProjection a b c d [(1,p)])) xs =
      weighted (fun p => (Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite).eval.toLinearMap)
        xs from congrArg (fun s => weighted s xs) (funext (singleton_mixed a b c d))]
  exact hs
private theorem weighted_atLeft {I : Type*} {p q : Word K H} {r : Word H J}
    (S : LabelledDrawing Complex p q) (s : I → LabelledDrawing Complex p q) (xs : List (Complex × I))
    (he : ev S = weighted (fun i => ev (s i)) xs) :
    ev (atLeft S r) = weighted (fun i => ev (atLeft (s i) r)) xs := by
  apply Finsupp.lhom_ext
  intro w c
  refine Quotient.inductionOn w (fun ⟨x,y⟩ => ?_)
  let T := c • (((Biset.pairLinear Complex q.basis r.basis).flip
    (Finsupp.single y 1)).comp (preapply (Finsupp.single x (1 : Complex))))
  have col (d : LabelledDrawing Complex p q) :
      ev (atLeft d r) (Finsupp.single (pair p r x y) c) = T (ev d) := by
    exact Biset.Hom.horizontal_single d.interpret.eval (Biset.Hom.id r.basis) x y c
  change ev (atLeft S r) (Finsupp.single (pair p r x y) c) =
    preapply (Finsupp.single (pair p r x y) c) (weighted (fun i => ev (atLeft (s i) r)) xs)
  rw [col S, he, map_weighted T, map_weighted]
  exact congrArg (fun v => weighted v xs) (funext fun i => (col (s i)).symm)

private theorem weighted_atRight {I : Type*} (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    (S : LabelledDrawing Complex (q.tensor r) (q'.tensor r'))
    (s : I → LabelledDrawing Complex (q.tensor r) (q'.tensor r')) (xs : List (Complex × I))
    (he : ev S = weighted (fun i => ev (s i)) xs) :
    ev (atRight p S) = weighted (fun i => ev (atRight p (s i))) xs := by
  let first := ev (.ordinary (.associate p q r))
  let last := ev (.ordinary (.unassociate p q' r'))
  let frame := composeAround first last
  have mid : ev (.horizontal (drawId p) S) =
      weighted (fun i => ev (.horizontal (drawId p) (s i))) xs := by
    apply Finsupp.lhom_ext
    intro w c
    refine Quotient.inductionOn w (fun ⟨x,y⟩ => ?_)
    let T := c • ((Biset.pairLinear Complex p.basis (q'.tensor r').basis
      (Finsupp.single x 1)).comp (preapply (Finsupp.single y (1 : Complex))))
    have col (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :
        ev (.horizontal (drawId p) d) (Finsupp.single (pair p (q.tensor r) x y) c) = T (ev d) := by
      exact Biset.Hom.horizontal_single (Biset.Hom.id p.basis) d.interpret.eval x y c
    change ev (.horizontal (drawId p) S) (Finsupp.single (pair p (q.tensor r) x y) c) =
      preapply (Finsupp.single (pair p (q.tensor r) x y) c)
        (weighted (fun i => ev (.horizontal (drawId p) (s i))) xs)
    rw [col S, he, map_weighted T, map_weighted]
    exact congrArg (fun v => weighted v xs) (funext fun i => (col (s i)).symm)
  have hframe (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :
      ev (atRight p d) = frame (ev (.horizontal (drawId p) d)) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hframe S, mid, map_weighted frame]
  exact congrArg (fun v => weighted v xs) (funext fun i => (hframe (s i)).symm)

end WeightedCrossings

variable {U : Type*} [Group U] {K H J L M : Subgroup U}

private theorem weighted_mixed (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J)
    (xs : List (Complex × Dot (a.comp c) (b.comp d))) :
    ev (.mixedMultiplication a b c d xs) =
      weighted (fun p => ev (.mixedMultiplication a b c d [(1,p)])) xs := by
  have hs := sum_eval ((Word.up c).tensor (.down d)) ((Word.down a).tensor (.up b))
    (xs.map fun t => (t.1, Diagram.mixedMultiplication (R := Complex) a b c d t.2))
  have single (p : Dot (a.comp c) (b.comp d)) :
      ev (.mixedMultiplication a b c d [(1,p)]) =
        (Diagram.mixedMultiplication (R := Complex) a b c d p).eval.toLinearMap := by
    apply LinearMap.ext
    intro x
    change (ScopedDiagram.linearCombination
      [(1, ScopedDiagram.ordinary (Diagram.mixedMultiplication a b c d p))]).eval.toLinearMap x = _
    rw [ScopedDiagram.eval_linearCombination_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
    rfl
  simp only [List.map_map] at hs
  rw [show weighted (fun p => ev (.mixedMultiplication a b c d [(1,p)])) xs =
      weighted (fun p => (Diagram.mixedMultiplication (R := Complex) a b c d p).eval.toLinearMap)
        xs from congrArg (fun s => weighted s xs) (funext single)]
  exact hs

private theorem weighted_before_left {I : Type*} {p q r : Word K H}
    (s : I → LabelledDrawing Complex p q) (t : LabelledDrawing Complex q r)
    (xs : List (Complex × I)) (S : LabelledDrawing Complex p q)
    (hS : ev S = weighted (fun i => ev (s i)) xs) :
    ev (before S t) = weighted (fun i => ev (before (s i) t)) xs := by
  let frame := composeAround (LinearMap.id : Vec p.basis.carrier →ₗ[Complex] _) (ev t)
  change frame (ev S) = _
  rw [hS, map_weighted]
  rfl

private theorem weighted_before_right {I : Type*} {p q r : Word K H}
    (s : I → LabelledDrawing Complex q r) (t : LabelledDrawing Complex p q)
    (xs : List (Complex × I)) (S : LabelledDrawing Complex q r)
    (hS : ev S = weighted (fun i => ev (s i)) xs) :
    ev (before t S) = weighted (fun i => ev (before t (s i))) xs := by
  let frame := composeAround (ev t) (LinearMap.id : Vec r.basis.carrier →ₗ[Complex] _)
  change frame (ev S) = _
  rw [hS, map_weighted]
  rfl

private theorem weighted_map_snd {I J M : Type*} [AddCommMonoid M] [Module Complex M]
    (s : J → M) (f : I → J) (xs : List (Complex × I)) :
    weighted s (xs.map fun t => (t.1, f t.2)) = weighted (fun i => s (f i)) xs := by
  simp only [weighted, List.map_map]
  rfl

variable {A G D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev leftMultiplications
    (y : Dot ((c.comp f).comp (ConjEmbedding.id E)) (c.comp f))
    (z : Dot ((d.comp e).comp (ConjEmbedding.id E)) (d.comp e))
    (xs : List (Complex × Dot (a.comp (d.comp e)) (b.comp (c.comp f)))) :=
  before (atLeft (.parallelUp d e (d.comp e) (ConjEmbedding.id E)
    [(1, z.inverse)]) (.down f))
    (before (atRight (.up (d.comp e))
      (.mixedMultiplication (c.comp f) c (ConjEmbedding.id E) f [(1, y)]))
      (atLeft (.mixedMultiplication a b (d.comp e) (c.comp f) xs) (.up c)))

private abbrev rightMultiplications (u : ConjEmbedding B A) (v : ConjEmbedding C B)
    (w : ConjEmbedding F B) (ell : Dot (b.comp c) (u.comp w))
    (m : Dot (a.comp d) (u.comp v)) (ns : List (Complex × Dot (v.comp e) (w.comp f))) :=
  before (atRight (.up d) (.mixedMultiplication v w e f ns))
    (before (atLeft (.mixedMultiplication a u d v [(1,m)]) (.up w))
      (atRight (.down a) (.parallelUp u w b c [(1,ell.inverse)])))

private theorem comparePlaced {I : Type*}
    (xs : List (Complex × I))
    (p : I → Dot (a.comp (d.comp e)) ((b.comp c).comp f))
    (hf : ∀ i, ∀ z, Set.Finite {k | Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f (p i) k = z})
    (hp : ∀ i, ∀ z, Set.Finite {k | Generator.mixedMultiplicationBasis a b (d.comp e) (c.comp f) (p i) k = z})
    (hs : ∀ z, Set.Finite {k | Generator.mixedMultiplicationBasis (c.comp f) c
      (ConjEmbedding.id E) f (Dot.id (c.comp f)) k = z})
    (u : ConjEmbedding B A) (v : ConjEmbedding C B) (w : ConjEmbedding F B)
    (ell : Dot (b.comp c) (u.comp w)) (m : Dot (a.comp d) (u.comp v))
    (n : I → Dot (v.comp e) (w.comp f))
    (hm : ∀ z, Set.Finite {k | Generator.mixedMultiplicationBasis a u d v m k = z})
    (hn : ∀ i, ∀ z, Set.Finite {k | Generator.mixedMultiplicationBasis v w e f (n i) k = z})
    (helem : ∀ i, rightParameter a b c d e f ell m (n i) = (p i).element) :
    let x := fun i => (⟨p i, hp i⟩ : ProjectionDot.Mixed a b (d.comp e) (c.comp f))
    let y : ProjectionDot.Mixed (c.comp f) c (ConjEmbedding.id E) f := ⟨Dot.id (c.comp f), hs⟩
    let z : Dot ((d.comp e).comp (ConjEmbedding.id E)) (d.comp e) := Dot.id (d.comp e)
    let n' := fun i => (⟨n i, hn i⟩ : ProjectionDot.Mixed v w e f)
    (rightDrawing a b c d e f u v w [(1,ell)] [(1,⟨m,hm⟩)]
        (xs.map fun t => (t.1, n' t.2))).interpret.eval =
      (leftDrawing a b c d e f (d.comp e) (c.comp f) (ConjEmbedding.id E)
        (xs.map fun t => (t.1, x t.2)) [(1,y)] [(1,z)]).interpret.eval ∧
    (rightMultiplications a b c d e f u v w ell m (xs.map fun t => (t.1,n t.2))).interpret.eval =
      (leftMultiplications a b c d e f y.dot z (xs.map fun t => (t.1,(x t.2).dot))).interpret.eval := by
  intro x y z n'
  let parameter := fun i => (⟨p i, hf i⟩ : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
  have hleft (i : I) :
      leftParameter a b c d e f (p i) y.dot z = (p i).element := by
    change a.toHom (1 : G)⁻¹ * (p i).element * b.toHom (1 : D) = _
    simp
  have hproj (i : I) :
      (rightDrawing a b c d e f u v w [(1,ell)] [(1,⟨m,hm⟩)] [(1,n' i)]).interpret.eval =
      (leftDrawing a b c d e f (d.comp e) (c.comp f) (ConjEmbedding.id E)
        [(1,x i)] [(1,y)] [(1,z)]).interpret.eval := by
    exact ((right_project_eval a b c d e f (parameter i) ell ⟨m,hm⟩ (n' i)).2 (helem i)).trans
      (((left_project_eval a b c d e f (parameter i) (x i) y z).2 (hleft i)).symm)
  have hmul (i : I) :
      (rightMultiplications a b c d e f u v w ell m [(1,n i)]).interpret.eval =
      (leftMultiplications a b c d e f y.dot z [(1,(x i).dot)]).interpret.eval := by
    exact ((right_mul_eval a b c d e f (parameter i) ell m (n i)).2 (helem i)).trans
      (((left_mul_eval a b c d e f (parameter i) (r := d.comp e) (s := c.comp f)
        (t := ConjEmbedding.id E) (p i) y.dot z).2 (hleft i)).symm)
  constructor
  · apply Biset.Hom.ext
    change ev (rightDrawing a b c d e f u v w [(1,ell)] [(1,⟨m,hm⟩)]
        (xs.map fun t => (t.1, n' t.2))) =
      ev (leftDrawing a b c d e f (d.comp e) (c.comp f) (ConjEmbedding.id E)
        (xs.map fun t => (t.1, x t.2)) [(1,y)] [(1,z)])
    simp only [rightDrawing, leftDrawing]
    rw [weighted_before_right _ _ _ _ (weighted_before_right _ _ _ _
      (weighted_atRight _ _ _ _ (weighted_compact _ _ _ _ _)))]
    rw [weighted_before_left _ _ _ _
      (weighted_atLeft _ _ _ (weighted_compact _ _ _ _ _))]
    rw [weighted_map_snd _ n' xs, weighted_map_snd _ x xs]
    exact congrArg (fun g => weighted g xs) (funext fun i =>
      congrArg Biset.Hom.toLinearMap (hproj i))
  · apply Biset.Hom.ext
    change ev (rightMultiplications a b c d e f u v w ell m (xs.map fun t => (t.1,n t.2))) =
      ev (leftMultiplications a b c d e f y.dot z (xs.map fun t => (t.1,(x t.2).dot)))
    simp only [rightMultiplications, leftMultiplications]
    rw [weighted_before_left _ _ _ _
      (weighted_atRight _ _ _ _ (weighted_mixed _ _ _ _ _))]
    rw [weighted_before_right _ _ _ _ (weighted_before_right _ _ _ _
      (weighted_atLeft _ _ _ (weighted_mixed _ _ _ _ _)))]
    rw [weighted_map_snd _ n xs, weighted_map_snd _ (fun i => (x i).dot) xs]
    exact congrArg (fun g => weighted g xs) (funext fun i =>
      congrArg Biset.Hom.toLinearMap (hmul i))

end
end CommonRightRegionAux

namespace CommonRightRegionAux
open MackeyDiagrams

private theorem leastContaining {A : Subgroup Finitary} (hA : Parabolic A)
    (S T : Subgroup A) {I : Type*} (diff : I → A) :
    ∃ H : Subgroup A, IsLeast {K : Subgroup A | Parabolic (K.map A.subtype) ∧
      S ≤ K ∧ T ≤ K ∧ ∀ i, diff i ∈ K} H := by
  let gen : Set A := (S : Set A) ∪ ((T : Set A) ∪ Set.range diff)
  let Q := Subgroup.closure gen
  let ambient := Finitary.subtype.comp A.subtype
  have hAmbient : Function.Injective ambient := Finitary.subtype_injective.comp A.subtype_injective
  have ambient_range : ambient.range = A.map Finitary.subtype := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have hmap (K : Subgroup A) : K.map ambient = (K.map A.subtype).map Finitary.subtype :=
    (Subgroup.map_map K Finitary.subtype A.subtype).symm
  let _ : Finite A := parabolic_finite hA
  let _ : Finite (Q.map ambient) :=
    Finite.of_injective _ (Q.equivMapOfInjective ambient hAmbient).symm.injective
  have hFin : Q.map ambient ≤ Finitary := by
    rintro _ ⟨x, _, rfl⟩
    exact x.val.property
  -- Lemma 7.2 applies to the generated subgroup. The candidate A supplies
  -- the bound that lets us pull the least ambient parabolic back into A.
  obtain ⟨P, hP⟩ : ∃ P : Subgroup Perm, IsLeast
      {K : Subgroup Perm | ParabolicPerm K ∧ Q.map ambient ≤ K} P := by
    have ext := (ExtremalParabolicsOfFiniteGroup (Q.map ambient) hFin).2
    exact ⟨_, ⟨⟨(parabolicPerm_iff _).2 ext.1.1, ext.1.2⟩,
      fun K hK => ext.2 ⟨(parabolicPerm_iff _).1 hK.1, hK.2⟩⟩⟩
  have P_le : P ≤ ambient.range := hP.2
    ⟨by rw [ambient_range]; exact hA, Subgroup.map_le_range _ _⟩
  let H := P.comap ambient
  have hH : H.map ambient = P := Subgroup.map_comap_eq_self P_le
  have Q_le : Q ≤ H := Subgroup.map_le_iff_le_comap.mp hP.1.2
  refine ⟨H, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show ParabolicPerm ((H.map A.subtype).map Finitary.subtype)
    rw [← hmap, hH]
    exact hP.1.1
  · intro x hx
    exact Q_le (Subgroup.subset_closure (Set.mem_union_left _ hx))
  · intro x hx
    exact Q_le (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_union_left _ hx)))
  · intro i
    exact Q_le (Subgroup.subset_closure (Set.mem_union_right _
      (Set.mem_union_right _ ⟨i, rfl⟩)))
  · rintro K ⟨hK, hS, hT, hd⟩
    have bounds : Q ≤ K := by
      apply (Subgroup.closure_le K).mpr
      rintro x (hx | hx)
      · exact hS hx
      · rcases hx with hx | ⟨i, rfl⟩
        · exact hT hx
        · exact hd i
    apply (Subgroup.map_le_map_iff_of_injective hAmbient).mp
    rw [hH]
    exact hP.2 ⟨by rw [hmap]; exact hK, Subgroup.map_mono bounds⟩

end CommonRightRegionAux


theorem ParabolicCommonRightRegionForLinearLabels : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let parabolic := fun (H : Subgroup U) =>
  ∃ (k : Nat) (blocks : Fin k → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H =
      iSup (fun i => MonoidHom.range
        (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ blocks i)))
∀ {G A D F C E : Subgroup U},
  parabolic G → parabolic A → parabolic D → parabolic F →
  parabolic C → parabolic E →
  ∀ (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let cf := comp c f
  let idE := MackeyDiagrams.ConjEmbedding.id E
  let image := fun {H K : Subgroup U} (i : MackeyDiagrams.ConjEmbedding H K) =>
    MonoidHom.range (hom i)
  ∀ (p₀ : A) (coeff : MackeyDiagrams.DotLabel Complex (comp a de) (comp bc f)),
  let Support := ↥(Finsupp.support coeff)
  let element := fun (p : Support) => MackeyDiagrams.Dot.element p.val
  let terms := fun {X : Type} (label : Support → X) =>
    List.map (fun p => (coeff p.val, label p))
      (Finset.toList (Finset.attach (Finsupp.support coeff)))
  let containing : Set (Subgroup A) := {H |
    parabolic (Subgroup.map (Subgroup.subtype A) H) ∧
    image ad ≤ H ∧
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj p₀)) (image bc) ≤ H ∧
    ∀ p : Support, element p * p₀⁻¹ ∈ H}
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let outside := tensor (tensor (down a) (up b)) (up c)
  let inside := tensor (tensor (up d) (up e)) (down f)
  let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let identity := fun {K H : Subgroup U} (x : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) x)
  let atRight := fun {K H J L J' : Subgroup U} (x : MackeyDiagrams.Word K H)
      {y : MackeyDiagrams.Word H J} {z : MackeyDiagrams.Word J L}
      {y' : MackeyDiagrams.Word H J'} {z' : MackeyDiagrams.Word J' L}
      (q : MackeyDiagrams.LabelledDrawing Complex (tensor y z) (tensor y' z')) =>
    vertical (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate x y z))
      (vertical (horizontal (identity x) q)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate x y' z')))
  let eval := fun {K H : Subgroup U} {x y : MackeyDiagrams.Word K H}
      (q : MackeyDiagrams.LabelledDrawing Complex x y) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret q)
  let basisMap := @MackeyDiagrams.Generator.mixedMultiplicationBasis U _
  let finiteFibers := fun {X Y : Type} (q : X → Y) => ∀ z, Set.Finite {w | q w = z}
  let x : Support → MackeyDiagrams.Dot (comp a de) (comp b cf) := fun p => p.val
  let y : MackeyDiagrams.Dot (comp cf idE) (comp c f) := MackeyDiagrams.Dot.id cf
  let z : MackeyDiagrams.Dot (comp de idE) de := MackeyDiagrams.Dot.id de
  (∀ p : Support, finiteFibers (basisMap a bc de f p.val)) ∧
  ∃ (firstFinite : ∀ p : Support, finiteFibers (basisMap a b de cf (x p)))
    (secondFinite : finiteFibers (basisMap cf c idE f y)),
  let leftProject : MackeyDiagrams.LabelledDrawing Complex outside inside :=
    vertical
      (horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b de cf
          (terms (fun p => ⟨x p, firstFinite p⟩)))
        (identity (up c)))
      (vertical
        (atRight (up de) (MackeyDiagrams.LabelledDrawing.compactProjection cf c idE f
          [((1 : Complex), ⟨y, secondFinite⟩)]))
        (horizontal (MackeyDiagrams.LabelledDrawing.parallelUp de idE d e [((1 : Complex), z)])
          (identity (down f))))
  let leftMultiply : MackeyDiagrams.LabelledDrawing Complex inside outside :=
    vertical
      (horizontal
        (MackeyDiagrams.LabelledDrawing.parallelUp d e de idE
          [((1 : Complex), MackeyDiagrams.Dot.inverse z)])
        (identity (down f)))
      (vertical
        (atRight (up de) (MackeyDiagrams.LabelledDrawing.mixedMultiplication cf c idE f
          [((1 : Complex), y)]))
        (horizontal (MackeyDiagrams.LabelledDrawing.mixedMultiplication a b de cf (terms x))
          (identity (up c))))
  let placed : Set (Subgroup A) := {H |
    ∃ (B : Subgroup U) (_ : parabolic B)
      (u : MackeyDiagrams.ConjEmbedding B A)
      (v : MackeyDiagrams.ConjEmbedding C B)
      (w : MackeyDiagrams.ConjEmbedding F B)
      (ell : MackeyDiagrams.Dot bc (comp u w))
      (m : MackeyDiagrams.Dot ad (comp u v))
      (n : Support → MackeyDiagrams.Dot (comp v e) (comp w f)),
      image u = H ∧
      MackeyDiagrams.Dot.element ell = p₀⁻¹ ∧
      MackeyDiagrams.Dot.element m = 1 ∧
      (∀ p, element p = hom u (MackeyDiagrams.Dot.element (n p)) * p₀) ∧
      ∃ (middleFinite : finiteFibers (basisMap a u d v m))
        (thirdFinite : ∀ p, finiteFibers (basisMap v w e f (n p))),
      let rightProject : MackeyDiagrams.LabelledDrawing Complex outside inside :=
        vertical
          (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp b c u w
            [((1 : Complex), ell)]))
          (vertical
            (horizontal
              (MackeyDiagrams.LabelledDrawing.compactProjection a u d v
                [((1 : Complex), ⟨m, middleFinite⟩)])
              (identity (up w)))
            (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f
              (terms (fun p => ⟨n p, thirdFinite p⟩)))))
      let rightMultiply : MackeyDiagrams.LabelledDrawing Complex inside outside :=
        vertical
          (atRight (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication v w e f (terms n)))
          (vertical
            (horizontal (MackeyDiagrams.LabelledDrawing.mixedMultiplication a u d v
              [((1 : Complex), m)]) (identity (up w)))
            (atRight (down a) (MackeyDiagrams.LabelledDrawing.parallelUp u w b c
              [((1 : Complex), MackeyDiagrams.Dot.inverse ell)])))
      eval rightProject = eval leftProject ∧ eval rightMultiply = eval leftMultiply}
  ∃ H : Subgroup A, IsLeast containing H ∧ IsLeast placed H
) :=
(by
  classical
  open MackeyDiagrams CommonRightRegionAux in
  intro finitary U parabolic G A D F C E hG hA hD hF hC hE a b c d e f
    comp hom bc ad de cf idE image p₀ coeff Support element terms containing
    up down tensor outside inside vertical horizontal identity atRight eval basisMap finiteFibers x y z
  -- Xiao, §8.3 after Example 8.4, archived PDF p. 39 (bc57d13777e7df14…)
  -- and the revised published PDF p. 41 (6d7e885955f23ae6…). The portal
  -- inventory has no exact numbered Alphabeta Math entry for the paragraph.
  -- Use the Case 1 projection and Case 3 multiplication wiring of Theorems
  -- 6.4 and 6.5, and Lemma 6.3 for the projection parameters. The original
  -- paragraph uses the same two fixed marks at every term of the label.
  let _ : Finite G := parabolic_finite hG
  let _ : Finite D := parabolic_finite hD
  let _ : Finite F := parabolic_finite hF
  let _ : Finite C := parabolic_finite hC
  let _ : Finite E := parabolic_finite hE
  have hf (p : Support) : finiteFibers (basisMap a bc de f p.val) :=
    finite_mixed a bc de f p.val
  have hx (p : Support) : finiteFibers (basisMap a b de cf (x p)) :=
    finite_mixed a b de cf (x p)
  have hy : finiteFibers (basisMap cf c idE f y) := finite_mixed cf c idE f y
  refine ⟨hf, hx, hy, ?_⟩
  intro leftProject leftMultiply placed
  obtain ⟨H, hH⟩ := leastContaining hA (image ad)
    ((image bc).map (MulAut.conj p₀).toMonoidHom) (fun p : Support => element p * p₀⁻¹)
  have hH' : IsLeast containing H := hH
  have necessary : placed ⊆ containing := by
    rintro K ⟨B, hB, u, v, w, ell, m, n, hK, hell, hm, hn, _⟩
    subst K
    refine ⟨parabolic_embedding u hB, ?_, ?_, ?_⟩
    · rintro _ ⟨k, rfl⟩
      refine ⟨hom v k, ?_⟩
      have he := m.intertwines k
      change hom ad k * m.element = m.element * hom u (hom v k) at he
      simpa only [hm, mul_one, one_mul] using he.symm
    · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨hom w k, ?_⟩
      have he := ell.inverse.intertwines k
      change hom u (hom w k) * ell.element⁻¹ = ell.element⁻¹ * hom bc k at he
      rw [hell, inv_inv] at he
      change hom u (hom w k) = p₀ * hom bc k * p₀⁻¹
      rw [← he, mul_inv_cancel_right]
    · intro p
      exact ⟨(n p).element, by rw [hn p, mul_inv_cancel_right]⟩
  -- Conversely use inclusion of the candidate and factor the two boundary
  -- embeddings through it. Cancellation in A justifies each third dot.
  have sufficient : containing ⊆ placed := by
    rintro K ⟨hK, hAd, hBc, hDiff⟩
    let B := K.map A.subtype
    let u := inclusion K
    let v := restrictTo ad K hAd
    let w := restrictTo (conjugated bc p₀) K (by rwa [conjugated_range])
    have hv (k : C) : hom u (hom v k) = hom ad k := rfl
    have hw (k : F) : hom u (hom w k) = p₀ * hom bc k * p₀⁻¹ := rfl
    let ell : Dot bc (comp u w) := ⟨p₀⁻¹, by
      intro k
      change hom bc k * p₀⁻¹ = p₀⁻¹ * hom u (hom w k)
      rw [hw, ← mul_assoc, inv_mul_cancel_left]⟩
    let m : Dot ad (comp u v) := ⟨1, by intro k; simp only [mul_one, one_mul]; exact (hv k).symm⟩
    let nElement (p : Support) : B :=
      ⟨((element p * p₀⁻¹ : A) : U), ⟨element p * p₀⁻¹, hDiff p, rfl⟩⟩
    have hn (p : Support) : element p = hom u (nElement p) * p₀ := by
      change element p = (element p * p₀⁻¹) * p₀
      rw [inv_mul_cancel_right]
    let n (p : Support) : Dot (comp v e) (comp w f) := ⟨nElement p, by
      intro k
      apply u.injective
      rw [map_mul, map_mul]
      change hom u (hom v (hom e k)) * (element p * p₀⁻¹) =
        (element p * p₀⁻¹) * hom u (hom w (hom f k))
      rw [hv, hw]
      have he := p.val.intertwines k
      change hom ad (hom e k) * element p = element p * hom bc (hom f k) at he
      calc
        _ = (hom ad (hom e k) * element p) * p₀⁻¹ := (mul_assoc _ _ _).symm
        _ = (element p * hom bc (hom f k)) * p₀⁻¹ := by rw [he]
        _ = _ := by group⟩
    let _ : Finite A := parabolic_finite hA
    let _ : Finite B := Finite.of_injective u.toHom u.injective
    have hm : finiteFibers (basisMap a u d v m) := finite_mixed a u d v m
    have hthird (p : Support) : finiteFibers (basisMap v w e f (n p)) :=
      finite_mixed v w e f (n p)
    refine ⟨B, hK, u, v, w, ell, m, n, inclusion_range K, rfl, rfl, hn, hm, hthird, ?_⟩
    -- Lemma 6.3 identifies the backwards transfer parameter and Case 3
    -- gives the same forward multiplication parameter. The local comparison
    -- fixes the marks that the public replacement suppliers leave existential.
    -- Apply it to the reviewed support list with each original coefficient.
    let entries := (Finset.toList (Finset.attach (Finsupp.support coeff))).map
      (fun p : Support => (coeff p.val, p))
    have helem (p : Support) : rightParameter a b c d e f ell m (n p) = element p := by
      change 1 * hom u (nElement p) * (p₀⁻¹)⁻¹ = element p
      simpa only [one_mul, inv_inv] using (hn p).symm
    have hc := comparePlaced a b c d e f entries (fun p : Support => p.val)
      hf hx hy u v w ell m n hm hthird helem
    simpa only [entries, List.map_map, Function.comp_def] using hc
  exact ⟨H, hH', ⟨sufficient hH'.1, fun _ h => hH'.2 (necessary h)⟩⟩
)
