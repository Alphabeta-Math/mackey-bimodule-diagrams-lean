import Mathlib.Data.ZMod.QuotientGroup
import MackeyDiagrams
import Proofs.ParabolicRightOrbitMultiplicity
import Proofs.ParabolicCaseSixStrictStabilizerObstruction

set_option maxHeartbeats 2000000

namespace CaseSixCharThree

open MackeyDiagrams
open scoped BigOperators

universe u v
variable {R : Type v} [CommRing R]

private noncomputable def weighted {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Diagram R p q) : ScopedDiagram R p q :=
  .linearCombination (I.toList.map fun i => (weight i, .ordinary (term i)))

private theorem weighted_apply {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Diagram R p q) (z : p.basis.carrier →₀ R) :
    (weighted (R := R) I weight term).eval.toLinearMap z =
      ∑ i ∈ I, weight i • (term i).eval.toLinearMap z := by
  rw [weighted, ScopedDiagram.eval_linearCombination_apply, List.map_map]
  exact Finset.sum_map_toList I _

private theorem frameLeft {U : Type*} [Group U] {K H J : Subgroup U}
    (p : Word K H) {q q' : Word H J} {ι : Type*}
    (I : Finset ι) (weight : ι → R) (term : ι → Diagram R q q') :
    ((Biset.Hom.id p.basis).horizontal (weighted (R := R) I weight term).eval).toLinearMap =
      ∑ i ∈ I, weight i • ((Biset.Hom.id p.basis).horizontal (term i).eval).toLinearMap := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((Biset.Hom.id p.basis).horizontal (weighted (R := R) I weight term).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) =
    (∑ i ∈ I, weight i • ((Biset.Hom.id p.basis).horizontal (term i).eval).toLinearMap)
      (Finsupp.single (p.basis.pair q.basis x y) r)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Biset.Hom.horizontal_single,
    weighted_apply, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, mul_comm r (weight i)]

private theorem frameRight {U : Type*} [Group U] {K H J : Subgroup U}
    {p p' : Word K H} (q : Word H J) {ι : Type*}
    (I : Finset ι) (weight : ι → R) (term : ι → Diagram R p p') :
    ((weighted (R := R) I weight term).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap =
      ∑ i ∈ I, weight i • ((term i).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((weighted (R := R) I weight term).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) =
    (∑ i ∈ I, weight i • ((term i).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap)
      (Finsupp.single (p.basis.pair q.basis x y) r)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Biset.Hom.horizontal_single,
    weighted_apply]
  let pair := (Biset.pairLinear R p'.basis q.basis).flip
    ((Biset.Hom.id q.basis).toLinearMap (Finsupp.single y 1))
  change r • pair (∑ i ∈ I, weight i • (term i).eval.toLinearMap (Finsupp.single x 1)) =
    ∑ i ∈ I, weight i • (r • pair ((term i).eval.toLinearMap (Finsupp.single x 1)))
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, mul_comm r (weight i)]

section
variable {U : Type*} [Group U] {G A D F C E B' : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (i : ConjEmbedding B' A) (j : ConjEmbedding B' F) (k : ConjEmbedding B' C)

private abbrev Inner := (Word.up i).tensor (.down j)
private abbrev Lower := Dot (b.comp i) (d.comp j)
private abbrev Middle := Dot (a.comp i) (c.comp k)
private abbrev Upper := Dot (e.comp k) (f.comp j)
private abbrev Bottom := (Word.up a).tensor ((Word.down b).tensor (.up d))
private abbrev Top := (Word.up c).tensor ((Word.down e).tensor (.up f))

private abbrev Fibers (r : Lower b d i j) :=
  ∀ x : D, Set.Finite {w | Generator.mixedProduct b d
    (Generator.mixedMultiplicationBasis b d i j r w) = x}

private def projectionDot (r : Lower b d i j) (hr : Fibers b d i j r) :
    ProjectionDot.Mixed b d i j :=
  ⟨r, fun z => (hr (Generator.mixedProduct b d z)).subset
    (fun _ hw => congrArg (Generator.mixedProduct b d) hw)⟩

private abbrev projection (r : ProjectionDot.Mixed b d i j) :
    Diagram R ((Word.down b).tensor (.up d)) (Inner i j) :=
  .mixedProjection b d i j r.dot r.finite

private abbrev parallel (t : Middle a c i k) :
    Diagram R ((Word.up a).tensor (.up i)) ((Word.up c).tensor (.up k)) :=
  .parallelUp a i c k t

private abbrev multiply (s : Upper e f j k) :
    Diagram R (Inner k j) ((Word.down e).tensor (.up f)) :=
  .mixedMultiplication e f k j s

private abbrev unassoc : Diagram R
    ((Word.up a).tensor (Inner i j)) (((Word.up a).tensor (.up i)).tensor (.down j)) :=
  .unassociate (.up a) (.up i) (.down j)

private abbrev assoc : Diagram R
    (((Word.up c).tensor (.up k)).tensor (.down j)) ((Word.up c).tensor (Inner k j)) :=
  .associate (.up c) (.up k) (.down j)

private noncomputable def drawing
    (lower : List (R × ProjectionDot.Mixed b d i j))
    (middle : List (R × Middle a c i k)) (upper : List (R × Upper e f j k)) :
    LabelledDrawing R (Bottom a b d) (Top c e f) :=
  .vertical
    (.horizontal (.ordinary (.id (.up a))) (.compactProjection b d i j lower))
    (.vertical (.ordinary (unassoc (R := R) a i j))
      (.vertical (.horizontal (.parallelUp a i c k middle) (.ordinary (.id (.down j))))
        (.vertical (.ordinary (assoc (R := R) c j k))
          (.horizontal (.ordinary (.id (.up c))) (.mixedMultiplication e f k j upper)))))

private noncomputable def input (g : G) (x : D) : (Bottom a b d).basis.carrier →₀ R :=
  Finsupp.single ((Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    g (Generator.mixedPair b d x)) 1

private noncomputable def output (t : Middle a c i k) (s : Upper e f j k)
    (g : G) (α : A) (h : F) : (Top c e f).basis.carrier →₀ R :=
  Finsupp.single ((Biset.induction c).pair ((Word.down e).tensor (.up f)).basis
    (g * a.toHom α * t.element) (Generator.mixedPair e f (s.element * f.toHom h))) 1

private noncomputable def column (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (Top c e f).basis.carrier →₀ R :=
  ∑ w ∈ (hr x).toFinset, output (R := R) a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

private noncomputable def tail (t : Middle a c i k) (s : Upper e f j k) :
    Diagram R ((Word.up a).tensor (Inner i j)) (Top c e f) :=
  (unassoc (R := R) a i j).vertical (((parallel (R := R) a c i k t).horizontal (.id (.down j))).vertical
    ((assoc (R := R) c j k).vertical ((Diagram.id (.up c)).horizontal (multiply (R := R) e f j k s))))

private theorem tail_pair (t : Middle a c i k) (s : Upper e f j k) (g : G) (α : A) (h : F) :
    (tail (R := R) a c e f i j k t s).eval.toLinearMap
      (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
        ((Biset.induction i).pair (Biset.restriction j) α h)) 1) =
    output (R := R) a c e f i j k t s g α h := by
  -- Use the merge, dot and split on singleton columns after reassociating.
  have hm : (parallel (R := R) a c i k t).eval.toLinearMap
      (Finsupp.single ((Biset.induction a).pair (Biset.induction i) g α) 1) =
      Finsupp.single ((Biset.induction c).pair (Biset.induction k)
        (g * a.toHom α * t.element) 1) 1 := by
    change (Diagram.splitUp (R := R) c k).eval.toLinearMap
      ((Diagram.upDot t).eval.toLinearMap
        ((Diagram.mergeUp a i).eval.toLinearMap
          (Finsupp.single ((Biset.induction a).pair (Biset.induction i) g α) 1))) = _
    rw [Diagram.eval_mergeUp_single (R := R) a i g α 1,
      Diagram.eval_upDot_single (R := R) t (g * a.toHom α) 1,
      Diagram.eval_splitUp_single (R := R) c k (g * a.toHom α * t.element) 1]
  -- Step 3: the unit inserted by the split leaves just the upper dot and f(h).
  have hp : (multiply (R := R) e f j k s).eval.toLinearMap
      (Finsupp.single ((Biset.induction k).pair (Biset.restriction j) (1 : C) h) 1) =
      Finsupp.single (Generator.mixedPair e f (s.element * f.toHom h)) 1 := by
    change (Generator.mixedMultiplication e f k j s R).toLinearMap _ = _
    rw [Generator.mixedMultiplication, Biset.Hom.ofFunction_single]
    change Finsupp.single (Generator.mixedPair e f (e.toHom 1 * s.element * f.toHom h)) 1 = _
    rw [map_one, one_mul]
  change ((Diagram.id (.up c)).horizontal (multiply (R := R) e f j k s)).eval.toLinearMap
    ((assoc (R := R) c j k).eval.toLinearMap
      (((parallel (R := R) a c i k t).horizontal (Diagram.id (.down j))).eval.toLinearMap
        ((unassoc (R := R) a i j).eval.toLinearMap
          (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
            ((Biset.induction i).pair (Biset.restriction j) α h)) 1)))) = _
  rw [Diagram.eval_unassociate_single (R := R) (.up a) (.up i) (.down j) g α h 1,
    Diagram.eval_horizontal_single (parallel (R := R) a c i k t) (Diagram.id (.down j)),
    one_smul, Diagram.eval_id_apply, hm, Biset.pairLinear_single, one_mul,
    Diagram.eval_associate_single (R := R) (.up c) (.up k) (.down j),
    Diagram.eval_horizontal_single (Diagram.id (.up c)) (multiply (R := R) e f j k s),
    one_smul, Diagram.eval_id_apply, hp, Biset.pairLinear_single, one_mul]
  rfl

private theorem projectionColumn (r : Lower b d i j) (hr : Fibers b d i j r) (x : D) :
    (projection (R := R) b d i j (projectionDot b d i j r hr)).eval.toLinearMap
      (Finsupp.single (Generator.mixedPair b d x) 1) =
    ∑ w ∈ (hr x).toFinset, Finsupp.single w 1 := by
  -- Step 1: use the transfer column of Proposition 5.1 with the given finite
  -- group fiber. The transfer formula and mixedEquiv identify the two
  -- fibers over the specified input, independently of the coefficient ring.
  let dot := projectionDot b d i j r hr
  have hf : (dot.finite (Generator.mixedPair b d x)).toFinset = (hr x).toFinset := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    change Generator.mixedMultiplicationBasis b d i j r w = Generator.mixedPair b d x ↔
      Generator.mixedProduct b d (Generator.mixedMultiplicationBasis b d i j r w) = x
    constructor
    · intro hw
      rw [hw, Generator.mixedProduct_mixedPair]
    · intro hw
      apply (Generator.mixedEquiv b d).injective
      exact hw.trans (Generator.mixedProduct_mixedPair b d x).symm
  change (Generator.mixedProjection b d i j dot.dot R dot.finite).toLinearMap
    (Finsupp.single (Generator.mixedPair b d x) 1) = _
  rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul,
    Biset.Hom.transferBasis_sum, hf]

private theorem oneTerm (r : Lower b d i j) (hr : Fibers b d i j r)
    (t : Middle a c i k) (s : Upper e f j k) (g : G) (x : D) :
    (tail (R := R) a c e f i j k t s).eval.toLinearMap
      (((Diagram.id (.up a)).horizontal (projection (R := R) b d i j (projectionDot b d i j r hr))).eval.toLinearMap
        (input (R := R) a b d g x)) =
    column (R := R) a b d c e f i j k r hr t s g x := by
  rw [input, Diagram.eval_horizontal_single (Diagram.id (.up a))
    (projection (R := R) b d i j (projectionDot b d i j r hr)),
    one_smul, Diagram.eval_id_apply, projectionColumn b d i j r hr x, map_sum, map_sum]
  unfold column
  apply Finset.sum_congr rfl
  intro w _
  rw [Biset.pairLinear_single, one_mul]
  have hw : (Biset.induction i).pair (Biset.restriction j) (Quotient.out w).1 (Quotient.out w).2 = w :=
    Quotient.out_eq' w
  calc
    _ = (tail (R := R) a c e f i j k t s).eval.toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g
          ((Biset.induction i).pair (Biset.restriction j) (Quotient.out w).1 (Quotient.out w).2)) 1) :=
      congrArg (fun v => (tail (R := R) a c e f i j k t s).eval.toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Inner i j).basis g v) 1)) hw.symm
    _ = _ := tail_pair a c e f i j k t s g (Quotient.out w).1 (Quotient.out w).2

private theorem projectionWeighted {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → ProjectionDot.Mixed b d i j) :
    (LabelledDrawing.compactProjection b d i j
      (I.toList.map fun u => (weight u, term u))).interpret =
      weighted (R := R) I weight (fun u => projection (R := R) b d i j (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem parallelWeighted {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Middle a c i k) :
    (LabelledDrawing.parallelUp a i c k (I.toList.map fun u => (weight u, term u))).interpret =
      weighted (R := R) I weight (fun u => parallel (R := R) a c i k (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem multiplyWeighted {ι : Type*} (I : Finset ι) (weight : ι → R)
    (term : ι → Upper e f j k) :
    (LabelledDrawing.mixedMultiplication e f k j (I.toList.map fun u => (weight u, term u))).interpret =
      weighted (R := R) I weight (fun u => multiply (R := R) e f j k (term u)) := by
  simp only [LabelledDrawing.interpret, weighted, List.map_map]
  rfl

private theorem weightedCase {ι₁ ι₂ ι₃ : Type*}
    (I : Finset ι₁) (J : Finset ι₂) (K : Finset ι₃)
    (l : ι₁ → R) (m : ι₂ → R) (n : ι₃ → R)
    (r : ι₁ → Lower b d i j) (hr : ∀ u, Fibers b d i j (r u))
    (t : ι₂ → Middle a c i k) (s : ι₃ → Upper e f j k) (g : G) (x : D) :
    (drawing (R := R) a b d c e f i j k
      (I.toList.map fun u => (l u, projectionDot b d i j (r u) (hr u)))
      (J.toList.map fun v => (m v, t v)) (K.toList.map fun w => (n w, s w))).interpret.eval.toLinearMap
        (input (R := R) a b d g x) =
    ∑ u ∈ I, ∑ v ∈ J, ∑ w ∈ K,
      (l u * m v * n w) • column (R := R) a b d c e f i j k (r u) (hr u) (t v) (s w) g x := by
  -- Step 4: linearity on the three supported labels. Use Finset-indexed sums
  -- through the shared, genuinely horizontal frames, then multiply the weights.
  let project u := projectionDot b d i j (r u) (hr u)
  let D₁ := LabelledDrawing.compactProjection b d i j (I.toList.map fun u => (l u, project u))
  let D₂ := LabelledDrawing.parallelUp a i c k (J.toList.map fun v => (m v, t v))
  let D₃ := LabelledDrawing.mixedMultiplication e f k j (K.toList.map fun w => (n w, s w))
  change ((Biset.Hom.id (Word.up c).basis).horizontal D₃.interpret.eval).toLinearMap
    ((assoc (R := R) c j k).eval.toLinearMap
      ((D₂.interpret.eval.horizontal (Biset.Hom.id (Word.down j).basis)).toLinearMap
        ((unassoc (R := R) a i j).eval.toLinearMap
          (((Biset.Hom.id (Word.up a).basis).horizontal D₁.interpret.eval).toLinearMap
            (input (R := R) a b d g x))))) = _
  have h₁ : D₁.interpret = weighted (R := R) I l (fun u => projection (R := R) b d i j (project u)) :=
    projectionWeighted b d i j I l project
  have h₂ : D₂.interpret = weighted (R := R) J m (fun v => parallel (R := R) a c i k (t v)) :=
    parallelWeighted a c i k J m t
  have h₃ : D₃.interpret = weighted (R := R) K n (fun w => multiply (R := R) e f j k (s w)) :=
    multiplyWeighted e f j k K n s
  rw [h₁, h₂, h₃]
  rw [frameLeft, frameRight, frameLeft]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  exact congrArg ((l u * m v * n w) • ·) (oneTerm (R := R) a b d c e f i j k (r u) (hr u) (t v) (s w) g x)

end


private abbrev finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (S : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
private abbrev parabolic (H : Subgroup finitary) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H.map finitary.subtype = iSup (fun i => blockSym (blocks i))
private abbrev points : Finset Nat := {1, 2, 3}
private abbrev S₃ := Subgroup.comap finitary.subtype (blockSym points)
private abbrev extendBlock (S : Finset Nat) := Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S)

private theorem extend_mem (σ : Equiv.Perm ↥points) : extendBlock points σ ∈ finitary := by
  apply _root_.mem_closure_isSwap'.2
  apply (Finset.finite_toSet points).subset
  intro n moved
  by_contra outside
  exact moved (MulAction.mem_fixedBy.mpr (Equiv.Perm.ofSubtype_apply_of_not_mem σ outside))

private def extend (σ : Equiv.Perm ↥points) : S₃ :=
  ⟨⟨extendBlock points σ, extend_mem σ⟩, ⟨σ, rfl⟩⟩

private theorem extend_surj : Function.Surjective extend := by
  intro ⟨⟨σ, _⟩, h⟩
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, Subtype.ext (Subtype.ext hρ)⟩

private instance : Finite S₃ := Finite.of_surjective extend extend_surj

private def extendHom : Equiv.Perm ↥points →* S₃ where
  toFun := extend
  map_one' := Subtype.ext (Subtype.ext (map_one (extendBlock points)))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul (extendBlock points) x y))

private theorem extend_inj : Function.Injective extendHom := by
  intro x y h
  have he := congrArg (fun u : S₃ => ((u : finitary) : Equiv.Perm Nat)) h
  exact Equiv.Perm.ofSubtype_injective he

private abbrev label₁ : ↥points := ⟨1, by decide⟩
private abbrev label₂ : ↥points := ⟨2, by decide⟩
private abbrev label₃ : ↥points := ⟨3, by decide⟩
private def c₀ := Equiv.swap label₁ label₂ * Equiv.swap label₂ label₃
private abbrev cycle := extendHom c₀
private abbrev transposition := extendHom (Equiv.swap label₁ label₂)

-- Step 1 of Example 8.5 (unnumbered in the portal): do the finite calculation
-- on the three actual points. These decidable computations are kernel-checked.
private theorem small_pow : c₀ ^ 3 = 1 := by decide
private theorem small_ne : c₀ ≠ 1 := by decide
private theorem small_symm_ne : c₀ ≠ c₀⁻¹ := by decide
private theorem small_flip : Equiv.swap label₁ label₂ * c₀ * (Equiv.swap label₁ label₂)⁻¹ =
    c₀⁻¹ := by decide
private theorem small_conj (g : Equiv.Perm ↥points) :
    g * c₀ * g⁻¹ = c₀ ∨ g * c₀ * g⁻¹ = c₀⁻¹ := by
  revert g
  decide

private theorem cycle_ne : cycle ≠ cycle⁻¹ := by
  intro h
  apply small_symm_ne
  exact extend_inj (h.trans (map_inv extendHom c₀).symm)

private theorem cycle_order : orderOf cycle = 3 := by
  rw [orderOf_injective _ extend_inj]
  exact orderOf_eq_prime small_pow small_ne

private theorem cycle_card : Nat.card (Subgroup.zpowers cycle) = 3 := by
  rw [Nat.card_zpowers, cycle_order]

private theorem cycle_flip : transposition * cycle * transposition⁻¹ = cycle⁻¹ := by
  simpa only [map_mul, map_inv] using congrArg extendHom small_flip

private theorem cycle_conj (g : S₃) :
    g * cycle * g⁻¹ = cycle ∨ g * cycle * g⁻¹ = cycle⁻¹ := by
  obtain ⟨g, rfl⟩ := extend_surj g
  change extendHom g * cycle * (extendHom g)⁻¹ = cycle ∨
    extendHom g * cycle * (extendHom g)⁻¹ = cycle⁻¹
  rcases small_conj g with h | h
  · left
    simpa only [map_mul, map_inv] using congrArg extendHom h
  · right
    simpa only [map_mul, map_inv] using congrArg extendHom h

private theorem S₃_parabolic : parabolic S₃ := by
  refine ⟨1, fun _ => points, fun _ => ⟨1, show 1 ∈ points by decide⟩, ?_, ?_⟩
  · intro i j h
    exact (h (Subsingleton.elim i j)).elim
  · change (Subgroup.comap finitary.subtype (blockSym points)).map finitary.subtype =
      ⨆ _ : Fin 1, blockSym points
    rw [iSup_const]
    apply Subgroup.map_comap_eq_self
    rintro _ ⟨σ, rfl⟩
    exact ⟨⟨extendBlock points σ, extend_mem σ⟩, rfl⟩

private theorem swap_order {σ : Equiv.Perm Nat} (hs : σ.IsSwap) : orderOf σ = 2 := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  apply orderOf_eq_prime
  · rw [pow_two, Equiv.swap_mul_self]
  · exact fun h => hab (Equiv.swap_eq_one_iff.mp h)

private theorem small_centralizer (g : Equiv.Perm ↥points) :
    g * c₀ = c₀ * g → g = 1 ∨ g = c₀ ∨ g = c₀⁻¹ := by
  revert g
  decide

private theorem cycle_centralizer {g : S₃} (h : g * cycle = cycle * g) :
    g ∈ Subgroup.zpowers cycle := by
  obtain ⟨g, rfl⟩ := extend_surj g
  change extendHom g * extendHom c₀ = extendHom c₀ * extendHom g at h
  rw [← map_mul, ← map_mul] at h
  rcases small_centralizer g (extend_inj h) with h | h | h
  · rw [h]
    change extendHom 1 ∈ Subgroup.zpowers cycle
    rw [map_one]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers _
  · rw [h]
    change extendHom c₀⁻¹ ∈ Subgroup.zpowers cycle
    rw [map_inv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

section IdentityBoundary

variable {W : Type*} [Group W] (H : Subgroup W)

private abbrev identity := ConjEmbedding.id H
private abbrev Up := Word.up (identity H)
private abbrev Down := Word.down (identity H)
private abbrev Mixed := (Down H).tensor (Up H)
private abbrev Boundary := (Up H).tensor (Mixed H)
private abbrev Basis := (Boundary H).basis.carrier
private abbrev PairBasis := Basis H × Basis H
private abbrev point (g x : H) : Basis H :=
  (Up H).basis.pair (Mixed H).basis g (Generator.mixedPair (identity H) (identity H) x)
private abbrev regularBasis (x : H) := point H x 1
private abbrev onBasis : MulAction (H × H) (Basis H) where
  smul := (Boundary H).basis.act
  one_smul := (Boundary H).basis.one_act
  mul_smul := (Boundary H).basis.mul_act
private abbrev onPairs : MulAction (H × H) (PairBasis H) where
  smul q z := ((Boundary H).basis.act q z.1, (Boundary H).basis.act q z.2)
  one_smul z := Prod.ext ((Boundary H).basis.one_act z.1) ((Boundary H).basis.one_act z.2)
  mul_smul q q' z := Prod.ext ((Boundary H).basis.mul_act q q' z.1)
    ((Boundary H).basis.mul_act q q' z.2)
private abbrev pairOrbit (z : PairBasis H) :=
  letI := onPairs H
  MulAction.orbit (H × H) z
private abbrev projectBasis (z : Basis H) :=
  (@MulAction.stabilizer (H × H) _ _ (onBasis H) z).map (MonoidHom.snd H H)
private abbrev projectPair (z : PairBasis H) :=
  (@MulAction.stabilizer (H × H) _ _ (onPairs H) z).map (MonoidHom.snd H H)
private abbrev ambientProject (z : PairBasis H) := (projectPair H z).map H.subtype

private theorem point_normal (g x : H) : point H g x = regularBasis H (g * x) := by
  apply Quotient.sound
  refine ⟨x⁻¹, ?_, ?_⟩
  · change 1 * g * (x⁻¹)⁻¹ = g * x
    rw [one_mul, inv_inv]
  · apply (Generator.mixedEquiv (identity H) (identity H)).injective
    change (x⁻¹ * x * (1 : H)⁻¹) * (1 * 1 * (1 : H)⁻¹) =
      Generator.mixedProduct (identity H) (identity H)
        (Generator.mixedPair (identity H) (identity H) 1)
    simp

private theorem regular_bijective : Function.Bijective (regularBasis H) := by
  constructor
  · intro x y hxy
    obtain ⟨h, hh, hb⟩ := Quotient.exact hxy
    have h₁ : 1 * x * h⁻¹ = y := hh
    have h₂ := congrArg (Generator.mixedProduct (identity H) (identity H)) hb
    change (h * 1 * (1 : H)⁻¹) * (1 * 1 * (1 : H)⁻¹) =
      Generator.mixedProduct (identity H) (identity H)
        (Generator.mixedPair (identity H) (identity H) 1) at h₂
    have he : h = 1 := by simpa using h₂
    simpa [he] using h₁
  · intro z
    obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
    obtain ⟨x, rfl⟩ := (Generator.mixedEquiv (identity H) (identity H)).symm.surjective y
    exact ⟨g * x, (point_normal H g x).symm⟩

private theorem act_regular (q : H × H) (x : H) :
    (Boundary H).basis.act q (regularBasis H x) = regularBasis H (q.1 * x * q.2⁻¹) := by
  have he : (Boundary H).basis.act q (regularBasis H x) = point H (q.1 * x) q.2⁻¹ := by
    change (Up H).basis.pair (Mixed H).basis
      (q.1 * x * (1 : H)⁻¹)
      ((Down H).basis.pair (Up H).basis
        ((1 : H) * 1 * (1 : H)⁻¹) ((1 : H) * 1 * q.2⁻¹)) = _
    simp only [inv_one, mul_one, one_mul]
    change (Up H).basis.pair (Mixed H).basis (q.1 * x)
      ((Down H).basis.pair (Up H).basis 1 q.2⁻¹) = _
    congr 1
    apply (Generator.mixedEquiv (identity H) (identity H)).injective
    change 1 * q.2⁻¹ = Generator.mixedProduct (identity H) (identity H)
      (Generator.mixedPair (identity H) (identity H) q.2⁻¹)
    simp
  rw [he, point_normal]

private theorem project_basis_top (x : H) : projectBasis H (regularBasis H x) = ⊤ := by
  apply top_unique
  intro h _
  refine ⟨(x * h * x⁻¹, h), ?_, rfl⟩
  change (Boundary H).basis.act _ (regularBasis H x) = _
  rw [act_regular]
  congr 1
  group

private theorem ambient_project_conj (q : H × H) (z : PairBasis H) :
    letI := onPairs H
    ambientProject H (q • z) =
      (projectPair H z).map (H.subtype.comp (MulAut.conj q.2).toMonoidHom) := by
  letI := onPairs H
  change (projectPair H (q • z)).map H.subtype = _
  unfold projectPair
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, Subgroup.map_map,
    Subgroup.map_map]
  congr 1 <;> rfl

end IdentityBoundary

private abbrev representative : PairBasis S₃ := (regularBasis S₃ 1, regularBasis S₃ cycle)

private theorem project_representative : projectPair S₃ representative = Subgroup.zpowers cycle := by
  classical
  letI := onPairs S₃
  have fixes (g h : S₃) :
      (g, h) • representative = representative ↔ g = h ∧ h * cycle = cycle * h := by
    change ((Boundary S₃).basis.act (g, h) (regularBasis S₃ 1),
      (Boundary S₃).basis.act (g, h) (regularBasis S₃ cycle)) = _ ↔ _
    rw [act_regular, act_regular, Prod.mk.injEq]
    simp only [(regular_bijective S₃).injective.eq_iff, mul_one]
    rw [mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h⟩
  apply le_antisymm
  · rintro h ⟨⟨g, g'⟩, hfix, rfl⟩
    exact cycle_centralizer ((fixes g g').mp hfix).2
  · apply Subgroup.zpowers_le.mpr
    exact ⟨(cycle, cycle), (fixes cycle cycle).mpr ⟨rfl, rfl⟩, rfl⟩

private theorem orbit_iff (x y : S₃) :
    (regularBasis S₃ x, regularBasis S₃ y) ∈ pairOrbit S₃ representative ↔
      y = x * cycle ∨ y = x * cycle⁻¹ := by
  letI := onPairs S₃
  have acts (g h : S₃) :
      (g, h) • representative =
        (regularBasis S₃ (g * h⁻¹), regularBasis S₃ (g * cycle * h⁻¹)) := by
    change ((Boundary S₃).basis.act (g, h) (regularBasis S₃ 1),
      (Boundary S₃).basis.act (g, h) (regularBasis S₃ cycle)) = _
    rw [act_regular, act_regular, mul_one]
  constructor
  · rintro ⟨⟨g, h⟩, hh⟩
    change (g, h) • representative = _ at hh
    rw [acts, Prod.mk.injEq] at hh
    rcases hh with ⟨hg, hy⟩
    have hg := (regular_bijective S₃).injective hg
    have hy := (regular_bijective S₃).injective hy
    have he : y = x * (h * cycle * h⁻¹) := by rw [← hg, ← hy]; group
    rcases cycle_conj h with hc | hc
    · exact Or.inl (he.trans (congrArg (x * ·) hc))
    · exact Or.inr (he.trans (congrArg (x * ·) hc))
  · rintro (rfl | rfl)
    · refine ⟨(x, 1), ?_⟩
      change (x, (1 : S₃)) • representative = _
      simp only [acts, inv_one, mul_one]
    · refine ⟨(x * transposition, transposition), ?_⟩
      change (x * transposition, transposition) • representative = _
      rw [acts, mul_inv_cancel_right, mul_assoc x transposition cycle, mul_assoc x, cycle_flip]

section Counts

variable {W : Type*} [Group W] {H B : Subgroup W} [Finite H]
variable (i j k : ConjEmbedding B H)

private abbrev RightDot (i j : ConjEmbedding B H) := Dot ((identity H).comp i) ((identity H).comp j)
private abbrev multiplyBasis (r : RightDot i j) :=
  Generator.mixedMultiplicationBasis (identity H) (identity H) i j r

private noncomputable abbrev hitCount (r : RightDot i j) (t : RightDot i k) (s : RightDot k j)
    (g x : H) (y : Basis H) :=
  Nat.card {w : (Inner i j).basis.carrier //
    multiplyBasis i j r w = Generator.mixedPair (identity H) (identity H) x ∧
    point H (g * (Quotient.out w).1 * t.element) (s.element * (Quotient.out w).2) = y}

private theorem finite_mixed_fibers (r : RightDot i j) :
    Fibers (identity H) (identity H) i j r := by
  letI : Finite (Inner i j).basis.carrier := Quotient.finite _
  exact fun _ => Set.toFinite _

private noncomputable abbrev drawLabels (r : DotLabel R ((identity H).comp i) ((identity H).comp j))
    (t : DotLabel R ((identity H).comp i) ((identity H).comp k))
    (s : DotLabel R ((identity H).comp k) ((identity H).comp j)) :=
  drawing (identity H) (identity H) (identity H) (identity H) (identity H) (identity H) i j k
    (r.terms.map fun (c, d) =>
      letI : Finite (Inner i j).basis.carrier := Quotient.finite _
      (c, (⟨d, fun _ => Set.toFinite _⟩ : ProjectionDot.Mixed (identity H) (identity H) i j)))
    t.terms s.terms

private theorem column_count (r : RightDot i j) (t : RightDot i k) (s : RightDot k j)
    (g x : H) (y : Basis H) :
    column (R := R) (identity H) (identity H) (identity H) (identity H) (identity H) (identity H)
      i j k r (finite_mixed_fibers i j r) t s g x y = (hitCount i j k r t s g x y : R) := by
  classical
  let fiber := (finite_mixed_fibers i j r x).toFinset
  let target : (Inner i j).basis.carrier → Basis H := fun w =>
    point H (g * (Quotient.out w).1 * t.element) (s.element * (Quotient.out w).2)
  let hits : Set (Inner i j).basis.carrier :=
    {w | multiplyBasis i j r w = Generator.mixedPair (identity H) (identity H) x ∧ target w = y}
  have hfinite : hits.Finite := by
    letI : Finite (Inner i j).basis.carrier := Quotient.finite _
    exact Set.toFinite _
  have hfilter : fiber.filter (fun w => target w = y) = hfinite.toFinset := by
    ext w
    simp only [Finset.mem_filter, fiber, Set.Finite.mem_toFinset, hits, Set.mem_ofPred_eq]
    have hx : Generator.mixedProduct (identity H) (identity H) (multiplyBasis i j r w) = x ↔
        multiplyBasis i j r w = Generator.mixedPair (identity H) (identity H) x := by
      constructor
      · intro hw
        apply (Generator.mixedEquiv (identity H) (identity H)).injective
        exact hw.trans (Generator.mixedProduct_mixedPair _ _ _).symm
      · intro hw
        rw [hw, Generator.mixedProduct_mixedPair]
    exact and_congr_left' hx
  change (∑ w ∈ fiber, Finsupp.single (target w) (1 : R)) y = (Nat.card hits : R)
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply, ← Finset.sum_filter]
  change (∑ w ∈ fiber.filter (fun w => target w = y), (1 : R)) = _
  letI := hfinite.fintype
  rw [hfilter, Finset.sum_const, nsmul_eq_mul, mul_one, Set.Finite.card_toFinset hfinite,
    Nat.card_eq_fintype_card]

private theorem eval_counts
    (r : DotLabel R ((identity H).comp i) ((identity H).comp j))
    (t : DotLabel R ((identity H).comp i) ((identity H).comp k))
    (s : DotLabel R ((identity H).comp k) ((identity H).comp j))
    (g x : H) (y : Basis H) :
    (drawLabels i j k r t s).interpret.eval.toLinearMap (Finsupp.single (point H g x) 1) y =
      ∑ rd ∈ r.support, ∑ td ∈ t.support, ∑ sd ∈ s.support,
        (r rd * t td * s sd) * (hitCount i j k rd td sd g x y : R) := by
  classical
  -- Example 8.5, Step 2. Generalize the local column calculation of the
  -- registered CaseSixRightShapeEvaluation from Complex to a commutative ring.
  -- Keep each mark as a single label. Expand its support only after evaluation.
  have h := weightedCase (R := R) (identity H) (identity H) (identity H)
    (identity H) (identity H) (identity H) i j k r.support t.support s.support r t s
    id (finite_mixed_fibers i j) id id g x
  simp only [drawLabels, DotLabel.terms, List.map_map, Function.comp_def]
  change (drawing (identity H) (identity H) (identity H) (identity H) (identity H) (identity H)
      i j k
      (r.support.toList.map fun rd =>
        (r rd, projectionDot (identity H) (identity H) i j rd (finite_mixed_fibers i j rd)))
      (t.support.toList.map fun td => (t td, td))
      (s.support.toList.map fun sd => (s sd, sd))).interpret.eval.toLinearMap
        (input (identity H) (identity H) (identity H) g x) y = _
  simp only [id_eq] at h
  rw [h]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro rd _
  apply Finset.sum_congr rfl
  intro td _
  apply Finset.sum_congr rfl
  intro sd _
  exact congrArg (fun c : R => (r rd * t td * s sd) * c)
    (column_count i j k rd td sd g x y)

end Counts

private abbrev image (j : ConjEmbedding B S₃) := (S₃.subtype.comp j.toHom).range

private theorem count_specialized {B : Subgroup finitary} (hB : parabolic B)
    (i j k : ConjEmbedding B S₃) (r : RightDot i j) (t : RightDot i k) (s : RightDot k j) :
    let z := (point S₃ 1 r.element, point S₃ t.element s.element)
    let P := ambientProject S₃ z
    image j ≤ P ∧ ∀ (g x : S₃) (y : Basis S₃),
      hitCount i j k r t s g x y =
        @ite Nat ((point S₃ g x, y) ∈ pairOrbit S₃ z)
          (Classical.propDecidable _) ((image j).relIndex P) 0 := by
  intro z P
  let a := identity S₃
  have h := (ParabolicRightOrbitMultiplicity S₃ S₃ S₃ S₃ S₃ S₃
    S₃_parabolic S₃_parabolic S₃_parabolic S₃_parabolic S₃_parabolic S₃_parabolic
    a a a a a a).2.2.2.1 B hB ⟨i, j, k, r, t, s⟩
  have hp : ambientProject S₃ z =
      (@MulAction.stabilizer (S₃ × S₃) _ _ (onPairs S₃) z).map
        (S₃.subtype.comp (MonoidHom.snd S₃ S₃)) := by
    unfold ambientProject projectPair
    rw [Subgroup.map_map]
  dsimp only [P]
  rw [hp]
  exact ⟨h.1, h.2.2⟩

-- Alphabeta Math, transposition generation, steps 1.1 through 3.1:
-- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
-- Here the contrapositive needs only the two-point swap in each possible
-- nonsingleton block. Identity extension puts that swap in the ambient group.
private theorem no_swap_parabolic {B : Subgroup finitary} (hB : parabolic B)
    (h : ∀ σ ∈ B.map finitary.subtype, ¬ Equiv.Perm.IsSwap σ) : B = ⊥ := by
  obtain ⟨n, blocks, _, _, hblocks⟩ := hB
  have htrivial (i : Fin n) : blockSym (blocks i) ≤ ⊥ := by
    have heq (a b : ↥(blocks i)) : a = b := by
      by_contra hne
      have hmem : Equiv.swap (a : Nat) (b : Nat) ∈ B.map finitary.subtype := by
        rw [hblocks]
        exact le_iSup (fun i => blockSym (blocks i)) i
          ⟨Equiv.swap a b, Equiv.Perm.ofSubtype_swap_eq a b⟩
      exact h _ hmem ⟨a, b, fun he => hne (Subtype.ext he), rfl⟩
    rintro σ ⟨p, rfl⟩
    have hp : p = 1 := Equiv.ext fun x => heq (p x) x
    rw [hp, map_one]
    exact Subgroup.one_mem _
  apply le_antisymm _ bot_le
  apply (Subgroup.map_le_map_iff_of_injective finitary.subtype_injective).mp
  rw [hblocks, Subgroup.map_bot]
  exact iSup_le htrivial

private theorem bot_parabolic : parabolic (⊥ : Subgroup finitary) := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  simp

private theorem bot_image {B : Subgroup finitary} [Subsingleton B]
    (j : ConjEmbedding B S₃) : image j = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim x 1, map_one]
  exact Subgroup.one_mem _

-- Example 8.5, Step 3. The projected stabilizer of any representative is
-- a conjugate of the order-three subgroup. A nontrivial parabolic source
-- would contribute an ambient transposition of order two, which is impossible.
private theorem index_on_orbit {B : Subgroup finitary} (hB : parabolic B)
    (j : ConjEmbedding B S₃) {z : PairBasis S₃}
    (hz : z ∈ pairOrbit S₃ representative) (hj : image j ≤ ambientProject S₃ z) :
    (image j).relIndex (ambientProject S₃ z) = 3 := by
  letI := onPairs S₃
  obtain ⟨q, rfl⟩ := hz
  let m := S₃.subtype.comp (MulAut.conj q.2).toMonoidHom
  have hP : ambientProject S₃ (q • representative) = (Subgroup.zpowers cycle).map m := by
    rw [ambient_project_conj, project_representative]
  have hinj : Function.Injective m := S₃.subtype_injective.comp (MulAut.conj q.2).injective
  have hc := Nat.card_congr ((Subgroup.zpowers cycle).equivMapOfInjective m hinj).toEquiv
  rw [cycle_card, ← hP] at hc
  have hbot : B = ⊥ := by
    apply no_swap_parabolic hB
    rintro σ ⟨b, hb, rfl⟩ hswap
    let x : B := ⟨b, hb⟩
    have hx : S₃.subtype (j.toHom x) ∈ image j := ⟨x, rfl⟩
    have hxP := hj hx
    rw [hP] at hxP
    obtain ⟨y, hy, he⟩ := hxP
    have he' : (MulAut.conj q.2) y = j.toHom x := S₃.subtype_injective he
    have ho₁ := orderOf_injective (finitary.subtype.comp B.subtype)
      (finitary.subtype_injective.comp B.subtype_injective) x
    change orderOf (b : Equiv.Perm Nat) = orderOf x at ho₁
    have ho₂ := orderOf_injective j.toHom j.injective x
    have ho₃ := orderOf_injective (MulAut.conj q.2).toMonoidHom
      (MulAut.conj q.2).injective y
    change orderOf ((MulAut.conj q.2) y) = orderOf y at ho₃
    rw [he', ho₂, ← ho₁] at ho₃
    have hswap' : orderOf (b : Equiv.Perm Nat) = 2 := swap_order hswap
    change orderOf (b : Equiv.Perm Nat) = orderOf y at ho₃
    rw [hswap'] at ho₃
    have hd := orderOf_dvd_of_mem_zpowers hy
    rw [← ho₃, cycle_order] at hd
    exact (by decide : ¬ 2 ∣ 3) hd
  haveI : Subsingleton B := by rw [hbot]; infer_instance
  rw [bot_image j, Subgroup.relIndex_bot_left, ← hc]

private def trivialEmbedding : ConjEmbedding (⊥ : Subgroup finitary) S₃ :=
  ConjEmbedding.ofConjugator 1 (fun h => by
    have hh : (h : finitary) = 1 := h.property
    simp [hh])

private def trivialDot (z : S₃) : RightDot trivialEmbedding trivialEmbedding :=
  ⟨z, fun h => by
    have hh : h = 1 := Subsingleton.elim _ _
    rw [hh, map_one, one_mul, mul_one]⟩

private theorem example_evaluation (x : S₃) :
    (drawLabels trivialEmbedding trivialEmbedding trivialEmbedding
        (Finsupp.single (trivialDot 1) (1 : R))
        (Finsupp.single (trivialDot cycle) (1 : R))
        (Finsupp.single (trivialDot 1) (1 : R))).interpret.eval.toLinearMap
      (Finsupp.single (regularBasis S₃ x) (1 : R)) =
      Finsupp.single (regularBasis S₃ (x * cycle)) (3 : R) +
      Finsupp.single (regularBasis S₃ (x * cycle⁻¹)) (3 : R) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · ext y
    obtain ⟨y, rfl⟩ := (regular_bijective S₃).surjective y
    rw [eval_counts trivialEmbedding trivialEmbedding trivialEmbedding]
    simp only [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul]
    have he := count_specialized bot_parabolic trivialEmbedding trivialEmbedding trivialEmbedding
      (trivialDot 1) (trivialDot cycle) (trivialDot 1)
    letI := onPairs S₃
    have hrep : representative ∈ pairOrbit S₃ representative := MulAction.mem_orbit_self representative
    have hidx := index_on_orbit bot_parabolic trivialEmbedding hrep he.1
    have hcount := he.2 x 1 (regularBasis S₃ y)
    change hitCount trivialEmbedding trivialEmbedding trivialEmbedding (trivialDot 1) (trivialDot cycle)
      (trivialDot 1) x 1 (regularBasis S₃ y) =
      @ite Nat ((regularBasis S₃ x, regularBasis S₃ y) ∈ pairOrbit S₃ representative)
        (Classical.propDecidable _) ((image trivialEmbedding).relIndex (ambientProject S₃ representative)) 0
      at hcount
    rw [hcount, hidx]
    have hne : x * cycle ≠ x * cycle⁻¹ := (mul_right_injective x).ne cycle_ne
    rw [orbit_iff]
    simp only [Finsupp.add_apply, Finsupp.single_apply, (regular_bijective S₃).injective.eq_iff]
    by_cases h : y = x * cycle
    · have hother : x * cycle⁻¹ ≠ y := fun he => hne (h.symm.trans he.symm)
      rw [ite_eq_left (Or.inl h), ite_eq_left h.symm, ite_eq_right hother, add_zero]
      <;> norm_num
    · by_cases hy : y = x * cycle⁻¹
      · rw [ite_eq_left (Or.inr hy), ite_eq_right (Ne.symm h), ite_eq_left hy.symm, zero_add]
        <;> norm_num
      · rw [ite_eq_right (not_or_intro h hy), ite_eq_right (Ne.symm h), ite_eq_right (Ne.symm hy),
          Nat.cast_zero, zero_add]

-- Step 4. Every supported triple contributes either zero or the cast of 3
-- times its product of weights. The finite sums preserve zero in characteristic 3.
private theorem char_three_vanish [CharP R 3] {B : Subgroup finitary} (hB : parabolic B)
    (i j k : ConjEmbedding B S₃)
    (r : DotLabel R ((identity S₃).comp i) ((identity S₃).comp j))
    (t : DotLabel R ((identity S₃).comp i) ((identity S₃).comp k))
    (s : DotLabel R ((identity S₃).comp k) ((identity S₃).comp j))
    (z : PairBasis S₃) (hz : z ∈ pairOrbit S₃ representative) :
    (drawLabels i j k r t s).interpret.eval.toLinearMap (Finsupp.single z.1 (1 : R)) z.2 = 0 := by
  classical
  obtain ⟨x, hx⟩ := (regular_bijective S₃).surjective z.1
  have he := eval_counts i j k r t s x 1 z.2
  change (drawLabels i j k r t s).interpret.eval.toLinearMap
    (Finsupp.single (regularBasis S₃ x) 1) z.2 = _ at he
  rw [← hx, he]
  apply Finset.sum_eq_zero
  intro rd _
  apply Finset.sum_eq_zero
  intro td _
  apply Finset.sum_eq_zero
  intro sd _
  let z' := (point S₃ 1 rd.element, point S₃ td.element sd.element)
  have hn := count_specialized hB i j k rd td sd
  have hcount := hn.2 x 1 z.2
  change hitCount i j k rd td sd x 1 z.2 =
    @ite Nat ((regularBasis S₃ x, z.2) ∈ pairOrbit S₃ z') (Classical.propDecidable _)
      ((image j).relIndex (ambientProject S₃ z')) 0 at hcount
  have hEq : (regularBasis S₃ x, z.2) = z := Prod.ext hx rfl
  rw [hEq] at hcount
  rw [hcount]
  letI := onPairs S₃
  by_cases h : z ∈ pairOrbit S₃ z'
  · have ho : pairOrbit S₃ z' = pairOrbit S₃ representative :=
      (MulAction.orbit_eq_iff.mpr h).symm.trans (MulAction.orbit_eq_iff.mpr hz)
    have hz' : z' ∈ pairOrbit S₃ representative := ho ▸ MulAction.mem_orbit_self z'
    rw [ite_eq_left h, index_on_orbit hB j hz' hn.1]
    have h3 : (3 : R) = 0 := CharP.cast_eq_zero R 3
    simp [h3]
  · rw [ite_eq_right h, Nat.cast_zero, mul_zero]

end CaseSixCharThree


theorem ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let extendBlock := fun (S : Finset Nat) =>
  Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S)
let blockSym := fun (S : Finset Nat) => MonoidHom.range (extendBlock S)
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
let points : Finset Nat := {1, 2, 3}
let S₃ := Subgroup.comap (Subgroup.subtype finitary) (blockSym points)
let extend : Equiv.Perm ↥points → S₃ := fun σ =>
  ⟨⟨extendBlock points σ, by
      apply _root_.mem_closure_isSwap'.2
      apply (Finset.finite_toSet points).subset
      intro n moved
      by_contra outside
      exact moved (MulAction.mem_fixedBy.mpr (Equiv.Perm.ofSubtype_apply_of_not_mem σ outside))
    ⟩, ⟨σ, rfl⟩⟩
letI : Finite S₃ := Finite.of_surjective extend (by
  intro ⟨⟨σ, hσ⟩, h⟩
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, Subtype.ext (Subtype.ext hρ)⟩)
let label₁ : ↥points := ⟨1, by decide⟩
let label₂ : ↥points := ⟨2, by decide⟩
let label₃ : ↥points := ⟨3, by decide⟩
let cycle := extend (Equiv.swap label₁ label₂ * Equiv.swap label₂ label₃)
let boundary := MackeyDiagrams.ConjEmbedding.id S₃
let up := MackeyDiagrams.Word.up boundary
let down := MackeyDiagrams.Word.down boundary
let mixed := MackeyDiagrams.Word.tensor down up
let word := MackeyDiagrams.Word.tensor up mixed
let X := MackeyDiagrams.Word.basis word
let basis : S₃ → X.carrier := fun x =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis up)
    (MackeyDiagrams.Word.basis mixed) x
    (MackeyDiagrams.Generator.mixedPair boundary boundary 1)
letI : MulAction (S₃ × S₃) X.carrier :=
  { smul := MackeyDiagrams.Biset.act X
    one_smul := MackeyDiagrams.Biset.one_act X
    mul_smul := MackeyDiagrams.Biset.mul_act X }
letI : MulAction (S₃ × S₃) (X.carrier × X.carrier) :=
  { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act X q z.2)
    one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
      (MackeyDiagrams.Biset.one_act X z.2)
    mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
      (MackeyDiagrams.Biset.mul_act X q q' z.2) }
let project := Subgroup.map (MonoidHom.snd S₃ S₃)
let representative := (basis 1, basis cycle)
let orbit := MulAction.orbit (S₃ × S₃) representative
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let trivialEmbedding : MackeyDiagrams.ConjEmbedding (⊥ : Subgroup U) S₃ :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (fun h => by
    have hh : (h : U) = 1 := h.property
    simp [hh])
let trivialDot := fun z : S₃ =>
  (⟨z, fun h => by
    have hh : h = 1 := Subsingleton.elim _ _
    rw [hh]
    simp⟩ : MackeyDiagrams.Dot (comp boundary trivialEmbedding) (comp boundary trivialEmbedding))
Function.Bijective basis ∧
project (MulAction.stabilizer (S₃ × S₃) representative.1) = ⊤ ∧
project (MulAction.stabilizer (S₃ × S₃) representative.2) = ⊤ ∧
project (MulAction.stabilizer (S₃ × S₃) representative) = Subgroup.zpowers cycle ∧
∀ (R : Type*) [CommRing R],
let rightDrawing := fun {B' : Subgroup U}
    (i j k : MackeyDiagrams.ConjEmbedding B' S₃)
    (r : MackeyDiagrams.DotLabel R (comp boundary i) (comp boundary j))
    (t : MackeyDiagrams.DotLabel R (comp boundary i) (comp boundary k))
    (s : MackeyDiagrams.DotLabel R (comp boundary k) (comp boundary j)) =>
  let ai := MackeyDiagrams.Word.up i
  let fj := MackeyDiagrams.Word.down j
  let ck := MackeyDiagrams.Word.up k
  letI : Finite (MackeyDiagrams.Word.basis (MackeyDiagrams.Word.tensor ai fj)).carrier :=
    Quotient.finite _
  let projectionTerms := (MackeyDiagrams.DotLabel.terms r).map
    (fun (c, d) => (c, (⟨d, fun _ => Set.toFinite _⟩ :
      MackeyDiagrams.ProjectionDot.Mixed boundary boundary i j)))
  let lower := MackeyDiagrams.LabelledDrawing.compactProjection
    boundary boundary i j projectionTerms
  let middle := MackeyDiagrams.LabelledDrawing.parallelUp
    boundary i boundary k (MackeyDiagrams.DotLabel.terms t)
  let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication
    boundary boundary k j (MackeyDiagrams.DotLabel.terms s)
  let straightUp := MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := R) up)
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal straightUp lower)
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate up ai fj))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal middle
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := R) fj)))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate up ck fj))
          (MackeyDiagrams.LabelledDrawing.horizontal straightUp upper))))
let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing R word word) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
(∀ x : S₃,
  evaluate
    (rightDrawing trivialEmbedding trivialEmbedding trivialEmbedding
      (Finsupp.single (trivialDot 1) (1 : R))
      (Finsupp.single (trivialDot cycle) (1 : R))
      (Finsupp.single (trivialDot 1) (1 : R)))
    (Finsupp.single (basis x) (1 : R)) =
      Finsupp.single (basis (x * cycle)) (3 : R) +
      Finsupp.single (basis (x * cycle⁻¹)) (3 : R)) ∧
∀ [CharP R 3] {B' : Subgroup U}, parabolic B' →
  ∀ (i j k : MackeyDiagrams.ConjEmbedding B' S₃)
    (r : MackeyDiagrams.DotLabel R (comp boundary i) (comp boundary j))
    (t : MackeyDiagrams.DotLabel R (comp boundary i) (comp boundary k))
    (s : MackeyDiagrams.DotLabel R (comp boundary k) (comp boundary j))
    (z : X.carrier × X.carrier), z ∈ orbit →
  evaluate (rightDrawing i j k r t s) (Finsupp.single z.1 (1 : R)) z.2 = 0
) :=
(by
  classical
  intro finitary U extendBlock blockSym parabolic points S₃ extend label₁ label₂ label₃ cycle
    boundary up down mixed word X basis project representative orbit comp trivialEmbedding trivialDot
  -- Xiao, Example 8.5, archived original p. 42 and published 28 November revision p. 44.
  -- The portal has no numbered proof for this example, so comments number its
  -- calculation here.
  -- Step 1. Reduce the balanced classes for the identity
  -- boundary to the regular biset. Its pair stabilizer projects to the
  -- centralizer of the cycle. The strict-stabilizer obstruction concerns
  -- left replacements over Complex, so the characteristic-three part uses
  -- the natural fiber counts from ParabolicRightOrbitMultiplicity.
  refine ⟨CaseSixCharThree.regular_bijective _, CaseSixCharThree.project_basis_top _ _,
    CaseSixCharThree.project_basis_top _ _, CaseSixCharThree.project_representative, ?_⟩
  intro R _ rightDrawing evaluate
  constructor
  · intro x
    exact CaseSixCharThree.example_evaluation x
  · intro _ B' hB i j k r t s z hz
    exact CaseSixCharThree.char_three_vanish hB i j k r t s z hz
)
