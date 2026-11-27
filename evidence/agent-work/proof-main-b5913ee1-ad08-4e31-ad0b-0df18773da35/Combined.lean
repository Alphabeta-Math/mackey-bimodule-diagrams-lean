import Mathlib.GroupTheory.Perm.ClosureSwap
import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.FiniteParabolicConjugateBlocks

set_option maxHeartbeats 2000000

namespace CaseSixTrivialAux
open MackeyDiagrams

abbrev P := Equiv.Perm Nat
abbrev finitary : Subgroup P := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
abbrev U := ↥finitary
abbrev blockSym (S : Finset Nat) := MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
abbrev points : Finset Nat := {1, 2, 3, 4}
abbrev small : Subgroup P := Subgroup.closure ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P)
abbrev A : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) small
abbrev D : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) (blockSym points)
abbrev F : Subgroup U := ⊥

theorem block_fixed {S : Finset Nat} {σ : P} (hσ : σ ∈ blockSym S) {n : Nat}
    (hn : n ∉ S) : σ n = n := by
  obtain ⟨f, rfl⟩ := hσ
  exact Equiv.Perm.ofSubtype_apply_of_not_mem f hn

theorem swap_block (S : Finset Nat) {m n : Nat} (hm : m ∈ S) (hn : n ∈ S) :
    Equiv.swap m n ∈ blockSym S :=
  ⟨Equiv.swap ⟨m, hm⟩ ⟨n, hn⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

theorem block_finitary (S : Finset Nat) : blockSym S ≤ finitary := by
  intro σ hσ
  apply mem_closure_isSwap'.2
  apply S.finite_toSet.subset
  intro n hn
  by_contra h
  exact hn (block_fixed hσ h)

theorem hAD : A ≤ D := by
  apply Subgroup.comap_mono
  apply (Subgroup.closure_le _).2
  intro σ hσ
  rcases Set.mem_insert_iff.mp hσ with rfl | hσ
  · exact swap_block points (show 1 ∈ points by decide) (show 2 ∈ points by decide)
  · rw [Set.mem_singleton_iff.mp hσ]
    exact swap_block points (show 3 ∈ points by decide) (show 4 ∈ points by decide)

abbrev incl {H K : Subgroup U} (h : H ≤ K) : ConjEmbedding H K :=
  ⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩

abbrev a := ConjEmbedding.id A
abbrev b := incl hAD
abbrev d := incl (show F ≤ D from bot_le)
abbrev i := incl (show F ≤ A from bot_le)
abbrev j := ConjEmbedding.id F

theorem F_eq_one (f : F) : f = 1 := Subtype.ext (Subgroup.mem_bot.mp f.property)

-- The supplier at one block identifies the conjugated full symmetric group.
theorem block_conj (p : U) (S : Finset Nat) (hS : S.Nonempty) :
    Subgroup.map (MulAut.conj (p : P)).toMonoidHom (blockSym S) =
      blockSym (S.image (p : P)) := by
  simpa only [iSup_unique] using
    (FiniteParabolicConjugateBlocks (fun _ : Unit => S) (fun _ => hS)
      (fun x y h => False.elim (h (Subsingleton.elim x y))) p)

theorem points_nonempty : points.Nonempty := ⟨1, by decide⟩


-- The two generators move all four support points. This proves inclusion
-- of the transported support in any block supporting the transported A.
theorem support_subset (p : U) (S : Finset Nat)
    (h : ∀ g : A, MulAut.conj (p : P) ((g : U) : P) ∈ blockSym S) :
    points.image (p : P) ⊆ S := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
  have moved {m l k : Nat} (hml : m ≠ l)
      (hgen : Equiv.swap m l ∈ ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P))
      (hne : Equiv.swap m l k ≠ k) : (p : P) k ∈ S := by
    let g : A := ⟨⟨Equiv.swap m l, Subgroup.subset_closure ⟨m, l, hml, rfl⟩⟩,
      Subgroup.subset_closure hgen⟩
    by_contra hk
    have hh := block_fixed (h g) hk
    change (p : P) (Equiv.swap m l ((p : P).symm ((p : P) k))) = (p : P) k at hh
    rw [Equiv.symm_apply_apply] at hh
    exact hne ((p : P).injective hh)
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simpa [points] using hk
  rcases hk' with rfl | rfl | rfl | rfl
  · exact moved (m := 1) (l := 2) (by decide) (by simp) (by decide)
  · exact moved (m := 1) (l := 2) (by decide) (by simp) (by decide)
  · exact moved (m := 3) (l := 4) (by decide) (by simp) (by decide)
  · exact moved (m := 3) (l := 4) (by decide) (by simp) (by decide)

theorem transport_ranges {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B)
    (r : Dot (u.comp a) (v.comp b)) :
    ∃ p : U, ∀ z : P, (∃ x : D, MulAut.conj ((r.element : U) : P) ((v.toHom x : U) : P) = z) ↔
      z ∈ blockSym (points.image (p : P)) := by
  obtain ⟨q, hq⟩ := v.hasRepresentative
  refine ⟨(r.element : U) * q, fun z => ?_⟩
  rw [← block_conj _ points points_nonempty]
  have hconj (x : D) :
      MulAut.conj ((r.element : U) : P) ((v.toHom x : U) : P) =
        MulAut.conj ((((r.element : U) * q : U) : P)) ((x : U) : P) := by
    have hx := congrArg (fun g : U => (g : P)) (hq x)
    change ((v.toHom x : U) : P) = (q : P) * ((x : U) : P) * (q : P)⁻¹ at hx
    change ((r.element : U) : P) * ((v.toHom x : U) : P) * (((r.element : U) : P))⁻¹ =
      (((r.element : U) : P) * (q : P)) * ((x : U) : P) *
        (((r.element : U) : P) * (q : P))⁻¹
    rw [hx]
    group
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : U), x.property, (hconj x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let y : D := ⟨⟨x, block_finitary points hx⟩, hx⟩
    exact ⟨y, hconj y⟩

-- Steps 2–3 of Example 8.6: use both vertex conditions and the equal
-- cardinality of the transported supports. The argument works in any B.
theorem ranges_eq {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (r : Dot (u.comp a) (v.comp b)) (s : Dot (u.comp a) (w.comp b)) :
    (fun x : D => r.element * v.toHom x * r.element⁻¹) '' (Set.univ : Set D) =
    (fun x : D => s.element * w.toHom x * s.element⁻¹) '' (Set.univ : Set D) := by
  obtain ⟨p, hp⟩ := transport_ranges u v r
  obtain ⟨q, hq⟩ := transport_ranges u w s
  obtain ⟨α, hα⟩ := u.hasRepresentative
  have overgroup (v : ConjEmbedding D B) (r : Dot (u.comp a) (v.comp b)) (g : A) :
      ∃ x : D, MulAut.conj ((r.element : U) : P) ((v.toHom x : U) : P) =
        MulAut.conj (α : P) ((g : U) : P) := by
    refine ⟨b.toHom g, ?_⟩
    have h := r.intertwines g
    change u.toHom g * r.element = r.element * v.toHom (b.toHom g) at h
    have he : r.element * v.toHom (b.toHom g) * r.element⁻¹ = u.toHom g := by
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    have hev := congrArg (fun z : B => ((z : U) : P)) he
    have hg := congrArg (fun z : U => (z : P)) (hα g)
    exact hev.trans hg
  have same (p : U) (ht : ∀ g : A,
      MulAut.conj (α : P) ((g : U) : P) ∈ blockSym (points.image (p : P))) :
      points.image (α : P) = points.image (p : P) := by
    apply Finset.eq_of_subset_of_card_le (support_subset α _ ht)
    rw [Finset.card_image_of_injective _ (p : P).injective,
      Finset.card_image_of_injective _ (α : P).injective]
  have he := (same p (fun g => (hp _).1 (overgroup v r g))).symm.trans
    (same q (fun g => (hq _).1 (overgroup w s g)))
  ext z
  have zcast (x y : B) (h : ((x : U) : P) = ((y : U) : P)) : x = y :=
    Subtype.ext (Subtype.ext h)
  constructor
  · rintro ⟨x, -, rfl⟩
    have hx := (hp _).1 ⟨x, rfl⟩
    rw [he] at hx
    obtain ⟨y, hy⟩ := (hq _).2 hx
    exact ⟨y, Set.mem_univ _, zcast _ _ hy⟩
  · rintro ⟨y, -, rfl⟩
    have hy := (hq _).1 ⟨y, rfl⟩
    rw [← he] at hy
    obtain ⟨x, hx⟩ := (hp _).2 hy
    exact ⟨x, Set.mem_univ _, zcast _ _ hx⟩

theorem outside : ∃ x : D, (x : U) ∉ A := by
  let x : D := ⟨⟨Equiv.swap 1 3, Subgroup.subset_closure ⟨1, 3, by decide, rfl⟩⟩,
    swap_block points (by decide) (by decide)⟩
  refine ⟨x, fun h => ?_⟩
  have preserve {σ : P} (hσ : σ ∈ small) :
      ∀ n : Nat, (σ n ∈ ({1, 2} : Finset Nat)) ↔ n ∈ ({1, 2} : Finset Nat) := by
    change σ ∈ Subgroup.closure _ at hσ
    induction hσ using Subgroup.closure_induction with
    | mem z hz =>
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · intro n
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [Equiv.swap_apply_def]
        split_ifs <;> simp_all
      · rw [Set.mem_singleton_iff.mp hz]
        intro n
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [Equiv.swap_apply_def]
        split_ifs <;> simp_all
    | one => exact fun _ => Iff.rfl
    | mul z w hz hw ihz ihw =>
      exact fun n => (ihz (w n)).trans (ihw n)
    | inv z hz ih =>
      intro n
      exact (by simpa using (ih (z.symm n)).symm)
  have hx := (preserve h 1).2 (by decide)
  change Equiv.swap (1 : Nat) 3 1 ∈ ({1, 2} : Finset Nat) at hx
  rw [Equiv.swap_apply_left] at hx
  exact (by decide : 3 ∉ ({1, 2} : Finset Nat)) hx
end CaseSixTrivialAux

namespace CaseSixTrivialAux
open MackeyDiagrams
noncomputable section

abbrev up := @Word.up U _
abbrev down := @Word.down U _
abbrev tensor := @Word.tensor U _
abbrev vertical := @LabelledDrawing.vertical U _ Complex _
abbrev horizontal := @LabelledDrawing.horizontal U _ Complex _
abbrev ordinary := @LabelledDrawing.ordinary U _ Complex _
abbrev straight {K L : Subgroup U} (p : Word K L) := ordinary (Diagram.id p)

abbrev atLeft {K J J' L M : Subgroup U}
    {p : Word K J} {q : Word J L} {p' : Word K J'} {q' : Word J' L}
    (tail : Word L M) (crossing : LabelledDrawing Complex (tensor p q) (tensor p' q')) :=
  vertical (ordinary (Diagram.unassociate p q tail))
    (vertical (horizontal crossing (straight tail)) (ordinary (Diagram.associate p' q' tail)))

abbrev ev {K L : Subgroup U} {p q : Word K L} (drawing : LabelledDrawing Complex p q) :=
  drawing.interpret.eval.toLinearMap

abbrev ad := tensor (down b) (up d)
abbrev word := tensor (up a) ad
abbrev coordinate (g : A) (x : D) := (up a).basis.pair ad.basis g (Generator.mixedPair b d x)
abbrev vector (x : D) := Finsupp.single (coordinate 1 x) (1 : Complex)

theorem coordinate_move (g : A) (x : D) :
    coordinate g x = coordinate 1 (b.toHom g * x) := by
  have eq := (up a).basis.pair_balance ad.basis g 1 (Generator.mixedPair b d x)
  have h₁ : (up a).basis.act (1, g⁻¹) 1 = g := by
    change (1 : A) * 1 * (a.toHom g⁻¹)⁻¹ = g
    change (1 : A) * 1 * (g⁻¹)⁻¹ = g
    simp only [one_mul, inv_inv]
  have h₂ : ad.basis.act (g, 1) (Generator.mixedPair b d x) =
      Generator.mixedPair b d (b.toHom g * x) := by
    change (down b).basis.pair (up d).basis (b.toHom g * x * (1 : D)⁻¹)
      (1 * 1 * (d.toHom 1)⁻¹) = _
    simp only [map_one, inv_one, mul_one]
    rfl
  rw [h₁, h₂] at eq
  exact eq

-- Step 1 of Example 8.6: the regular A factor and the balanced D pair
-- reduce to multiplication. Build the equivalence on the whole quotient.
def coordinates : word.basis.carrier ≃ D where
  toFun p := Generator.mixedProduct b d (Biset.leftUnitBasis ad.basis p)
  invFun := coordinate 1
  left_inv p := by
    refine Quotient.inductionOn p (fun ⟨g, z⟩ => ?_)
    obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective z
    change coordinate 1 (Generator.mixedProduct b d
      (ad.basis.act (g, 1) (Generator.mixedPair b d x))) = coordinate g x
    change coordinate 1 (Generator.mixedProduct b d
      ((down b).basis.pair (up d).basis (b.toHom g * x * (1 : D)⁻¹)
        (1 * 1 * (d.toHom 1)⁻¹))) = coordinate g x
    simp only [map_one, inv_one, mul_one]
    change coordinate 1 (Generator.mixedProduct b d (Generator.mixedPair b d (b.toHom g * x))) =
      coordinate g x
    rw [Generator.mixedProduct_mixedPair]
    exact (coordinate_move g x).symm
  right_inv x := by
    change Generator.mixedProduct b d (ad.basis.act (1, 1) (Generator.mixedPair b d x)) = x
    rw [show ((1, 1) : A × F) = 1 from rfl, Biset.one_act, Generator.mixedProduct_mixedPair]

theorem coordinates_pair (g : A) (x : D) : coordinates (coordinate g x) = b.toHom g * x := by
  rw [coordinate_move]
  exact coordinates.apply_symm_apply _

abbrev RDot {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B) :=
  Dot (u.comp a) (v.comp b)
abbrev TDot {B : Subgroup U} (v w : ConjEmbedding D B) := Dot (v.comp d) (w.comp d)
abbrev SDot {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B) :=
  ProjectionDot.Mixed u w a b

abbrev left {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (rs : List (Complex × RDot u v)) (ts : List (Complex × TDot v w))
    (ss : List (Complex × SDot u w)) :=
  vertical (atLeft (up d) (.mixedMultiplication u v a b rs))
    (vertical (horizontal (straight (down u)) (.parallelUp v d w d ts))
      (atLeft (up d) (.compactProjection u w a b ss)))

-- A fixed spectator is a linear map in the active tensor factor.
def frame {K J J' L M : Subgroup U} {p : Word K J} {q : Word J L}
    {p' : Word K J'} {q' : Word J' L} (tail : Word L M)
    (f : ((tensor p q).basis.carrier →₀ Complex) →ₗ[Complex]
      ((tensor p' q').basis.carrier →₀ Complex)) (z : tail.basis.carrier) :
    ((tensor p q).basis.carrier →₀ Complex) →ₗ[Complex]
      ((tensor p' (tensor q' tail)).basis.carrier →₀ Complex) :=
  (Diagram.associate (R := Complex) p' q' tail).eval.toLinearMap.comp
    (((Biset.pairLinear Complex (tensor p' q').basis tail.basis).flip (Finsupp.single z 1)).comp f)

theorem atLeft_pair {K J J' L M : Subgroup U} {p : Word K J} {q : Word J L}
    {p' : Word K J'} {q' : Word J' L} (tail : Word L M)
    (f : LabelledDrawing Complex (tensor p q) (tensor p' q'))
    (x : p.basis.carrier) (y : q.basis.carrier) (z : tail.basis.carrier) :
    ev (atLeft tail f) (Finsupp.single (p.basis.pair (tensor q tail).basis x (q.basis.pair tail.basis y z)) 1)
      = frame tail (ev f) z (Finsupp.single (p.basis.pair q.basis x y) 1) := by
  change (Diagram.associate p' q' tail).eval.toLinearMap
    ((f.interpret.eval.horizontal (Diagram.id tail).eval).toLinearMap
      ((Diagram.unassociate p q tail).eval.toLinearMap _)) = _
  rw [Diagram.eval_unassociate_single, Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply]
  rfl

abbrev mid {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B) (z : B) :=
  (down u).basis.pair (tensor (up v) (up d)).basis z ((up v).basis.pair (up d).basis 1 1)

-- Lemma 6.6, equation (6.3), steps 1–3. The registered left formula
-- brackets (up a, down b) first and normalizes the spectator to 1.
-- These local columns compute the same operations at the reviewed
-- right-associated boundary and on arbitrary label lists.
theorem lower_column {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B)
    (rs : List (Complex × RDot u v)) (x : D) :
    ev (atLeft (up d) (.mixedMultiplication u v a b rs)) (vector x) =
      (rs.map fun (c,r) => c • Finsupp.single (mid u v (r.element * v.toHom x)) 1).sum := by
  have eq := atLeft_pair (up d) (.mixedMultiplication u v a b rs) 1 x 1
  change ev (atLeft (up d) (.mixedMultiplication u v a b rs)) (vector x) = _ at eq
  rw [eq]
  let act := (Diagram.associate (R := Complex) (down u) (up v) (up d)).eval.toLinearMap.comp
    ((Biset.pairLinear Complex (tensor (down u) (up v)).basis (up d).basis).flip
      (Finsupp.single 1 1))
  change act ((ScopedDiagram.linearCombination (rs.map fun (c,r) =>
    (c, .ordinary (Diagram.mixedMultiplication u v a b r)))).eval.toLinearMap
      (Finsupp.single ((up a).basis.pair (down b).basis 1 x) 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨c,r⟩ _
  simp only [Function.comp_apply, map_smul]
  congr 1
  change act ((Generator.mixedMultiplication u v a b r Complex).toLinearMap
    (Finsupp.single ((up a).basis.pair (down b).basis 1 x) 1)) = _
  rw [Generator.mixedMultiplication, Biset.Hom.ofFunction_single]
  change act (Finsupp.single (Generator.mixedPair u v (u.toHom 1 * r.element * v.toHom x)) 1) = _
  rw [map_one, one_mul]
  simp only [act, LinearMap.comp_apply, LinearMap.flip_apply]
  rw [Biset.pairLinear_single, one_mul]
  exact Diagram.eval_associate_single (R := Complex) (down u) (up v) (up d) (r.element * v.toHom x) 1 1 1

theorem middle_column {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (ts : List (Complex × TDot v w)) (z : B) :
    ev (horizontal (straight (down u)) (.parallelUp v d w d ts))
      (Finsupp.single (mid u v z) 1) =
      (ts.map fun (c,t) => c • Finsupp.single (mid u w (z * t.element)) 1).sum := by
  let vword := tensor (up v) (up d)
  let wword := tensor (up w) (up d)
  let act := Biset.pairLinear Complex (down u).basis wword.basis (Finsupp.single z 1)
  let terms := ts.map fun (c,t) =>
    (c, ScopedDiagram.ordinary (Diagram.parallelUp (R := Complex) v d w d t))
  change ((Diagram.id (R := Complex) (down u)).eval.horizontal
    (ScopedDiagram.linearCombination terms).eval).toLinearMap
      (Finsupp.single ((down u).basis.pair vword.basis z ((up v).basis.pair (up d).basis 1 1)) 1) = _
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply]
  change act ((ScopedDiagram.linearCombination terms).eval.toLinearMap
    (Finsupp.single ((up v).basis.pair (up d).basis 1 1) 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [terms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨c,t⟩ _
  simp only [Function.comp_apply, map_smul]
  congr 1
  change act ((Diagram.splitUp (R := Complex) w d).eval.toLinearMap
    ((Diagram.upDot t).eval.toLinearMap
      ((Diagram.mergeUp v d).eval.toLinearMap (Finsupp.single ((up v).basis.pair (up d).basis 1 1) 1)))) = _
  rw [Diagram.eval_mergeUp_single, map_one, mul_one, Diagram.eval_upDot_single, one_mul,
    Diagram.eval_splitUp_single]
  unfold act
  rw [Biset.pairLinear_single, one_mul]
  congr 1
  have eq := (down u).basis.pair_balance wword.basis t.element z ((up w).basis.pair (up d).basis 1 1)
  change (down u).basis.pair wword.basis (u.toHom 1 * z * t.element⁻¹⁻¹)
    ((up w).basis.pair (up d).basis 1 1) =
    (down u).basis.pair wword.basis z
      ((up w).basis.pair (up d).basis (t.element * 1 * (w.toHom 1)⁻¹) (1 * 1 * (d.toHom 1)⁻¹)) at eq
  simpa only [map_one, one_mul, mul_one, inv_one, inv_inv] using eq.symm

end
end CaseSixTrivialAux

namespace CaseSixTrivialAux
open MackeyDiagrams
open scoped BigOperators
noncomputable section

def mass : (word.basis.carrier →₀ Complex) →ₗ[Complex] Complex :=
  Finsupp.lsum Complex (fun _ => LinearMap.id)

theorem mass_apply (z : word.basis.carrier →₀ Complex) : mass z = z.sum (fun _ c => c) := rfl

@[simp] theorem mass_single (p : word.basis.carrier) : mass (Finsupp.single p 1) = 1 := by
  rw [mass_apply, Finsupp.sum_single_index]
  rfl

abbrev upperFunction {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) := Generator.mixedMultiplicationBasis u w a b s.dot

abbrev pairAB (g : A) (x : D) := (up a).basis.pair (down b).basis g x

theorem pairAB_move (g : A) (x : D) : pairAB g x = pairAB 1 (b.toHom g * x) := by
  have eq := (up a).basis.pair_balance (down b).basis g 1 x
  change pairAB (1 * 1 * (g⁻¹)⁻¹) x = pairAB 1 (b.toHom g * x * (1 : D)⁻¹) at eq
  simpa only [inv_inv, mul_one, one_mul, inv_one] using eq

theorem upperFunction_pair {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (y : D) :
    upperFunction u w s (pairAB 1 y) = Generator.mixedPair u w (s.dot.element * w.toHom y) := by
  change Generator.mixedPair u w (u.toHom 1 * s.dot.element * w.toHom y) = _
  rw [map_one, one_mul]

theorem upperFunction_injective {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) : Function.Injective (upperFunction u w s) := by
  intro p q
  refine Quotient.inductionOn₂ p q (fun ⟨g,x⟩ ⟨h,y⟩ => ?_)
  change upperFunction u w s (pairAB g x) = upperFunction u w s (pairAB h y) → _
  have hg := pairAB_move g x
  have hh := pairAB_move h y
  change upperFunction u w s (pairAB g x) = upperFunction u w s (pairAB h y) →
    pairAB g x = pairAB h y
  rw [hg, hh, upperFunction_pair, upperFunction_pair]
  intro eq
  have hprod := (Generator.mixedEquiv u w).symm.injective eq
  rw [mul_right_inj] at hprod
  exact congrArg (pairAB 1) (w.injective hprod)

abbrev upperFiber {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (z : B) := (s.finite (Generator.mixedPair u w z)).toFinset

theorem upperFiber_mass {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (z : B) :
    mass (ev (atLeft (up d) (.compactProjection u w a b [(1, s)]))
      (Finsupp.single (mid u w z) 1)) = (upperFiber u w s z).card := by
  have eq := atLeft_pair (up d) (.compactProjection u w a b [(1, s)]) z 1 1
  change ev (atLeft (up d) (.compactProjection u w a b [(1, s)]))
    (Finsupp.single (mid u w z) 1) = _ at eq
  rw [eq]
  let act := (Diagram.associate (R := Complex) (up a) (down b) (up d)).eval.toLinearMap.comp
    ((Biset.pairLinear Complex (tensor (up a) (down b)).basis (up d).basis).flip (Finsupp.single 1 1))
  let p := Generator.mixedPair u w z
  let f := (Diagram.mixedProjection (R := Complex) u w a b s.dot s.finite).eval.toLinearMap
  change mass (act ((ScopedDiagram.linearCombination [(1, .ordinary
    (Diagram.mixedProjection u w a b s.dot s.finite))]).eval.toLinearMap (Finsupp.single p 1))) = _
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul]
  change mass (act (f (Finsupp.single p 1))) = _
  have hcol : f (Finsupp.single p 1) =
      ∑ v ∈ upperFiber u w s z, Finsupp.single v 1 := by
    change (Generator.mixedProjection u w a b s.dot Complex s.finite).toLinearMap
      (Finsupp.single p 1) = _
    rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul,
      Biset.Hom.transferBasis_sum]
  rw [hcol, map_sum, map_sum]
  have hmass (v : (tensor (up a) (down b)).basis.carrier) :
      mass (act (Finsupp.single v 1)) = 1 := by
    refine Quotient.inductionOn v (fun ⟨g,y⟩ => ?_)
    change mass (act (Finsupp.single (pairAB g y) 1)) = _
    simp only [act, LinearMap.comp_apply, LinearMap.flip_apply]
    rw [Biset.pairLinear_single, one_mul, Diagram.eval_associate_single (up a) (down b) (up d), mass_single]
  simp only [hmass, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem upper_mass {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (ss : List (Complex × SDot u w)) (z : B) :
    mass (ev (atLeft (up d) (.compactProjection u w a b ss))
      (Finsupp.single (mid u w z) 1)) =
      (ss.map fun (c,s) => c * (upperFiber u w s z).card).sum := by
  let act := mass.comp ((Diagram.associate (R := Complex) (up a) (down b) (up d)).eval.toLinearMap.comp
    ((Biset.pairLinear Complex (tensor (up a) (down b)).basis (up d).basis).flip (Finsupp.single 1 1)))
  let p := Generator.mixedPair u w z
  have apply_terms (labels : List (Complex × SDot u w)) :
      mass (ev (atLeft (up d) (.compactProjection u w a b labels))
        (Finsupp.single (mid u w z) 1)) =
      act ((ScopedDiagram.linearCombination (labels.map fun (c,s) =>
        (c, .ordinary (Diagram.mixedProjection u w a b s.dot s.finite)))).eval.toLinearMap
          (Finsupp.single p 1)) := by
    rw [atLeft_pair (up d) (.compactProjection u w a b labels) z 1 1]
    rfl
  rw [apply_terms, ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨c,s⟩ _
  simp only [Function.comp_apply, map_smul, smul_eq_mul]
  congr 1
  have h := upperFiber_mass u w s z
  rw [apply_terms, ScopedDiagram.eval_linearCombination_apply] at h
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] using h

theorem fiber_card_of_exists {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B)
    (s : SDot u w) (z : B) :
    ((∃ y : D, s.dot.element * w.toHom y = z) → (upperFiber u w s z).card = 1) ∧
    ((¬ ∃ y : D, s.dot.element * w.toHom y = z) → (upperFiber u w s z).card = 0) := by
  classical
  have mem (p : (tensor (up a) (down b)).basis.carrier) :
      p ∈ upperFiber u w s z ↔ upperFunction u w s p = Generator.mixedPair u w z :=
    Set.Finite.mem_toFinset _
  constructor
  · rintro ⟨y, hy⟩
    have hp : pairAB 1 y ∈ upperFiber u w s z := by
      rw [mem, upperFunction_pair, hy]
    apply Finset.card_eq_one.mpr
    refine ⟨pairAB 1 y, ?_⟩
    ext p
    rw [Finset.mem_singleton]
    exact ⟨fun hin => upperFunction_injective u w s ((mem p).1 hin |>.trans ((mem _).1 hp).symm),
      fun e => e ▸ hp⟩
  · intro h
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p
    refine Quotient.inductionOn p (fun ⟨g,y⟩ => ?_)
    change pairAB g y ∉ upperFiber u w s z
    rw [pairAB_move, mem, upperFunction_pair]
    exact fun eq => h ⟨_, (Generator.mixedEquiv u w).symm.injective eq⟩

-- Step 4 of Example 8.6. The upper fiber has one element precisely when
-- the relative translation belongs to the common subgroup.
theorem fiber_card_constant {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (r : RDot u v) (t : TDot v w) (s : SDot u w) (x y : D) :
    (upperFiber u w s (r.element * v.toHom x * t.element)).card =
    (upperFiber u w s (r.element * v.toHom y * t.element)).card := by
  classical
  let R := MulAut.conj r.element
  let S := MulAut.conj s.dot.element
  let offset := r.element * t.element * s.dot.element⁻¹
  let H := Subgroup.map (R.toMonoidHom.comp v.toHom) ⊤
  have hrange : (fun x : D => r.element * v.toHom x * r.element⁻¹) '' (Set.univ : Set D) =
      (H : Set B) := by
    ext z
    change (∃ x : D, x ∈ (Set.univ : Set D) ∧ R (v.toHom x) = z) ↔
      (∃ x : D, x ∈ (⊤ : Subgroup D) ∧ R (v.toHom x) = z)
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, Subgroup.mem_top _, hx⟩,
      fun ⟨x, _, hx⟩ => ⟨x, Set.mem_univ _, hx⟩⟩
  have hs (z : B) : (∃ k : D, S (w.toHom k) = z) ↔ z ∈ H := by
    rw [← show z ∈ (H : Set B) ↔ z ∈ H from Iff.rfl, ← hrange, ranges_eq u v w r s.dot]
    simp [S]
  have translate (x : D) :
      (∃ k : D, s.dot.element * w.toHom k = r.element * v.toHom x * t.element) ↔ offset ∈ H := by
    have hx : R (v.toHom x) ∈ H := ⟨x, Subgroup.mem_top _, rfl⟩
    have eq (k : D) :
        s.dot.element * w.toHom k = r.element * v.toHom x * t.element ↔
          S (w.toHom k) = R (v.toHom x) * offset := by
      change _ ↔ s.dot.element * w.toHom k * s.dot.element⁻¹ =
        (r.element * v.toHom x * r.element⁻¹) * (r.element * t.element * s.dot.element⁻¹)
      rw [show (r.element * v.toHom x * r.element⁻¹) *
          (r.element * t.element * s.dot.element⁻¹) =
            r.element * v.toHom x * t.element * s.dot.element⁻¹ by group, mul_left_inj]
    simp only [eq]
    rw [hs]
    exact ⟨fun h => by simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hx) h,
      H.mul_mem hx⟩
  by_cases h : offset ∈ H
  · exact ((fiber_card_of_exists u w s _).1 ((translate x).2 h)).trans
      ((fiber_card_of_exists u w s _).1 ((translate y).2 h)).symm
  · exact ((fiber_card_of_exists u w s _).2 (fun hx => h ((translate x).1 hx))).trans
      ((fiber_card_of_exists u w s _).2 (fun hy => h ((translate y).1 hy))).symm

-- Step 5. Distribute over the actual three finite lists. Empty lists,
-- repeated labels and vanishing coefficients are all covered.
theorem left_mass {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (rs : List (Complex × RDot u v)) (ts : List (Complex × TDot v w))
    (ss : List (Complex × SDot u w)) (x y : D) :
    mass (ev (left u v w rs ts ss) (vector x)) = mass (ev (left u v w rs ts ss) (vector y)) := by
  let next := ev (horizontal (straight (down u)) (.parallelUp v d w d ts))
  let last := mass.comp (ev (atLeft (up d) (.compactProjection u w a b ss)))
  have expand (x : D) : mass (ev (left u v w rs ts ss) (vector x)) =
      (rs.map fun (cr,r) => cr • (ts.map fun (ct,t) => ct •
        (ss.map fun (cs,s) => cs * (upperFiber u w s (r.element * v.toHom x * t.element)).card).sum).sum).sum := by
    change last (next (ev (atLeft (up d) (.mixedMultiplication u v a b rs)) (vector x))) = _
    rw [lower_column, map_list_sum, map_list_sum]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ⟨cr,r⟩ _
    simp only [Function.comp_apply, map_smul]
    congr 1
    change last (ev (horizontal (straight (down u)) (.parallelUp v d w d ts))
      (Finsupp.single (mid u v (r.element * v.toHom x)) 1)) = _
    rw [middle_column, map_list_sum]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ⟨ct,t⟩ _
    simp only [Function.comp_apply, map_smul, last, LinearMap.comp_apply]
    rw [upper_mass]
  rw [expand x, expand y]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cr,r⟩ _
  apply congrArg (cr • ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨ct,t⟩ _
  apply congrArg (ct • ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cs,s⟩ _
  exact congrArg (fun n : Nat => cs * (n : Complex)) (fiber_card_constant u v w r t s x y)

end
end CaseSixTrivialAux

namespace CaseSixTrivialAux
open MackeyDiagrams
open scoped BigOperators
noncomputable section

abbrev endDot : Dot (b.comp i) (d.comp j) :=
  ⟨1, fun x => by rw [F_eq_one x]; simp only [map_one, mul_one]⟩

abbrev right
    (lower : List (Complex × ProjectionDot.Mixed b d i j))
    (middle : List (Complex × Dot (a.comp i) (a.comp i)))
    (upper : List (Complex × Dot (b.comp i) (d.comp j))) :=
  vertical (horizontal (straight (up a)) (.compactProjection b d i j lower))
    (vertical (atLeft (down j) (.parallelUp a i a i middle))
      (horizontal (straight (up a)) (.mixedMultiplication b d i j upper)))

abbrev fiberWord := tensor (up i) (down j)
abbrev fiberBasis := fiberWord.basis.carrier
abbrev fiberPair (g : A) : fiberBasis := (up i).basis.pair (down j).basis g 1

abbrev rightFunction :=
  Generator.mixedMultiplicationBasis b d i j endDot

abbrev rightProduct (w : fiberBasis) : D := Generator.mixedProduct b d (rightFunction w)

theorem rightProduct_pair (g : A) : rightProduct (fiberPair g) = b.toHom g := by
  change Generator.mixedProduct b d
    (Generator.mixedPair b d (b.toHom g * (1 : D) * d.toHom 1)) = _
  rw [Generator.mixedProduct_mixedPair, map_one, mul_one, mul_one]

theorem fiberPair_out (w : fiberBasis) : fiberPair (Quotient.out w).1 = w := by
  have hw := Quotient.out_eq w
  change (up i).basis.pair (down j).basis (Quotient.out w).1 (Quotient.out w).2 = w at hw
  rw [F_eq_one (Quotient.out w).2] at hw
  exact hw

theorem rightProduct_injective : Function.Injective rightProduct := by
  intro p q h
  have h' : rightProduct (fiberPair (Quotient.out p).1) =
      rightProduct (fiberPair (Quotient.out q).1) := by rw [fiberPair_out, fiberPair_out, h]
  rw [rightProduct_pair, rightProduct_pair] at h'
  exact (fiberPair_out p).symm.trans ((congrArg fiberPair (b.injective h')).trans (fiberPair_out q))

theorem rightGroupFinite (x : D) : Set.Finite {w | rightProduct w = x} := by
  classical
  by_cases h : ∃ w, rightProduct w = x
  · obtain ⟨w, hw⟩ := h
    apply (Set.finite_singleton w).subset
    exact fun v hv => Set.mem_singleton_iff.mpr (rightProduct_injective (hv.trans hw.symm))
  · exact Set.finite_empty.subset (fun w hw => (h ⟨w, hw⟩).elim)

theorem rightFinite (z : ad.basis.carrier) : Set.Finite {w | rightFunction w = z} :=
  (rightGroupFinite (Generator.mixedProduct b d z)).subset
    (fun _ hw => congrArg (Generator.mixedProduct b d) hw)

abbrev rightEval := ev
  (right [(1, ⟨endDot, rightFinite⟩)] [(1, Dot.id (a.comp i))] [(1, endDot)])

-- Step 1 of Example 8.6 and Lemma 6.6, equation (6.4), steps 1–4.
-- Use the registered singleton formula at B' = F. Its finiteness
-- hypothesis holds by injectivity of the lower product on the quotient.
theorem right_formula (x : D) :
    rightEval (vector x) =
      ∑ w ∈ (rightGroupFinite x).toFinset, Finsupp.single (coordinate (Quotient.out w).1 1) 1 := by
  have he := ((EvaluationWithOneProjection a b d a b d).2 F i j i).1
    endDot rightGroupFinite (Dot.id (a.comp i)) endDot 1 x
  change rightEval (vector x) = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro w _
  change Finsupp.single
      (coordinate (1 * a.toHom (Quotient.out w).1 * (1 : A)) (1 * d.toHom (Quotient.out w).2)) 1 = _
  have hm : a.toHom (Quotient.out w).1 = (Quotient.out w).1 := rfl
  rw [hm, F_eq_one (Quotient.out w).2, map_one, one_mul, mul_one, mul_one]

theorem right_action (x : D) :
    ((x : U) ∈ A → rightEval (vector x) = vector x) ∧
    ((x : U) ∉ A → rightEval (vector x) = 0) := by
  classical
  have mem (w : fiberBasis) : w ∈ (rightGroupFinite x).toFinset ↔ rightProduct w = x :=
    Set.Finite.mem_toFinset _
  rw [right_formula]
  constructor
  · intro hx
    let g : A := ⟨x, hx⟩
    have hg : b.toHom g = x := rfl
    have hf : (rightGroupFinite x).toFinset = {fiberPair g} := by
      ext w
      rw [mem, Finset.mem_singleton, ← hg, ← rightProduct_pair g]
      exact rightProduct_injective.eq_iff
    rw [hf, Finset.sum_singleton, coordinate_move, ← vector, ← rightProduct_pair,
      fiberPair_out, rightProduct_pair, hg, mul_one]
  · intro hx
    have hf : (rightGroupFinite x).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hw' := (mem w).1 hw
      rw [← fiberPair_out w, rightProduct_pair] at hw'
      have hproperty := (Quotient.out w).1.property
      exact hx ((congrArg (fun y : D => (y : U)) hw') ▸ hproperty)
    rw [hf, Finset.sum_empty]

end
end CaseSixTrivialAux

open CaseSixTrivialAux

theorem CaseSixCounterexampleWithTrivialProjectedStabilizers : (
let P := Equiv.Perm Nat
let finitary : Subgroup P := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (S : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let points : Finset Nat := {1, 2, 3, 4}
let small : Subgroup P :=
  Subgroup.closure ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P)
let A : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) small
let D : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) (blockSym points)
let F : Subgroup U := ⊥
let swapInBlock := fun (S : Finset Nat) (m n : Nat) (hm : m ∈ S) (hn : n ∈ S) =>
  (show Equiv.swap m n ∈ blockSym S from
    ⟨Equiv.swap (⟨m, hm⟩ : {k : Nat // k ∈ S}) ⟨n, hn⟩,
      Equiv.Perm.ofSubtype_swap_eq _ _⟩)
let hAD : A ≤ D := by
  have hsmall : small ≤ blockSym points := by
    refine (Subgroup.closure_le (blockSym points)).2 ?_
    intro σ hσ
    change σ ∈ ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P) at hσ
    rcases Set.mem_insert_iff.mp hσ with hσ | hσ
    · rw [hσ]
      exact swapInBlock points 1 2 (by decide) (by decide)
    · rw [Set.mem_singleton_iff.mp hσ]
      exact swapInBlock points 3 4 (by decide) (by decide)
  exact Subgroup.comap_mono hsmall
let parabolic := fun (B : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) B = iSup (fun i => blockSym (blocks i))
let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
  (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
let a := MackeyDiagrams.ConjEmbedding.id A
let b := incl hAD
let d := incl (show F ≤ D from bot_le)
let i := incl (show F ≤ A from bot_le)
let j := MackeyDiagrams.ConjEmbedding.id F
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let straight := fun {K L : Subgroup U} (p : MackeyDiagrams.Word K L) =>
  ordinary (MackeyDiagrams.Diagram.id p)
let word := tensor (up a) (tensor (down b) (up d))
let atLeft := fun {K J J' L M : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
    (tail : MackeyDiagrams.Word L M)
    (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
  vertical (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
    (vertical (horizontal crossing (straight tail))
      (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
let left := fun {B : Subgroup U}
    (u : MackeyDiagrams.ConjEmbedding A B) (v w : MackeyDiagrams.ConjEmbedding D B)
    (lower : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
    (middle : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w d)))
    (upper : List (Complex × MackeyDiagrams.ProjectionDot.Mixed u w a b)) =>
  vertical
    (atLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b lower))
    (vertical
      (horizontal (straight (down u))
        (MackeyDiagrams.LabelledDrawing.parallelUp v d w d middle))
      (atLeft (up d) (MackeyDiagrams.LabelledDrawing.compactProjection u w a b upper)))
let IsLeft := fun (drawing : MackeyDiagrams.LabelledDrawing Complex word word) =>
  ∃ (B : Subgroup U), parabolic B ∧
    ∃ (u : MackeyDiagrams.ConjEmbedding A B) (v w : MackeyDiagrams.ConjEmbedding D B)
      (lower : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
      (middle : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w d)))
      (upper : List (Complex × MackeyDiagrams.ProjectionDot.Mixed u w a b)),
      drawing = left u v w lower middle upper
let endDot : MackeyDiagrams.Dot (comp b i) (comp d j) :=
  ⟨1, fun x => by
    have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.property)
    simp [hx]⟩
let right := fun
    (lower : List (Complex × MackeyDiagrams.ProjectionDot.Mixed b d i j))
    (middle : List (Complex × MackeyDiagrams.Dot (comp a i) (comp a i)))
    (upper : List (Complex × MackeyDiagrams.Dot (comp b i) (comp d j))) =>
  vertical
    (horizontal (straight (up a))
      (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
    (vertical
      (atLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i a i middle))
      (horizontal (straight (up a))
        (MackeyDiagrams.LabelledDrawing.mixedMultiplication b d i j upper)))
let basis := MackeyDiagrams.Word.basis word
let coordinate := fun (g : A) (x : D) =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor (down b) (up d))) g
    (MackeyDiagrams.Generator.mixedPair b d x)
let basisVector := fun x : D => Finsupp.single (coordinate 1 x) (1 : Complex)
let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex word word) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
let coefficientSum := fun (z : Finsupp basis.carrier Complex) => Finsupp.sum z (fun _ c => c)
let projectsToTrivial := fun (S : Set (A × F)) =>
  Set.image Prod.snd S = ({1} : Set F)
let stabilizes := fun (p : basis.carrier) (k : A × F) => MackeyDiagrams.Biset.act basis k p = p
(∃ coordinates : basis.carrier ≃ D,
  ∀ (g : A) (x : D), coordinates (coordinate g x) = MackeyDiagrams.ConjEmbedding.toHom b g * x) ∧
(∀ p q : basis.carrier,
  projectsToTrivial {k | stabilizes p k} ∧
  projectsToTrivial {k | stabilizes q k} ∧
  projectsToTrivial {k | stabilizes p k ∧ stabilizes q k}) ∧
∃ (hr : ∀ z, Set.Finite {w |
    MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j endDot w = z}),
  let rightEval := evaluate
    (right [(1, ⟨endDot, hr⟩)] [(1, MackeyDiagrams.Dot.id (comp a i))] [(1, endDot)])
  (∀ x : D,
    ((x : U) ∈ A → rightEval (basisVector x) = basisVector x) ∧
    ((x : U) ∉ A → rightEval (basisVector x) = 0)) ∧
  ∀ (ι : Type) (terms : MackeyDiagrams.IndexedDrawing Complex word word ι)
      (coefficients : ι → Complex),
    (∀ k ∈ terms.indices, IsLeft (terms.summand k)) →
    let leftEval := MackeyDiagrams.IndexedDrawing.eval
      { terms with summand := fun k =>
          MackeyDiagrams.LabelledDrawing.scale (coefficients k) (terms.summand k) }
    (∀ x y : D, coefficientSum (leftEval (basisVector x)) = coefficientSum (leftEval (basisVector y))) ∧
    leftEval ≠ rightEval
) :=
(by
  -- Xiao, Example 8.6, archived p. 42 and published 28 November revision p. 44.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  classical
  change (∃ e : word.basis.carrier ≃ D, ∀ g x, e (coordinate g x) = b.toHom g * x) ∧ _
  refine ⟨⟨coordinates, coordinates_pair⟩, ?_, ?_⟩
  · -- The individual and joint stabilizers contain the identity.
    -- Their second coordinate belongs to F = 1.
    intro p q
    have trivial (S : Set (A × F)) (h : (1, 1) ∈ S) :
        Prod.snd '' S = ({1} : Set F) := by
      ext f
      exact ⟨fun _ => Set.mem_singleton_iff.mpr (F_eq_one f),
        fun hf => ⟨(1, 1), h, (Set.mem_singleton_iff.mp hf).symm⟩⟩
    have hp : word.basis.act (1, 1) p = p := word.basis.one_act p
    have hq : word.basis.act (1, 1) q = q := word.basis.one_act q
    exact ⟨trivial _ hp, trivial _ hq, trivial _ ⟨hp, hq⟩⟩
  · refine ⟨rightFinite, right_action, ?_⟩
    intro ι terms coefficients hterms
    let scaled : MackeyDiagrams.IndexedDrawing Complex word word ι :=
      {terms with summand := fun k => .scale (coefficients k) (terms.summand k)}
    have const (x y : D) :
        mass (scaled.eval (vector x)) = mass (scaled.eval (vector y)) := by
      rw [MackeyDiagrams.IndexedDrawing.eval_apply, MackeyDiagrams.IndexedDrawing.eval_apply,
        map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨B, _, u, v, w, rs, ts, ss, hs⟩ := hterms k hk
      change mass ((coefficients k) • ev (terms.summand k) (vector x)) =
        mass ((coefficients k) • ev (terms.summand k) (vector y))
      rw [map_smul, map_smul]
      congr 1
      change terms.summand k = left u v w rs ts ss at hs
      rw [hs]
      exact left_mass u v w rs ts ss x y
    refine ⟨fun x y => const x y, ?_⟩
    -- Step 6. Apply the two evaluated morphisms to the identity input
    -- and the explicit cross-block swap, then compare coefficients.
    change scaled.eval ≠ rightEval
    intro eq
    obtain ⟨x, hx⟩ := outside
    have disagree := const 1 x
    have h1 : ((1 : D) : U) ∈ A := A.one_mem
    rw [eq, (right_action 1).1 h1, (right_action x).2 hx, map_zero, mass_single] at disagree
    exact one_ne_zero disagree)

#print axioms CaseSixCounterexampleWithTrivialProjectedStabilizers
