import MackeyDiagrams
import Proofs.CommonMackeyIntersectionSum
import Proofs.MackeyIdentityDiagram
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.Group.TypeTags.Finite

namespace TwoMackeySummandsAux

private abbrev P := Equiv.Perm (Fin 3)
private abbrev C := Multiplicative (ZMod 2)
private abbrev U := P × C
private abbrev a : P := Equiv.swap 0 1
private abbrev b : P := Equiv.swap 0 2
private abbrev K : Subgroup U := (Subgroup.zpowers a).prod ⊤
private abbrev L : Subgroup U := (⊥ : Subgroup P).prod ⊤
private abbrev s : U := (b, 1)

private theorem perm_cases (p : P) :
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b ∨ p = b * a ∨ p = a * b * a :=
  (by decide : ∀ p : P,
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b ∨ p = b * a ∨ p = a * b * a) p

private theorem a_order : orderOf a = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, Equiv.swap_mul_self]
  · decide

private theorem mem_cyclic (p : P) : p ∈ Subgroup.zpowers a ↔ p = 1 ∨ p = a := by
  rw [mem_zpowers_iff_mem_range_orderOf, a_order]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have h : n = 0 ∨ n = 1 := by omega
    rcases h with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, pow_zero _⟩
    · exact ⟨1, by decide, pow_one _⟩

private theorem cosets_ne : DoubleCoset.mk K K (1 : U) ≠ DoubleCoset.mk K K s := by
  intro h
  obtain ⟨x, hx, y, hy, he⟩ := DoubleCoset.eq.mp h
  have hs : s ∈ K := by rw [he, mul_one]; exact K.mul_mem hx hy
  have hp := (mem_cyclic b).mp hs.1
  exact (by decide : ¬ (b = 1 ∨ b = a)) hp

private theorem cosets_all (j : DoubleCoset.Quotient (K : Set U) (K : Set U)) :
    j = DoubleCoset.mk K K (1 : U) ∨ j = DoubleCoset.mk K K s := by
  induction j using Quotient.inductionOn' with
  | h g =>
    change DoubleCoset.mk K K g = DoubleCoset.mk K K 1 ∨
      DoubleCoset.mk K K g = DoubleCoset.mk K K s
    have km (x : P) (hx : x = 1 ∨ x = a) (z : C) : (x,z) ∈ K :=
      ⟨(mem_cyclic x).mpr hx, Subgroup.mem_top _⟩
    have left (x : P) (hx : x = 1 ∨ x = a) (e : g.1 = x) :
        DoubleCoset.mk K K g = DoubleCoset.mk K K 1 := by
      symm
      apply DoubleCoset.eq.mpr
      refine ⟨(x,g.2), km x hx _, 1, K.one_mem, ?_⟩
      rw [mul_one, mul_one]
      exact Prod.ext e rfl
    have right (x y : P) (hx : x = 1 ∨ x = a) (hy : y = 1 ∨ y = a)
        (e : g.1 = x * b * y) : DoubleCoset.mk K K g = DoubleCoset.mk K K s := by
      symm
      apply DoubleCoset.eq.mpr
      exact ⟨(x,g.2), km x hx _, (y,1), km y hy _,
        Prod.ext e (by change g.2 = g.2 * 1 * 1; simp)⟩
    rcases perm_cases g.1 with h | h | h | h | h | h
    · exact Or.inl (left 1 (Or.inl rfl) h)
    · exact Or.inl (left a (Or.inr rfl) h)
    · exact Or.inr (right 1 1 (Or.inl rfl) (Or.inl rfl) (by simpa using h))
    · exact Or.inr (right a 1 (Or.inr rfl) (Or.inl rfl) (by simpa using h))
    · exact Or.inr (right 1 a (Or.inl rfl) (Or.inr rfl) (by simpa using h))
    · exact Or.inr (right a a (Or.inr rfl) (Or.inr rfl) h)

private theorem conjugate_one {V : Type*} [Group V] (S : Subgroup V) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : V))) S = S := by
  have h : MulEquiv.toMonoidHom (MulAut.conj (1 : V)) = MonoidHom.id V := by
    ext x
    change (1 : V) * x * 1⁻¹ = x
    simp
  rw [h, Subgroup.map_id]

private theorem intersection_s :
    K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) K = L := by
  ext x
  change (x ∈ K ∧ x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) K) ↔ x ∈ L
  constructor
  · rintro ⟨hx, hm⟩
    obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp hm
    have he' : b * y.1 * b⁻¹ = x.1 := congrArg Prod.fst he
    refine ⟨Subgroup.mem_bot.mpr ?_, Subgroup.mem_top _⟩
    rcases (mem_cyclic x.1).mp hx.1 with h | h
    · exact h
    · rcases (mem_cyclic y.1).mp hy.1 with h' | h'
      · exact False.elim ((by decide : b * 1 * b⁻¹ ≠ a) ((h' ▸ he').trans h))
      · exact False.elim ((by decide : b * a * b⁻¹ ≠ a) ((h' ▸ he').trans h))
  · intro hx
    have hx' : x.1 = 1 := Subgroup.mem_bot.mp hx.1
    have hk : x ∈ K := ⟨(mem_cyclic _).mpr (Or.inl hx'), Subgroup.mem_top _⟩
    refine ⟨hk, Subgroup.mem_map.mpr ⟨x, hk, Prod.ext ?_ ?_⟩⟩
    · change b * x.1 * b⁻¹ = x.1
      simp [hx']
    · change (1 : C) * x.2 * 1⁻¹ = x.2
      simp

private theorem index_K : L.relIndex K = 2 := by
  have hk : Nat.card K = 4 := by
    change Nat.card ((Subgroup.zpowers a).prod (⊤ : Subgroup C)) = 4
    rw [Nat.card_congr ((Subgroup.zpowers a).prodEquiv (⊤ : Subgroup C)).toEquiv,
      Nat.card_prod, Nat.card_zpowers, a_order, Subgroup.card_top]
    change 2 * Nat.card (ZMod 2) = 4
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hl : Nat.card L = 2 := by
    change Nat.card ((⊥ : Subgroup P).prod (⊤ : Subgroup C)) = 2
    rw [Nat.card_congr ((⊥ : Subgroup P).prodEquiv (⊤ : Subgroup C)).toEquiv,
      Nat.card_prod, Subgroup.card_bot, Subgroup.card_top]
    change 1 * Nat.card (ZMod 2) = 2
    rw [Nat.card_eq_fintype_card, ZMod.card, one_mul]
  have h := Subgroup.relIndex_mul_card L K
  have hLK : L ≤ K := Subgroup.prod_mono bot_le le_rfl
  rw [inf_eq_left.mpr hLK, hl, hk] at h
  omega

end TwoMackeySummandsAux

namespace TwoMackeySummandsAux

open MackeyDiagrams

variable {V : Type*} [Group V]

private abbrev conjugate (t : V) (K : Subgroup V) :=
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) K

private abbrev top (V : Type*) [Group V] : Subgroup V := ⊤

private abbrev outerEmbedding (K : Subgroup V) : ConjEmbedding K (top V) :=
  ConjEmbedding.ofConjugator 1 (fun _ => Subgroup.mem_top _)

private abbrev outerWord (K : Subgroup V) :=
  (Word.down (outerEmbedding K)).tensor (.up (outerEmbedding K))

private abbrev identityDrawing (K : Subgroup V) : Diagram Complex (outerWord K) (outerWord K) :=
  Diagram.horizontal (.id (.down (outerEmbedding K))) (.id (.up (outerEmbedding K)))

private abbrev intersection (K : Subgroup V) (t : top V) :=
  conjugate 1 K ⊓ conjugate ((t : V) * 1) K

private abbrev leftEmbedding (K S : Subgroup V) (t : top V) (h : S ≤ intersection K t) :
    ConjEmbedding S K :=
  ConjEmbedding.ofConjugator ((1 : V)⁻¹) (by
    intro x
    have hx := (h x.property).1
    change (x : V) ∈ conjugate 1 K at hx
    rw [show conjugate 1 K = K from conjugate_one K] at hx
    simpa using hx)

private abbrev rightEmbedding (K S : Subgroup V) (t : top V) (h : S ≤ intersection K t) :
    ConjEmbedding S K :=
  ConjEmbedding.ofConjugator ((1 : V)⁻¹ * (t : V)⁻¹) (by
    intro x
    obtain ⟨y, hy, he⟩ := (h x.property).2
    change ((t : V) * 1) * y * ((t : V) * 1)⁻¹ = (x : V) at he
    change y ∈ K at hy
    convert hy using 1
    rw [← he]
    group)

private abbrev crossingDot (K S : Subgroup V) (t : top V) (h : S ≤ intersection K t) :
    Dot ((outerEmbedding K).comp (leftEmbedding K S t h))
      ((outerEmbedding K).comp (rightEmbedding K S t h)) :=
  ⟨t, by
    intro x
    apply Subtype.ext
    change (1 : V) * ((1 : V)⁻¹ * (x : V) * ((1 : V)⁻¹)⁻¹) * 1⁻¹ * (t : V) =
      (t : V) * ((1 : V) * ((1⁻¹ * (t : V)⁻¹) * (x : V) * (1⁻¹ * (t : V)⁻¹)⁻¹) * 1⁻¹)
    group⟩

private theorem fibers [Finite V] {K S : Subgroup V}
    (l r : ConjEmbedding S K) (d : Dot ((outerEmbedding K).comp l) ((outerEmbedding K).comp r)) :
    ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis (outerEmbedding K) (outerEmbedding K) l r d w = z} := by
  let : Finite K := Finite.of_injective Subtype.val Subtype.val_injective
  let : Finite (Biset.tensor (Biset.induction l) (Biset.restriction r)).carrier := by
    change Finite (Quotient (Biset.balance (Biset.induction l) (Biset.restriction r)))
    infer_instance
  intro z
  exact Set.toFinite _

private noncomputable abbrev stack [Finite V] {K S : Subgroup V}
    (l r : ConjEmbedding S K) (d : Dot ((outerEmbedding K).comp l) ((outerEmbedding K).comp r)) :
    Diagram Complex (outerWord K) (outerWord K) :=
  .vertical (.mixedProjection _ _ l r d (fibers l r d)) (.mixedMultiplication _ _ l r d)

private noncomputable abbrev canonicalStack [Finite V] (K S : Subgroup V)
    (t : top V) (h : S ≤ intersection K t) : Diagram Complex (outerWord K) (outerWord K) :=
  stack (leftEmbedding K S t h) (rightEmbedding K S t h) (crossingDot K S t h)

private theorem stack_congr [Finite V] {K S : Subgroup V}
    {l r l' r' : ConjEmbedding S K}
    {d : Dot ((outerEmbedding K).comp l) ((outerEmbedding K).comp r)}
    {d' : Dot ((outerEmbedding K).comp l') ((outerEmbedding K).comp r')}
    (hl : l = l') (hr : r = r') (hd : d.element = d'.element) :
    stack l r d = stack l' r' d' := by
  subst l' r'
  rw [Dot.ext hd]

private abbrev A (K : Subgroup V) := Subgroup.comap (Subgroup.subtype (top V)) (conjugate 1 K)

private theorem range_eq (K : Subgroup V) : (outerEmbedding K).toHom.range = A K := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.property, rfl⟩
  · rintro ⟨k, hk, he⟩
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩

private abbrev J (K : Subgroup V) := DoubleCoset.Quotient (A K : Set (top V)) (A K : Set (top V))

private abbrev mk (K : Subgroup V) (t : top V) : J K := DoubleCoset.mk (A K) (A K) t

private theorem mk_eq (K : Subgroup V) (x y : top V) :
    mk K x = mk K y ↔ DoubleCoset.mk K K (x : V) = DoubleCoset.mk K K (y : V) := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨l, hl, r, hr, h⟩
    change (l : V) ∈ conjugate 1 K at hl
    change (r : V) ∈ conjugate 1 K at hr
    rw [show conjugate 1 K = K from conjugate_one K] at hl hr
    exact ⟨l, hl, r, hr, congrArg Subtype.val h⟩
  · rintro ⟨l, hl, r, hr, h⟩
    refine ⟨⟨l, Subgroup.mem_top _⟩, ?_, ⟨r, Subgroup.mem_top _⟩, ?_, Subtype.ext h⟩
    · change l ∈ conjugate 1 K
      rwa [show conjugate 1 K = K from conjugate_one K]
    · change r ∈ conjugate 1 K
      rwa [show conjugate 1 K = K from conjugate_one K]

private theorem normalizeStack [Finite V] (K S : Subgroup V)
    (σ : J K → top V) (reps : ∀ j, mk K (σ j) = j)
    (j : J K) (h : S ≤ intersection K (σ j)) (hi : S.IsFiniteRelIndex (intersection K (σ j))) :
    (canonicalStack K S (σ j) h).eval =
      (Diagram.scale (S.relIndex (intersection K (σ j)) : Complex)
        (canonicalStack K (intersection K (σ j)) (σ j) le_rfl)).eval := by
  have hRange (B : Subgroup (top V)) (hB : B = (outerEmbedding K).toHom.range)
      (τ : DoubleCoset.Quotient (B : Set (top V)) (B : Set (top V)) → top V)
      (hτ : ∀ i, DoubleCoset.mk B B (τ i) = i) (i : DoubleCoset.Quotient
        (B : Set (top V)) (B : Set (top V)))
      (hS : S ≤ intersection K (τ i)) (hIndex : S.IsFiniteRelIndex (intersection K (τ i))) :
      (canonicalStack K S (τ i) hS).eval =
        (Diagram.scale (S.relIndex (intersection K (τ i)) : Complex)
          (canonicalStack K (intersection K (τ i)) (τ i) le_rfl)).eval := by
    subst B
    obtain ⟨hf, hfJ, he⟩ := (CommonMackeyIntersectionSum K K (top V) 1 1
      (fun _ _ => Subgroup.mem_top _) (fun _ _ => Subgroup.mem_top _) τ hτ).1 i S hS hIndex
    exact he
  exact hRange (A K) (range_eq K).symm σ reps j h hi

private theorem fullIdentity [Finite V] (K : Subgroup V)
    (σ : J K → top V) (reps : ∀ j, mk K (σ j) = j)
    (j₁ j₂ : J K) (hne : j₁ ≠ j₂) (hall : ∀ j, j = j₁ ∨ j = j₂) :
    (identityDrawing K).eval = (Diagram.add
      (canonicalStack K (intersection K (σ j₁)) (σ j₁) le_rfl)
      (canonicalStack K (intersection K (σ j₂)) (σ j₂) le_rfl)).eval := by
  classical
  obtain ⟨hf, ⟨finite, hid⟩, _, _⟩ :=
    MackeyIdentityDiagram K K (top V) 1 1
      (fun _ _ => Subgroup.mem_top _) (fun _ _ => Subgroup.mem_top _) σ reps
  let term (x : (outerWord K).basis.carrier →₀ Complex) (j : J K) :=
    (canonicalStack K (intersection K (σ j)) (σ j) le_rfl).eval.toLinearMap x
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change (identityDrawing K).eval.toLinearMap x = term x j₁ + term x j₂
  have hs : (identityDrawing K).eval.toLinearMap x = ∑ j ∈ (finite x).toFinset, term x j := hid x
  rw [hs]
  rw [Finset.sum_subset (s₂ := {j₁, j₂})]
  · simp [hne]
  · intro j _
    rcases hall j with rfl | rfl <;> simp
  · intro j _ hj
    have hnot : j ∉ Function.support (term x) := by
      intro hmem
      exact hj ((Set.Finite.mem_toFinset (finite x)).mpr hmem)
    simpa only [Function.mem_support, not_not] using hnot

end TwoMackeySummandsAux

theorem TwoMackeySummandsWithSameInternalLabels : (
let U := Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)
let G : Subgroup U := ⊤
let K : Subgroup U :=
  Subgroup.prod (Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)) ⊤
let L : Subgroup U :=
  Subgroup.prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) ⊤
let s : U := (Equiv.swap (0 : Fin 3) 2, 1)
let intersectionAt := fun t : U =>
  K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) K
let L₁ := intersectionAt 1
let L₂ := intersectionAt s
let j₁ := DoubleCoset.mk K K (1 : U)
let j₂ := DoubleCoset.mk K K s
let hLK : L ≤ K := Subgroup.prod_mono bot_le le_rfl
let commutes : ∀ (t : U) (x : L), (x : U) * t = t * (x : U) := by
  intro t x
  have hx : (x : U).1 = 1 := Subgroup.mem_bot.mp x.property.1
  apply Prod.ext
  · change (x : U).1 * t.1 = t.1 * (x : U).1
    rw [hx, one_mul, mul_one]
  · exact mul_comm (x : U).2 t.2
let conjOnL : ∀ (t : U) (x : L), t * (x : U) * t⁻¹ = (x : U) := by
  intro t x
  rw [← commutes t x, mul_assoc, mul_inv_cancel, mul_one]
let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) (1 : U)
  (fun k => Subgroup.mem_top _)
let inner := fun t : U =>
  MackeyDiagrams.ConjEmbedding.ofConjugator (H := L) (G := K) t (by
    intro x
    rw [conjOnL t x]
    exact hLK x.property)
let l := inner 1
let dot := fun t : U =>
  show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a l)
    (MackeyDiagrams.ConjEmbedding.comp a (inner t⁻¹)) from
  ⟨⟨t, Subgroup.mem_top _⟩, by
    intro x
    apply Subtype.ext
    change (1 : U) * ((1 : U) * (x : U) * (1 : U)⁻¹) * (1 : U)⁻¹ * t =
      t * ((1 : U) * (t⁻¹ * (x : U) * (t⁻¹)⁻¹) * (1 : U)⁻¹)
    simp only [conjOnL, inv_one, one_mul, mul_one]
    exact commutes t x⟩
let M := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.down a) (MackeyDiagrams.Word.up a)
let pair := fun t : U =>
  let r := inner t⁻¹
  let d := dot t
  letI : Finite U := inferInstanceAs (Finite (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
  letI : Finite K := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (MackeyDiagrams.Biset.tensor
      (MackeyDiagrams.Biset.induction l) (MackeyDiagrams.Biset.restriction r)).carrier := by
    change Finite (Quotient (MackeyDiagrams.Biset.balance
      (MackeyDiagrams.Biset.induction l) (MackeyDiagrams.Biset.restriction r)))
    infer_instance
  show MackeyDiagrams.Diagram Complex M M from
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.mixedProjection a a l r d (fun _ => Set.toFinite _))
      (MackeyDiagrams.Diagram.mixedMultiplication a a l r d)
let straight : MackeyDiagrams.Diagram Complex M M :=
  MackeyDiagrams.Diagram.horizontal
    (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down a))
    (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up a))
j₁ ≠ j₂ ∧
  (∀ j : DoubleCoset.Quotient (K : Set U) (K : Set U), j = j₁ ∨ j = j₂) ∧
  L₁ = K ∧ L₂ = L ∧ L = L₁ ⊓ L₂ ∧
  L ≤ Subgroup.center U ∧ inner ((1 : U)⁻¹) = inner s⁻¹ ∧
  Subgroup.relIndex L L₁ = 2 ∧ Subgroup.relIndex L L₂ = 1 ∧
  MackeyDiagrams.Diagram.eval straight =
    MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.add
        (MackeyDiagrams.Diagram.scale ((1 : Complex) / 2) (pair 1)) (pair s))
) :=
open MackeyDiagrams TwoMackeySummandsAux in
by
  classical
  intro U G K L s intersectionAt L₁ L₂ j₁ j₂ hLK commutes conjOnL a inner l dot M pair straight
  -- Xiao, Example 5.1, archive p. 17 and published revision p. 19.
  -- There is no numbered Alphabeta Math proof recorded for the example.
  -- The two finite double cosets and intersection groups give the inputs
  -- to Proposition 5.1 and the Mackey identity used in the preceding subsection.
  have hL₁ : L₁ = K := by
    change K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : U))) K = K
    rw [conjugate_one, inf_idem]
  have hL₂ : L₂ = L := intersection_s
  have hIndex₁ : L.relIndex L₁ = 2 := hL₁ ▸ index_K
  have hIndex₂ : L.relIndex L₂ = 1 := hL₂ ▸ Subgroup.relIndex_self L
  refine ⟨cosets_ne, cosets_all, hL₁, hL₂, ?_, ?_, ?_, hIndex₁, hIndex₂, ?_⟩
  · rw [hL₁, hL₂, inf_eq_right.mpr hLK]
  · intro x hx
    exact Subgroup.mem_center_iff.mpr (fun t => (commutes t ⟨x, hx⟩).symm)
  · apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact (conjOnL _ x).trans (conjOnL _ x).symm
  let : Finite U := inferInstanceAs (Finite (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
  let t₁ : top U := ⟨1, Subgroup.mem_top _⟩
  let t₂ : top U := ⟨s, Subgroup.mem_top _⟩
  let i₁ := mk K t₁
  let i₂ := mk K t₂
  have hne : i₁ ≠ i₂ := fun h => cosets_ne ((mk_eq K t₁ t₂).mp h)
  have hall (j : J K) : j = i₁ ∨ j = i₂ := by
    induction j using Quotient.inductionOn' with
    | h t =>
      change mk K t = i₁ ∨ mk K t = i₂
      rcases cosets_all (DoubleCoset.mk K K (t : U)) with h | h
      · exact Or.inl ((mk_eq K t t₁).mpr h)
      · exact Or.inr ((mk_eq K t t₂).mpr h)
  let σ (j : J K) := if j = i₁ then t₁ else t₂
  have hσ₁ : σ i₁ = t₁ := by simp [σ]
  have hσ₂ : σ i₂ = t₂ := by simp [σ, hne.symm]
  have reps (j : J K) : mk K (σ j) = j := by
    rcases hall j with rfl | rfl
    · rw [hσ₁]
    · rw [hσ₂]
  -- Use the per-summand scaling from CommonMackeyIntersectionSum, since
  -- the two representatives and their common intersection are already explicit.
  -- Both formulas use the actual evaluated crossings with the given dot.
  have hS (t : top U) (ht : (t : U) = 1 ∨ (t : U) = s) :
      L ≤ intersection K t := by
    change L ≤ conjugate (1 : U) K ⊓ conjugate ((t : U) * 1) K
    rw [show conjugate (1 : U) K = K from conjugate_one K, mul_one]
    rcases ht with ht | ht
    · rw [ht, show conjugate (1 : U) K = K from conjugate_one K, inf_idem]
      exact hLK
    · rw [ht]
      exact hL₂.ge
  have pair_eq (t : top U) (h : L ≤ intersection K t) :
      canonicalStack K L t h = pair (t : U) := by
    apply stack_congr
    · apply ConjEmbedding.ext
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      change (1 : U)⁻¹ * (x : U) * ((1 : U)⁻¹)⁻¹ = 1 * (x : U) * (1 : U)⁻¹
      simp
    · apply ConjEmbedding.ext
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      change ((1 : U)⁻¹ * (t : U)⁻¹) * (x : U) * ((1 : U)⁻¹ * (t : U)⁻¹)⁻¹ =
        (t : U)⁻¹ * (x : U) * ((t : U)⁻¹)⁻¹
      simp
    · rfl
  have eval_norm (i : J K) (t : top U) (e : σ i = t) (ht : (t : U) = 1 ∨ (t : U) = s)
      (n : ℕ) (hn : L.relIndex (intersection K t) = n) :
      (pair (t : U)).eval =
        (Diagram.scale (n : Complex) (canonicalStack K (intersection K (σ i)) (σ i) le_rfl)).eval := by
    subst t
    have hi : L.IsFiniteRelIndex (intersection K (σ i)) := Subgroup.isFiniteRelIndex_of_finiteIndex
    have hs := normalizeStack K L σ reps i (hS (σ i) ht) hi
    rwa [pair_eq, hn] at hs
  have hN₁ := eval_norm i₁ t₁ hσ₁ (Or.inl rfl) 2 (by
    change L.relIndex (conjugate (1 : U) K ⊓ conjugate ((1 : U) * 1) K) = 2
    rw [show conjugate (1 : U) K = K from conjugate_one K, mul_one,
      show conjugate (1 : U) K = K from conjugate_one K, inf_idem]
    exact index_K)
  have hN₂ := eval_norm i₂ t₂ hσ₂ (Or.inr rfl) 1 (by
    change L.relIndex (conjugate (1 : U) K ⊓ conjugate (s * 1) K) = 1
    rw [show conjugate (1 : U) K = K from conjugate_one K, mul_one]
    exact hIndex₂)
  -- MackeyIdentityDiagram sums over the support at each input. The checked
  -- two-class comparison pads that sum with zero terms, yielding the binary
  -- addition in the drawing with a coefficient on the first complete stack.
  have hID := fullIdentity K σ reps i₁ i₂ hne hall
  let c₁ := canonicalStack K (intersection K (σ i₁)) (σ i₁) le_rfl
  let c₂ := canonicalStack K (intersection K (σ i₂)) (σ i₂) le_rfl
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change straight.eval.toLinearMap x =
    (1 / 2 : Complex) • (pair 1).eval.toLinearMap x + (pair s).eval.toLinearMap x
  change (pair 1).eval = (Diagram.scale (2 : Complex) c₁).eval at hN₁
  change (pair s).eval = (Diagram.scale (1 : Complex) c₂).eval at hN₂
  have hx := congrArg (fun f => Biset.Hom.toLinearMap f x) hID
  change straight.eval.toLinearMap x = c₁.eval.toLinearMap x + c₂.eval.toLinearMap x at hx
  rw [hx, hN₁, hN₂]
  change c₁.eval.toLinearMap x + c₂.eval.toLinearMap x =
    (1 / 2 : Complex) • ((2 : Complex) • c₁.eval.toLinearMap x) + (1 : Complex) • c₂.eval.toLinearMap x
  rw [smul_smul, one_smul, show (1 / 2 : Complex) * 2 = 1 by norm_num, one_smul]

#print axioms TwoMackeySummandsWithSameInternalLabels
