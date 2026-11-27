import MackeyDiagrams
import Proofs.ParabolicCurlJoinIntersection

set_option maxHeartbeats 2000000

namespace UnequalParabolicCurlProof

open MackeyDiagrams

private abbrev finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev U := ↥finitary
private abbrev block (S : Finset Nat) : Subgroup U :=
  Subgroup.comap finitary.subtype
    (MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S)))

private def extend (S : Finset Nat) : Equiv.Perm ↥S →* U :=
  (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S)).codRestrict finitary (fun σ => by
    refine mem_closure_isSwap'.mpr (S.finite_toSet.subset ?_)
    intro x hx
    by_contra hn
    exact hx ((MulAction.mem_fixedBy).2 (Equiv.Perm.ofSubtype_apply_of_not_mem σ hn)))

private theorem extend_range (S : Finset Nat) : (extend S).range = block S := by
  ext σ
  change (∃ τ, extend S τ = σ) ↔ ∃ τ, Equiv.Perm.ofSubtype τ = (σ : Equiv.Perm Nat)
  exact ⟨fun ⟨τ, h⟩ => ⟨τ, congrArg Subtype.val h⟩, fun ⟨τ, h⟩ => ⟨τ, Subtype.ext h⟩⟩

private noncomputable def blockEquiv (S : Finset Nat) : Equiv.Perm ↥S ≃ ↥(block S) :=
  Equiv.ofBijective (fun σ => ⟨extend S σ, by
    rw [← extend_range]
    exact ⟨σ, rfl⟩⟩) (by
      constructor
      · intro σ τ h
        exact Equiv.Perm.ofSubtype_injective (congrArg (fun x : ↥(block S) =>
          (x.val : Equiv.Perm Nat)) h)
      · intro σ
        obtain ⟨τ, hτ⟩ := show σ.val ∈ (extend S).range by
          rw [extend_range]
          exact σ.property
        exact ⟨τ, Subtype.ext hτ⟩)

private theorem card_block (S : Finset Nat) : Nat.card ↥(block S) = S.card.factorial := by
  rw [← Nat.card_congr (blockEquiv S), Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]

-- Alphabeta Math, transpositions generate the symmetric group, Steps 1.1,
-- 2.1 and 3.1. The factorization applies on the finite block subtype.
-- Swap induction packages the cycle factorization and extends each factor
-- by the identity to Nat. The generated subgroup is tested after extension.
-- https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group
private theorem block_le_of_swaps (S : Finset Nat) (K : Subgroup U)
    (hs : ∀ x y : ↥S, x ≠ y → extend S (Equiv.swap x y) ∈ K) : block S ≤ K := by
  rw [← extend_range]
  rintro _ ⟨σ, rfl⟩
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simpa only [map_one] using K.one_mem
  | swap_mul τ x y hxy ih =>
    rw [map_mul]
    exact K.mul_mem (hs x y hxy) ih

private abbrev transposition {S : Finset Nat} (x y : ↥S) (h : (x : Nat) ≠ (y : Nat)) : U :=
  ⟨Equiv.swap (x : Nat) (y : Nat), Subgroup.subset_closure ⟨(x : Nat), (y : Nat), h, rfl⟩⟩

private theorem extend_swap {S : Finset Nat} (x y : ↥S) (h : (x : Nat) ≠ (y : Nat)) :
    extend S (Equiv.swap x y) = transposition x y h :=
  Subtype.ext (Equiv.Perm.ofSubtype_swap_eq x y)

private theorem block_pair {S : Finset Nat} (x y : ↥S) (h : (x : Nat) ≠ (y : Nat)) :
    block {(x : Nat), (y : Nat)} = Subgroup.zpowers (transposition x y h) := by
  let T : Finset Nat := {(x : Nat), (y : Nat)}
  let p : ↥T := ⟨x, Finset.mem_insert_self _ _⟩
  let q : ↥T := ⟨y, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have e : extend T (Equiv.swap p q) = transposition x y h :=
    Subtype.ext (Equiv.Perm.ofSubtype_swap_eq p q)
  have mem : extend T (Equiv.swap p q) ∈ Subgroup.zpowers (transposition x y h) :=
    e.symm ▸ Subgroup.mem_zpowers _
  have casesT (i : ↥T) : i = p ∨ i = q := by
    have hi := i.property
    change (i : Nat) ∈ {(x : Nat), (y : Nat)} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact Or.inl (Subtype.ext hi)
    · exact Or.inr (Subtype.ext hi)
  apply le_antisymm
  · apply block_le_of_swaps
    intro i j hij
    rcases casesT i with rfl | rfl <;> rcases casesT j with rfl | rfl
    · exact (hij rfl).elim
    · exact mem
    · rwa [Equiv.swap_comm]
    · exact (hij rfl).elim
  · apply Subgroup.zpowers_le.mpr
    rw [← e, ← extend_range]
    exact ⟨_, rfl⟩

private theorem fixes_outside {S : Finset Nat} {σ : U} (hσ : σ ∈ block S)
    {x : Nat} (hx : x ∉ S) : (σ : Equiv.Perm Nat) x = x := by
  obtain ⟨τ, hτ⟩ := hσ
  change Equiv.Perm.ofSubtype τ = (σ : Equiv.Perm Nat) at hτ
  rw [← hτ]
  exact Equiv.Perm.ofSubtype_apply_of_not_mem τ hx

private theorem preserves_block {S : Finset Nat} {σ : U} (hσ : σ ∈ block S)
    {x : Nat} (hx : x ∈ S) : (σ : Equiv.Perm Nat) x ∈ S := by
  obtain ⟨τ, hτ⟩ := hσ
  change Equiv.Perm.ofSubtype τ = (σ : Equiv.Perm Nat) at hτ
  rw [← hτ]
  exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem τ x).2 hx

private abbrev S : Finset Nat := {1, 2, 3}
private abbrev p : ↥S := ⟨1, by decide⟩
private abbrev q : ↥S := ⟨2, by decide⟩
private abbrev r : ↥S := ⟨3, by decide⟩
private abbrev A := Subgroup.zpowers (transposition p q (by decide))
private abbrev B := Subgroup.zpowers (transposition q r (by decide))
private abbrev H := block S

private theorem concrete_intersection : A ⊓ B = ⊥ := by
  have eA : block {1, 2} = A := block_pair p q (by decide)
  have eB : block {2, 3} = B := block_pair q r (by decide)
  rw [← eA, ← eB]
  apply le_antisymm ?_ bot_le
  intro σ hσ
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (σ : Equiv.Perm Nat) x = x
  have h1 : (σ : Equiv.Perm Nat) 1 = 1 := fixes_outside hσ.2 (by decide)
  by_cases hx : x ∈ ({1, 2} : Finset Nat)
  · rcases (show x = 1 ∨ x = 2 by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx)
      with rfl | rfl
    · exact h1
    · have h2 := preserves_block hσ.1 hx
      rcases (show (σ : Equiv.Perm Nat) 2 = 1 ∨ (σ : Equiv.Perm Nat) 2 = 2 by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using h2) with e | e
      · exact (by decide : (2 : Nat) ≠ 1) ((σ : Equiv.Perm Nat).injective (e.trans h1.symm)) |>.elim
      · exact e
  · exact fixes_outside hσ.1 hx

private theorem concrete_join (hA : A ≤ H) (hB : B ≤ H) : A ⊔ B = H := by
  apply le_antisymm (sup_le hA hB)
  have hpq : extend S (Equiv.swap p q) ∈ A ⊔ B := by
    rw [extend_swap p q (by decide)]
    exact (le_sup_left : A ≤ A ⊔ B) (Subgroup.mem_zpowers _)
  have hqr : extend S (Equiv.swap q r) ∈ A ⊔ B := by
    rw [extend_swap q r (by decide)]
    exact (le_sup_right : B ≤ A ⊔ B) (Subgroup.mem_zpowers _)
  have hpr : extend S (Equiv.swap p r) ∈ A ⊔ B := by
    -- The missing swap (13) is the conjugate of (12) by (23).
    rw [Equiv.swap_comm p r,
      ← Equiv.swap_mul_swap_mul_swap (x := p) (y := q) (z := r) (by decide) (by decide),
      map_mul, map_mul]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem hqr hpq) hqr
  have casesS (i : ↥S) : i = p ∨ i = q ∨ i = r := by
    have hi := i.property
    change (i : Nat) ∈ {1, 2, 3} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi
    · exact Or.inl (Subtype.ext hi)
    · exact Or.inr (Or.inl (Subtype.ext hi))
    · exact Or.inr (Or.inr (Subtype.ext hi))
  apply block_le_of_swaps
  intro i j hij
  rcases casesS i with rfl | rfl | rfl <;> rcases casesS j with rfl | rfl | rfl
  all_goals first | exact (hij rfl).elim | exact hpq | exact hqr | exact hpr |
    (rw [Equiv.swap_comm]; first | exact hpq | exact hqr | exact hpr)

private abbrev blockGroup (P : Finset (Finset Nat)) : Subgroup U :=
  iSup (fun V : ↥P => block (V : Finset Nat))

private abbrev partition (T : Finset Nat) (P : Finset (Finset Nat)) : Prop :=
  (∀ V ∈ P, Finset.Nonempty V) ∧
  (∀ V ∈ P, ∀ W ∈ P, V ≠ W → Disjoint V W) ∧
  (∀ x : Nat, x ∈ T ↔ ∃ V ∈ P, x ∈ V)

private abbrev parabolic (L : Subgroup U) : Prop :=
  ∃ T P, partition T P ∧ L = blockGroup P

private theorem singleton_block (x : Nat) : block {x} = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply block_le_of_swaps
  intro a b hab
  have ha : (a : Nat) = x := Finset.mem_singleton.mp a.property
  have hb : (b : Nat) = x := Finset.mem_singleton.mp b.property
  exact (hab (Subtype.ext (ha.trans hb.symm))).elim

private theorem singleton_partition (T : Finset Nat) (hT : T.Nonempty) :
    partition T {T} ∧ block T = blockGroup {T} := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro V hV
    rwa [Finset.mem_singleton.mp hV]
  · intro V hV W hW hne
    exact (hne ((Finset.mem_singleton.mp hV).trans (Finset.mem_singleton.mp hW).symm)).elim
  · intro x
    simp
  · apply le_antisymm
    · exact le_iSup (fun V : ↥({T} : Finset (Finset Nat)) => block V.val) ⟨T, by simp⟩
    · apply iSup_le
      intro V
      rw [Finset.mem_singleton.mp V.property]

private theorem pair_partition (x y z : Nat) (hxz : x ≠ z) (hyz : y ≠ z) :
    partition {x, y, z} {{x, y}, {z}} ∧ block {x, y} = blockGroup {{x, y}, {z}} := by
  have hdisj : Disjoint ({x, y} : Finset Nat) {z} := by
    rw [Finset.disjoint_left]
    intro u hu hv
    have e := Finset.mem_singleton.mp hv
    subst u
    simpa [Ne.symm hxz, Ne.symm hyz] using hu
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · exact ⟨x, by simp⟩
    · rw [Finset.mem_singleton.mp hV]
      exact ⟨z, by simp⟩
  · intro V hV W hW hne
    rcases Finset.mem_insert.mp hV with rfl | hV <;>
      rcases Finset.mem_insert.mp hW with rfl | hW
    · exact (hne rfl).elim
    · rwa [Finset.mem_singleton.mp hW]
    · rw [Finset.mem_singleton.mp hV]
      exact hdisj.symm
    · exact (hne ((Finset.mem_singleton.mp hV).trans (Finset.mem_singleton.mp hW).symm)).elim
  · intro u
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl)
      · exact ⟨{x, y}, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨{x, y}, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨{z}, Or.inr rfl, rfl⟩
    · rintro ⟨V, hV, hu⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hV ⊢
      rcases hV with rfl | rfl
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        exact hu.elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Finset.mem_singleton.mp hu))
  · apply le_antisymm
    · exact le_iSup (fun V : ↥({{x, y}, {z}} : Finset (Finset Nat)) => block V.val)
        ⟨{x, y}, by simp⟩
    · apply iSup_le
      intro V
      rcases Finset.mem_insert.mp V.property with hV | hV
      · rw [hV]
      · rw [Finset.mem_singleton.mp hV, singleton_block]
        exact bot_le

private theorem card_product_of_inf_eq_bot {V : Type*} [Group V] (A B : Subgroup V)
    (h : A ⊓ B = ⊥) :
    Nat.card ↥(Set.image2 (fun a b : V => a * b) (A : Set V) (B : Set V)) =
      Nat.card ↥A * Nat.card ↥B := by
  let f : ↥A × ↥B → ↥(Set.image2 (fun a b : V => a * b) (A : Set V) (B : Set V)) :=
    fun x => ⟨x.1.val * x.2.val, ⟨x.1.val, x.1.property, x.2.val, x.2.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ e
      have he : a.val * b.val = c.val * d.val := congrArg Subtype.val e
      have hd : a.val⁻¹ * c.val = b.val * d.val⁻¹ := by
        simpa [mul_assoc] using (congrArg (fun w => a.val⁻¹ * (w * d.val⁻¹)) he).symm
      have hm : a.val⁻¹ * c.val ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a.property) c.property, hd ▸ B.mul_mem b.property (B.inv_mem d.property)⟩
      rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hm
      have hn : b.val = d.val := mul_left_cancel (hm ▸ he)
      exact Prod.ext (Subtype.ext hm.symm) (Subtype.ext hn)
    · rintro ⟨_, a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

private abbrev inclusion {L K : Subgroup U} (h : L ≤ K) : ConjEmbedding L K :=
  ⟨Subgroup.inclusion h, ⟨1, fun x => by
    simp only [Subgroup.coe_inclusion, one_mul, inv_one, mul_one]⟩⟩

private noncomputable abbrev eval {K L : Subgroup U} {u v : Word K L}
    (d : LabelledDrawing Complex u v) :=
  d.interpret.eval

private noncomputable abbrev curls {L K G : Subgroup U}
    (a : ConjEmbedding K G) (d : ConjEmbedding L K) (f : Subgroup.FiniteIndex d.toHom.range) :
    LabelledDrawing Complex (Word.up a) (Word.up a) ×
      LabelledDrawing Complex (Word.down a) (Word.down a) :=
  (.vertical (.trivalent (.upToUpDown a d f)) (.trivalent (.upDownToUp a d)),
   .vertical (.trivalent (.downToUpDown a d f)) (.trivalent (.upDownToDown a d)))

-- These are the two oriented composites in the example. ReidemeisterOne
-- applies with the inner conjugator 1 and finite index of the inclusion image.
private theorem eval_curls {K L G : Subgroup U}
    (α : U) (hα : ∀ x : K, α * (x : U) * α⁻¹ ∈ G)
    (h : L ≤ K) (f : Subgroup.FiniteIndex (inclusion h).toHom.range) :
    let a := ConjEmbedding.ofConjugator α hα
    let c := curls a (inclusion h) f
    let n : Complex := (inclusion h).toHom.range.index
    eval c.1 = (Biset.Hom.id (Word.up a).basis).scale n ∧
      eval c.2 = (Biset.Hom.id (Word.down a).basis).scale n := by
  let hδ : ∀ x : L, (1 : U) * (x : U) * 1⁻¹ ∈ K := fun x => by
    simpa only [one_mul, inv_one, mul_one] using h x.property
  have e : inclusion h = ConjEmbedding.ofConjugator 1 hδ := by
    apply ConjEmbedding.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    simp only [ConjEmbedding.ofConjugator_apply, Subgroup.coe_inclusion, one_mul, inv_one, mul_one]
  simp only [e]
  have ev := ReidemeisterOne L K G 1 α hδ hα
  exact ⟨ev.1 f, ev.2.2.2 f⟩

private theorem inclusion_index {L K : Subgroup U} (h : L ≤ K) :
    (inclusion h).toHom.range.index * Nat.card ↥L = Nat.card ↥K := by
  have e : (inclusion h).toHom.range = L.subgroupOf K := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x.val, hx⟩, rfl⟩⟩
  rw [e, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.index_mul_card _

private theorem eval_stack {K L : Subgroup U} {w : Word K L}
    (bottom top : LabelledDrawing Complex w w) (r s : Complex)
    (hr : eval bottom = (Biset.Hom.id w.basis).scale r)
    (hs : eval top = (Biset.Hom.id w.basis).scale s) :
    eval (.vertical bottom top) = eval (.scale (r * s) (.ordinary (.id (R := Complex) w))) := by
  change (eval bottom).vertical (eval top) = (Biset.Hom.id w.basis).scale (r * s)
  rw [hr, hs, Biset.Hom.vertical_scale_left, Biset.Hom.vertical_scale_right, Biset.Hom.vertical_id]
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change r • (s • x) = (r * s) • x
  exact smul_smul r s x

private theorem compare_stacks {K G L M : Subgroup U} (α : U)
    (hα : ∀ x : K, α * (x : U) * α⁻¹ ∈ G) (hK : parabolic K) (hG : parabolic G)
    (T : Finset Nat) (P Q : Finset (Finset Nat))
    (hP : partition T P) (hQ : partition T Q)
    (eL : L = blockGroup P) (eM : M = blockGroup Q) (hL : L ≤ K) (hM : M ≤ K)
    (fL : Subgroup.FiniteIndex (inclusion hL).toHom.range)
    (fM : Subgroup.FiniteIndex (inclusion hM).toHom.range)
    (fI : Subgroup.FiniteIndex (inclusion (le_trans inf_le_left hL)).toHom.range)
    (fJ : Subgroup.FiniteIndex (inclusion (sup_le hL hM)).toHom.range) :
    let a := ConjEmbedding.ofConjugator α hα
    let cL := curls a (inclusion hL) fL
    let cM := curls a (inclusion hM) fM
    let cI := curls a (inclusion (le_trans inf_le_left hL)) fI
    let cJ := curls a (inclusion (sup_le hL hM)) fJ
    let LM : Set U := Set.image2 (fun x y : U => x * y) (L : Set U) (M : Set U)
    let ratio : Complex := (Nat.card ↥LM : Complex) / (Nat.card ↥(L ⊔ M) : Complex)
    eval (.vertical cJ.1 cI.1) = eval (.scale ratio (.vertical cM.1 cL.1)) ∧
    eval (.vertical cJ.2 cI.2) = eval (.scale ratio (.vertical cM.2 cL.2)) := by
  subst L
  subst M
  obtain ⟨gL, gM, gI, gJ, hup, hdown, _⟩ :=
    ParabolicCurlJoinIntersection K G α hα hK hG T P Q hP hQ hL hM
  exact ⟨hup, hdown⟩

end UnequalParabolicCurlProof
