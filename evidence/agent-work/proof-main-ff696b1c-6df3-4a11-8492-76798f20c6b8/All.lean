import MackeyDiagrams
import Proofs.LargestCommonMixedCrossingParabolic
import Proofs.MackeyIdentityDiagram
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Interval.Finset.Nat

namespace CommonParabolicExample
open MackeyDiagrams
open scoped Pointwise

private abbrev F := Subgroup.closure {g : Equiv.Perm Nat | g.IsSwap}
private abbrev U := ↥F
private abbrev blockPerm (X : Finset Nat) :=
  (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X)).range
private abbrev block (X : Finset Nat) := (blockPerm X).comap F.subtype
private def sw (i j : Nat) : U := ⟨Equiv.swap i j, by
  by_cases h : i = j
  · subst j
    rw [Equiv.swap_self]
    exact F.one_mem
  · exact Subgroup.subset_closure ⟨i, j, h, rfl⟩⟩
private def act (g : U) (x : Nat) : Nat := (g : Equiv.Perm Nat) x
private theorem act_ext {g h : U} (e : ∀ x, act g x = act h x) : g = h :=
  Subtype.ext (Equiv.ext e)
@[simp] private theorem act_mul (g h : U) (x : Nat) : act (g * h) x = act g (act h x) := rfl
@[simp] private theorem act_one (x : Nat) : act (1 : U) x = x := rfl
@[simp] private theorem act_sw (i j x : Nat) : act (sw i j) x = Equiv.swap i j x := rfl
private theorem act_inj (g : U) : Function.Injective (act g) := (g : Equiv.Perm Nat).injective

private theorem perm_mem_block {X : Finset Nat} {g : Equiv.Perm Nat} :
    g ∈ blockPerm X ↔ ∀ x ∉ X, g x = x := by
  constructor
  · rintro ⟨p, rfl⟩
    exact fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem p hx
  · intro h
    obtain ⟨p, hp⟩ := (Equiv.Perm.subtypeEquivSubtypePerm (p := fun x : Nat => x ∈ X)).surjective ⟨g,h⟩
    exact ⟨p, congrArg Subtype.val hp⟩

private theorem mem_block {X : Finset Nat} {g : U} :
    g ∈ block X ↔ ∀ x ∉ X, act g x = x :=
  perm_mem_block

private theorem block_preserves {X : Finset Nat} {g : U} (h : g ∈ block X) (x : Nat) :
    act g x ∈ X ↔ x ∈ X := by
  have fix := mem_block.mp h
  constructor
  · intro hx
    by_contra hn
    exact hn (fix x hn ▸ hx)
  · intro hx
    by_contra hn
    have e : x = act g x := act_inj g (fix _ hn).symm
    exact hn (e ▸ hx)

private theorem sw_mem {X : Finset Nat} {i j : Nat} (hi : i ∈ X) (hj : j ∈ X) :
    sw i j ∈ block X := by
  apply mem_block.mpr
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hx hi) (by rintro rfl; exact hx hj)

private theorem parabolic_map_block (X : Finset Nat) : (block X).map F.subtype = blockPerm X := by
  apply Subgroup.map_comap_eq_self
  rw [Subgroup.range_subtype]
  intro g hg
  obtain ⟨p, rfl⟩ := hg
  change Equiv.Perm.ofSubtype p ∈ F
  induction p using Equiv.Perm.swap_induction_on with
  | one => simpa only [map_one] using F.one_mem
  | swap_mul p i j hij ih =>
    rw [map_mul]
    refine F.mul_mem ?_ ih
    ·
      rw [Equiv.Perm.ofSubtype_swap_eq]
      exact Subgroup.subset_closure ⟨i, j, fun h => hij (Subtype.ext h), rfl⟩

private theorem commute_blocks {X Y : Finset Nat} (hXY : Disjoint X Y)
    {g h : U} (hg : g ∈ block X) (hh : h ∈ block Y) : Commute g h := by
  apply act_ext
  intro x
  simp only [act_mul]
  by_cases hx : x ∈ X
  · rw [mem_block.mp hh x (Finset.disjoint_left.mp hXY hx),
        mem_block.mp hh _ (Finset.disjoint_left.mp hXY ((block_preserves hg x).mpr hx))]
  · by_cases hy : x ∈ Y
    · rw [mem_block.mp hg x hx,
          mem_block.mp hg _ (Finset.disjoint_right.mp hXY ((block_preserves hh x).mpr hy))]
    · simp only [mem_block.mp hg x hx, mem_block.mp hh x hy]

private theorem joinLeft {V : Type*} [Group V] {A B : Subgroup V} {g : V} (h : g ∈ A) :
    g ∈ A ⊔ B := (show A ≤ A ⊔ B from le_sup_left) h
private theorem joinRight {V : Type*} [Group V] {A B : Subgroup V} {g : V} (h : g ∈ B) :
    g ∈ A ⊔ B := (show B ≤ A ⊔ B from le_sup_right) h

private theorem mem_sup_blocks {X Y : Finset Nat} {A B : Subgroup U}
    (hXA : A ≤ block X) (hYB : B ≤ block Y) (hXY : Disjoint X Y) {g : U} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  have hnorm : A ≤ Subgroup.normalizer B := by
    intro a ha
    apply Subgroup.mem_normalizer_iff.mpr
    intro b
    constructor
    · intro hb
      rwa [(commute_blocks hXY (hXA ha) (hYB hb)).eq, mul_inv_cancel_right]
    · intro hb
      have hc := commute_blocks hXY (hXA ha) (hYB (show a * b * a⁻¹ ∈ B from hb))
      have heq : a * b * a⁻¹ = b := by
        calc
          a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by rw [hc.eq]
          _ = b := by group
      rwa [heq] at hb
  change g ∈ (↑(A ⊔ B) : Set U) ↔ _
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm]
  rfl

private theorem mul_blocks_inj {X Y : Finset Nat} {A B : Subgroup U}
    (hXA : A ≤ block X) (hYB : B ≤ block Y) (hXY : Disjoint X Y)
    {a a' b b' : U} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (he : a * b = a' * b') : a = a' ∧ b = b' := by
  have e : a = a' := by
    apply act_ext
    intro x
    by_cases hx : x ∈ X
    · have hx' := Finset.disjoint_left.mp hXY hx
      simpa only [act_mul, mem_block.mp (hYB hb) x hx', mem_block.mp (hYB hb') x hx']
        using congrArg (fun f => act f x) he
    · rw [mem_block.mp (hXA ha) x hx, mem_block.mp (hXA ha') x hx]
  subst a'
  exact ⟨rfl, mul_left_cancel he⟩

private theorem card_sup_blocks {X Y : Finset Nat} {A B : Subgroup U}
    (hXA : A ≤ block X) (hYB : B ≤ block Y) (hXY : Disjoint X Y) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : A × B → ↥(A ⊔ B) := fun ⟨a,b⟩ =>
    ⟨a.val * b.val, (A ⊔ B).mul_mem (joinLeft a.property) (joinRight b.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a,b⟩ ⟨a',b'⟩ h
      obtain ⟨ha,hb⟩ := mul_blocks_inj hXA hYB hXY a.property a'.property b.property b'.property
        (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · intro g
      obtain ⟨a,ha,b,hb,h⟩ := (mem_sup_blocks hXA hYB hXY).mp g.property
      exact ⟨(⟨a,ha⟩,⟨b,hb⟩), Subtype.ext h⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

private theorem card_block (X : Finset Nat) : Nat.card (block X) = X.card.factorial := by
  let e := Equiv.ofBijective
    (fun g : block X => (⟨(g.val : Equiv.Perm Nat), g.property⟩ : blockPerm X)) (by
      constructor
      · intro a b h
        exact Subtype.ext (Subtype.ext (congrArg (fun q : blockPerm X => q.val) h))
      · intro g
        obtain ⟨f,hf,he⟩ := show g.val ∈ (block X).map F.subtype from
          (parabolic_map_block X).symm ▸ g.property
        exact ⟨⟨f,hf⟩, Subtype.ext he⟩)
  let e' := Equiv.ofBijective (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X)).rangeRestrict
    ⟨fun a b h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩
  rw [Nat.card_congr e, Nat.card_congr e'.symm, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_coe]

private theorem pair_eq {i j : Nat} (hij : i ≠ j) {g : U} (hg : g ∈ block {i,j}) :
    g = 1 ∨ g = sw i j := by
  have images (x : Nat) (hx : x = i ∨ x = j) : act g x = i ∨ act g x = j := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (block_preserves hg x).mpr (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx)
  rcases images i (Or.inl rfl) with hi | hi
  · have hj : act g j = j := (images j (Or.inr rfl)).resolve_left
      (fun h => hij (act_inj g (hi.trans h.symm)))
    left
    apply act_ext
    intro x
    by_cases hxi : x = i
    · simpa [hxi] using hi
    by_cases hxj : x = j
    · simpa [hxj] using hj
    exact mem_block.mp hg x (by simp [hxi,hxj])
  · have hj : act g j = i := (images j (Or.inr rfl)).resolve_right
      (fun h => hij (act_inj g (hi.trans h.symm)))
    right
    apply act_ext
    intro x
    by_cases hxi : x = i
    · subst x
      simpa using hi
    by_cases hxj : x = j
    · subst x
      simpa using hj
    rw [mem_block.mp hg x (by simp [hxi,hxj]), act_sw, Equiv.swap_apply_of_ne_of_ne hxi hxj]

private theorem pair_cyclic {i j : Nat} (hij : i ≠ j) :
    block {i,j} = Subgroup.zpowers (sw i j) := by
  apply le_antisymm
  · intro g hg
    rcases pair_eq hij hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (sw_mem (by simp) (by simp))

private theorem sw_square (i j : Nat) : sw i j * sw i j = 1 := by
  apply Subtype.ext
  exact Equiv.swap_mul_self i j

private theorem card_pair {i j : Nat} (hij : i ≠ j) : Nat.card (Subgroup.zpowers (sw i j)) = 2 := by
  rw [← pair_cyclic hij, card_block]
  simp [hij]

private abbrev X3 := Finset.Icc 1 3
private abbrev X5 := Finset.Icc 4 8
private abbrev S3 := block X3
private abbrev S5 := block X5
private abbrev C12 := Subgroup.zpowers (sw 1 2)
private abbrev C23 := Subgroup.zpowers (sw 2 3)
private abbrev L78 := Subgroup.zpowers (sw 7 8)
private abbrev G := S3 ⊔ S5
private abbrev K := C12 ⊔ S5
private abbrev cyc := sw 4 5 * sw 5 6
private abbrev tau := sw 1 3
private abbrev sig := tau * cyc

private theorem blocks_disjoint : Disjoint X3 X5 := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_Icc] at hx hy
  omega
private theorem C12_le : C12 ≤ S3 := Subgroup.zpowers_le.mpr (sw_mem (by decide) (by decide))
private theorem C23_le : C23 ≤ S3 := Subgroup.zpowers_le.mpr (sw_mem (by decide) (by decide))
private theorem L78_le : L78 ≤ S5 := Subgroup.zpowers_le.mpr (sw_mem (by decide) (by decide))
private theorem K_le_G : K ≤ G := sup_le_sup_right C12_le _
private theorem cyc_mem : cyc ∈ S5 := S5.mul_mem (sw_mem (by decide) (by decide)) (sw_mem (by decide) (by decide))
private theorem tau_mem : tau ∈ S3 := sw_mem (by decide) (by decide)
private theorem sig_mem : sig ∈ G := G.mul_mem (joinLeft tau_mem) (joinRight cyc_mem)

private theorem first_fix {g : U} (hg : g ∈ S3) (h3 : act g 3 = 3) : g ∈ C12 := by
  change g ∈ Subgroup.zpowers (sw 1 2)
  rw [← pair_cyclic (i := 1) (j := 2) (by decide)]
  apply mem_block.mpr
  intro x hx
  by_cases h : x ∈ X3
  · rw [Finset.mem_Icc] at h
    have hx1 : x ≠ 1 := fun he => hx (by simp [he])
    have hx2 : x ≠ 2 := fun he => hx (by simp [he])
    have hx3 : x = 3 := by omega
    simpa only [hx3] using h3
  · exact mem_block.mp hg x h

private theorem first_double {g : U} (hg : g ∈ S3) :
    g ∈ C12 ∨ ∃ a ∈ C12, ∃ b ∈ C12, a * tau * b = g := by
  by_cases h : act g 3 = 3
  · exact Or.inl (first_fix hg h)
  · have him : act g 3 ∈ X3 := (block_preserves hg 3).mpr (by decide)
    rw [Finset.mem_Icc] at him
    have hx : act g 3 = 1 ∨ act g 3 = 2 := by omega
    have cut (a : U) (ha : a ∈ C12) (ha2 : a * a = 1)
        (hx : act (tau * a * g) 3 = 3) :
        ∃ a ∈ C12, ∃ b ∈ C12, a * tau * b = g := by
      refine ⟨a,ha,tau * a * g,first_fix (S3.mul_mem (S3.mul_mem tau_mem (C12_le ha)) hg) hx,?_⟩
      simp only [mul_assoc, ← mul_assoc tau tau, sw_square, one_mul, ← mul_assoc a a, ha2]
    right
    rcases hx with hx | hx
    · exact cut 1 (C12.one_mem) (one_mul 1) (by simp [hx])
    · exact cut (sw 1 2) (Subgroup.mem_zpowers _) (sw_square _ _) (by simp [hx])

private def mkIncl {V : Type} [Group V] (K G : Subgroup V) (h : K ≤ G) :
    ConjEmbedding K G :=
  ⟨Subgroup.inclusion h, ⟨1, fun x => by
    change (x : V) = 1 * (x : V) * (1 : V)⁻¹
    simp⟩⟩

private theorem range_incl {V : Type} [Group V] {K G : Subgroup V} (h : K ≤ G) :
    (mkIncl K G h).toHom.range = K.comap G.subtype := by
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    exact k.property
  · intro hx
    exact ⟨⟨x.val,hx⟩,rfl⟩

private theorem quotient_classes :
    let A := (mkIncl K G K_le_G).toHom.range
    let q := DoubleCoset.mk A A
    q 1 ≠ q ⟨sig,sig_mem⟩ ∧ q ⟨tau,joinLeft tau_mem⟩ = q ⟨sig,sig_mem⟩ ∧
      (∀ j : DoubleCoset.Quotient (A : Set G) (A : Set G), j = q 1 ∨ j = q ⟨sig,sig_mem⟩) := by
  have tau_ne : tau ∉ K := by
    intro h
    obtain ⟨a,ha,b,hb,he⟩ := (mem_sup_blocks C12_le le_rfl blocks_disjoint).mp h
    have haB : a ∈ block {1,2} := by
      rw [pair_cyclic (by decide)]
      exact ha
    have ha3 : act a 3 = 3 := mem_block.mp haB 3 (by decide)
    have hb3 : act b 3 = 3 := mem_block.mp hb 3 (by decide)
    have e := congrArg (fun f => act f 3) he
    simp only [act_mul,hb3,ha3,act_sw] at e
    exact (by decide : Equiv.swap 1 3 (3 : Nat) ≠ 3) e.symm
  dsimp only
  rw [range_incl]
  let A := K.comap G.subtype
  let q := DoubleCoset.mk A A
  let t : G := ⟨tau,joinLeft tau_mem⟩
  let s : G := ⟨sig,sig_mem⟩
  have hts : q t = q s := by
    apply DoubleCoset.eq.mpr
    exact ⟨1,A.one_mem,⟨cyc,joinRight cyc_mem⟩,joinRight cyc_mem,Subtype.ext (one_mul sig).symm⟩
  change q 1 ≠ q s ∧ q t = q s ∧ (∀ j, j = q 1 ∨ j = q s)
  refine ⟨?_, hts, ?_⟩
  · rw [← hts]
    intro he
    obtain ⟨x,hx,y,hy,h⟩ := DoubleCoset.eq.mp he
    have hk : (x : U) * 1 * (y : U) ∈ K := K.mul_mem (K.mul_mem hx K.one_mem) hy
    have hv := congrArg (fun z : G => z.val) h
    change tau = (x : U) * 1 * (y : U) at hv
    exact tau_ne (hv.symm ▸ hk)
  · intro j
    obtain ⟨g,rfl⟩ := Quotient.mk_surjective j
    change q g = q 1 ∨ q g = q s
    obtain ⟨a,ha,b,hb,hg⟩ := (mem_sup_blocks (A := S3) (B := S5) le_rfl le_rfl blocks_disjoint).mp g.property
    rcases first_double ha with ha' | ⟨x,hx,y,hy,hxy⟩
    · left
      symm
      apply DoubleCoset.eq.mpr
      refine ⟨⟨a,joinLeft ha⟩, joinLeft ha', ⟨b,joinRight hb⟩,joinRight hb,?_⟩
      apply Subtype.ext
      change (g : U) = a * 1 * b
      simpa only [mul_one] using hg.symm
    · right
      rw [← hts]
      symm
      apply DoubleCoset.eq.mpr
      refine ⟨⟨x,joinLeft (C12_le hx)⟩,joinLeft hx,
        ⟨y*b,G.mul_mem (joinLeft (C12_le hy)) (joinRight hb)⟩,
        K.mul_mem (joinLeft hy) (joinRight hb),?_⟩
      apply Subtype.ext
      change (g : U) = x * tau * (y * b)
      rw [← mul_assoc, hxy, hg]


private abbrev conjMap {V : Type} [Group V] (s : V) := (MulAut.conj s).toMonoidHom
private abbrev mac {V : Type} [Group V] (A : Subgroup V) (s : V) := A ⊓ A.map (conjMap s)

private theorem conjMap_one {V : Type} [Group V] : conjMap (1 : V) = MonoidHom.id V := by
  ext x
  change 1 * x * (1 : V)⁻¹ = x
  simp

private theorem mac_one {V : Type} [Group V] (A : Subgroup V) : mac A 1 = A := by
  change A ⊓ A.map (conjMap (1 : V)) = A
  rw [conjMap_one, Subgroup.map_id, inf_idem]

private theorem normalizes_of_commutes {V : Type} [Group V] (A : Subgroup V) (g : V)
    (h : ∀ x ∈ A, Commute g x) : g ∈ Subgroup.normalizer A := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rwa [(h x hx).eq, mul_inv_cancel_right]
  · intro hx
    have e := (h _ hx).eq
    have e' := congrArg (fun y => g⁻¹ * y * g) e
    have he : g * x * g⁻¹ = x := by
      calc
        g * x * g⁻¹ = g⁻¹ * (g * (g*x*g⁻¹)) * g * g⁻¹ := by group
        _ = g⁻¹ * ((g*x*g⁻¹) * g) * g * g⁻¹ := by rw [e]
        _ = x := by group
    rwa [he] at hx

private theorem tau_conjC12 : C12.map (conjMap tau) = C23 := by
  change (Subgroup.zpowers (sw 1 2)).map (conjMap tau) = Subgroup.zpowers (sw 2 3)
  rw [MonoidHom.map_zpowers]
  congr 1
  apply Subtype.ext
  exact (Equiv.swap_apply_apply (Equiv.swap 1 3) 1 2).symm.trans (Equiv.swap_comm 3 2)

private theorem conj_K {s : U} (hs : s ∈ S5) :
    K.map (conjMap (tau * s)) = C23 ⊔ S5 := by
  have c : Commute s (sw 1 2) :=
    (commute_blocks blocks_disjoint (C12_le (Subgroup.mem_zpowers _)) hs).symm
  have hC : (conjMap (tau * s)) (sw 1 2) = (conjMap tau) (sw 1 2) := by
    change tau * s * sw 1 2 * (tau * s)⁻¹ = tau * sw 1 2 * tau⁻¹
    rw [mul_inv_rev, mul_assoc tau s (sw 1 2), c.eq]
    group
  have ht : tau ∈ Subgroup.normalizer S5 :=
    normalizes_of_commutes S5 tau (fun _ hx => commute_blocks blocks_disjoint tau_mem hx)
  have hn : tau * s ∈ Subgroup.normalizer S5 :=
    (Subgroup.normalizer (S5 : Set U)).mul_mem ht ((show S5 ≤ Subgroup.normalizer S5 from Subgroup.le_normalizer) hs)
  have ht' : S5.map (conjMap (tau * s)) = S5 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  change K.map (conjMap (tau * s)) = _
  change (Subgroup.zpowers (sw 1 2) ⊔ S5).map (conjMap (tau * s)) = _
  rw [Subgroup.map_sup, ht', MonoidHom.map_zpowers, hC, ← MonoidHom.map_zpowers]
  exact congrArg (· ⊔ S5) tau_conjC12

private theorem mac_eq {s : U} (hs : s ∈ S5) : mac K (tau * s) = S5 := by
  change K ⊓ K.map (conjMap (tau * s)) = S5
  rw [conj_K hs]
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  rintro g ⟨hg, hg'⟩
  obtain ⟨a,ha,b,hb,rfl⟩ := (mem_sup_blocks C12_le le_rfl blocks_disjoint).mp hg
  obtain ⟨a',ha',b',hb',he⟩ := (mem_sup_blocks C23_le le_rfl blocks_disjoint).mp hg'
  obtain ⟨hea,_⟩ := mul_blocks_inj (A := S3) (B := S5) le_rfl le_rfl blocks_disjoint
    (C23_le ha') (C12_le ha) hb' hb he
  have ha1 : a = 1 := by
    have haB : a ∈ block {1,2} := by rw [pair_cyclic (by decide)]; exact ha
    have haB' : a' ∈ block {2,3} := by rw [pair_cyclic (by decide)]; exact ha'
    rcases pair_eq (by decide) haB with h | h
    · exact h
    · have hfix : act a' 1 = 1 :=
        mem_block.mp haB' 1 (by decide)
      rw [hea,h] at hfix
      exact False.elim ((by decide : (2 : Nat) ≠ 1) hfix)
  simpa only [ha1,one_mul] using hb

private theorem mac_tau : mac K tau = S5 := by
  simpa only [mul_one] using mac_eq (S5.one_mem : (1 : U) ∈ S5)
private theorem mac_sig : mac K sig = S5 := mac_eq cyc_mem

private abbrev X456 := Finset.Icc 4 6
private abbrev X78 := ({7,8} : Finset Nat)

private theorem cyc_mem456 : cyc ∈ block X456 :=
  (block X456).mul_mem (sw_mem (by decide) (by decide)) (sw_mem (by decide) (by decide))
private theorem disjoint45678 : Disjoint X456 X78 := by
  decide

private theorem cyc_square_mem : cyc ^ 2 ∈ block X456 := (block X456).pow_mem cyc_mem456 2
private theorem cyc_fix_iff (x : Nat) : act cyc x = x ↔ x ∉ X456 := by
  constructor
  · intro h hx
    change x ∈ Finset.Icc (4 : Nat) 6 at hx
    rw [Finset.mem_Icc] at hx
    obtain ⟨hxLo,hxHi⟩ := hx
    interval_cases x <;> contradiction
  · exact mem_block.mp cyc_mem456 x

private theorem cycle_centralizer (g : U) (hg : g ∈ S5) :
    Commute g cyc ↔ g ∈ Subgroup.zpowers cyc ⊔ L78 := by
  constructor
  · intro h
    have hx (x : Nat) : act g (act cyc x) = act cyc (act g x) :=
      congrArg (fun f => act f x) h.eq
    have preserve (x : Nat) : act g x ∈ X456 ↔ x ∈ X456 := by
      have e : act cyc (act g x) = act g x ↔ act cyc x = x := by
        rw [← hx x]
        exact (act_inj g).eq_iff
      exact not_iff_not.mp ((cyc_fix_iff _).symm.trans (e.trans (cyc_fix_iff _)))
    have h4 := (preserve 4).mpr (by decide)
    rw [Finset.mem_Icc] at h4
    have h7 := (block_preserves hg 7).mpr (by decide)
    rw [Finset.mem_Icc] at h7
    have not7 : act g 7 ∉ X456 := fun hm => (by decide : 7 ∉ X456) ((preserve 7).mp hm)
    rw [Finset.mem_Icc] at not7
    have h8 := (block_preserves hg 8).mpr (by decide)
    rw [Finset.mem_Icc] at h8
    have not8 : act g 8 ∉ X456 := fun hm => (by decide : 8 ∉ X456) ((preserve 8).mp hm)
    rw [Finset.mem_Icc] at not8
    have h78 : act g 7 ≠ act g 8 := fun he => (by decide : (7 : Nat) ≠ 8) (act_inj g he)
    have cp (a b : U) (ha : a ∈ Subgroup.zpowers cyc) (hb : b ∈ L78)
        (ha4 : act g 4 = act a 4) (hb7 : act g 7 = act b 7) (hb8 : act g 8 = act b 8) :
        g ∈ Subgroup.zpowers cyc ⊔ L78 := by
      have haB : a ∈ block X456 := Subgroup.zpowers_le.mpr cyc_mem456 ha
      have hbB : b ∈ block X78 := by change b ∈ block {7,8}; rw [pair_cyclic (by decide)]; exact hb
      have ham : Commute cyc a := by
        obtain ⟨n,rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact Commute.self_zpow _ _
      have haComm (x : Nat) : act cyc (act a x) = act a (act cyc x) :=
        congrArg (fun f => act f x) ham.eq
      have ha5 : act g 5 = act a 5 := by
        calc
          act g 5 = act cyc (act g 4) := hx 4
          _ = act cyc (act a 4) := congrArg (act cyc) ha4
          _ = act a 5 := haComm 4
      have ha6 : act g 6 = act a 6 := by
        calc
          act g 6 = act cyc (act g 5) := hx 5
          _ = act cyc (act a 5) := congrArg (act cyc) ha5
          _ = act a 6 := haComm 5
      have he : g = a * b := by
        apply act_ext
        intro x
        simp only [act_mul]
        by_cases hx5 : x ∈ X5
        · rw [Finset.mem_Icc] at hx5
          obtain ⟨hlo,hhi⟩ := hx5
          interval_cases x
          · rw [mem_block.mp hbB _ (by decide : 4 ∉ X78)]
            exact ha4
          · rw [mem_block.mp hbB _ (by decide : 5 ∉ X78)]
            exact ha5
          · rw [mem_block.mp hbB _ (by decide : 6 ∉ X78)]
            exact ha6
          · rw [← hb7, mem_block.mp haB _ (by rwa [Finset.mem_Icc])]
          · rw [← hb8, mem_block.mp haB _ (by rwa [Finset.mem_Icc])]
        · rw [mem_block.mp hg _ hx5, mem_block.mp hbB _ (fun hh => hx5 (by
                simp only [X78,Finset.mem_insert,Finset.mem_singleton] at hh
                rcases hh with rfl | rfl <;> decide)),
              mem_block.mp haB _ (fun hh => hx5 (by
                rw [Finset.mem_Icc] at hh ⊢
                omega))]
      rw [he]
      exact Subgroup.mul_mem _ (joinLeft ha) (joinRight hb)
    have chooseB (a : U) (ha : a ∈ Subgroup.zpowers cyc) (ha4 : act g 4 = act a 4) :
        g ∈ Subgroup.zpowers cyc ⊔ L78 := by
      by_cases h : act g 7 = 7
      · exact cp a 1 ha (L78.one_mem) ha4 h (by change act g 8 = 8; omega)
      · exact cp a (sw 7 8) ha (Subgroup.mem_zpowers _) ha4
          (by change act g 7 = 8; omega) (by change act g 8 = 7; omega)
    have hCases : act g 4 = 4 ∨ act g 4 = 5 ∨ act g 4 = 6 := by omega
    rcases hCases with h | h | h
    · exact chooseB 1 (Subgroup.one_mem _) h
    · exact chooseB cyc (Subgroup.mem_zpowers _) h
    · exact chooseB (cyc^2) (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) h
  · intro hm
    have hL : L78 ≤ block X78 := le_of_eq (pair_cyclic (i:=7) (j:=8) (by decide)).symm
    obtain ⟨a,ha,b,hb,rfl⟩ := (mem_sup_blocks (Subgroup.zpowers_le.mpr cyc_mem456) hL disjoint45678).mp hm
    have hca : Commute a cyc := by
      obtain ⟨n,rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact Commute.zpow_self _ _
    exact hca.mul_left (commute_blocks disjoint45678 cyc_mem456 (hL hb)).symm


private def common (K G : Subgroup U) (s : U) :=
  (mac K 1 ⊓ mac K s) ⊓ (G ⊓ Subgroup.centralizer ({(1 : U) * s⁻¹} : Set U))

private theorem centralizer_single {x s : U} :
    x ∈ Subgroup.centralizer ({(1 : U) * s⁻¹} : Set U) ↔ Commute x s := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq, one_mul]
  constructor
  · intro h
    exact (show Commute s⁻¹ x from h).inv_left.symm
  · intro h
    exact h.inv_right.symm.eq

private theorem common_sig : common K G sig = Subgroup.zpowers cyc ⊔ L78 := by
  unfold common
  rw [mac_one, mac_sig]
  have hS : S5 ≤ K := le_sup_right
  rw [inf_eq_right.mpr hS]
  ext x
  constructor
  · rintro ⟨hx, _, hcen⟩
    have hτ : Commute x tau := (commute_blocks blocks_disjoint tau_mem hx).symm
    have hs : Commute x (tau * cyc) := centralizer_single.mp hcen
    have hc : Commute x cyc := by
      change x * cyc = cyc * x
      apply mul_left_cancel (a:=tau)
      calc
        tau * (x * cyc) = x * (tau * cyc) := by rw [← mul_assoc, ← hτ.eq, mul_assoc]
        _ = (tau * cyc) * x := hs.eq
        _ = tau * (cyc * x) := mul_assoc _ _ _
    exact (cycle_centralizer x hx).mp hc
  · intro hx
    have hle : Subgroup.zpowers cyc ⊔ L78 ≤ S5 :=
      sup_le (Subgroup.zpowers_le.mpr cyc_mem) L78_le
    have hx5 := hle hx
    exact ⟨hx5, joinRight hx5, centralizer_single.mpr
      ((commute_blocks blocks_disjoint tau_mem hx5).symm.mul_right
        ((cycle_centralizer x hx5).mpr hx))⟩

private theorem common_tau : common K G tau = S5 := by
  unfold common
  rw [mac_one, mac_tau]
  have hS : S5 ≤ K := le_sup_right
  rw [inf_eq_right.mpr hS]
  exact inf_eq_left.mpr (fun x hx => ⟨joinRight hx,
    centralizer_single.mpr (commute_blocks blocks_disjoint tau_mem hx).symm⟩)

private theorem swap_fixes_or {g : U} (hg : (g : Equiv.Perm Nat).IsSwap) :
    ¬ (act g 4 ≠ 4 ∧ act g 5 ≠ 5 ∧ act g 6 ≠ 6) := by
  obtain ⟨i,j,_,e⟩ := hg
  rintro ⟨h4,h5,h6⟩
  have moved (x : Nat) (h : act g x ≠ x) : x = i ∨ x = j := by
    by_contra hn
    push Not at hn
    exact h (show (g : Equiv.Perm Nat) x = x from e.symm ▸ Equiv.swap_apply_of_ne_of_ne hn.1 hn.2)
  rcases moved 4 h4 with h | h <;>
    rcases moved 5 h5 with h' | h' <;> rcases moved 6 h6 with h'' | h'' <;> omega

private theorem swap_part_sig :
    Subgroup.closure {x : U | x ∈ common K G sig ∧ (x : Equiv.Perm Nat).IsSwap} = L78 := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨hx,hswap⟩
    have hx5 : x ∈ S5 := by
      have he := hx
      change x ∈ common K G sig at he
      rw [common_sig] at he
      exact (show Subgroup.zpowers cyc ⊔ L78 ≤ S5 from sup_le (Subgroup.zpowers_le.mpr cyc_mem) L78_le) he
    have hc : Commute x cyc := (cycle_centralizer x hx5).mpr (common_sig ▸ hx)
    have step (n m : Nat) (hnm : act cyc n = m) : act x n = n ↔ act x m = m := by
      have h := congrArg (fun g : U => act g n) hc.eq
      change act x (act cyc n) = act cyc (act x n) at h
      rw [hnm] at h
      rw [h, ← hnm]
      exact (act_inj cyc).eq_iff.symm
    have h45 := step 4 5 rfl
    have h56 := step 5 6 rfl
    have h4 : act x 4 = 4 := by
      by_contra h
      exact swap_fixes_or hswap ⟨h,h ∘ h45.mpr,h ∘ h45.mpr ∘ h56.mpr⟩
    have hb : x ∈ block X78 := by
      apply mem_block.mpr
      intro n hn
      by_cases hm : n ∈ X5
      · change 4 ≤ n ∧ n ≤ 8 at hm
        obtain ⟨hl,hu⟩ := hm
        interval_cases n
        · exact h4
        · exact h45.mp h4
        · exact h56.mp (h45.mp h4)
        · exact False.elim (hn (by decide))
        · exact False.elim (hn (by decide))
      · exact mem_block.mp hx5 n hm
    change x ∈ Subgroup.zpowers (sw 7 8)
    exact (pair_cyclic (i:=7) (j:=8) (by decide)) ▸ hb
  · apply Subgroup.zpowers_le.mpr
    apply Subgroup.subset_closure
    exact ⟨common_sig.symm ▸ (show sw 7 8 ∈ Subgroup.zpowers cyc ⊔ L78 from
      joinRight (Subgroup.mem_zpowers _)), ⟨7,8,by decide,rfl⟩⟩

private theorem block_swap_closure (X : Finset Nat) :
    Subgroup.closure {x : U | x ∈ block X ∧ (x : Equiv.Perm Nat).IsSwap} = block X := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_
  · intro x hx
    exact (show x ∈ block X ∧ (x : Equiv.Perm Nat).IsSwap from hx).1
  intro x hx
  obtain ⟨p,hp⟩ := hx
  have h (q : Equiv.Perm ↥X) :
      ∀ y : U, Equiv.Perm.ofSubtype q = (y : Equiv.Perm Nat) →
        y ∈ Subgroup.closure {z : U | z ∈ block X ∧ (z : Equiv.Perm Nat).IsSwap} := by
    induction q using Equiv.Perm.swap_induction_on with
    | one =>
      intro y hy
      rw [map_one] at hy
      have e : 1 = y := Subtype.ext hy
      exact e ▸ Subgroup.one_mem _
    | swap_mul q i j hij ih =>
      intro y hy
      have he : Equiv.Perm.ofSubtype q = (↑((sw i j)⁻¹ * y) : Equiv.Perm Nat) := by
        rw [map_mul, Equiv.Perm.ofSubtype_swap_eq] at hy
        change _ = (Equiv.swap i.val j.val)⁻¹ * (y : Equiv.Perm Nat)
        rw [← hy, inv_mul_cancel_left]
      have hrest := ih _ he
      have hsw : sw i j ∈ Subgroup.closure {z : U | z ∈ block X ∧ (z : Equiv.Perm Nat).IsSwap} :=
        Subgroup.subset_closure ⟨sw_mem i.property j.property,
          ⟨i,j,fun h => hij (Subtype.ext h),rfl⟩⟩
      simpa only [mul_inv_cancel_left] using Subgroup.mul_mem _ hsw hrest
  exact h p x hp

private theorem swap_part_tau :
    Subgroup.closure {x : U | x ∈ common K G tau ∧ (x : Equiv.Perm Nat).IsSwap} = S5 := by
  rw [common_tau]
  exact block_swap_closure X5

private theorem card_S5 : Nat.card S5 = 120 := by
  change Nat.card (block X5) = 120
  rw [card_block, Nat.card_Icc]
  decide

private theorem card_K : Nat.card K = 240 := by
  change Nat.card ↥(C12 ⊔ S5) = 240
  rw [card_sup_blocks C12_le le_rfl blocks_disjoint, card_S5]
  have h := card_pair (i:=1) (j:=2) (by decide)
  change Nat.card C12 = 2 at h
  rw [h]

private theorem card_L78 : Nat.card L78 = 2 := card_pair (by decide)

private theorem indices :
    L78.relIndex (mac K 1) = 120 ∧
    L78.relIndex (mac K sig) = 60 ∧
    S5.relIndex (mac K 1) = 2 ∧
    S5.relIndex (mac K tau) = 1 := by
  rw [mac_one,mac_sig,mac_tau]
  have hS : S5 ≤ K := le_sup_right
  have hL : L78 ≤ K := L78_le.trans hS
  have h₁ := Subgroup.relIndex_mul_card (H:=L78) (K:=K)
  have h₂ := Subgroup.relIndex_mul_card (H:=L78) (K:=S5)
  have h₃ := Subgroup.relIndex_mul_card (H:=S5) (K:=K)
  rw [inf_eq_left.mpr hL, card_L78, card_K] at h₁
  rw [inf_eq_left.mpr L78_le, card_L78, card_S5] at h₂
  rw [inf_eq_left.mpr hS, card_S5, card_K] at h₃
  exact ⟨by omega, by omega, by omega, Subgroup.relIndex_self _⟩

end CommonParabolicExample
namespace CommonParabolicExample
open MackeyDiagrams
open scoped BigOperators

private def par (S : Subgroup U) : Prop :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat), (∀ i, (blocks i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    S.map F.subtype = ⨆ i, blockPerm (blocks i)

private theorem range_conjugator {V : Type*} [Group V] {K G : Subgroup V} (α : V)
    (h : ∀ k : K, α * (k : V) * α⁻¹ ∈ G) :
    (ConjEmbedding.ofConjugator α h).toHom.range = (K.map (MulAut.conj α).toMonoidHom).comap G.subtype := by
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨k,k.property,rfl⟩
  · rintro ⟨k,hk,hx⟩
    exact ⟨⟨k,hk⟩,Subtype.ext hx⟩

universe u
private theorem fullRange : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U),
  let Kα := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K
  let Hβ := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj β)) H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun k => hK ⟨(k : U), k.property, rfl⟩)
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun h => hH ⟨(h : U), h.property, rfl⟩)
    let A := a.toHom.range
    let B := b.toHom.range
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let L := fun j : J =>
        Kα ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H
      let l := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹
          (by
            intro ℓ
            obtain ⟨k, hk, h⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at h
            change k ∈ K at hk
            rw [← h]
            convert hk using 1
            group)
      let r := fun j : J =>
        let s := σ j
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
          (β⁻¹ * (s : U)⁻¹)
          (by
            intro ℓ
            obtain ⟨h, hh, e⟩ := ℓ.property.2
            change (s : U) * β * h * ((s : U) * β)⁻¹ = (ℓ : U) at e
            change h ∈ H at hh
            rw [← e]
            convert hh using 1
            group)
      let d := fun j : J =>
        let s := σ j
        show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (l j))
          (MackeyDiagrams.ConjEmbedding.comp b (r j)) from
          ⟨s, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (s : U) =
              (s : U) * (β * ((β⁻¹ * (s : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (s : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
      let down := MackeyDiagrams.Word.down a
      let up := MackeyDiagrams.Word.up b
      let M := MackeyDiagrams.Word.tensor down up
      let Mj := fun j : J =>
        MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (l j)) (MackeyDiagrams.Word.down (r j))
      ∃ hf : ∀ (j : J) (z : (MackeyDiagrams.Word.basis M).carrier),
          Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b (l j) (r j) (d j) w = z},
        let inclusion : ∀ j : J, MackeyDiagrams.Diagram Complex (Mj j) M := fun j =>
          MackeyDiagrams.Diagram.mixedMultiplication a b (l j) (r j) (d j)
        let projection : ∀ j : J, MackeyDiagrams.Diagram Complex M (Mj j) := fun j =>
          MackeyDiagrams.Diagram.mixedProjection a b (l j) (r j) (d j) (hf j)
        let straight : MackeyDiagrams.Diagram Complex M M :=
          MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id down) (MackeyDiagrams.Diagram.id up)
        let crossed : J → MackeyDiagrams.Diagram Complex M M := fun j =>
          MackeyDiagrams.Diagram.vertical (projection j) (inclusion j)
        let term := fun (x : (MackeyDiagrams.Word.basis M).carrier →₀ Complex) (j : J) =>
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval (crossed j)) x
        (∃ finite : ∀ x, Set.Finite (Function.support (term x)),
          let sum : MackeyDiagrams.PointwiseIndexedDrawing Complex M M J :=
            ⟨fun j => MackeyDiagrams.LabelledDrawing.ordinary (crossed j), finite⟩
          ∀ x, MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval straight) x =
            sum.evalAt x)
) := by
  intro V inst K H G α β Kα Hβ hK hH a b A B J
  have hrA : A = Kα.comap G.subtype := range_conjugator _ _
  have hrB : B = Hβ.comap G.subtype := range_conjugator _ _
  have h := @MackeyIdentityDiagram V inst K H G α β hK hH
  rw [← hrA, ← hrB] at h
  intro σ hσ
  obtain ⟨hf, hF, _, _⟩ := h σ hσ
  exact ⟨hf, hF⟩

private theorem compactOuterEval {U : Type*} [Group U] {K H G S : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding S K)
    (r : ConjEmbedding S H) (d : Dot (a.comp l) (b.comp r))
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (LabelledDrawing.vertical (LabelledDrawing.compactProjection a b l r [(1, ⟨d, hf⟩)])
      (LabelledDrawing.mixedMultiplication a b l r [(1, d)])).interpret.eval =
    (Diagram.vertical (Diagram.mixedProjection (R := Complex) a b l r d hf)
      (Diagram.mixedMultiplication a b l r d)).eval := by
  exact congrArg₂ (fun p i => p.vertical i)
    (MackeyCrossingProof.compact_projection a b l r d hf)
    (MackeyCrossingProof.compact_inclusion a b l r d)


private theorem sum_two_indices {ι M : Type*} [AddCommMonoid M] (fi : Fintype ι)
    (e : Fin 2 ≃ ι) (f : ι → M) :
    ∑ i ∈ @Finset.univ ι fi, f i = f (e 0) + f (e 1) := by
  let := fi
  rw [← Fin.sum_univ_two (fun j => f (e j))]
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

private def univEquiv (ι : Type*) : ι ≃ {j : ι // j ∈ (Set.univ : Set ι)} where
  toFun j := ⟨j, Set.mem_univ _⟩
  invFun j := j.val
  left_inv _ := rfl
  right_inv _ := rfl

private theorem canonicalBoth : (
let parabolic := par
∀ (K H G : Subgroup U) (α β : U),
  parabolic K → parabolic H → parabolic G →
  let conjugate := fun (c : U) (S : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
  ∀ (hα : conjugate α K ≤ G) (hβ : conjugate β H ≤ G),
    let a : MackeyDiagrams.ConjEmbedding K G :=
      MackeyDiagrams.ConjEmbedding.ofConjugator α
        (fun k => hα ⟨(k : U), k.property, rfl⟩)
    let b : MackeyDiagrams.ConjEmbedding H G :=
      MackeyDiagrams.ConjEmbedding.ofConjugator β
        (fun h => hβ ⟨(h : U), h.property, rfl⟩)
    let A := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
    let B := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b)
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j) (E : Fin 2 ≃ J),
      let Lj := fun j : J => conjugate α K ⊓ conjugate ((σ j : U) * β) H
      let left := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := K) α⁻¹ (by
          intro ℓ
          obtain ⟨k, hk, heq⟩ := (hS ℓ.property).1
          change α * k * α⁻¹ = (ℓ : U) at heq
          rw [← heq]
          change k ∈ K at hk
          convert hk using 1
          group)
      let right := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := S) (G := H)
          (β⁻¹ * (σ j : U)⁻¹) (by
            intro ℓ
            obtain ⟨h, hh, heq⟩ := (hS ℓ.property).2
            change (σ j : U) * β * h * ((σ j : U) * β)⁻¹ = (ℓ : U) at heq
            rw [← heq]
            change h ∈ H at hh
            convert hh using 1
            group)
      let dot := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        show MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a (left j S hS))
          (MackeyDiagrams.ConjEmbedding.comp b (right j S hS)) from
          ⟨σ j, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (σ j : U) =
              (σ j : U) * (β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
      let M := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.down a)
        (MackeyDiagrams.Word.up b)
      let finiteFibers := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j) =>
        ∀ z : (MackeyDiagrams.Word.basis M).carrier,
          Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a b
            (left j S hS) (right j S hS) (dot j S hS) w = z}
      let outer := fun (j : J) (S : Subgroup U) (hS : S ≤ Lj j)
          (hf : finiteFibers j S hS) =>
        show MackeyDiagrams.LabelledDrawing Complex M M from
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.compactProjection a b (left j S hS) (right j S hS)
              [(1, ⟨dot j S hS, hf⟩)])
            (MackeyDiagrams.LabelledDrawing.mixedMultiplication a b (left j S hS) (right j S hS)
              [(1, dot j S hS)])
      let J₀ : Set J := Set.univ
        let I := {j : J // j ∈ J₀}
        let j₀ : I := ⟨E 0, Set.mem_univ _⟩
          let C := G ⊓ Subgroup.centralizer
            (Set.range (fun j : I => (σ j₀.val : U) * (σ j.val : U)⁻¹))
          let P := (iInf (fun j : I => Lj j.val)) ⊓ C
          let L := Subgroup.closure {g : U | g ∈ P ∧ Equiv.Perm.IsSwap (Subtype.val g)}
          let hL : ∀ j : I, L ≤ Lj j.val := fun j =>
            le_trans ((Subgroup.closure_le P).mpr (fun _ hg => hg.1))
              (le_trans inf_le_left (iInf_le (fun i : I => Lj i.val) j))
          let admissible := fun S : Subgroup U =>
            parabolic S ∧
              ∃ hS : ∀ j : I, S ≤ Lj j.val,
                ∀ i j : I,
                  left i.val S (hS i) = left j.val S (hS j) ∧
                  right i.val S (hS i) = right j.val S (hS j)
          IsGreatest {S : Subgroup U | admissible S} L ∧
          ∃ (hf₀ : finiteFibers (E 0) L (hL (univEquiv J (E 0))))
              (hf₁ : finiteFibers (E 1) L (hL (univEquiv J (E 1)))),
            let straight := LabelledDrawing.horizontal
              (.ordinary (Diagram.id (R := Complex) (Word.down a)))
              (.ordinary (Diagram.id (Word.up b)))
            straight.interpret.eval =
              (LabelledDrawing.add
                (.scale ((L.relIndex (Lj (E 0)) : Complex)⁻¹)
                  (outer (E 0) L (hL (univEquiv J (E 0))) hf₀))
                (.scale ((L.relIndex (Lj (E 1)) : Complex)⁻¹)
                  (outer (E 1) L (hL (univEquiv J (E 1))) hf₁))).interpret.eval
) := by
  classical
  intro parabolic K H G α β hK hH hG conjugate hα hβ a b A B J σ hσ E
    Lj left right dot M finiteFibers outer J₀ I j₀ C P L hL admissible
  obtain ⟨hGreatest, _, fi, hfL, hfJ, hnorm⟩ :=
    LargestCommonMixedCrossingParabolic K H G α β hK hH hG hα hβ σ hσ J₀ j₀
  obtain ⟨hFullFibers, hsupp, hfull⟩ := fullRange K H G α β hα hβ σ hσ
  let EI : Fin 2 ≃ I := E.trans (univEquiv J)
  let fj : Fintype J := Fintype.ofEquiv (Fin 2) E
  refine ⟨hGreatest, hfL (EI 0), hfL (EI 1), ?_⟩
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  have hnormx := congrArg (fun f : (M.basis.carrier →₀ Complex) →ₗ[Complex]
    (M.basis.carrier →₀ Complex) => f x) hnorm
  simp only [IndexedDrawing.eval_apply, sum_two_indices fi EI] at hnormx
  have hfullx := hfull x
  rw [PointwiseIndexedDrawing.evalAt_def] at hfullx
  have hlift :
      (∑ j ∈ (hsupp x).toFinset,
        (Diagram.vertical (R := Complex) (Diagram.mixedProjection a b (left j (Lj j) le_rfl)
          (right j (Lj j) le_rfl) (dot j (Lj j) le_rfl) (hFullFibers j))
          (Diagram.mixedMultiplication a b (left j (Lj j) le_rfl)
            (right j (Lj j) le_rfl) (dot j (Lj j) le_rfl))).eval.toLinearMap x)
      = ∑ j ∈ @Finset.univ J fj,
        (outer j (Lj j) le_rfl (hfJ (univEquiv J j))).interpret.eval.toLinearMap x := by
    calc
      _ = ∑ j ∈ @Finset.univ J fj,
        (Diagram.vertical (R := Complex) (Diagram.mixedProjection a b (left j (Lj j) le_rfl)
          (right j (Lj j) le_rfl) (dot j (Lj j) le_rfl) (hFullFibers j))
          (Diagram.mixedMultiplication a b (left j (Lj j) le_rfl)
            (right j (Lj j) le_rfl) (dot j (Lj j) le_rfl))).eval.toLinearMap x := by
          refine Finset.sum_subset (fun j _ => @Finset.mem_univ J fj j) ?_
          intro j _ hj
          exact not_ne_iff.mp (fun hn => hj (Set.Finite.mem_toFinset.mpr hn))
      _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [compactOuterEval]
  rw [sum_two_indices fj E] at hlift
  have hx := hfullx.trans (hlift.trans hnormx.symm)
  exact hx

end CommonParabolicExample
namespace CommonParabolicExample
open MackeyDiagrams

private theorem par_block (X : Finset Nat) (hX : X.Nonempty) : par (block X) := by
  refine ⟨1, fun _ => X, fun _ => hX, ?_, ?_⟩
  · intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  · rw [parabolic_map_block, iSup_unique]

private def twoValues {T : Type*} (a b : T) (i : Fin 2) : T := if i = 0 then a else b
@[simp] private theorem twoValues_zero {T : Type*} (a b : T) : twoValues a b 0 = a := ite_eq_left rfl
@[simp] private theorem twoValues_one {T : Type*} (a b : T) : twoValues a b 1 = b := ite_eq_right (by decide)

private noncomputable def twoEquiv {T : Type*} (a b : T) (hne : a ≠ b) (hall : ∀ x, x = a ∨ x = b) :
    Fin 2 ≃ T :=
  Equiv.ofBijective (twoValues a b) (by
    constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · intro x
      rcases hall x with rfl | rfl
      · exact ⟨0, twoValues_zero _ _⟩
      · exact ⟨1, twoValues_one _ _⟩)

private theorem par_two {X Y : Finset Nat} (hX : X.Nonempty) (hY : Y.Nonempty) (hd : Disjoint X Y) :
    par (block X ⊔ block Y) := by
  refine ⟨2, twoValues X Y, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simpa
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Disjoint.symm hd]
  · rw [Subgroup.map_sup, parabolic_map_block, parabolic_map_block]
    apply le_antisymm
    · exact sup_le (by simpa only [twoValues_zero] using
          (le_iSup (fun i => blockPerm (twoValues X Y i)) 0))
        (by simpa only [twoValues_one] using (le_iSup (fun i => blockPerm (twoValues X Y i)) 1))
    · apply iSup_le
      intro i
      fin_cases i
      · change blockPerm X ≤ blockPerm X ⊔ blockPerm Y
        exact le_sup_left
      · change blockPerm Y ≤ blockPerm X ⊔ blockPerm Y
        exact le_sup_right

private theorem par_K : par K := by
  change par (Subgroup.zpowers (sw 1 2) ⊔ block X5)
  rw [← pair_cyclic (by decide)]
  apply par_two (by decide) (by decide)
  exact Finset.disjoint_left.mpr (by
    intro x hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    exact (by rcases hx with rfl | rfl <;> decide : x ∉ X5) hy)

private theorem par_G : par G := par_two (by decide) (by decide) blocks_disjoint

private def mkLeft {V : Type} [Group V] (K : Subgroup V) (s : V) (L : Subgroup V) (h : L ≤ mac K s) :=
  mkIncl L K (h.trans inf_le_left)

private def mkRight {V : Type} [Group V] (K : Subgroup V) (s : V) (L : Subgroup V) (h : L ≤ mac K s) :=
  ConjEmbedding.ofConjugator (H := L) (G := K) s⁻¹ (by
    intro x
    obtain ⟨k,hk,e⟩ := (h x.property).2
    change s * k * s⁻¹ = (x : V) at e
    rw [← e]
    change k ∈ K at hk
    convert hk using 1
    group)

private def mkDot {V : Type} [Group V] {K G L : Subgroup V} (hKG : K ≤ G) (s : G)
    (h : L ≤ mac K (s : V)) :
    Dot ((mkIncl K G hKG).comp (mkLeft K s L h)) ((mkIncl K G hKG).comp (mkRight K s L h)) :=
  ⟨s, by
    intro x
    apply Subtype.ext
    change (x : V) * (s : V) = (s : V) * ((s : V)⁻¹ * (x : V) * ((s : V)⁻¹)⁻¹)
    group⟩

private def binaryRow {V : Type} [Group V] {K H G L : Subgroup V}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l₀ l₁ : ConjEmbedding L K) (r₀ r₁ : ConjEmbedding L H)
    (d₀ : Dot (a.comp l₀) (b.comp r₀)) (d₁ : Dot (a.comp l₁) (b.comp r₁))
    (c₀ : Complex) (c₁ : Option Complex) : Prop :=
  ∃ (hf₀ : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l₀ r₀ d₀ w = z})
      (hf₁ : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l₁ r₁ d₁ w = z}),
    let M := (Word.down a).tensor (Word.up b)
    let straight : LabelledDrawing Complex M M :=
      .horizontal (.ordinary (Diagram.id _)) (.ordinary (Diagram.id _))
    let T₀ : LabelledDrawing Complex M M := .vertical
      (.compactProjection a b l₀ r₀ [(1, ⟨d₀,hf₀⟩)])
      (.mixedMultiplication a b l₀ r₀ [(1,d₀)])
    let T₁ : LabelledDrawing Complex M M := .vertical
      (.compactProjection a b l₁ r₁ [(1, ⟨d₁,hf₁⟩)])
      (.mixedMultiplication a b l₁ r₁ [(1,d₁)])
    straight.interpret.eval =
      (LabelledDrawing.add (.scale c₀ T₀) (Option.elim c₁ T₁ (fun c => .scale c T₁))).interpret.eval

private theorem unscaleOne {V : Type} [Group V] {K H G L : Subgroup V}
    {a : ConjEmbedding K G} {b : ConjEmbedding H G}
    {l₀ l₁ : ConjEmbedding L K} {r₀ r₁ : ConjEmbedding L H}
    {d₀ : Dot (a.comp l₀) (b.comp r₀)} {d₁ : Dot (a.comp l₁) (b.comp r₁)} {c : Complex}
    (h : binaryRow a b l₀ l₁ r₀ r₁ d₀ d₁ c (some 1)) :
    binaryRow a b l₀ l₁ r₀ r₁ d₀ d₁ c none := by
  obtain ⟨f₀,f₁,h⟩ := h
  refine ⟨f₀,f₁,h.trans ?_⟩
  apply Biset.Hom.ext
  change _ + (1 : Complex) • _ = _ + _
  rw [one_smul]
  rfl

private theorem transferRow {V : Type} [Group V] {K H G L : Subgroup V}
    {a a' : ConjEmbedding K G} {b b' : ConjEmbedding H G}
    {l₀ l₁ l₀' l₁' : ConjEmbedding L K} {r₀ r₁ r₀' r₁' : ConjEmbedding L H}
    {d₀ : Dot (a.comp l₀) (b.comp r₀)} {d₁ : Dot (a.comp l₁) (b.comp r₁)}
    {d₀' : Dot (a'.comp l₀') (b'.comp r₀')} {d₁' : Dot (a'.comp l₁') (b'.comp r₁')}
    {c₀ : Complex} {c₁ : Option Complex}
    (ha : a = a') (hb : b = b') (hl₀ : l₀ = l₀') (hl₁ : l₁ = l₁') (hr₀ : r₀ = r₀') (hr₁ : r₁ = r₁')
    (hd₀ : d₀.element = d₀'.element) (hd₁ : d₁.element = d₁'.element)
    (h : binaryRow a b l₀ l₁ r₀ r₁ d₀ d₁ c₀ c₁) :
    binaryRow a' b' l₀' l₁' r₀' r₁' d₀' d₁' c₀ c₁ := by
  cases ha
  cases hb
  cases hl₀
  cases hl₁
  cases hr₀
  cases hr₁
  cases Dot.ext hd₀
  cases Dot.ext hd₁
  exact h

private def admissible (s : U) (S : Subgroup U) : Prop :=
  par S ∧ ∃ (h₁ : S ≤ mac K 1) (h₂ : S ≤ mac K s),
    mkLeft K 1 S h₁ = mkLeft K s S h₂ ∧ mkRight K 1 S h₁ = mkRight K s S h₂

private def exampleRow (s : G) (L : Subgroup U) (c₀ : Complex) (c₁ : Option Complex) : Prop :=
  ∃ (h₀ : L ≤ mac K 1) (h₁ : L ≤ mac K (s : U)),
    let a := mkIncl K G K_le_G
    binaryRow a a (mkLeft K 1 L h₀) (mkLeft K s L h₁) (mkRight K 1 L h₀) (mkRight K s L h₁)
      (mkDot K_le_G (1 : G) h₀) (mkDot K_le_G s h₁) c₀ c₁

private abbrev macCanon (s : G) :=
  K.map (conjMap (1 : U)) ⊓ K.map (conjMap ((s : U) * 1))

private theorem macCanon_eq (s : G) : macCanon s = mac K (s : U) := by
  change K.map (conjMap (1 : U)) ⊓ K.map (conjMap ((s : U) * 1)) = _
  rw [mul_one, conjMap_one, Subgroup.map_id]

private def canonLeft (s : G) (S : Subgroup U) (h : S ≤ macCanon s) : ConjEmbedding S K :=
  ConjEmbedding.ofConjugator (1 : U)⁻¹ (by
    intro ℓ
    obtain ⟨k, hk, heq⟩ := (h ℓ.property).1
    change (1 : U) * k * (1 : U)⁻¹ = (ℓ : U) at heq
    rw [← heq]
    change k ∈ K at hk
    convert hk using 1
    group)

private def canonRight (s : G) (S : Subgroup U) (h : S ≤ macCanon s) : ConjEmbedding S K :=
  ConjEmbedding.ofConjugator ((1 : U)⁻¹ * (s : U)⁻¹) (by
    intro ℓ
    obtain ⟨k, hk, heq⟩ := (h ℓ.property).2
    change ((s : U) * 1) * k * ((s : U) * 1)⁻¹ = (ℓ : U) at heq
    rw [← heq]
    change k ∈ K at hk
    convert hk using 1
    group)

private theorem left_align (s : G) (S : Subgroup U) (h : S ≤ macCanon s) (h' : S ≤ mac K (s : U)) :
    canonLeft s S h = mkLeft K s S h' := by
  apply ConjEmbedding.ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change (1 : U)⁻¹ * (x : U) * ((1 : U)⁻¹)⁻¹ = (x : U)
  simp

private theorem right_align (s : G) (S : Subgroup U) (h : S ≤ macCanon s) (h' : S ≤ mac K (s : U)) :
    canonRight s S h = mkRight K s S h' := by
  apply ConjEmbedding.ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change ((1 : U)⁻¹ * (s : U)⁻¹) * (x : U) * ((1 : U)⁻¹ * (s : U)⁻¹)⁻¹ =
    (s : U)⁻¹ * (x : U) * ((s : U)⁻¹)⁻¹
  simp

private theorem macCanonLe {s : G} {S : Subgroup U} (h : S ≤ macCanon s) : S ≤ mac K (s : U) :=
  macCanon_eq s ▸ h

private theorem macCanonLe' {s : G} {S : Subgroup U} (h : S ≤ mac K (s : U)) : S ≤ macCanon s :=
  (macCanon_eq s).symm ▸ h

private theorem right_congr_rep {s t : G} (he : s = t) (S : Subgroup U)
    (h : S ≤ mac K (s : U)) (h' : S ≤ mac K (t : U)) :
    mkRight K (s : U) S h = mkRight K (t : U) S h' := by
  subst t
  rfl

private theorem labelled_admissible {I : Type} (representatives : I → G) (i₀ i₁ : I)
    (h₀ : representatives i₀ = 1) (h₁ : ∀ i, representatives i = 1 ∨ representatives i = representatives i₁)
    (S : Subgroup U) :
    (par S ∧ ∃ hS : ∀ i, S ≤ macCanon (representatives i), ∀ i j,
      canonLeft (representatives i) S (hS i) = canonLeft (representatives j) S (hS j) ∧
      canonRight (representatives i) S (hS i) = canonRight (representatives j) S (hS j))
      ↔ admissible (representatives i₁) S := by
  have h₀' : (representatives i₀ : U) = 1 := congrArg (fun z : G => z.val) h₀
  have hf₀ (h : S ≤ macCanon (representatives i₀)) : S ≤ mac K 1 :=
    h₀' ▸ macCanonLe h
  constructor
  · rintro ⟨hp,h,he⟩
    refine ⟨hp,hf₀ (h i₀),macCanonLe (h i₁),rfl,?_⟩
    have he' := (right_align (representatives i₀) S (h i₀) (macCanonLe (h i₀))).symm.trans
      ((he i₀ i₁).2.trans (right_align _ _ _ _))
    exact (right_congr_rep h₀ S _ _).symm.trans he' 
  · rintro ⟨hp,hL₀,hL₁,_,hr⟩
    have hmac (i : I) : S ≤ mac K (representatives i : U) := by
      rcases h₁ i with hi | hi
      · exact (congrArg (fun z : G => z.val) hi).symm ▸ hL₀
      · exact (congrArg (fun z : G => z.val) hi).symm ▸ hL₁
    refine ⟨hp, fun i => macCanonLe' (hmac i), fun i j => ⟨?_,?_⟩⟩
    · exact (left_align _ _ _ _).trans (left_align _ _ _ _).symm
    · have hr' (i : I) : canonRight (representatives i) S (macCanonLe' (hmac i)) = mkRight K 1 S hL₀ := by
        rw [right_align _ _ _ (hmac i)]
        rcases h₁ i with hi | hi
        · exact right_congr_rep hi S _ _
        · exact (right_congr_rep hi S _ _).trans hr.symm
      exact (hr' i).trans (hr' j).symm

end CommonParabolicExample
namespace CommonParabolicExample
open MackeyDiagrams

private theorem canon_K_le : K.map (conjMap (1 : U)) ≤ G := by
  rw [conjMap_one, Subgroup.map_id]
  exact K_le_G

private def canonIncl : ConjEmbedding K G :=
  ConjEmbedding.ofConjugator (1 : U)
    (fun k => canon_K_le ⟨(k : U), k.property, rfl⟩)

private theorem incl_align : canonIncl = mkIncl K G K_le_G := by
  apply ConjEmbedding.ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change 1 * (x : U) * (1 : U)⁻¹ = (x : U)
  simp

private def canonDot (s : G) (S : Subgroup U) (h : S ≤ macCanon s) :
    Dot (canonIncl.comp (canonLeft s S h)) (canonIncl.comp (canonRight s S h)) :=
  ⟨s, by
    intro x
    apply Subtype.ext
    change (1 : U) * ((1 : U)⁻¹ * (x : U) * ((1 : U)⁻¹)⁻¹) * (1 : U)⁻¹ * (s : U) =
      (s : U) * ((1 : U) * (((1 : U)⁻¹ * (s : U)⁻¹) * (x : U) *
        ((1 : U)⁻¹ * (s : U)⁻¹)⁻¹) * (1 : U)⁻¹)
    simp only [inv_one, one_mul, mul_one, inv_inv]
    group⟩

private theorem case_geometry {I : Type} (rep : I → G) (i₀ i₁ : I)
    (h₀ : rep i₀ = 1) (hall : ∀ i, rep i = 1 ∨ rep i = rep i₁) :
    (iInf (fun i => macCanon (rep i))) ⊓
      (G ⊓ Subgroup.centralizer (Set.range (fun i => (rep i₀ : U) * (rep i : U)⁻¹))) =
        common K G (rep i₁ : U) := by
  have hI : iInf (fun i => macCanon (rep i)) = mac K 1 ⊓ mac K (rep i₁ : U) := by
    apply le_antisymm
    · apply le_inf
      · have h := iInf_le (fun i => macCanon (rep i)) i₀
        rw [macCanon_eq, h₀] at h
        exact h
      · have h := iInf_le (fun i => macCanon (rep i)) i₁
        rw [macCanon_eq] at h
        exact h
    · apply le_iInf
      intro i
      rw [macCanon_eq]
      rcases hall i with hi | hi
      · rw [hi]
        exact inf_le_left
      · rw [hi]
        exact inf_le_right
  have hC : Subgroup.centralizer (Set.range (fun i => (rep i₀ : U) * (rep i : U)⁻¹)) =
      Subgroup.centralizer ({(1 : U) * (rep i₁ : U)⁻¹} : Set U) := by
    ext x
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro hx s hs
      rw [Set.mem_singleton_iff] at hs
      exact hx s ⟨i₁, by rw [h₀, hs]; rfl⟩
    · rintro hx _ ⟨i,rfl⟩
      change (rep i₀ : U) * (rep i : U)⁻¹ * x = x * ((rep i₀ : U) * (rep i : U)⁻¹)
      rcases hall i with hi | hi
      · rw [h₀, hi]
        change (1 : U) * 1⁻¹ * x = x * (1 * 1⁻¹)
        simp
      · rw [h₀,hi]
        exact hx _ (Set.mem_singleton _)
  rw [hI,hC]
  rfl

private theorem canonical_to_reviewed {t₀ t₁ s : G} (e₀ : t₀ = 1) (e₁ : t₁ = s)
    {L : Subgroup U} (h₀ : L ≤ macCanon t₀) (h₁ : L ≤ macCanon t₁)
    {c₀ : Complex} {c₁ : Option Complex}
    (h : binaryRow canonIncl canonIncl
      (canonLeft t₀ L h₀) (canonLeft t₁ L h₁) (canonRight t₀ L h₀) (canonRight t₁ L h₁)
      (canonDot t₀ L h₀) (canonDot t₁ L h₁) c₀ c₁) :
    exampleRow s L c₀ c₁ := by
  subst t₀
  subst t₁
  let hL₀ := macCanonLe h₀
  let hL₁ := macCanonLe h₁
  refine ⟨hL₀, hL₁, ?_⟩
  have hr₀ := right_align (1 : G) L h₀ hL₀
  have hr₁ := right_align s L h₁ hL₁
  exact transferRow incl_align incl_align (left_align 1 L h₀ hL₀) (left_align s L h₁ hL₁)
    hr₀ hr₁ rfl rfl h

private theorem exampleCase (s : G) (L : Subgroup U) (n₀ n₁ : Nat)
    (hne : DoubleCoset.mk canonIncl.toHom.range canonIncl.toHom.range (1 : G) ≠
      DoubleCoset.mk canonIncl.toHom.range canonIncl.toHom.range s)
    (hall : ∀ j, j = DoubleCoset.mk canonIncl.toHom.range canonIncl.toHom.range (1 : G) ∨
      j = DoubleCoset.mk canonIncl.toHom.range canonIncl.toHom.range s)
    (hS : Subgroup.closure {x : U | x ∈ common K G (s : U) ∧ (x : Equiv.Perm Nat).IsSwap} = L)
    (hn₀ : L.relIndex (mac K 1) = n₀) (hn₁ : L.relIndex (mac K (s : U)) = n₁) :
    IsGreatest {S : Subgroup U | admissible s S} L ∧
      exampleRow s L ((n₀ : Complex)⁻¹) (some ((n₁ : Complex)⁻¹)) := by
  classical
  let A := canonIncl.toHom.range
  let q := DoubleCoset.mk A A
  let J := DoubleCoset.Quotient (A : Set G) (A : Set G)
  let E : Fin 2 ≃ J := twoEquiv (q 1) (q s) hne hall
  let rep : J → G := fun j => twoValues 1 s (E.symm j)
  have rep_section (j : J) : q (rep j) = j := by
    obtain ⟨i,rfl⟩ := E.surjective j
    change q (twoValues 1 s (E.symm (E i))) = E i
    rw [E.symm_apply_apply]
    fin_cases i <;> rfl
  let I := {j : J // j ∈ (Set.univ : Set J)}
  let EI : Fin 2 ≃ I := E.trans (univEquiv J)
  let refs : I → G := fun i => rep i.val
  have rep₀ : rep (E 0) = 1 := by simp [rep]
  have rep₁ : rep (E 1) = s := by simp [rep]
  have h₀ : refs (EI 0) = 1 := rep₀
  have h₁ : refs (EI 1) = s := rep₁
  have hreps (i : I) : refs i = 1 ∨ refs i = refs (EI 1) := by
    obtain ⟨j,rfl⟩ := EI.surjective i
    fin_cases j
    · exact Or.inl h₀
    · exact Or.inr rfl
  let P := iInf (fun i => macCanon (refs i)) ⊓
    (G ⊓ Subgroup.centralizer (Set.range (fun i => (refs (EI 0) : U) * (refs i : U)⁻¹)))
  let L' := Subgroup.closure {g : U | g ∈ P ∧ (g : Equiv.Perm Nat).IsSwap}
  have hP : P = common K G (s : U) := by
    exact (case_geometry refs (EI 0) (EI 1) h₀ hreps).trans
      (congrArg (fun z : G => common K G (z : U)) h₁)
  have hL : L' = L := by
    change Subgroup.closure {g : U | g ∈ P ∧ _} = L
    rw [hP]
    exact hS
  obtain ⟨hGreat, hf₀, hf₁, eval⟩ :=
    canonicalBoth K K G 1 1 par_K par_K par_G canon_K_le canon_K_le rep rep_section E
  have hPred (T : Subgroup U) :
      (par T ∧ ∃ hT : ∀ i, T ≤ macCanon (refs i), ∀ i j,
        canonLeft (refs i) T (hT i) = canonLeft (refs j) T (hT j) ∧
        canonRight (refs i) T (hT i) = canonRight (refs j) T (hT j)) ↔ admissible s T := by
    rw [← h₁]
    exact labelled_admissible refs (EI 0) (EI 1) h₀ hreps T
  have hGreat' : IsGreatest {S : Subgroup U | admissible s S} L' := by
    exact ⟨(hPred _).mp hGreat.1, fun _ hT => hGreat.2 ((hPred _).mpr hT)⟩
  have hsmall (i : I) : L' ≤ macCanon (refs i) :=
    le_trans ((Subgroup.closure_le P).mpr (fun _ hg => hg.1))
      (le_trans inf_le_left (iInf_le (fun i : I => macCanon (refs i)) i))
  have hindex₀ : L'.relIndex (macCanon (refs (EI 0))) = n₀ := by
    rw [macCanon_eq, h₀, hL]
    exact hn₀
  have hindex₁ : L'.relIndex (macCanon (refs (EI 1))) = n₁ := by
    rw [macCanon_eq, h₁, hL]
    exact hn₁
  have hrow :
      binaryRow canonIncl canonIncl
        (canonLeft (refs (EI 0)) L' (hsmall (EI 0))) (canonLeft (refs (EI 1)) L' (hsmall (EI 1)))
        (canonRight (refs (EI 0)) L' (hsmall (EI 0))) (canonRight (refs (EI 1)) L' (hsmall (EI 1)))
        (canonDot (refs (EI 0)) L' (hsmall (EI 0))) (canonDot (refs (EI 1)) L' (hsmall (EI 1)))
        (↑(L'.relIndex (macCanon (refs (EI 0)))) : Complex)⁻¹
        (some (↑(L'.relIndex (macCanon (refs (EI 1)))) : Complex)⁻¹) := by
    exact ⟨hf₀, hf₁, eval⟩
  rw [hindex₀,hindex₁] at hrow
  exact ⟨hL ▸ hGreat', hL ▸ canonical_to_reviewed h₀ h₁ _ _ hrow⟩

private theorem exampleRow_unscale {s : G} {L : Subgroup U} {c : Complex}
    (h : exampleRow s L c (some 1)) : exampleRow s L c none := by
  obtain ⟨h₀,h₁,h⟩ := h
  exact ⟨h₀,h₁,unscaleOne h⟩

end CommonParabolicExample
