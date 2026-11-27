import MackeyDiagrams
import Proofs.LargestCommonMixedCrossingParabolic
import Proofs.MackeyIdentityDiagram

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

-- Split the first block by the image of 3. The second block is absorbed
-- by K on the right, so the two sections have the same two classes.
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

-- Test the action on the ambient Nat permutation pointwise. This proves
-- invariance of {4,5,6} by injectivity and commutation, with no finite
-- universe hypothesis on Nat. The images of 4 and 7 determine the factors.
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

end CommonParabolicExample
