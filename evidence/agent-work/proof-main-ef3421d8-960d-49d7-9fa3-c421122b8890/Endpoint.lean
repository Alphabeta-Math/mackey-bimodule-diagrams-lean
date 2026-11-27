import MackeyDiagrams
import Proofs.ParabolicCurlsFromBlockRefinements

set_option maxHeartbeats 2000000

namespace CurlJoinIntersectionProof

open MackeyDiagrams
open scoped Pointwise

private abbrev finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev U := ↥finitary
private abbrev ambientBlock (S : Finset Nat) : Subgroup (Equiv.Perm Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S))
private abbrev blockSym (S : Finset Nat) : Subgroup U :=
  Subgroup.comap finitary.subtype (ambientBlock S)
private abbrev blockGroup (P : Finset (Finset Nat)) : Subgroup U :=
  ⨆ S : ↥P, blockSym (S : Finset Nat)
private abbrev partition (T : Finset Nat) (P : Finset (Finset Nat)) : Prop :=
  (∀ S ∈ P, S.Nonempty) ∧
    (∀ S ∈ P, ∀ V ∈ P, S ≠ V → Disjoint S V) ∧
    (∀ x : Nat, x ∈ T ↔ ∃ S ∈ P, x ∈ S)

private theorem uniqueBlock {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    {x : Nat} {S V : Finset Nat} (hS : S ∈ P) (hV : V ∈ P) (hxS : x ∈ S) (hxV : x ∈ V) :
    S = V := by
  by_contra hn
  exact Finset.disjoint_left.mp (h.2.1 S hS V hV hn) hxS hxV

private theorem perm_mem_iff {S : Set Nat} (σ : Equiv.Perm Nat)
    (h : ∀ x ∈ S, σ x ∈ S) (hi : ∀ x ∈ S, σ⁻¹ x ∈ S) (x : Nat) :
    σ x ∈ S ↔ x ∈ S := by
  refine ⟨fun hx => ?_, h x⟩
  simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hi (σ x) hx

private theorem action_of_mem {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    {σ : U} (hσ : σ ∈ blockGroup P) :
    (∀ S ∈ P, ∀ x ∈ S, (σ : Equiv.Perm Nat) x ∈ S) ∧
      (∀ x ∉ T, (σ : Equiv.Perm Nat) x = x) := by
  refine Subgroup.iSup_induction (fun S : ↥P => blockSym (S : Finset Nat))
    (C := fun f : U =>
      (∀ S ∈ P, ∀ x ∈ S, (f : Equiv.Perm Nat) x ∈ S) ∧
      (∀ x ∉ T, (f : Equiv.Perm Nat) x = x)) hσ ?_ ?_ ?_
  · intro S f hf
    obtain ⟨τ, hτ⟩ := (show (f : Equiv.Perm Nat) ∈ ambientBlock S from hf)
    rw [← hτ]
    constructor
    · intro V hV x hx
      by_cases he : V = S.val
      · subst V
        exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem τ x).2 hx
      · rwa [Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun hs =>
          he (uniqueBlock h hV S.property hx hs))]
    · intro x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem τ
        (fun hs => hx ((h.2.2 x).2 ⟨S, S.property, hs⟩))
  · exact ⟨fun _ _ _ hx => hx, fun _ _ => rfl⟩
  · exact fun f g hf hg =>
      ⟨fun S hS x hx => hf.1 S hS _ (hg.1 S hS x hx),
        fun x hx => show (f : Equiv.Perm Nat) ((g : Equiv.Perm Nat) x) = x by
          rw [hg.2 x hx, hf.2 x hx]⟩

private theorem action_iff {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    {σ : U} (hσ : σ ∈ blockGroup P) {S : Finset Nat} (hS : S ∈ P) (x : Nat) :
    (σ : Equiv.Perm Nat) x ∈ S ↔ x ∈ S :=
  perm_mem_iff (σ : Equiv.Perm Nat) ((action_of_mem h hσ).1 S hS)
    ((action_of_mem h ((blockGroup P).inv_mem hσ)).1 S hS) x

private theorem mem_ambientSwap {S : Finset Nat} {x y : Nat} (hx : x ∈ S) (hy : y ∈ S) :
    Equiv.swap x y ∈ ambientBlock S :=
  ⟨Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

private theorem ambientBlock_le_finitary (S : Finset Nat) : ambientBlock S ≤ finitary := by
  rintro σ ⟨τ, rfl⟩
  apply mem_closure_isSwap'.mpr
  exact S.finite_toSet.subset (fun x hx => by
    by_contra h
    exact hx ((MulAction.mem_fixedBy).2 (Equiv.Perm.ofSubtype_apply_of_not_mem τ h)))

private theorem map_blockGroup (P : Finset (Finset Nat)) :
    (blockGroup P).map finitary.subtype = ⨆ S : ↥P, ambientBlock (S : Finset Nat) := by
  rw [show blockGroup P = ⨆ S : ↥P, blockSym (S : Finset Nat) from rfl, Subgroup.map_iSup]
  congr 1
  funext S
  apply Subgroup.map_comap_eq_self
  rw [Subgroup.range_subtype]
  exact ambientBlock_le_finitary S

-- Alphabeta Math, transpositions generate the symmetric group, Steps 1.1,
-- 2.1 and 3.1 (https://alphabetamath.cc/item/thm-transpositions-generate-the-symmetric-group).
-- The numbered proof expands finite cycles into transpositions and passes
-- to the generated subgroup. For permutations of Nat, apply the checked
-- finite-support swap-closure criterion to the set of genuine internal
-- swaps. The carrier bounds the moved points. Each moved point and its
-- image lie in the same block, so their swap gives the orbit witness.
private theorem ambient_mem_of_action {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P)
    {σ : Equiv.Perm Nat}
    (preserve : ∀ S ∈ P, ∀ x ∈ S, σ x ∈ S)
    (fixes : ∀ x ∉ T, σ x = x) : σ ∈ (blockGroup P).map finitary.subtype := by
  rw [map_blockGroup]
  let swaps : Set (Equiv.Perm Nat) :=
    {f | ∃ S ∈ P, ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f = Equiv.swap x y}
  have genuine : ∀ f ∈ swaps, Equiv.Perm.IsSwap f := by
    rintro f ⟨S, hS, x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, y, hxy, rfl⟩
  have hle : Subgroup.closure swaps ≤ ⨆ S : ↥P, ambientBlock (S : Finset Nat) := by
    apply (Subgroup.closure_le _).2
    rintro f ⟨S, hS, x, hx, y, hy, hxy, rfl⟩
    exact Subgroup.mem_iSup_of_mem (⟨S, hS⟩ : ↥P) (mem_ambientSwap hx hy)
  apply hle
  refine (mem_closure_isSwap genuine).2 ⟨T.finite_toSet.subset ?_, ?_⟩
  · intro x hx
    by_contra ht
    exact hx ((MulAction.mem_fixedBy).2 (fixes x ht))
  · intro x
    by_cases hx : σ x = x
    · rw [hx]
      exact MulAction.mem_orbit_self x
    · have ht : x ∈ T := by
        by_contra hn
        exact hx (fixes x hn)
      obtain ⟨S, hS, hs⟩ := (h.2.2 x).1 ht
      have hswap : Equiv.swap x (σ x) ∈ Subgroup.closure swaps :=
        Subgroup.subset_closure ⟨S, hS, x, hs, σ x, preserve S hS x hs, Ne.symm hx, rfl⟩
      exact MulAction.mem_orbit_iff.mpr ⟨⟨_, hswap⟩, Equiv.swap_apply_left _ _⟩

private theorem blockGroup_finite {T : Finset Nat} {P : Finset (Finset Nat)} (h : partition T P) :
    Finite ↥(blockGroup P) := by
  have carrier (σ : blockGroup P) (x : Nat) : (σ.val : Equiv.Perm Nat) x ∈ T ↔ x ∈ T := by
    rw [h.2.2, h.2.2]
    exact exists_congr fun S => and_congr_right fun hS => action_iff h σ.property hS x
  let restrict (σ : blockGroup P) : Equiv.Perm ↥T :=
    (σ.val : Equiv.Perm Nat).subtypePerm (carrier σ)
  refine Finite.of_injective restrict ?_
  intro σ τ he
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ T
  · exact congrArg (fun p : Equiv.Perm ↥T => (p ⟨x, hx⟩).val) he
  · rw [(action_of_mem h σ.property).2 x hx, (action_of_mem h τ.property).2 x hx]

private abbrev ambientFamily {ι : Type} (F : ι → Finset Nat) : Subgroup (Equiv.Perm Nat) :=
  ⨆ i, ambientBlock (F i)

private theorem ambient_image {ι : Type} [Fintype ι] (F : ι → Finset Nat) :
    (blockGroup (Finset.univ.image F)).map finitary.subtype = ambientFamily F := by
  rw [map_blockGroup]
  apply le_antisymm
  · refine iSup_le fun S => ?_
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp S.property
    exact hi ▸ le_iSup (fun i => ambientBlock (F i)) i
  · exact iSup_le fun i => le_iSup (fun S : ↥(Finset.univ.image F) => ambientBlock S)
      ⟨F i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

-- The registered closure theorem is in ambient permutations, so transfer
-- its join through the injective subtype map from the finitary group.
private theorem join_partition {T : Finset Nat} {P Q : Finset (Finset Nat)}
    (hp : partition T P) (hq : partition T Q) :
    ∃ R, partition T R ∧ blockGroup P ⊔ blockGroup Q = blockGroup R := by
  classical
  have asIndexed (V : Finset (Finset Nat)) (h : partition T V) :
      ∃ (n : Nat) (F : Fin n → Finset Nat),
        Finset.univ.image F = V ∧
        (∀ i, (F i).Nonempty) ∧ Pairwise (fun i j => Disjoint (F i) (F j)) ∧
        (∀ x, x ∈ T ↔ ∃ i, x ∈ F i) := by
    let e := (Fintype.equivFin (↥V)).symm
    let F (i : Fin (Fintype.card ↥V)) := (e i).val
    have image : Finset.univ.image F = V := by
      ext S
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => hi ▸ (e i).property,
        fun hs => ⟨e.symm ⟨S, hs⟩, congrArg Subtype.val (e.apply_symm_apply ⟨S, hs⟩)⟩⟩
    refine ⟨Fintype.card ↥V, F, image, fun i => h.1 _ (e i).property, ?_, ?_⟩
    · intro i j hij
      exact h.2.1 _ (e i).property _ (e j).property
        (fun he => hij (e.injective (Subtype.ext he)))
    · intro x
      rw [h.2.2]
      constructor
      · rintro ⟨S, hS, hxS⟩
        exact ⟨e.symm ⟨S, hS⟩, by simpa [F] using hxS⟩
      · rintro ⟨i, hi⟩
        exact ⟨F i, (e i).property, hi⟩
  obtain ⟨n, F, hFP, hf, hdF, htF⟩ := asIndexed P hp
  obtain ⟨m, E, hEQ, he, hdE, htE⟩ := asIndexed Q hq
  have supplier := FiniteParabolicClosure.2 T (ambientFamily F) (ambientFamily E)
    ⟨n, F, hf, hdF, htF, rfl⟩ ⟨m, E, he, hdE, htE, rfl⟩
  obtain ⟨k, D, hd, hdD, htD, hjoin⟩ := supplier.2
  let R := Finset.univ.image D
  refine ⟨R, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    exact hd i
  · intro S hS V hV hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hV
    exact hdD (fun hij => hn (congrArg D hij))
  · intro x
    rw [htD]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨D i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
    · rintro ⟨S, hs, hx⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨i, hx⟩
  · apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_sup, ← hFP, ← hEQ, ambient_image, ambient_image, ambient_image]
    exact hjoin

private abbrev productSet (A B : Subgroup U) : Set U :=
  Set.image2 (fun x y : U => x * y) (A : Set U) (B : Set U)

private abbrev orbit (J : Subgroup U) (x : Nat) : Set Nat :=
  {y | ∃ j : ↥J, ((j : U) : Equiv.Perm Nat) x = y}

private theorem product_subset_join (A B : Subgroup U) :
    productSet A B ⊆ (↑(A ⊔ B) : Set U) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (A ⊔ B).mul_mem ((show A ≤ A ⊔ B from le_sup_left) ha) ((show B ≤ A ⊔ B from le_sup_right) hb)

private theorem block_orbit {T : Finset Nat} {R : Finset (Finset Nat)} (h : partition T R)
    {S : Finset Nat} (hS : S ∈ R) {x : Nat} (hx : x ∈ S) :
    (S : Set Nat) = orbit (blockGroup R) x := by
  ext y
  constructor
  · intro hy
    have hswap := mem_ambientSwap hx (show y ∈ S from hy)
    let u : U := ⟨Equiv.swap x y, ambientBlock_le_finitary S hswap⟩
    exact ⟨⟨u, Subgroup.mem_iSup_of_mem (⟨S, hS⟩ : ↥R) hswap⟩, Equiv.swap_apply_left _ _⟩
  · rintro ⟨j, rfl⟩
    exact (action_of_mem h j.property).1 S hS x hx

-- A transposition between different parts of both partitions cannot lie in
-- AB. This is the paper's double-coset obstruction at the identity coset.
-- The obstruction is witnessed by one finite cell S ∩ V. A factorization
-- would make b⁻¹ inject that cell into itself while missing x.
private theorem not_cross_swap {T : Finset Nat} {P Q : Finset (Finset Nat)}
    (hp : partition T P) (hq : partition T Q)
    {S V : Finset Nat} (hS : S ∈ P) (hV : V ∈ Q)
    {x y : Nat} (hxS : x ∈ S) (hxV : x ∈ V) (hyS : y ∉ S) (hyV : y ∉ V)
    {u : U} (hu : (u : Equiv.Perm Nat) = Equiv.swap x y)
    (hab : u ∈ productSet (blockGroup P) (blockGroup Q)) : False := by
  obtain ⟨a, ha, b, hb, e⟩ := hab
  have hswap (w : Nat) : Equiv.swap x y w =
      (a : Equiv.Perm Nat) ((b : Equiv.Perm Nat) w) :=
    congrArg (fun f : Equiv.Perm Nat => f w)
      (hu.symm.trans (congrArg Subtype.val e).symm)
  let cell := S ∩ V
  have pre (z : ↥cell) :
      ((b : Equiv.Perm Nat).symm z.val ∈ cell) ∧ (b : Equiv.Perm Nat).symm z.val ≠ x := by
    obtain ⟨hzS, hzV⟩ := Finset.mem_inter.mp z.property
    let w := (b : Equiv.Perm Nat).symm z.val
    have bw : (b : Equiv.Perm Nat) w = z.val := (b : Equiv.Perm Nat).apply_symm_apply _
    have hwV : w ∈ V := (action_iff hq hb hV w).mp (bw.symm ▸ hzV)
    have hs : Equiv.swap x y w ∈ S := by
      rw [hswap w, bw]
      exact (action_of_mem hp ha).1 S hS _ hzS
    have hne : w ≠ x := by
      intro h
      rw [h, Equiv.swap_apply_left] at hs
      exact hyS hs
    rw [Equiv.swap_apply_of_ne_of_ne (b := y) hne (fun h => hyV (h ▸ hwV))] at hs
    exact ⟨Finset.mem_inter.mpr ⟨hs, hwV⟩, hne⟩
  let f (z : ↥cell) : ↥cell := ⟨(b : Equiv.Perm Nat).symm z.val, (pre z).1⟩
  have inj : Function.Injective f := fun z w e =>
    Subtype.ext ((b : Equiv.Perm Nat).symm.injective (congrArg Subtype.val e))
  obtain ⟨z, hz⟩ := Finite.surjective_of_injective inj ⟨x, Finset.mem_inter.mpr ⟨hxS, hxV⟩⟩
  exact (pre z).2 (congrArg Subtype.val hz)

private theorem block_whole_of_product {T : Finset Nat} {P Q R : Finset (Finset Nat)}
    (hp : partition T P) (hq : partition T Q) (hr : partition T R)
    (hjoin : blockGroup P ⊔ blockGroup Q = blockGroup R)
    (hprod : productSet (blockGroup P) (blockGroup Q) = (↑(blockGroup R) : Set U))
    {C : Finset Nat} (hC : C ∈ R) {x : Nat} (hx : x ∈ C) (hxt : x ∈ T) :
    C ∈ P ∪ Q := by
  classical
  have covers (z : Nat) (hz : z ∈ C) {S V : Finset Nat} (hS : S ∈ P) (hV : V ∈ Q)
      (hzS : z ∈ S) (hzV : z ∈ V) (w : Nat) (hw : w ∈ C) : w ∈ S ∨ w ∈ V := by
    by_contra hn
    push Not at hn
    have hswap := mem_ambientSwap hz hw
    let u : U := ⟨Equiv.swap z w, ambientBlock_le_finitary C hswap⟩
    have hu : u ∈ blockGroup R := Subgroup.mem_iSup_of_mem (⟨C, hC⟩ : ↥R) hswap
    have hab : u ∈ productSet (blockGroup P) (blockGroup Q) :=
      hprod.symm ▸ (show u ∈ (↑(blockGroup R) : Set U) from hu)
    exact not_cross_swap hp hq hS hV hzS hzV hn.1 hn.2 rfl hab
  have subsetC {S : Finset Nat} (hxS : x ∈ S)
      (hle : blockSym S ≤ blockGroup R) : S ⊆ C := by
    intro y hy
    have hswap := mem_ambientSwap hxS hy
    let u : U := ⟨Equiv.swap x y, ambientBlock_le_finitary S hswap⟩
    have hy' := (action_of_mem hr (hle (show u ∈ blockSym S from hswap))).1 C hC x hx
    exact (Equiv.swap_apply_left x y) ▸ hy'
  obtain ⟨S, hS, hxS⟩ := (hp.2.2 x).mp hxt
  obtain ⟨V, hV, hxV⟩ := (hq.2.2 x).mp hxt
  have hSC : S ⊆ C := subsetC hxS (hjoin ▸
    (le_iSup (fun S : ↥P => blockSym S) ⟨S, hS⟩).trans le_sup_left)
  have hVC : V ⊆ C := subsetC hxV (hjoin ▸
    (le_iSup (fun V : ↥Q => blockSym V) ⟨V, hV⟩).trans le_sup_right)
  by_cases hCS : C ⊆ S
  · exact Finset.mem_union_left Q ((Finset.Subset.antisymm hSC hCS) ▸ hS)
  by_cases hCV : C ⊆ V
  · exact Finset.mem_union_right P ((Finset.Subset.antisymm hVC hCV) ▸ hV)
  simp only [Finset.subset_iff, not_forall] at hCS hCV
  obtain ⟨y, hyC, hyS⟩ := hCS
  obtain ⟨z, hzC, hzV⟩ := hCV
  have hyV := (covers x hx hS hV hxS hxV y hyC).resolve_left hyS
  have hzS := (covers x hx hS hV hxS hxV z hzC).resolve_right hzV
  have hyt : y ∈ T := (hr.2.2 y).mpr ⟨C, hC, hyC⟩
  obtain ⟨W, hW, hyW⟩ := (hp.2.2 y).mp hyt
  have hzW : z ∉ W := fun h => hyS ((uniqueBlock hp hW hS h hzS) ▸ hyW)
  exact False.elim ((covers y hyC hW hV hyW hyV z hzC).elim hzW hzV)

private theorem orbit_apply {J : Subgroup U} (j : J) (x : Nat) :
    orbit J ((j.val : Equiv.Perm Nat) x) = orbit J x := by
  ext y
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g * j, hg⟩
  · rintro ⟨g, hg⟩
    refine ⟨g * j⁻¹, ?_⟩
    change (g.val : Equiv.Perm Nat) ((j.val : Equiv.Perm Nat).symm
      ((j.val : Equiv.Perm Nat) x)) = y
    rw [Equiv.symm_apply_apply, hg]

private theorem product_eq_join {T : Finset Nat} {P Q R : Finset (Finset Nat)}
    (hp : partition T P) (hq : partition T Q) (hr : partition T R)
    (hjoin : blockGroup P ⊔ blockGroup Q = blockGroup R) :
    productSet (blockGroup P) (blockGroup Q) = (↑(blockGroup P ⊔ blockGroup Q) : Set U) ↔
      ∀ x ∈ T, ∃ V ∈ P ∪ Q, (V : Set Nat) = orbit (blockGroup P ⊔ blockGroup Q) x := by
  classical
  rw [hjoin]
  constructor
  · intro hab x hx
    obtain ⟨C, hC, hxC⟩ := (hr.2.2 x).mp hx
    exact ⟨C, block_whole_of_product hp hq hr hjoin hab hC hxC hx, block_orbit hr hC hxC⟩
  · intro hall
    apply Set.Subset.antisymm (hjoin ▸ product_subset_join _ _)
    intro u hu
    let J := blockGroup R
    let j : J := ⟨u, hu⟩
    let σ : Equiv.Perm Nat := u
    -- On each join orbit, assign σ to the P factor if that orbit is
    -- an entire P-part. The remaining orbits use the Q factor.
    let chooseP : Set Nat := {x | ∃ S ∈ P, (S : Set Nat) = orbit J x}
    have stable (x : Nat) : σ x ∈ chooseP ↔ x ∈ chooseP := by
      change (∃ S ∈ P, (S : Set Nat) = orbit J ((j.val : Equiv.Perm Nat) x)) ↔ _
      exact iff_of_eq (congrArg (fun O => ∃ S ∈ P, (S : Set Nat) = O) (orbit_apply j x))
    let a := Equiv.Perm.ofSubtype (σ.subtypePerm stable)
    let b := Equiv.Perm.ofSubtype (σ.subtypePerm (p := fun x => x ∉ chooseP) (fun x => not_congr (stable x)))
    have actA (x : Nat) (hx : x ∈ chooseP) : a x = σ x :=
      Equiv.Perm.ofSubtype_apply_of_mem _ hx
    have actB (x : Nat) (hx : x ∉ chooseP) : b x = σ x :=
      Equiv.Perm.ofSubtype_apply_of_mem (p := fun y => y ∉ chooseP) _ hx
    have fixA (x : Nat) (hx : x ∉ chooseP) : a x = x :=
      Equiv.Perm.ofSubtype_apply_of_not_mem _ hx
    have fixB (x : Nat) (hx : x ∈ chooseP) : b x = x :=
      Equiv.Perm.ofSubtype_apply_of_not_mem _ (not_not_intro hx)
    have hjx (x : Nat) : σ x ∈ orbit J x := ⟨j, rfl⟩
    have hself (x : Nat) : x ∈ orbit J x := ⟨1, rfl⟩
    have ma : a ∈ (blockGroup P).map finitary.subtype := by
      apply ambient_mem_of_action hp
      · intro S hS x hxS
        by_cases hx : x ∈ chooseP
        · rw [actA x hx]
          obtain ⟨V, hV, he⟩ := hx
          have hv : x ∈ V := by
            change x ∈ (V : Set Nat)
            rw [he]
            exact hself x
          have hs := uniqueBlock hp hV hS hv hxS
          rw [← hs]
          change σ x ∈ (V : Set Nat)
          rw [he]
          exact hjx x
        · rwa [fixA x hx]
      · intro x hx
        by_cases h : x ∈ chooseP
        · rw [actA x h]
          exact (action_of_mem hr hu).2 x hx
        · exact fixA x h
    have mb : b ∈ (blockGroup Q).map finitary.subtype := by
      apply ambient_mem_of_action hq
      · intro V hV x hxV
        by_cases hx : x ∈ chooseP
        · rwa [fixB x hx]
        · have hxt := (hq.2.2 x).mpr ⟨V, hV, hxV⟩
          obtain ⟨W, hW, he⟩ := hall x hxt
          have hWQ := (Finset.mem_union.mp hW).resolve_left (fun hp => hx ⟨W, hp, he⟩)
          have hw : x ∈ W := by
            change x ∈ (W : Set Nat)
            rw [he]
            exact hself x
          have hv := uniqueBlock hq hWQ hV hw hxV
          rw [actB x hx, ← hv]
          change σ x ∈ (W : Set Nat)
          rw [he]
          exact hjx x
      · intro x hx
        by_cases h : x ∈ chooseP
        · exact fixB x h
        · rw [actB x h]
          exact (action_of_mem hr hu).2 x hx
    obtain ⟨a', ha', hea⟩ := ma
    obtain ⟨b', hb', heb⟩ := mb
    refine ⟨a', ha', b', hb', Subtype.ext ?_⟩
    change (a' : Equiv.Perm Nat) * (b' : Equiv.Perm Nat) = σ
    change (a' : Equiv.Perm Nat) = a at hea
    change (b' : Equiv.Perm Nat) = b at heb
    rw [hea, heb]
    ext x
    change a (b x) = σ x
    by_cases hx : x ∈ chooseP
    · rw [fixB x hx, actA x hx]
    · rw [actB x hx, fixA (σ x) (fun h => hx ((stable x).mp h))]

universe u

-- Count the left cosets aB in AB using their representatives in A.
-- The coset map on A identifies two representatives exactly when the
-- inverse of the first times the second lies in B ∩ A.
private theorem card_product_mul_card_inf {V : Type u} [Group V] (A B : Subgroup V) :
    Nat.card ↑(Set.image2 (fun a b : V => a * b) (A : Set V) (B : Set V)) *
      Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let q : (A ⧸ B.subgroupOf A) → (V ⧸ B) :=
    Quotient.map' Subtype.val (by
      intro x y
      simp only [QuotientGroup.leftRel_eq, Subgroup.mem_subgroupOf]
      exact id)
  have hq : Function.Injective q := by
    intro x y
    refine QuotientGroup.induction_on x (fun a => ?_)
    refine QuotientGroup.induction_on y (fun b => ?_)
    intro e
    change QuotientGroup.mk (s := B) (a : V) = QuotientGroup.mk (b : V) at e
    exact QuotientGroup.eq.mpr ((QuotientGroup.eq (s := B)).mp e)
  let S : Set (V ⧸ B) := QuotientGroup.mk '' (A : Set V)
  have hrange : Set.range q = S := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      refine QuotientGroup.induction_on c (fun a => ?_)
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩
  have hcard : Nat.card ↑S = B.relIndex A := by
    rw [← hrange]
    exact (Nat.card_congr (Equiv.ofInjective q hq)).symm
  have hidx := Subgroup.relIndex_mul_card B A
  rw [inf_comm B A] at hidx
  rw [Set.image2_mul, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient,
    show (QuotientGroup.mk '' (A : Set V) : Set (V ⧸ B)) = S from rfl, hcard,
    mul_assoc, hidx, mul_comm]

private theorem scalar_one_iff (A B : Subgroup U) [Finite ↥(A ⊔ B)] :
    (Nat.card ↑(productSet A B) : Complex) / (Nat.card ↥(A ⊔ B) : Complex) = 1 ↔
      productSet A B = (↑(A ⊔ B) : Set U) := by
  have hJ : (Nat.card ↥(A ⊔ B) : Complex) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥(A ⊔ B))).ne'
  rw [div_eq_iff hJ, one_mul]
  constructor
  · intro h
    have hc : Nat.card ↑(productSet A B) = Nat.card ↥(A ⊔ B) := by exact_mod_cast h
    exact Set.eq_of_subset_of_ncard_le (product_subset_join A B) hc.symm.le
      (Set.toFinite _)
  · intro h
    rw [h]
    rfl

private theorem inclusion_index {V : Type u} [Group V] {L H : Subgroup V}
    (d : ConjEmbedding L H) (hle : L ≤ H)
    (hd : d.toHom = Subgroup.inclusion hle) :
    d.toHom.range.index * Nat.card ↥L = Nat.card ↥H := by
  rw [hd]
  have range : (Subgroup.inclusion hle).range = L.subgroupOf H := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x.val, hx⟩, rfl⟩⟩
  rw [range, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact Subgroup.index_mul_card _

private theorem index_product {A B H : Subgroup U} [Finite ↥H]
    (a : A ≤ H) (b : B ≤ H)
    (iA iB iI iJ : Nat)
    (eA : iA * Nat.card ↥A = Nat.card ↥H)
    (eB : iB * Nat.card ↥B = Nat.card ↥H)
    (eI : iI * Nat.card ↥(A ⊓ B) = Nat.card ↥H)
    (eJ : iJ * Nat.card ↥(A ⊔ B) = Nat.card ↥H) :
    (iI : Complex) * (iJ : Complex) =
      ((Nat.card ↑(productSet A B) : Complex) / (Nat.card ↥(A ⊔ B) : Complex)) *
        ((iA : Complex) * (iB : Complex)) := by
  let _ : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective a)
  let _ : Finite ↥B := Finite.of_injective _ (Subgroup.inclusion_injective b)
  let _ : Finite ↥(A ⊓ B) := Finite.of_injective _
    (Subgroup.inclusion_injective (inf_le_left.trans a : A ⊓ B ≤ H))
  let _ : Finite ↥(A ⊔ B) := Finite.of_injective _ (Subgroup.inclusion_injective (sup_le a b))
  have nz (L : Subgroup U) [Finite ↥L] : (Nat.card ↥L : Complex) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥L)).ne'
  have index (L : Subgroup U) [Finite ↥L] (i : Nat) (e : i * Nat.card ↥L = Nat.card ↥H) :
      (i : Complex) = (Nat.card ↥H : Complex) / (Nat.card ↥L : Complex) :=
    (eq_div_iff (nz L)).mpr (by exact_mod_cast e)
  have hp := card_product_mul_card_inf A B
  have hp' : (Nat.card ↑(productSet A B) : Complex) * (Nat.card ↥(A ⊓ B) : Complex) =
      (Nat.card ↥A : Complex) * (Nat.card ↥B : Complex) := by exact_mod_cast hp
  rw [index A iA eA, index B iB eB, index (A ⊓ B) iI eI, index (A ⊔ B) iJ eJ]
  field_simp [nz A, nz B, nz (A ⊓ B), nz (A ⊔ B)]
  apply (div_eq_iff (nz (A ⊓ B))).2
  simpa only [mul_assoc] using congrArg
    (fun z : Complex => (Nat.card ↥H : Complex)^2 * z) hp'.symm

private noncomputable abbrev eval {V : Type u} [Group V] {K H : Subgroup V} {p q : Word K H}
    (d : LabelledDrawing Complex p q) :=
  d.interpret.eval

private noncomputable abbrev indexedCurls {V : Type u} [Group V] {L H G : Subgroup V}
    (a : ConjEmbedding H G) (d : ConjEmbedding L H) (f : Subgroup.FiniteIndex d.toHom.range) :
    LabelledDrawing Complex (Word.up a) (Word.up a) ×
    LabelledDrawing Complex (Word.down a) (Word.down a) :=
  (.vertical (.trivalent (.upToUpDown a d f)) (.trivalent (.upDownToUp a d)),
   .vertical (.trivalent (.downToUpDown a d f)) (.trivalent (.upDownToDown a d)))

-- ParabolicCurlsFromBlockRefinements computes a refinement ratio using
-- a shared carrier for H and the internal image. Here H can come from
-- a separate carrier, so use ReidemeisterOne, the checked declaration
-- used by that supplier for its direct curls. Its hypotheses are the
-- two conjugators and finite index of the internal image.
private theorem inclusion_curls {V : Type u} [Group V] {L H G : Subgroup V}
    (α : V) (hα : ∀ x : H, α * (x : V) * α⁻¹ ∈ G)
    (d : ConjEmbedding L H) (hle : L ≤ H) (hd : d.toHom = Subgroup.inclusion hle)
    (f : Subgroup.FiniteIndex d.toHom.range) :
    let a := ConjEmbedding.ofConjugator α hα
    let c := indexedCurls a d f
    let n : Complex := d.toHom.range.index
    eval c.1 = (Biset.Hom.id (Word.up a).basis).scale n ∧
      eval c.2 = (Biset.Hom.id (Word.down a).basis).scale n := by
  let hδ : ∀ x : L, (1 : V) * (x : V) * 1⁻¹ ∈ H := fun x => by
    simpa only [one_mul, inv_one, mul_one] using hle x.property
  have ed : d = ConjEmbedding.ofConjugator 1 hδ := by
    apply ConjEmbedding.ext
    rw [hd]
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    simp only [ConjEmbedding.ofConjugator_apply, Subgroup.coe_inclusion, one_mul, inv_one, mul_one]
  subst d
  have ev := ReidemeisterOne L H G 1 α hδ hα
  exact ⟨ev.1 f, ev.2.2.2 f⟩

private theorem scaled_id_comp {K H : Type u} [Group K] [Group H]
    (X : Biset K H) (r s : Complex) :
    ((Biset.Hom.id X).scale r).vertical ((Biset.Hom.id X).scale s) =
      (Biset.Hom.id X).scale (s * r) := by
  rw [Biset.Hom.vertical_scale_left, Biset.Hom.vertical_scale_right, Biset.Hom.vertical_id]
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change r • (s • x) = (s * r) • x
  rw [smul_smul, mul_comm r s]

private theorem scaled_id_scale {K H : Type u} [Group K] [Group H]
    (X : Biset K H) (r s : Complex) :
    ((Biset.Hom.id X).scale r).scale s = (Biset.Hom.id X).scale (s * r) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  exact smul_smul s r x

private theorem compare_curl_stacks {V : Type u} [Group V] {K H : Subgroup V} {w : Word K H}
    (cA cB cI cJ : LabelledDrawing Complex w w) (iA iB iI iJ scalar : Complex)
    (hA : eval cA = (Biset.Hom.id w.basis).scale iA)
    (hB : eval cB = (Biset.Hom.id w.basis).scale iB)
    (hI : eval cI = (Biset.Hom.id w.basis).scale iI)
    (hJ : eval cJ = (Biset.Hom.id w.basis).scale iJ)
    (hscalar : iI * iJ = scalar * (iA * iB)) :
    eval (.vertical cJ cI) = eval (.scale scalar (.vertical cB cA)) := by
  change (eval cJ).vertical (eval cI) = ((eval cB).vertical (eval cA)).scale scalar
  rw [hA, hB, hI, hJ, scaled_id_comp, scaled_id_comp, scaled_id_scale, hscalar]

end CurlJoinIntersectionProof

theorem ParabolicCurlJoinIntersection : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym : Finset Nat → Subgroup U :=
  fun S => Subgroup.comap (Subgroup.subtype finitary)
    (MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ S)))
let blockGroup : Finset (Finset Nat) → Subgroup U :=
  fun P => iSup (fun V : ↥P => blockSym (V : Finset Nat))
let partition : Finset Nat → Finset (Finset Nat) → Prop :=
  fun T P =>
    (∀ V ∈ P, Finset.Nonempty V) ∧
    (∀ V ∈ P, ∀ W ∈ P, V ≠ W → Disjoint V W) ∧
    (∀ x : Nat, x ∈ T ↔ ∃ V ∈ P, x ∈ V)
let parabolic : Subgroup U → Prop :=
  fun L => ∃ T P, partition T P ∧ L = blockGroup P
let inclusion : ∀ {L H : Subgroup U}, L ≤ H → MackeyDiagrams.ConjEmbedding L H :=
  fun h => ⟨Subgroup.inclusion h, ⟨1, fun x => by
    simp only [Subgroup.coe_inclusion, one_mul, inv_one, mul_one]⟩⟩
∀ (H G : Subgroup U) (α : U) (hα : ∀ x : H, α * (x : U) * α⁻¹ ∈ G),
  parabolic H → parabolic G →
  ∀ (T : Finset Nat) (P Q : Finset (Finset Nat)),
    partition T P → partition T Q →
    let A := blockGroup P
    let B := blockGroup Q
    ∀ (hA : A ≤ H) (hB : B ≤ H),
      let I := A ⊓ B
      let J := A ⊔ B
      let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
      let up := MackeyDiagrams.Word.up a
      let down := MackeyDiagrams.Word.down a
      let finiteIndex : ∀ {L : Subgroup U}, MackeyDiagrams.ConjEmbedding L H → Prop :=
        fun d => Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d))
      let curls : ∀ {L : Subgroup U} (d : MackeyDiagrams.ConjEmbedding L H),
          finiteIndex d →
          MackeyDiagrams.LabelledDrawing Complex up up ×
            MackeyDiagrams.LabelledDrawing Complex down down :=
        fun d finite =>
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.trivalent
              (MackeyDiagrams.TrivalentVertex.upToUpDown a d finite))
            (MackeyDiagrams.LabelledDrawing.trivalent
              (MackeyDiagrams.TrivalentVertex.upDownToUp a d)),
           MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.trivalent
              (MackeyDiagrams.TrivalentVertex.downToUpDown a d finite))
            (MackeyDiagrams.LabelledDrawing.trivalent
              (MackeyDiagrams.TrivalentVertex.upDownToDown a d)))
      let dA := inclusion hA
      let dB := inclusion hB
      let dI := inclusion (show I ≤ H from le_trans inf_le_left hA)
      let dJ := inclusion (show J ≤ H from sup_le hA hB)
      let AB : Set U := Set.image2 (fun x y : U => x * y) (A : Set U) (B : Set U)
      let scalar : Complex := (Nat.card ↥AB : Complex) / (Nat.card ↥J : Complex)
      let joinBlock : Nat → Set Nat :=
        fun x => {y | ∃ j : ↥J, ((j : U) : Equiv.Perm Nat) x = y}
      ∃ (fA : finiteIndex dA) (fB : finiteIndex dB)
        (fI : finiteIndex dI) (fJ : finiteIndex dJ),
        let cA := curls dA fA
        let cB := curls dB fB
        let cI := curls dI fI
        let cJ := curls dJ fJ
        let leftUp := MackeyDiagrams.LabelledDrawing.vertical (Prod.fst cJ) (Prod.fst cI)
        let leftDown := MackeyDiagrams.LabelledDrawing.vertical (Prod.snd cJ) (Prod.snd cI)
        let rightUp := MackeyDiagrams.LabelledDrawing.scale scalar
          (MackeyDiagrams.LabelledDrawing.vertical (Prod.fst cB) (Prod.fst cA))
        let rightDown := MackeyDiagrams.LabelledDrawing.scale scalar
          (MackeyDiagrams.LabelledDrawing.vertical (Prod.snd cB) (Prod.snd cA))
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret leftUp) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret rightUp) ∧
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret leftDown) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret rightDown) ∧
        (scalar = 1 ↔ ∀ x ∈ T, ∃ V ∈ P ∪ Q, (V : Set Nat) = joinBlock x)
) :=
(by
  classical
  -- Xiao, Proposition 8.2 and the two stacks displayed with Example 8.1.
  -- Archived original PDF p. 34 (SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2).
  -- Revised published PDF p. 36 (SHA-256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  intro _finitary _U _blockSym _blockGroup _partition _parabolic inclusion
    H G α hα hH _hG T P Q hp hq A B hA hB I J a _up _down
    finiteIndex curls dA dB dI dJ AB scalar joinBlock
  have finiteH : Finite ↥H := by
    obtain ⟨X, R, hR, h⟩ := hH
    subst H
    exact CurlJoinIntersectionProof.blockGroup_finite hR
  let _ : Finite ↥H := finiteH
  have hI : I ≤ H := le_trans inf_le_left hA
  have hJ : J ≤ H := sup_le hA hB
  let _ : Finite ↥J := Finite.of_injective _ (Subgroup.inclusion_injective hJ)
  have fA : finiteIndex dA := inferInstanceAs (Subgroup.FiniteIndex dA.toHom.range)
  have fB : finiteIndex dB := inferInstanceAs (Subgroup.FiniteIndex dB.toHom.range)
  have fI : finiteIndex dI := inferInstanceAs (Subgroup.FiniteIndex dI.toHom.range)
  have fJ : finiteIndex dJ := inferInstanceAs (Subgroup.FiniteIndex dJ.toHom.range)
  refine ⟨fA, fB, fI, fJ, ?_⟩
  intro cA cB cI cJ leftUp leftDown rightUp rightDown
  have eA := CurlJoinIntersectionProof.inclusion_curls α hα dA hA rfl fA
  have eB := CurlJoinIntersectionProof.inclusion_curls α hα dB hB rfl fB
  have eI := CurlJoinIntersectionProof.inclusion_curls α hα dI hI rfl fI
  have eJ := CurlJoinIntersectionProof.inclusion_curls α hα dJ hJ rfl fJ
  have scalar_eq : (dI.toHom.range.index : Complex) * (dJ.toHom.range.index : Complex) =
      scalar * ((dA.toHom.range.index : Complex) * (dB.toHom.range.index : Complex)) :=
    CurlJoinIntersectionProof.index_product hA hB _ _ _ _
      (CurlJoinIntersectionProof.inclusion_index dA hA rfl)
      (CurlJoinIntersectionProof.inclusion_index dB hB rfl)
      (CurlJoinIntersectionProof.inclusion_index dI hI rfl)
      (CurlJoinIntersectionProof.inclusion_index dJ hJ rfl)
  refine ⟨?_, ?_, ?_⟩
  · exact CurlJoinIntersectionProof.compare_curl_stacks cA.1 cB.1 cI.1 cJ.1
      _ _ _ _ scalar eA.1 eB.1 eI.1 eJ.1 scalar_eq
  · exact CurlJoinIntersectionProof.compare_curl_stacks cA.2 cB.2 cI.2 cJ.2
      _ _ _ _ scalar eA.2 eB.2 eI.2 eJ.2 scalar_eq
  · obtain ⟨R, hr, hjoin⟩ := CurlJoinIntersectionProof.join_partition hp hq
    exact (CurlJoinIntersectionProof.scalar_one_iff A B).trans
      (CurlJoinIntersectionProof.product_eq_join hp hq hr hjoin))

#print axioms ParabolicCurlJoinIntersection
