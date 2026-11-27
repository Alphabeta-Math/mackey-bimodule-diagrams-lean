import MackeyDiagrams
import Proofs.ThreeInductionCrossingMultipliers
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks

set_option maxHeartbeats 2000000

namespace ExtremalThreeInduction
open MackeyDiagrams

private abbrev conj {V : Type*} [Group V] (p : V) (H : Subgroup V) :=
  H.map (MulAut.conj p).toMonoidHom

section Group
variable {V : Type*} [Group V]

private theorem conj_compose (p q : V) (H : Subgroup V) :
    conj p (conj q H) = conj (p * q) H := by
  rw [conj, conj, Subgroup.map_map]
  congr 1
  ext x
  change p * (q * x * q⁻¹) * p⁻¹ = (p * q) * x * (p * q)⁻¹
  group

private theorem conj_one (H : Subgroup V) : conj 1 H = H := by
  have h : (MulAut.conj (1 : V)).toMonoidHom = MonoidHom.id V := by
    ext x
    simp
  change H.map _ = H
  rw [h, Subgroup.map_id]

private theorem conj_inner {H : Subgroup V} {p : V} (hp : p ∈ H) :
    conj p H = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hp hx) (H.inv_mem hp)
  · intro x hx
    refine ⟨p⁻¹ * x * p, H.mul_mem (H.mul_mem (H.inv_mem hp) hx) hp, ?_⟩
    change p * (p⁻¹ * x * p) * p⁻¹ = x
    group

private theorem conj_mono (r : V) {H K : Subgroup V} (h : H ≤ K) :
    conj r H ≤ conj r K := Subgroup.map_mono h

private theorem undo_conj {H K : Subgroup V} {r : V} (h : H ≤ conj r K) :
    conj r⁻¹ H ≤ K := by
  simpa only [conj_compose, inv_mul_cancel, conj_one] using conj_mono r⁻¹ h

private theorem conj_eq_of_action {H : Subgroup V} {a b : V}
    (h : ∀ x : H, a * (x : V) * a⁻¹ = b * (x : V) * b⁻¹) :
    conj a H = conj b H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (h ⟨x, hx⟩).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, h ⟨x, hx⟩⟩

private abbrev embed {H K : Subgroup V} (r : V) (h : conj r H ≤ K) :
    ConjEmbedding H K :=
  ConjEmbedding.ofConjugator r (fun x => h ⟨x, x.property, rfl⟩)

private theorem comp_conj {H K L : Subgroup V} {r s : V}
    {hr : conj r K ≤ L} {hs : conj s H ≤ K} (x : H) :
    ((embed r hr).comp (embed s hs) |>.toHom x : V) =
      (r * s) * (x : V) * (r * s)⁻¹ := by
  simp only [ConjEmbedding.comp_apply, ConjEmbedding.ofConjugator_apply, mul_inv_rev]
  group

private theorem dot_conj {H K : Subgroup V}
    {i j : ConjEmbedding H K} (dot : Dot i j) {r s : V}
    (hi : ∀ x : H, (i.toHom x : V) = r * (x : V) * r⁻¹)
    (hj : ∀ x : H, (j.toHom x : V) = s * (x : V) * s⁻¹) :
    conj r H = conj (dot.element * s) H := by
  apply conj_eq_of_action
  intro x
  have hd := congrArg (fun k : K => (k : V)) (dot.intertwines x)
  simp only [Subgroup.coe_mul, hi, hj] at hd
  calc
    r * (x : V) * r⁻¹ = (r * x * r⁻¹ * dot.element) * (dot.element : V)⁻¹ := by group
    _ = (dot.element * (s * x * s⁻¹)) * (dot.element : V)⁻¹ := by rw [hd]
    _ = _ := by group

private def mkDot {H K : Subgroup V} {i j : ConjEmbedding H K}
    (z : K) {r s : V}
    (hi : ∀ x : H, (i.toHom x : V) = r * (x : V) * r⁻¹)
    (hj : ∀ x : H, (j.toHom x : V) = s * (x : V) * s⁻¹)
    (h : ∀ x : H, r * (x : V) * r⁻¹ = ((z : V) * s) * (x : V) * ((z : V) * s)⁻¹) :
    Dot i j where
  element := z
  intertwines x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hi, hj, h]
    group

end Group

private abbrev Perm := Equiv.Perm Nat
private abbrev Finitary := Subgroup.closure {σ : Perm | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) : Subgroup Perm :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ X))

private abbrev ParabolicPerm (H : Subgroup Perm) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧ Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H = ⨆ i, blockSym (blocks i)

private abbrev Parabolic (H : Subgroup Finitary) := ParabolicPerm (H.map Finitary.subtype)

private theorem of_family {ι : Type} [Finite ι] (blocks : ι → Finset Nat)
    (hne : ∀ i, (blocks i).Nonempty)
    (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) :
    ParabolicPerm (⨆ i, blockSym (blocks i)) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  exact ⟨_, blocks ∘ e, fun i => hne (e i),
    fun i j hij => hd (fun h => hij (e.injective h)),
    (e.iSup_comp (g := fun i => blockSym (blocks i))).symm⟩

private theorem same_block {ι : Type} {X : ι → Finset Nat}
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) {i j : ι} {x : Nat}
    (hi : x ∈ X i) (hj : x ∈ X j) : i = j := by
  by_contra h
  exact Finset.disjoint_left.mp (hd h) hi hj

private theorem block_trivial (S : Finset Nat) (h : ∀ x y, x ∈ S → y ∈ S → x = y) :
    blockSym S = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨σ, rfl⟩
  apply Subgroup.mem_bot.mpr
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ S
  · rw [Equiv.Perm.ofSubtype_apply_of_mem σ hx]
    exact h _ _ (σ ⟨x, hx⟩).property hx
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem σ hx

private def padded {ι : Type} (X : Finset Nat) (S : ι → Finset Nat) (Y : Finset Nat) :
    ι ⊕ ↥(X \ Y) → Finset Nat := Sum.elim S (fun x => {x.val})

private theorem pad_blocks {ι : Type} [Fintype ι] (X : Finset Nat) (S : ι → Finset Nat)
    (hS : ∀ i, S i ⊆ X) (hne : ∀ i, (S i).Nonempty)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    let Y := Finset.univ.biUnion S
    let T := padded X S Y
    (∀ i, (T i).Nonempty) ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
    (∀ x, x ∈ X ↔ ∃ i, x ∈ T i) ∧ (⨆ i, blockSym (S i)) = ⨆ i, blockSym (T i) := by
  classical
  intro Y T
  have hY (x : Nat) : x ∈ Y ↔ ∃ i, x ∈ S i := by simp [Y]
  constructor
  · rintro (i | x)
    · exact hne i
    · exact Finset.singleton_nonempty _
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases i with (i | i) <;> rcases j with (j | j)
    · exact hij (congrArg Sum.inl (same_block hd hx hy))
    · have h : x = j.val := Finset.mem_singleton.mp hy
      exact (Finset.mem_sdiff.mp j.property).2 (h ▸ (hY x).mpr ⟨i, hx⟩)
    · have h : x = i.val := Finset.mem_singleton.mp hx
      exact (Finset.mem_sdiff.mp i.property).2 (h ▸ (hY x).mpr ⟨j, hy⟩)
    · exact hij (congrArg Sum.inr (Subtype.ext
        ((Finset.mem_singleton.mp hx).symm.trans (Finset.mem_singleton.mp hy))))
  constructor
  · intro x
    constructor
    · intro hx
      by_cases hy : x ∈ Y
      · obtain ⟨i, hi⟩ := (hY x).mp hy
        exact ⟨Sum.inl i, hi⟩
      · exact ⟨Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hy⟩⟩, Finset.mem_singleton_self x⟩
    · rintro ⟨i | j, hx⟩
      · exact hS i hx
      · rw [Finset.mem_singleton.mp hx]
        exact (Finset.mem_sdiff.mp j.property).1
  apply le_antisymm
  · exact iSup_le fun i => le_iSup (fun k => blockSym (T k)) (Sum.inl i)
  · apply iSup_le
    rintro (i | j)
    · exact le_iSup (fun k => blockSym (S k)) i
    · change blockSym {j.val} ≤ _
      rw [block_trivial _ (fun x y hx hy =>
        (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm)]
      exact bot_le

private theorem parabolic_conj_perm {H : Subgroup Perm} (hH : ParabolicPerm H) (σ : Perm) :
    ParabolicPerm (conj σ H) := by
  classical
  obtain ⟨n, X, hne, hd, rfl⟩ := hH
  have image_block (S : Finset Nat) : conj σ (blockSym S) = blockSym (S.image σ) := by
    let Y := S.image σ
    have mem_image (x : Nat) : x ∈ S ↔ σ x ∈ Y := by simp [Y]
    let e : S ≃ Y := σ.subtypeEquiv mem_image
    have commute (f : Equiv.Perm S) :
        MulAut.conj σ (Equiv.Perm.ofSubtype f) = Equiv.Perm.ofSubtype (e.permCongr f) := by
      apply Equiv.ext
      intro x
      obtain ⟨y, rfl⟩ := σ.surjective x
      change σ (Equiv.Perm.ofSubtype f (σ.symm (σ y))) = Equiv.Perm.ofSubtype (e.permCongr f) (σ y)
      rw [σ.symm_apply_apply]
      by_cases hy : y ∈ S
      · rw [Equiv.Perm.ofSubtype_apply_of_mem f hy,
          Equiv.Perm.ofSubtype_apply_of_mem _ ((mem_image y).mp hy)]
        change (e (f ⟨y, hy⟩) : Nat) = (e.permCongr f (e ⟨y, hy⟩) : Nat)
        simp
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem f hy, Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun h =>
          hy ((mem_image y).mpr h))]
    ext τ
    constructor
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨e.permCongr f, (commute f).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨f, rfl⟩ := e.permCongr.surjective g
      exact ⟨Equiv.Perm.ofSubtype f, ⟨f, rfl⟩, commute f⟩
  change ParabolicPerm (Subgroup.map _ (⨆ i, blockSym (X i)))
  rw [Subgroup.map_iSup]
  simp only [show ∀ S, (blockSym S).map (MulAut.conj σ).toMonoidHom = blockSym (S.image σ) from image_block]
  refine ⟨n, fun i => (X i).image σ, fun i => (hne i).image _, ?_, rfl⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hi hj
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hi
  obtain ⟨z, hz, hxz⟩ := Finset.mem_image.mp hj
  exact Finset.disjoint_left.mp (hd hij) hy (σ.injective (hxz.trans hxy.symm) ▸ hz)

private theorem parabolic_inf_on {ι κ : Type} [Finite ι] [Finite κ] (X : Finset Nat)
    (A : ι → Finset Nat) (B : κ → Finset Nat)
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ j, (B j).Nonempty)
    (dA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (dB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (coverA : ∀ x, x ∈ X ↔ ∃ i, x ∈ A i)
    (coverB : ∀ x, x ∈ X ↔ ∃ j, x ∈ B j) :
    ParabolicPerm ((⨆ i, blockSym (A i)) ⊓ (⨆ j, blockSym (B j))) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  let Cell := {ij : ι × κ // (A ij.1 ∩ B ij.2).Nonempty}
  let cell (ij : Cell) := A ij.val.1 ∩ B ij.val.2
  rw [FiniteParabolicIntersectionBlocks X A B hA hB dA dB coverA coverB]
  have omitEmpty : (⨆ i, ⨆ j, blockSym (A i ∩ B j)) = ⨆ ij, blockSym (cell ij) := by
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun j => ?_
      by_cases h : (A i ∩ B j).Nonempty
      · exact le_iSup (fun ij => blockSym (cell ij)) (⟨(i, j), h⟩ : Cell)
      · rw [block_trivial _ (fun x _ hx _ => (h ⟨x, hx⟩).elim)]
        exact bot_le
    · refine iSup_le fun ij => ?_
      exact (le_iSup (fun j => blockSym (A ij.val.1 ∩ B j)) ij.val.2).trans
        (le_iSup (fun i => ⨆ j, blockSym (A i ∩ B j)) ij.val.1)
  change ParabolicPerm (⨆ i, ⨆ j, blockSym (A i ∩ B j))
  rw [omitEmpty]
  refine of_family cell (fun ij => ij.property) ?_
  intro ij kl h
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
  obtain ⟨hk, hl⟩ := Finset.mem_inter.mp hy
  exact h (Subtype.ext (Prod.ext (same_block dA hi hk) (same_block dB hj hl)))

private theorem parabolic_sup_on {ι κ : Type} [Finite ι] [Finite κ] (X : Finset Nat) (A : ι → Finset Nat)
    (B : κ → Finset Nat) (hA : ∀ i, (A i).Nonempty) (hB : ∀ j, (B j).Nonempty)
    (dA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (dB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (coverA : ∀ x, x ∈ X ↔ ∃ i, x ∈ A i)
    (coverB : ∀ x, x ∈ X ↔ ∃ j, x ∈ B j) :
    ParabolicPerm ((⨆ i, blockSym (A i)) ⊔ (⨆ j, blockSym (B j))) := by
  classical
  let block : ι ⊕ κ → Finset Nat := Sum.elim A B
  let overlap : (ι ⊕ κ) → (ι ⊕ κ) → Prop := fun u v =>
    match u, v with
    | Sum.inl i, Sum.inr j => (A i ∩ B j).Nonempty
    | _, _ => False
  let graph := SimpleGraph.fromRel overlap
  let componentBlock : graph.ConnectedComponent → Finset Nat := fun c =>
    let inComponent : Nat → Prop := fun x =>
      ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v
    @Finset.filter Nat inComponent (Classical.decPred inComponent) X
  have memComponent (c : graph.ConnectedComponent) (x : Nat) :
      x ∈ componentBlock c ↔ x ∈ X ∧
        ∃ v, graph.connectedComponentMk v = c ∧ x ∈ block v :=
    @Finset.mem_filter Nat _ (Classical.decPred _) _ _
  have blockNonempty (v : ι ⊕ κ) : (block v).Nonempty := by
    cases v with
    | inl i => exact hA i
    | inr j => exact hB j
  have blockSubset (v : ι ⊕ κ) : block v ⊆ X := by
    intro x hx
    cases v with
    | inl i => exact (coverA x).mpr ⟨i, hx⟩
    | inr j => exact (coverB x).mpr ⟨j, hx⟩
  have overlap_component {u v : ι ⊕ κ} {x : Nat}
      (hu : x ∈ block u) (hv : x ∈ block v) :
      graph.connectedComponentMk u = graph.connectedComponentMk v := by
    cases u with
    | inl i =>
      cases v with
      | inl j => rw [same_block dA hu hv]
      | inr j =>
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        apply (SimpleGraph.fromRel_adj overlap _ _).mpr
        exact ⟨Sum.inl_ne_inr, Or.inl ⟨x, Finset.mem_inter.mpr ⟨hu, hv⟩⟩⟩
    | inr j =>
      cases v with
      | inl i =>
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        apply (SimpleGraph.fromRel_adj overlap _ _).mpr
        exact ⟨Sum.inr_ne_inl, Or.inr ⟨x, Finset.mem_inter.mpr ⟨hv, hu⟩⟩⟩
      | inr k => rw [same_block dB hu hv]
  have joinFormula :
      ((⨆ i, blockSym (A i)) ⊔ (⨆ j, blockSym (B j))) =
        ⨆ c, blockSym (componentBlock c) :=
    FiniteParabolicJoinBlocks X A B hA hB dA dB coverA coverB
  rw [joinFormula]
  let _ : Finite (ι ⊕ κ) := by
    let _ : Fintype ι := Fintype.ofFinite ι
    let _ : Fintype κ := Fintype.ofFinite κ
    exact Finite.of_fintype _
  refine of_family componentBlock ?_ ?_
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      obtain ⟨x, hx⟩ := blockNonempty v
      exact ⟨x, (memComponent _ x).mpr ⟨blockSubset v hx, v, rfl, hx⟩⟩
  · intro c d h
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨_, u, huc, hu⟩ := (memComponent c x).mp hx
    obtain ⟨_, v, hvd, hv⟩ := (memComponent d x).mp hy
    exact h (huc.symm.trans ((overlap_component hu hv).trans hvd))

private theorem parabolic_lattice {H K : Subgroup Perm}
    (hH : ParabolicPerm H) (hK : ParabolicPerm K) :
    ParabolicPerm (H ⊓ K) ∧ ParabolicPerm (H ⊔ K) := by
  classical
  obtain ⟨n, A, hA, dA, rfl⟩ := hH
  obtain ⟨m, B, hB, dB, rfl⟩ := hK
  let X := Finset.univ.biUnion A ∪ Finset.univ.biUnion B
  obtain ⟨hA', dA', cA, eqA⟩ := pad_blocks X A
    (fun i x hx => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hA dA
  obtain ⟨hB', dB', cB, eqB⟩ := pad_blocks X B
    (fun i x hx => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hB dB
  rw [eqA, eqB]
  exact ⟨parabolic_inf_on X _ _ hA' hB' dA' dB' cA cB,
    parabolic_sup_on X _ _ hA' hB' dA' dB' cA cB⟩


private theorem parabolic_conj {H : Subgroup Finitary} (hH : Parabolic H) (r : Finitary) :
    Parabolic (conj r H) := by
  have commutes :
      Finitary.subtype.comp (MulAut.conj r).toMonoidHom =
        (MulAut.conj (r : Perm)).toMonoidHom.comp Finitary.subtype := by
    ext x
    rfl
  change ParabolicPerm ((H.map (MulAut.conj r).toMonoidHom).map Finitary.subtype)
  rw [Subgroup.map_map, commutes, ← Subgroup.map_map]
  exact parabolic_conj_perm hH r

private theorem parabolic_inf {H K : Subgroup Finitary} (hH : Parabolic H) (hK : Parabolic K) :
    Parabolic (H ⊓ K) := by
  change ParabolicPerm ((H ⊓ K).map Finitary.subtype)
  rw [Subgroup.map_inf _ _ _ Finitary.subtype_injective]
  exact (parabolic_lattice hH hK).1

private theorem parabolic_sup {H K : Subgroup Finitary} (hH : Parabolic H) (hK : Parabolic K) :
    Parabolic (H ⊔ K) := by
  change ParabolicPerm ((H ⊔ K).map Finitary.subtype)
  rw [Subgroup.map_sup]
  exact (parabolic_lattice hH hK).2

noncomputable section Evaluation
variable {V : Type*} [Group V]
variable {G A D F C E B : Subgroup V}

private abbrev GA (H : Subgroup V) := MonoidAlgebra Complex H

private abbrev word {P Q S T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) (k : ConjEmbedding T S) :=
  Word.tensor (Word.tensor (Word.up i) (Word.up j)) (Word.up k)

private abbrev straight {P Q : Subgroup V} (i : ConjEmbedding Q P) :=
  LabelledDrawing.ordinary (Diagram.id (R := Complex) (Word.up i))

private abbrev merge {P Q S : Subgroup V} (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) :=
  LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.mergeUp i j)

private abbrev split {P Q S : Subgroup V} (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) :=
  LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.splitUp i j)

private abbrev dCrossing {P Q Q' S : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (i' : ConjEmbedding Q' P) (j' : ConjEmbedding S Q')
    (dot : Dot (ConjEmbedding.comp i j)
      (ConjEmbedding.comp i' j')) :=
  Diagram.vertical (Diagram.mergeUp (R := Complex) i j)
    (Diagram.vertical (Diagram.upDot dot)
      (Diagram.splitUp i' j'))
private abbrev dCrossLeft {P Q Q' S T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (i' : ConjEmbedding Q' P) (j' : ConjEmbedding S Q')
    (k : ConjEmbedding T S)
    (dot : Dot (ConjEmbedding.comp i j)
      (ConjEmbedding.comp i' j')) :=
  Diagram.horizontal (dCrossing i j i' j' dot)
    (Diagram.id (Word.up k))
private abbrev dCrossRight {P Q S S' T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (k : ConjEmbedding T S)
    (j' : ConjEmbedding S' Q) (k' : ConjEmbedding T S')
    (dot : Dot (ConjEmbedding.comp j k)
      (ConjEmbedding.comp j' k')) :=
  Diagram.vertical
    (Diagram.associate (Word.up i)
      (Word.up j) (Word.up k))
    (Diagram.vertical
      (Diagram.horizontal (Diagram.id (Word.up i))
        (dCrossing j k j' k' dot))
      (Diagram.unassociate (Word.up i)
        (Word.up j') (Word.up k')))

private abbrev wCrossing {P Q Q' S : Subgroup V}
    (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q')
    (weights : DotLabel Complex (ConjEmbedding.comp a b)
      (ConjEmbedding.comp a' b')) :=
  LabelledDrawing.vertical (merge a b)
    (LabelledDrawing.vertical (DotLabel.upDrawing weights)
      (split a' b'))
private abbrev wCrossLeft {P Q Q' S T : Subgroup V}
    (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q')
    (c : ConjEmbedding T S)
    (weights : DotLabel Complex (ConjEmbedding.comp a b)
      (ConjEmbedding.comp a' b')) :=
  LabelledDrawing.horizontal (wCrossing a b a' b' weights)
    (straight c)
private abbrev wCrossRight {P Q S S' T : Subgroup V}
    (a : ConjEmbedding Q P)
    (b : ConjEmbedding S Q) (c : ConjEmbedding T S)
    (b' : ConjEmbedding S' Q) (c' : ConjEmbedding T S')
    (weights : DotLabel Complex (ConjEmbedding.comp b c)
      (ConjEmbedding.comp b' c')) :=
  LabelledDrawing.vertical
    (LabelledDrawing.ordinary
      (Diagram.associate (Word.up a) (Word.up b)
        (Word.up c)))
    (LabelledDrawing.vertical
      (LabelledDrawing.horizontal (straight a)
        (wCrossing b c b' c' weights))
      (LabelledDrawing.ordinary
        (Diagram.unassociate (Word.up a) (Word.up b')
          (Word.up c'))))


private theorem singleton_dot {P Q : Subgroup V} {i j : ConjEmbedding Q P}
    (x : Dot i j) :
    (DotLabel.upDrawing (R := Complex) (Finsupp.single x 1)).interpret.eval =
      (Diagram.upDot (R := Complex) x).eval := by
  rw [DotLabel.eval_upDrawing]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  rw [Diagram.eval_linearUpDot_apply, freeLift_single, one_smul]

private theorem crossLeft_eval {P Q Q' S T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (i' : ConjEmbedding Q' P) (j' : ConjEmbedding S Q') (k : ConjEmbedding T S)
    (x : Dot (i.comp j) (i'.comp j')) :
    (wCrossLeft i j i' j' k (Finsupp.single x 1)).interpret.eval =
      (dCrossLeft i j i' j' k x).eval := by
  simp only [LabelledDrawing.interpret,
    ScopedDiagram.eval, TrivalentVertex.expand, Diagram.eval, singleton_dot]

private theorem crossRight_eval {P Q S S' T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) (k : ConjEmbedding T S)
    (j' : ConjEmbedding S' Q) (k' : ConjEmbedding T S')
    (x : Dot (j.comp k) (j'.comp k')) :
    (wCrossRight i j k j' k' (Finsupp.single x 1)).interpret.eval =
      (dCrossRight i j k j' k' x).eval := by
  simp only [LabelledDrawing.interpret,
    ScopedDiagram.eval, TrivalentVertex.expand, Diagram.eval, singleton_dot]

private abbrev splitBottom (ga : ConjEmbedding A G) (ad : ConjEmbedding D A)
    (df : ConjEmbedding F D) :=
  Diagram.vertical (Diagram.splitUp (R := Complex) (ga.comp ad) df)
    (Diagram.horizontal (Diagram.splitUp ga ad) (Diagram.id (Word.up df)))

private abbrev mergeTop (gc : ConjEmbedding C G) (ce : ConjEmbedding E C)
    (ef : ConjEmbedding F E) :=
  Diagram.vertical (Diagram.horizontal (Diagram.mergeUp (R := Complex) gc ce)
    (Diagram.id (Word.up ef))) (Diagram.mergeUp (gc.comp ce) ef)

private abbrev framed
    {ga : ConjEmbedding A G} {ad : ConjEmbedding D A} {df : ConjEmbedding F D}
    {gc : ConjEmbedding C G} {ce : ConjEmbedding E C} {ef : ConjEmbedding F E}
    (d : Diagram Complex (word ga ad df) (word gc ce ef)) (z : GA G) : GA G :=
  MonoidAlgebra.ofCoeff
    (((splitBottom ga ad df).vertical (d.vertical (mergeTop gc ce ef))).eval.toLinearMap
      (MonoidAlgebra.coeff z))

private abbrev framedDrawing
    {ga : ConjEmbedding A G} {ad : ConjEmbedding D A} {df : ConjEmbedding F D}
    {gc : ConjEmbedding C G} {ce : ConjEmbedding E C} {ef : ConjEmbedding F E}
    (d : LabelledDrawing Complex (word ga ad df) (word gc ce ef)) (z : GA G) : GA G :=
  MonoidAlgebra.ofCoeff
    (((split (ga.comp ad) df).vertical ((split ga ad).horizontal (straight df)) |>.interpret.eval).vertical
      (d.interpret.eval.vertical
        ((((merge gc ce).horizontal (straight ef)).vertical (merge (gc.comp ce) ef)).interpret.eval))
      |>.toLinearMap (MonoidAlgebra.coeff z))

private theorem framed_eq
    {ga : ConjEmbedding A G} {ad : ConjEmbedding D A} {df : ConjEmbedding F D}
    {gc : ConjEmbedding C G} {ce : ConjEmbedding E C} {ef : ConjEmbedding F E}
    (d : Diagram Complex (word ga ad df) (word gc ce ef))
    (w : LabelledDrawing Complex (word ga ad df) (word gc ce ef))
    (h : w.interpret.eval = d.eval) (z : GA G) :
    framedDrawing w z = framed d z := by
  unfold framedDrawing framed
  rw [h]
  rfl

private theorem dotValue_single {P Q : Subgroup V} {i j : ConjEmbedding Q P} (x : Dot i j) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (Finsupp.single x (1 : Complex))) =
      MonoidAlgebra.single x.element 1 := by
  rw [Finsupp.mapDomain_single, MonoidAlgebra.ofCoeff_single]

private theorem along_single {P Q : Subgroup V} (i : ConjEmbedding Q P) (x : Q) :
    MonoidAlgebra.mapDomainAlgHom Complex Complex i.toHom (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single (i.toHom x) 1 :=
  MonoidAlgebra.mapDomain_single


section Boundary
variable (ga : ConjEmbedding A G) (ad : ConjEmbedding D A) (df : ConjEmbedding F D)
variable (gc : ConjEmbedding C G) (ce : ConjEmbedding E C) (ef : ConjEmbedding F E)

private abbrev dLeft (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) :=
  Diagram.vertical (dCrossLeft ga ad gb bd df x₁)
    (Diagram.vertical (dCrossRight gb bd df be ef x₂) (dCrossLeft gb be gc ce ef x₃))

private abbrev wLeft (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) :=
  LabelledDrawing.vertical (wCrossLeft ga ad gb bd df (Finsupp.single x₁ 1))
    (LabelledDrawing.vertical (wCrossRight gb bd df be ef (Finsupp.single x₂ 1)) (wCrossLeft gb be gc ce ef (Finsupp.single x₃ 1)))

private abbrev leftMultiplier (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) : G :=
  x₁.element * gb.toHom x₂.element * x₃.element

private theorem leftDrawing_eval (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) :
    (wLeft ga ad df gc ce ef gb bd be x₁ x₂ x₃).interpret.eval = (dLeft ga ad df gc ce ef gb bd be x₁ x₂ x₃).eval := by
  change Biset.Hom.vertical _ (Biset.Hom.vertical _ _) =
    Biset.Hom.vertical _ (Biset.Hom.vertical _ _)
  rw [crossLeft_eval, crossRight_eval, crossLeft_eval]

private abbrev dRight (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) :=
  Diagram.vertical (dCrossRight ga ad df ab bf y₁)
    (Diagram.vertical (dCrossLeft ga ab gc cb bf y₂) (dCrossRight gc cb bf ce ef y₃))

private abbrev wRight (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) :=
  LabelledDrawing.vertical (wCrossRight ga ad df ab bf (Finsupp.single y₁ 1))
    (LabelledDrawing.vertical (wCrossLeft ga ab gc cb bf (Finsupp.single y₂ 1)) (wCrossRight gc cb bf ce ef (Finsupp.single y₃ 1)))

private abbrev rightMultiplier (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) : G :=
  ga.toHom y₁.element * y₂.element * gc.toHom y₃.element

private theorem rightDrawing_eval (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) :
    (wRight ga ad df gc ce ef ab cb bf y₁ y₂ y₃).interpret.eval = (dRight ga ad df gc ce ef ab cb bf y₁ y₂ y₃).eval := by
  change Biset.Hom.vertical _ (Biset.Hom.vertical _ _) =
    Biset.Hom.vertical _ (Biset.Hom.vertical _ _)
  rw [crossRight_eval, crossLeft_eval, crossRight_eval]

end Boundary

section Representatives
variable (a d df c e ef : V)
variable (ha : conj a A ≤ G) (hd : conj d D ≤ A) (hdf : conj df F ≤ D)
variable (hc : conj c C ≤ G) (he : conj e E ≤ C) (hef : conj ef F ≤ E)

local notation "ga" => embed a ha
local notation "ad" => embed d hd
local notation "dfE" => embed df hdf
local notation "gc" => embed c hc
local notation "ce" => embed e he
local notation "efE" => embed ef hef

private theorem left_evaluation (gb : ConjEmbedding B G) (bd : ConjEmbedding D B)
    (be : ConjEmbedding E B) (x₁ : Dot ((ga).comp ad) (gb.comp bd))
    (x₂ : Dot (bd.comp dfE) (be.comp efE)) (x₃ : Dot (gb.comp be) ((gc).comp ce))
    (z : GA G) :
    framed (dLeft ga ad dfE gc ce efE gb bd be x₁ x₂ x₃) z =
      z * MonoidAlgebra.single (leftMultiplier ga ad dfE gc ce efE gb bd be x₁ x₂ x₃) 1 := by
  obtain ⟨_, _, hAll, _, _, hLeft, _⟩ :=
    ThreeInductionCrossingMultipliers G A D F C E a d df c e ef
      (fun x => ((ga).toHom x).property) (fun x => ((ad).toHom x).property)
      (fun x => ((dfE).toHom x).property) (fun x => ((gc).toHom x).property)
      (fun x => ((ce).toHom x).property) (fun x => ((efE).toHom x).property)
  let w := wLeft ga ad dfE gc ce efE gb bd be x₁ x₂ x₃
  have atOne := (hLeft B gb bd be (Finsupp.single x₁ 1) (Finsupp.single x₂ 1)
    (Finsupp.single x₃ 1)).1
  have hz : framedDrawing w z = z * framedDrawing w 1 := hAll w z
  have product : framedDrawing w 1 =
      MonoidAlgebra.single (leftMultiplier ga ad dfE gc ce efE gb bd be x₁ x₂ x₃) 1 := by
    simpa only [dotValue_single, along_single, MonoidAlgebra.single_mul_single, one_mul]
      using atOne
  rw [← framed_eq _ w (leftDrawing_eval ga ad dfE gc ce efE gb bd be x₁ x₂ x₃), hz, product]

private theorem right_evaluation (ab : ConjEmbedding B A) (cb : ConjEmbedding B C)
    (bf : ConjEmbedding F B) (y₁ : Dot ((ad).comp dfE) (ab.comp bf))
    (y₂ : Dot ((ga).comp ab) ((gc).comp cb)) (y₃ : Dot (cb.comp bf) ((ce).comp efE))
    (z : GA G) :
    framed (dRight ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃) z =
      z * MonoidAlgebra.single (rightMultiplier ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃) 1 := by
  obtain ⟨_, _, hAll, _, _, _, hRight⟩ :=
    ThreeInductionCrossingMultipliers G A D F C E a d df c e ef
      (fun x => ((ga).toHom x).property) (fun x => ((ad).toHom x).property)
      (fun x => ((dfE).toHom x).property) (fun x => ((gc).toHom x).property)
      (fun x => ((ce).toHom x).property) (fun x => ((efE).toHom x).property)
  let w := wRight ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃
  have atOne := (hRight B ab cb bf (Finsupp.single y₁ 1) (Finsupp.single y₂ 1)
    (Finsupp.single y₃ 1)).1
  have hz : framedDrawing w z = z * framedDrawing w 1 := hAll w z
  have product : framedDrawing w 1 =
      MonoidAlgebra.single (rightMultiplier ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃) 1 := by
    simpa only [dotValue_single, along_single, MonoidAlgebra.single_mul_single, one_mul]
      using atOne
  rw [← framed_eq _ w (rightDrawing_eval ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃), hz, product]

private theorem evaluation_eq
    (l r : LabelledDrawing Complex (word ga ad dfE) (word gc ce efE))
    (h : framedDrawing l 1 = framedDrawing r 1) : l.interpret.eval = r.interpret.eval := by
  obtain ⟨_, _, _, hEq, _, _, _⟩ :=
    ThreeInductionCrossingMultipliers G A D F C E a d df c e ef
      (fun x => ((ga).toHom x).property) (fun x => ((ad).toHom x).property)
      (fun x => ((dfE).toHom x).property) (fun x => ((gc).toHom x).property)
      (fun x => ((ce).toHom x).property) (fun x => ((efE).toHom x).property)
  exact (hEq l r).mpr h

end Representatives
end Evaluation

end ExtremalThreeInduction

open MackeyDiagrams ExtremalThreeInduction

theorem ParabolicExtremalThreeInductionRegions : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (X : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
let conjugate := fun (r : U) (H : Subgroup U) =>
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj r)) H
let embed := fun {H K : Subgroup U} (r : U) (h : conjugate r H ≤ K) =>
  MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := K) r
    (fun x => h ⟨(x : U), x.property, rfl⟩)
∀ (G A D F C E : Subgroup U),
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  ∀ (a d df c e ef : U)
    (ha : conjugate a A ≤ G) (hd : conjugate d D ≤ A) (hdf : conjugate df F ≤ D)
    (hc : conjugate c C ≤ G) (he : conjugate e E ≤ C) (hef : conjugate ef F ≤ E)
    (p : G),
  let u := a * d * df
  let v := c * e * ef
  u⁻¹ * (p : U) * v ∈ Subgroup.centralizer (F : Set U) →
  let ga := embed a ha
  let ad := embed d hd
  let dfEmbedding := embed df hdf
  let gc := embed c hc
  let ce := embed e he
  let efEmbedding := embed ef hef
  let bottomPair := MackeyDiagrams.ConjEmbedding.comp ga ad
  let topPair := MackeyDiagrams.ConjEmbedding.comp gc ce
  let word := fun {P Q S T : Subgroup U}
      (i : MackeyDiagrams.ConjEmbedding Q P) (j : MackeyDiagrams.ConjEmbedding S Q)
      (k : MackeyDiagrams.ConjEmbedding T S) =>
    MackeyDiagrams.Word.tensor
      (MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up i) (MackeyDiagrams.Word.up j))
      (MackeyDiagrams.Word.up k)
  let bottom := word ga ad dfEmbedding
  let top := word gc ce efEmbedding
  let splitBottom :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.splitUp (R := Complex) bottomPair dfEmbedding)
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.splitUp ga ad)
        (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up dfEmbedding)))
  let mergeTop :=
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.mergeUp (R := Complex) gc ce)
        (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up efEmbedding)))
      (MackeyDiagrams.Diagram.mergeUp topPair efEmbedding)
  let BoundaryDiagram := MackeyDiagrams.Diagram Complex bottom top
  let realizes := fun (diagram : BoundaryDiagram) =>
    ∀ z : MonoidAlgebra Complex G,
      MonoidAlgebra.ofCoeff
        (MackeyDiagrams.Biset.Hom.toLinearMap
          (MackeyDiagrams.Diagram.eval
            (MackeyDiagrams.Diagram.vertical splitBottom
              (MackeyDiagrams.Diagram.vertical diagram mergeTop)))
          (MonoidAlgebra.coeff z)) = z * MonoidAlgebra.single p (1 : Complex)
  let crossing := fun {P Q Q' S : Subgroup U}
      (i : MackeyDiagrams.ConjEmbedding Q P) (j : MackeyDiagrams.ConjEmbedding S Q)
      (i' : MackeyDiagrams.ConjEmbedding Q' P) (j' : MackeyDiagrams.ConjEmbedding S Q')
      (dot : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp i j)
        (MackeyDiagrams.ConjEmbedding.comp i' j')) =>
    MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.mergeUp (R := Complex) i j)
      (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.upDot dot)
        (MackeyDiagrams.Diagram.splitUp i' j'))
  let crossLeft := fun {P Q Q' S T : Subgroup U}
      (i : MackeyDiagrams.ConjEmbedding Q P) (j : MackeyDiagrams.ConjEmbedding S Q)
      (i' : MackeyDiagrams.ConjEmbedding Q' P) (j' : MackeyDiagrams.ConjEmbedding S Q')
      (k : MackeyDiagrams.ConjEmbedding T S)
      (dot : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp i j)
        (MackeyDiagrams.ConjEmbedding.comp i' j')) =>
    MackeyDiagrams.Diagram.horizontal (crossing i j i' j' dot)
      (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up k))
  let crossRight := fun {P Q S S' T : Subgroup U}
      (i : MackeyDiagrams.ConjEmbedding Q P) (j : MackeyDiagrams.ConjEmbedding S Q)
      (k : MackeyDiagrams.ConjEmbedding T S)
      (j' : MackeyDiagrams.ConjEmbedding S' Q) (k' : MackeyDiagrams.ConjEmbedding T S')
      (dot : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp j k)
        (MackeyDiagrams.ConjEmbedding.comp j' k')) =>
    MackeyDiagrams.Diagram.vertical
      (MackeyDiagrams.Diagram.associate (MackeyDiagrams.Word.up i)
        (MackeyDiagrams.Word.up j) (MackeyDiagrams.Word.up k))
      (MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up i))
          (crossing j k j' k' dot))
        (MackeyDiagrams.Diagram.unassociate (MackeyDiagrams.Word.up i)
          (MackeyDiagrams.Word.up j') (MackeyDiagrams.Word.up k')))
  let leftLabelling := fun (B : Subgroup U) (rGB rBD rBE : U)
      (holds : U → U → U → BoundaryDiagram → Prop) =>
    parabolic B ∧
    ∃ (hGB : conjugate rGB B ≤ G) (hBD : conjugate rBD D ≤ B) (hBE : conjugate rBE E ≤ B),
      let gb := embed rGB hGB
      let bd := embed rBD hBD
      let be := embed rBE hBE
      ∃ (x₁ : MackeyDiagrams.Dot bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd))
        (x₂ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp bd dfEmbedding)
          (MackeyDiagrams.ConjEmbedding.comp be efEmbedding))
        (x₃ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp gb be) topPair),
        holds (x₁.element : U) (x₂.element : U) (x₃.element : U)
          (MackeyDiagrams.Diagram.vertical (crossLeft ga ad gb bd dfEmbedding x₁)
            (MackeyDiagrams.Diagram.vertical (crossRight gb bd dfEmbedding be efEmbedding x₂)
              (crossLeft gb be gc ce efEmbedding x₃)))
  let rightLabelling := fun (B' : Subgroup U) (rAB' rCB' rB'F : U)
      (holds : U → U → U → BoundaryDiagram → Prop) =>
    parabolic B' ∧
    ∃ (hAB' : conjugate rAB' B' ≤ A) (hCB' : conjugate rCB' B' ≤ C)
      (hB'F : conjugate rB'F F ≤ B'),
      let ab' := embed rAB' hAB'
      let cb' := embed rCB' hCB'
      let b'f := embed rB'F hB'F
      ∃ (y₁ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp ad dfEmbedding)
          (MackeyDiagrams.ConjEmbedding.comp ab' b'f))
        (y₂ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp ga ab')
          (MackeyDiagrams.ConjEmbedding.comp gc cb'))
        (y₃ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp cb' b'f)
          (MackeyDiagrams.ConjEmbedding.comp ce efEmbedding)),
        holds (y₁.element : U) (y₂.element : U) (y₃.element : U)
          (MackeyDiagrams.Diagram.vertical (crossRight ga ad dfEmbedding ab' b'f y₁)
            (MackeyDiagrams.Diagram.vertical (crossLeft ga ab' gc cb' b'f y₂)
              (crossRight gc cb' b'f ce efEmbedding y₃)))
  let leftRegions : Set (Subgroup U) := {H |
    ∃ (B : Subgroup U) (rGB rBD rBE : U),
      leftLabelling B rGB rBD rBE (fun x₁ _ _ diagram =>
        H = conjugate (x₁ * rGB) B ∧ realizes diagram)}
  let rightRegions : Set (Subgroup U) := {H |
    ∃ (B' : Subgroup U) (rAB' rCB' rB'F : U),
      rightLabelling B' rAB' rCB' rB'F (fun y₁ _ _ diagram =>
        H = conjugate (a * y₁ * rAB') B' ∧ realizes diagram)}
  let Bmin := conjugate (a * d) D ⊔ conjugate ((p : U) * c * e) E
  let Bmax := conjugate a A ⊓ conjugate ((p : U) * c) C
  IsLeast leftRegions Bmin ∧ IsGreatest rightRegions Bmax ∧
    leftLabelling Bmin 1 (a * d) ((p : U) * c * e) (fun x₁ x₂ x₃ left =>
      x₁ = 1 ∧ x₂ = 1 ∧ x₃ = (p : U) ∧ realizes left ∧
      rightLabelling Bmax a⁻¹ (c⁻¹ * (p : U)⁻¹) u (fun y₁ y₂ y₃ right =>
        y₁ = 1 ∧ y₂ = (p : U) ∧ y₃ = 1 ∧ realizes right ∧
        MackeyDiagrams.Diagram.eval left = MackeyDiagrams.Diagram.eval right))
) :=
(by
  classical
  -- Xiao, Proposition 8.5, archived original PDF pp. 37–38 and revised PDF
  -- pp. 39–40, with the singleton multiplier formulas from Lemma 6.1.
  -- This endpoint has no verified Alphabeta Math counterpart with numbered steps.
  intro finitary U blockSym parabolic conjugate embedding G A D F C E
    _hG hA hD _hF hC hE a d df c e ef ha hd hdf hc he hef p u v hp
    ga ad dfE gc ce efE bottomPair topPair boundaryWord bottom top
    splitBottomDiagram mergeTopDiagram BoundaryDiagram realizes crossing crossLeft crossRight
    leftLabelling rightLabelling leftRegions rightRegions Bmin Bmax
  have pAction (f : F) :
      u * (f : U) * u⁻¹ = ((p : U) * v) * (f : U) * ((p : U) * v)⁻¹ := by
    have hf := Subgroup.mem_centralizer_iff.mp hp f f.property
    change (f : U) * (u⁻¹ * p * v) = (u⁻¹ * p * v) * f at hf
    calc
      u * (f : U) * u⁻¹ = u * ((f : U) * (u⁻¹ * p * v)) * ((p : U) * v)⁻¹ := by group
      _ = u * ((u⁻¹ * p * v) * (f : U)) * ((p : U) * v)⁻¹ := by rw [hf]
      _ = _ := by group
  -- Join and intersection closure. The block suppliers require a common cover.
  -- Pad with singleton blocks on the union, then omit empty intersection cells.
  have minParabolic : parabolic Bmin :=
    parabolic_sup (parabolic_conj hD (a * d)) (parabolic_conj hE ((p : U) * c * e))
  have maxParabolic : parabolic Bmax :=
    parabolic_inf (parabolic_conj hA a) (parabolic_conj hC ((p : U) * c))
  have minInG : Bmin ≤ G := by
    apply sup_le
    · change conj (a * d) D ≤ G
      rw [← conj_compose]
      exact (conj_mono a hd).trans ha
    · change conj ((p : U) * c * e) E ≤ G
      rw [mul_assoc, ← conj_compose, ← conj_compose]
      exact (conj_mono p ((conj_mono c he).trans hc)).trans (conj_inner p.property).le
  have hGB : conjugate 1 Bmin ≤ G := by
    change conj 1 Bmin ≤ G
    rw [conj_one]
    exact minInG
  have hBD : conjugate (a * d) D ≤ Bmin := le_sup_left
  have hBE : conjugate ((p : U) * c * e) E ≤ Bmin := le_sup_right
  have hAB : conjugate a⁻¹ Bmax ≤ A :=
    undo_conj (show Bmax ≤ conjugate a A from inf_le_left)
  have hCB : conjugate (c⁻¹ * (p : U)⁻¹) Bmax ≤ C := by
    rw [← mul_inv_rev]
    exact undo_conj (show Bmax ≤ conjugate ((p : U) * c) C from inf_le_right)
  have hBF : conjugate u F ≤ Bmax := by
    apply le_inf
    · change conj (a * d * df) F ≤ conj a A
      rw [mul_assoc, ← conj_compose, ← conj_compose]
      exact conj_mono a ((conj_mono d hdf).trans hd)
    · have htop : conjugate ((p : U) * v) F ≤ conjugate ((p : U) * c) C := by
        change conj ((p : U) * (c * e * ef)) F ≤ conj ((p : U) * c) C
        rw [show ((p : U) * (c * e * ef)) = ((p : U) * c) * (e * ef) by group,
          ← conj_compose, ← conj_compose]
        exact conj_mono ((p : U) * c) ((conj_mono e hef).trans he)
      exact (conj_eq_of_action pAction).le.trans htop
  let gb := embed 1 hGB
  let bd := embed (a * d) hBD
  let be := embed ((p : U) * c * e) hBE
  let ab := embed a⁻¹ hAB
  let cb := embed (c⁻¹ * (p : U)⁻¹) hCB
  let bf := embed u hBF
  -- Attainment. The outside and middle dots use the source representatives.
  -- The left middle and upper right eligibility checks use pAction pointwise on F.
  let x₁ : Dot bottomPair (gb.comp bd) :=
    mkDot (1 : G) (comp_conj (hr := ha) (hs := hd))
      (comp_conj (hr := hGB) (hs := hBD)) (fun _ => by simp)
  let x₂ : Dot (bd.comp dfE) (be.comp efE) :=
    mkDot (1 : Bmin) (comp_conj (hr := hBD) (hs := hdf))
      (comp_conj (hr := hBE) (hs := hef)) (fun f => by
        simp only [Subgroup.coe_one, one_mul]
        simpa only [u, v, mul_assoc] using pAction f)
  let x₃ : Dot (gb.comp be) topPair :=
    mkDot p (comp_conj (hr := hGB) (hs := hBE)) (comp_conj (hr := hc) (hs := he))
      (fun _ => by simp only [one_mul, mul_assoc])
  let y₁ : Dot (ad.comp dfE) (ab.comp bf) :=
    mkDot (1 : A) (comp_conj (hr := hd) (hs := hdf)) (comp_conj (hr := hAB) (hs := hBF))
      (fun _ => by simp only [u, Subgroup.coe_one, one_mul]; group)
  let y₂ : Dot (ga.comp ab) (gc.comp cb) :=
    mkDot p (comp_conj (hr := ha) (hs := hAB)) (comp_conj (hr := hc) (hs := hCB))
      (fun _ => by group)
  let y₃ : Dot (cb.comp bf) (ce.comp efE) :=
    mkDot (1 : C) (comp_conj (hr := hCB) (hs := hBF)) (comp_conj (hr := he) (hs := hef))
      (fun f => by
        simp only [Subgroup.coe_one, one_mul]
        calc
          _ = (c⁻¹ * (p : U)⁻¹) * (u * (f : U) * u⁻¹) * (c⁻¹ * (p : U)⁻¹)⁻¹ := by group
          _ = _ := by rw [pAction f]; dsimp only [v]; group)
  let left := dLeft ga ad dfE gc ce efE gb bd be x₁ x₂ x₃
  let right := dRight ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃
  have leftRealizes : realizes left := by
    intro z
    change framed left z = _
    rw [left_evaluation a d df c e ef ha hd hdf hc he hef gb bd be x₁ x₂ x₃ z]
    have hx : leftMultiplier ga ad dfE gc ce efE gb bd be x₁ x₂ x₃ = p := by
      change (1 : G) * gb.toHom 1 * p = p
      simp
    rw [hx]
  have rightRealizes : realizes right := by
    intro z
    change framed right z = _
    rw [right_evaluation a d df c e ef ha hd hdf hc he hef ab cb bf y₁ y₂ y₃ z]
    have hy : rightMultiplier ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃ = p := by
      change ga.toHom 1 * p * gc.toHom 1 = p
      simp
    rw [hy]
  have sameEval : left.eval = right.eval := by
    let l := wLeft ga ad dfE gc ce efE gb bd be x₁ x₂ x₃
    let r := wRight ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃
    have hl : l.interpret.eval = left.eval := leftDrawing_eval ga ad dfE gc ce efE gb bd be x₁ x₂ x₃
    have hr : r.interpret.eval = right.eval := rightDrawing_eval ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃
    rw [← hl, ← hr]
    apply evaluation_eq a d df c e ef ha hd hdf hc he hef
    rw [framed_eq left l hl, framed_eq right r hr]
    exact (leftRealizes 1).trans (rightRealizes 1).symm
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨Bmin, 1, a * d, (p : U) * c * e, minParabolic, hGB, hBD, hBE, x₁, x₂, x₃, ?_, leftRealizes⟩
    change Bmin = conj ((1 : U) * 1) Bmin
    rw [one_mul, conj_one]
  · intro H hH
    obtain ⟨B, r, s, t, _, hr, hs, ht, x, y, z, hRegion, hRealizes⟩ := hH
    let ir := embed r hr
    let js := embed s hs
    let it := embed t ht
    let diagram := dLeft ga ad dfE gc ce efE ir js it x y z
    let μ := leftMultiplier ga ad dfE gc ce efE ir js it x y z
    change ∀ w : GA G, framed diagram w = w * MonoidAlgebra.single p 1 at hRealizes
    have hFormula : framed diagram 1 = (1 : GA G) * MonoidAlgebra.single μ 1 :=
      left_evaluation a d df c e ef ha hd hdf hc he hef ir js it x y z 1
    have hEval : MonoidAlgebra.single p (1 : Complex) = MonoidAlgebra.single μ 1 :=
      by simpa only [one_mul] using (hRealizes 1).symm.trans hFormula
    have hProduct := MonoidAlgebra.single_left_injective (one_ne_zero : (1 : Complex) ≠ 0) hEval
    have hValue := congrArg (fun q : G => (q : U)) hProduct
    change (p : U) = _ at hValue
    simp only [μ, ir, leftMultiplier, Subgroup.coe_mul, ConjEmbedding.ofConjugator_apply] at hValue
    change H = conj ((x.element : U) * r) B at hRegion
    rw [hRegion]
    -- The first and third dots compare conjugation actions. In the second bound,
    -- the image of y lies in B, so its conjugation preserves the region.
    change conj (a * d) D ⊔ conj ((p : U) * c * e) E ≤ conj ((x.element : U) * r) B
    apply sup_le
    · rw [dot_conj x (comp_conj (hr := ha) (hs := hd)) (comp_conj (hr := hr) (hs := hs))]
      rw [← mul_assoc, ← conj_compose]
      exact conj_mono _ hs
    · have eDot := dot_conj z (comp_conj (hr := hr) (hs := ht)) (comp_conj (hr := hc) (hs := he))
      have key : ((p : U) * c * e) =
          ((x.element : U) * r * y.element * r⁻¹) * (z.element * (c * e)) := by
        rw [hValue]
        group
      calc
        conj ((p : U) * c * e) E =
            conj ((x.element : U) * r * y.element * r⁻¹)
              (conj ((z.element : U) * (c * e)) E) := by rw [conj_compose, key]
        _ = conj ((x.element : U) * r) (conj (y.element : U) (conj t E)) := by
          rw [← eDot]
          simp only [conj_compose]
          congr 1
          group
        _ ≤ conj ((x.element : U) * r) B :=
          conj_mono _ ((conj_mono _ ht).trans (conj_inner y.element.property).le)
  · refine ⟨Bmax, a⁻¹, c⁻¹ * (p : U)⁻¹, u, maxParabolic, hAB, hCB, hBF, y₁, y₂, y₃, ?_, rightRealizes⟩
    change Bmax = conj (a * (1 : U) * a⁻¹) Bmax
    rw [mul_one, mul_inv_cancel, conj_one]
  · intro H hH
    obtain ⟨B, r, s, t, _, hr, hs, ht, x, y, z, hRegion, hRealizes⟩ := hH
    let ir := embed r hr
    let js := embed s hs
    let it := embed t ht
    let diagram := dRight ga ad dfE gc ce efE ir js it x y z
    let μ := rightMultiplier ga ad dfE gc ce efE ir js it x y z
    change ∀ w : GA G, framed diagram w = w * MonoidAlgebra.single p 1 at hRealizes
    have hFormula : framed diagram 1 = (1 : GA G) * MonoidAlgebra.single μ 1 :=
      right_evaluation a d df c e ef ha hd hdf hc he hef ir js it x y z 1
    have hEval : MonoidAlgebra.single p (1 : Complex) = MonoidAlgebra.single μ 1 :=
      by simpa only [one_mul] using (hRealizes 1).symm.trans hFormula
    have hProduct := MonoidAlgebra.single_left_injective (one_ne_zero : (1 : Complex) ≠ 0) hEval
    have hValue := congrArg (fun q : G => (q : U)) hProduct
    change (p : U) = _ at hValue
    simp only [μ, rightMultiplier, Subgroup.coe_mul, ConjEmbedding.ofConjugator_apply] at hValue
    change H = conj (a * (x.element : U) * r) B at hRegion
    rw [hRegion]
    change conj (a * (x.element : U) * r) B ≤ conj a A ⊓ conj ((p : U) * c) C
    apply le_inf
    · calc
        conj (a * (x.element : U) * r) B = conj a (conj (x.element : U) (conj r B)) := by
          simp only [conj_compose, mul_assoc]
        _ ≤ conj a (conj (x.element : U) A) := conj_mono _ (conj_mono _ hr)
        _ = conj a A := by rw [conj_inner x.element.property]
    · have middle := dot_conj y (comp_conj (hr := ha) (hs := hr)) (comp_conj (hr := hc) (hs := hs))
      have htarget : conj ((p : U) * c * (z.element : U)⁻¹) C = conj ((p : U) * c) C := by
        rw [← conj_compose, conj_inner (C.inv_mem z.element.property)]
      calc
        conj (a * (x.element : U) * r) B =
            conj (a * (x.element : U) * a⁻¹) (conj (a * r) B) := by
          simp only [conj_compose]
          congr 1
          group
        _ = conj (a * (x.element : U) * a⁻¹) (conj ((y.element : U) * (c * s)) B) := by
          rw [middle]
        _ = conj ((p : U) * c * (z.element : U)⁻¹) (conj s B) := by
          simp only [conj_compose]
          congr 1
          rw [hValue]
          group
        _ ≤ conj ((p : U) * c) C := (conj_mono _ hs).trans htarget.le
  · exact ⟨minParabolic, hGB, hBD, hBE, x₁, x₂, x₃, rfl, rfl, rfl, leftRealizes,
      maxParabolic, hAB, hCB, hBF, y₁, y₂, y₃, rfl, rfl, rfl, rightRealizes, sameEval⟩)

#print axioms ParabolicExtremalThreeInductionRegions
