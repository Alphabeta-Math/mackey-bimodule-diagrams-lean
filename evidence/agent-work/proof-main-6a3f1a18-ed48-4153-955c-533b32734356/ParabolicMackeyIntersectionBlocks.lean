import MackeyDiagrams
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.ParabolicDoubleCosetRepresentatives

set_option maxHeartbeats 2000000

theorem ParabolicMackeyIntersectionBlocks : (∀ (X : Finset Nat) (r c : Nat) (A : Fin r → Finset ↥X) (B : Fin c → Finset ↥X),
  (∀ i, Finset.Nonempty (A i)) →
  (∀ j, Finset.Nonempty (B j)) →
  Pairwise (fun i i' => Disjoint (A i) (A i')) →
  Pairwise (fun j j' => Disjoint (B j) (B j')) →
  (∀ x : ↥X, ∃ i, x ∈ A i) →
  (∀ x : ↥X, ∃ j, x ∈ B j) →
  let G := Equiv.Perm ↥X
  let blockSym := fun S : Finset ↥X =>
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun x : ↥X => x ∈ S))
  let K : Subgroup G := iSup (fun i => blockSym (A i))
  let H : Subgroup G := iSup (fun j => blockSym (B j))
  ∀ σ : G,
    K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj σ)) H =
      iSup (fun i => iSup (fun j =>
        blockSym (A i ∩ Finset.map (Equiv.toEmbedding σ) (B j))))) :=
(by
  intro X r c A B nonemptyA nonemptyB disjointA disjointB coverA coverB G blockSym K H σ
  let point : ↥X ↪ Nat := ⟨Subtype.val, Subtype.val_injective⟩
  let extend : Equiv.Perm ↥X →* Equiv.Perm Nat :=
    Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X)
  have extend_injective : Function.Injective extend := Equiv.Perm.ofSubtype_injective
  let liftBlock (S : Finset ↥X) : Finset Nat := S.map point
  let blockNat (T : Finset Nat) : Subgroup (Equiv.Perm Nat) :=
    MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ T))
  -- Xiao, §7.2 after Prop. 7.3 (project PDF p. 30, published PDF p. 32),
  -- applies the conjugation and intersection formulas of Prop. 7.1.
  -- The registered formulas act on Nat, so extend by the identity outside X
  -- and identify each extended block factor there.
  have block_extension (S : Finset ↥X) :
      (blockSym S).map extend = blockNat (liftBlock S) := by
    have mem_lift (x : ↥X) : (x : Nat) ∈ liftBlock S ↔ x ∈ S :=
      Finset.mem_map' point
    have in_carrier {n : Nat} (hn : n ∈ liftBlock S) : n ∈ X := by
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hn
      exact x.property
    let e : ↥S ≃ ↥(liftBlock S) :=
      { toFun := fun x => ⟨x.val.val, (mem_lift x.val).mpr x.property⟩
        invFun := fun n =>
          ⟨⟨n.val, in_carrier n.property⟩, (mem_lift _).mp n.property⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
    have commute (g : Equiv.Perm ↥S) :
        extend (Equiv.Perm.ofSubtype g) = Equiv.Perm.ofSubtype (e.permCongr g) := by
      apply Equiv.ext
      intro n
      by_cases hn : n ∈ X
      · let x : ↥X := ⟨n, hn⟩
        rw [show extend (Equiv.Perm.ofSubtype g) n =
          ((Equiv.Perm.ofSubtype g) x : Nat) from
            Equiv.Perm.ofSubtype_apply_of_mem _ hn]
        by_cases hx : x ∈ S
        · rw [Equiv.Perm.ofSubtype_apply_of_mem g hx,
            Equiv.Perm.ofSubtype_apply_of_mem _ ((mem_lift x).mpr hx)]
          rfl
        · rw [Equiv.Perm.ofSubtype_apply_of_not_mem g hx,
            Equiv.Perm.ofSubtype_apply_of_not_mem _
              (fun h => hx ((mem_lift x).mp h))]
      · rw [show extend (Equiv.Perm.ofSubtype g) n = n from
          Equiv.Perm.ofSubtype_apply_of_not_mem _ hn,
          Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun h => hn (in_carrier h))]
    apply Subgroup.ext
    intro f
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨e.permCongr g, (commute g).symm⟩
    · rintro ⟨f, rfl⟩
      obtain ⟨g, rfl⟩ := e.permCongr.surjective f
      exact ⟨Equiv.Perm.ofSubtype g, ⟨g, rfl⟩, commute g⟩
  have lift_partition {ι : Type} (D : ι → Finset ↥X)
      (nonempty : ∀ i, (D i).Nonempty)
      (disjoint : Pairwise (fun i j => Disjoint (D i) (D j)))
      (cover : ∀ x : ↥X, ∃ i, x ∈ D i) :
      (∀ i, (liftBlock (D i)).Nonempty) ∧
        Pairwise (fun i j => Disjoint (liftBlock (D i)) (liftBlock (D j))) ∧
        (∀ n, n ∈ X ↔ ∃ i, n ∈ liftBlock (D i)) := by
    refine ⟨fun i => (nonempty i).map, ?_, ?_⟩
    · intro i j hij
      exact (Finset.disjoint_map point).mpr (disjoint hij)
    · intro n
      constructor
      · intro hn
        obtain ⟨i, hi⟩ := cover ⟨n, hn⟩
        exact ⟨i, Finset.mem_map_of_mem point hi⟩
      · rintro ⟨i, hi⟩
        obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hi
        exact x.property
  -- The project records no separate numbered Alphabeta Math proof here.
  -- Xiao's §7.2 steps 1–2 construct an ordered tableau representative.
  -- The intersection formula applies to every σ, so it uses the transported
  -- column blocks directly, without invoking ParabolicDoubleCosetRepresentatives.
  let C (j : Fin c) : Finset ↥X := (B j).map σ.toEmbedding
  have nonemptyC (j : Fin c) : (C j).Nonempty := (nonemptyB j).map
  have disjointC : Pairwise (fun i j => Disjoint (C i) (C j)) :=
    fun _ _ hij => (Finset.disjoint_map σ.toEmbedding).mpr (disjointB hij)
  have coverC (x : ↥X) : ∃ j, x ∈ C j := by
    obtain ⟨j, hj⟩ := coverB (σ.symm x)
    exact ⟨j, Finset.mem_map_equiv.mpr hj⟩
  obtain ⟨nonemptyA', disjointA', coverA'⟩ :=
    lift_partition A nonemptyA disjointA coverA
  obtain ⟨nonemptyB', disjointB', _⟩ :=
    lift_partition B nonemptyB disjointB coverB
  obtain ⟨nonemptyC', disjointC', coverC'⟩ :=
    lift_partition C nonemptyC disjointC coverC
  -- The conjugation supplier requires a finitary permutation of Nat.
  -- Every moved point of the extension lies in the finite set X.
  have finitary : extend σ ∈ Subgroup.closure {τ : Equiv.Perm Nat | τ.IsSwap} := by
    apply mem_closure_isSwap'.mpr
    apply X.finite_toSet.subset
    intro n hn
    by_contra hnX
    exact hn (Equiv.Perm.ofSubtype_apply_of_not_mem σ hnX)
  have image_block (j : Fin c) :
      (liftBlock (B j)).image (extend σ) = liftBlock (C j) := by
    calc
      _ = (liftBlock (B j)).map (extend σ).toEmbedding :=
        (Finset.map_eq_image _ _).symm
      _ = _ := by
        change ((B j).map point).map (extend σ).toEmbedding =
          ((B j).map σ.toEmbedding).map point
        rw [Finset.map_map, Finset.map_map]
        have commute : point.trans (extend σ).toEmbedding = σ.toEmbedding.trans point :=
          Function.Embedding.ext fun x => Equiv.Perm.ofSubtype_apply_coe σ x
        rw [commute]
  have map_conj :
      extend.comp (MulAut.conj σ).toMonoidHom =
        (MulAut.conj (extend σ)).toMonoidHom.comp extend := by
    apply MonoidHom.ext
    intro τ
    change extend (σ * τ * σ⁻¹) = extend σ * extend τ * (extend σ)⁻¹
    simp only [map_mul, map_inv]
  have extended_conjugate :
      (Subgroup.map (MulAut.conj σ).toMonoidHom H).map extend =
        iSup (fun j => blockNat (liftBlock (C j))) := by
    change ((iSup (fun j => blockSym (B j))).map (MulAut.conj σ).toMonoidHom).map extend = _
    rw [Subgroup.map_map, map_conj, ← Subgroup.map_map]
    simp only [Subgroup.map_iSup (f := extend), block_extension]
    have conjugate := FiniteParabolicConjugateBlocks
      (fun j => liftBlock (B j)) nonemptyB' disjointB' ⟨extend σ, finitary⟩
    change Subgroup.map (MulAut.conj (extend σ)).toMonoidHom
        (iSup (fun j => blockNat (liftBlock (B j)))) =
      iSup (fun j => blockNat ((liftBlock (B j)).image (extend σ))) at conjugate
    simpa only [image_block] using conjugate
  -- Apply the registered intersection formula after conjugation, then
  -- return to Sym(X) by injectivity of extension.
  have intersection := FiniteParabolicIntersectionBlocks X
    (fun i => liftBlock (A i)) (fun j => liftBlock (C j))
    nonemptyA' nonemptyC' disjointA' disjointC' coverA' coverC'
  change (iSup (fun i => blockNat (liftBlock (A i)))) ⊓
      (iSup (fun j => blockNat (liftBlock (C j)))) =
    iSup (fun i => iSup (fun j => blockNat (liftBlock (A i) ∩ liftBlock (C j)))) at intersection
  apply Subgroup.map_injective extend_injective
  rw [Subgroup.map_inf _ _ extend extend_injective, extended_conjugate]
  change (iSup (fun i => blockSym (A i))).map extend ⊓
      iSup (fun j => blockNat (liftBlock (C j))) =
    (iSup (fun i => iSup (fun j => blockSym (A i ∩ C j)))).map extend
  simp only [Subgroup.map_iSup, block_extension]
  have lift_inter (S T : Finset ↥X) :
      liftBlock (S ∩ T) = liftBlock S ∩ liftBlock T := Finset.map_inter S T
  simpa only [lift_inter] using intersection)
