import MackeyDiagrams
import Proofs.GeneralizedMackeyDecomposition
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.ParabolicMackeyIntersectionBlocks
import Proofs.ProductParabolicDoubleCosets
namespace ParabolicMackeyAssembly

universe v

private abbrev P := Equiv.Perm Nat
private abbrev conj {U : Type} [Group U] (p : U) := MulAut.conj p
private abbrev conjugate {U : Type} [Group U] (p : U) (S : Subgroup U) :=
  S.map (conj p).toMonoidHom
private abbrev blockSym (S : Finset Nat) : Subgroup P :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
private abbrev forward {U : Type} [Group U] {S T : Subgroup U}
    (p : U) (hp : conjugate p S ≤ T) : S →* T :=
  (Subgroup.inclusion hp).comp (MonoidHom.subgroupMap (conj p).toMonoidHom S)
private abbrev backward {U : Type} [Group U] {S T : Subgroup U}
    (p : U) (hp : T ≤ conjugate p S) : T →* S :=
  (MulEquiv.subgroupMap (conj p) S).symm.toMonoidHom.comp (Subgroup.inclusion hp)

private theorem backward_val {U : Type} [Group U] {S T : Subgroup U}
    (p : U) (hp : T ≤ conjugate p S) (t : T) :
    (backward p hp t : U) = p⁻¹ * (t : U) * p := by
  exact MulAut.conj_inv_apply p (t : U)

private abbrev indices {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (i : Fin g) :=
  Finset.univ.filter (fun a => A a ⊆ D i)

private abbrev blockIndex {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (i : Fin g) :=
  Finset.orderIsoOfFin (indices D A i) rfl

private abbrev part {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (i : Fin g) (a : Fin (indices D A i).card) :=
  (A ((blockIndex D A i) a).val).subtype (fun n => n ∈ D i)

private theorem restrictedPartition {g r : Nat} (D : Fin g → Finset Nat)
    (A : Fin r → Finset Nat) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (ha : ∀ a, (A a).Nonempty) (hda : Pairwise (fun a b => Disjoint (A a) (A b)))
    (href : ∀ a, ∃ i, A a ⊆ D i) (hcover : ∀ i x, x ∈ D i → ∃ a, x ∈ A a)
    (i : Fin g) :
    (∀ a, (part D A i a).Nonempty) ∧
      Pairwise (fun a b => Disjoint (part D A i a) (part D A i b)) ∧
      ∀ x : ↥(D i), ∃ a, x ∈ part D A i a := by
  let e := blockIndex D A i
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := ha (e a).val
    exact ⟨⟨x, (Finset.mem_filter.mp (e a).property).2 hx⟩, Finset.mem_subtype.mpr hx⟩
  · intro a b hab
    have hne : (e a).val ≠ (e b).val := fun h => hab (e.injective (Subtype.ext h))
    exact Finset.disjoint_left.mpr fun x hx hy =>
      Finset.disjoint_left.mp (hda hne) (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hy)
  · intro x
    obtain ⟨a, hxa⟩ := hcover i x.val x.property
    obtain ⟨j, hj⟩ := href a
    have hij : i = j := by
      by_contra h
      exact Finset.disjoint_left.mp (hd h) x.property (hj hxa)
    subst j
    let b : ↥(indices D A i) := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    refine ⟨e.symm b, Finset.mem_subtype.mpr ?_⟩
    change x.val ∈ A (e (e.symm b)).val
    rw [e.apply_symm_apply]
    exact hxa

private theorem productFinitary (X : Finset Nat) {g : Nat} (D : Fin g → Finset Nat)
    (hD : ∀ i, D i ⊆ X) (s : P) (hs : s ∈ iSup (fun i => blockSym (D i))) :
    s ∈ Subgroup.closure {p : P | p.IsSwap} := by
  have hf : ∀ x, x ∉ X → s x = x := by
    refine Subgroup.iSup_induction _ (C := fun p : P => ∀ x, x ∉ X → p x = x) hs ?_ ?_ ?_
    · rintro i _ ⟨p, rfl⟩ x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem p (fun hxD => hx (hD i hxD))
    · exact fun _ _ => rfl
    · intro p q hp hq x hx
      change p (q x) = x
      rw [hq x hx, hp x hx]
  exact mem_closure_isSwap'.mpr (X.finite_toSet.subset fun x hx => by
    by_contra hn
    exact hx (hf x hn))

private theorem intersection (X : Finset Nat) {r c : Nat}
    (A : Fin r → Finset Nat) (B : Fin c → Finset Nat)
    (ha : ∀ a, (A a).Nonempty) (hb : ∀ b, (B b).Nonempty)
    (hda : Pairwise (fun a b => Disjoint (A a) (A b)))
    (hdb : Pairwise (fun a b => Disjoint (B a) (B b)))
    (hca : ∀ x, x ∈ X ↔ ∃ a, x ∈ A a) (hcb : ∀ x, x ∈ X ↔ ∃ b, x ∈ B b)
    (s : P) (hs : s ∈ Subgroup.closure {p : P | p.IsSwap})
    (hsX : ∀ x, x ∈ X ↔ s x ∈ X) :
    (iSup (fun a => blockSym (A a))) ⊓ conjugate s (iSup (fun b => blockSym (B b))) =
      iSup (fun a => iSup (fun b => blockSym (A a ∩ (B b).map s.toEmbedding))) := by
  let C (b : Fin c) := (B b).map s.toEmbedding
  have hconj := FiniteParabolicConjugateBlocks B hb hdb ⟨s, hs⟩
  change conjugate s (iSup (fun b => blockSym (B b))) =
    iSup (fun b => blockSym ((B b).image s)) at hconj
  have hconj' : conjugate s (iSup (fun b => blockSym (B b))) =
      iSup (fun b => blockSym (C b)) := by
    rw [hconj]
    congr 1
    funext b
    exact congrArg blockSym (Finset.map_eq_image s.toEmbedding (B b)).symm
  rw [hconj']
  -- Section 7.2 computes the intersection on Sym(X). Here the factors
  -- already lie in Perm Nat, so use its registered Prop. 7.1 supplier directly.
  exact FiniteParabolicIntersectionBlocks X A C ha (fun b => (hb b).map)
    hda (fun _ _ hij => (Finset.disjoint_map s.toEmbedding).mpr (hdb hij)) (hca) (by
      intro x
      constructor
      · intro hx
        obtain ⟨b, hb'⟩ := (hcb (s.symm x)).mp (by
          apply (hsX (s.symm x)).mpr
          simpa only [s.apply_symm_apply] using hx)
        exact ⟨b, Finset.mem_map_equiv.mpr hb'⟩
      · rintro ⟨b, hx⟩
        have h := (hcb (s.symm x)).mpr ⟨b, Finset.mem_map_equiv.mp hx⟩
        simpa only [s.apply_symm_apply] using (hsX (s.symm x)).mp h)

open CategoryTheory CategoryTheory.Limits

private abbrev Mod (S : Type) [Group S] := ModuleCat.{v} (MonoidAlgebra Complex S)
private abbrev Res {S T : Type} [Group S] [Group T] (f : S →* T) :
    Mod.{v} T ⥤ Mod.{v} S :=
  ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex f).toRingHom
private abbrev Ind {S T : Type} [Group S] [Group T] (f : S →* T) :
    Mod.{v} S ⥤ Mod.{v} T :=
  (Rep.ofModuleMonoidAlgebra (k := Complex) (G := S) ⋙
    Rep.indFunctor Complex f) ⋙ Rep.toModuleMonoidAlgebra (k := Complex) (G := T)

private theorem mackeyIso {U : Type} [Group U] (K H G : Subgroup U) (α β : U)
    (hK : conjugate α K ≤ G) (hH : conjugate β H ≤ G)
    {J : Type}
    (classify : DoubleCoset.Quotient
      (Subgroup.comap G.subtype (conjugate α K) : Set G)
      (Subgroup.comap G.subtype (conjugate β H) : Set G) ≃ J)
    (σ : J → G)
    (hσ : ∀ R, DoubleCoset.mk (Subgroup.comap G.subtype (conjugate α K))
      (Subgroup.comap G.subtype (conjugate β H)) (σ R) = classify.symm R) :
    let L := fun R : J => conjugate α K ⊓ conjugate ((σ R : U) * β) H
    Nonempty ((Ind.{v} (forward β hH) ⋙ Res.{v} (forward α hK)) ≅
      sigmaObj (fun R : J =>
        Res.{v} (backward ((σ R : U) * β) (show L R ≤ _ from inf_le_right)) ⋙
          Ind.{v} (backward α (show L R ≤ _ from inf_le_left)))) := by
  intro L
  let s := σ ∘ classify
  have hs j := (hσ (classify j)).trans (classify.symm_apply_apply j)
  obtain ⟨_, _, _, _, _, _, _, ⟨iso⟩⟩ :=
    GeneralizedMackeyDecomposition.{0,v} K H G α β hK hH s hs
  let l := fun R : J => backward α (show L R ≤ _ from inf_le_left)
  let m := fun R : J => backward ((σ R : U) * β) (show L R ≤ _ from inf_le_right)
  let F := fun R : J => Res.{v} (m R) ⋙ Ind.{v} (l R)
  -- Theorem 2.2 uses quotient indices and typed conjugation embeddings.
  -- Identify their homomorphisms before transporting the actual coproduct.
  have hIso : Nonempty ((Ind.{v} (forward β hH) ⋙ Res.{v} (forward α hK)) ≅
      sigmaObj (fun j => F (classify j))) := by
    have hl (j) (w : ∀ t : L (classify j), α⁻¹ * (t : U) * (α⁻¹)⁻¹ ∈ K) :
        (MackeyDiagrams.ConjEmbedding.ofConjugator α⁻¹ w).toHom = l (classify j) := by
      apply MonoidHom.ext
      intro t
      apply Subtype.ext
      rw [backward_val]
      change α⁻¹ * (t : U) * (α⁻¹)⁻¹ = _
      rw [inv_inv]
    have hm (j) (w : ∀ t : L (classify j),
        (β⁻¹ * (s j : U)⁻¹) * (t : U) * (β⁻¹ * (s j : U)⁻¹)⁻¹ ∈ H) :
        (MackeyDiagrams.ConjEmbedding.ofConjugator (β⁻¹ * (s j : U)⁻¹) w).toHom =
          m (classify j) := by
      apply MonoidHom.ext
      intro t
      apply Subtype.ext
      rw [backward_val]
      change (β⁻¹ * (s j : U)⁻¹) * (t : U) * (β⁻¹ * (s j : U)⁻¹)⁻¹ =
        ((s j : U) * β)⁻¹ * (t : U) * ((s j : U) * β)
      group
    simp only [hl, hm] at iso
    exact ⟨iso⟩
  obtain ⟨e⟩ := hIso
  exact ⟨e ≪≫ Sigma.whiskerEquiv classify (fun _ => Iso.refl _)⟩

end ParabolicMackeyAssembly
