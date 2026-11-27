universe v

namespace ParabolicMackeyAssembly

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
  -- ParabolicMackeyIntersectionBlocks computes the intersection on Sym(X).
  -- The factors here already lie in Perm Nat. Its registered Prop. 7.1
  -- supplier FiniteParabolicIntersectionBlocks applies to this carrier directly.
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
private noncomputable abbrev Res {S T : Type} [Group S] [Group T] (f : S →* T) :
    Mod.{v} T ⥤ Mod.{v} S :=
  ModuleCat.restrictScalars (MonoidAlgebra.mapDomainAlgHom Complex Complex f).toRingHom
private noncomputable abbrev Ind {S T : Type} [Group S] [Group T] (f : S →* T) :
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

private theorem conjugate_mul {U : Type} [Group U] (p q : U) (H : Subgroup U) :
    conjugate (p * q) H = conjugate p (conjugate q H) := by
  change H.map (conj (p * q)).toMonoidHom =
    (H.map (conj q).toMonoidHom).map (conj p).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change (p * q) * x * (p * q)⁻¹ = p * (q * x * q⁻¹) * p⁻¹
  group

private theorem conjugate_eq_of_forward {U : Type} [Group U] {S T : Subgroup U}
    (p : U) (h : conjugate p S ≤ T) (hf : ∀ x : S, (forward p h x : U) = x) :
    conjugate p S = S := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (forward p h ⟨x, hx⟩ : U) ∈ S
    rw [hf ⟨x, hx⟩]
    exact hx
  · intro hy
    exact ⟨y, hy, hf ⟨y, hy⟩⟩

private theorem inclusionIso {U : Type} [Group U] (K H G : Subgroup U) (α β : U)
    (hK : conjugate α K ≤ G) (hH : conjugate β H ≤ G)
    {J : Type} (σ : J → G)
    (hα : ∀ k : K, (forward α hK k : U) = k)
    (hβ : ∀ h : H, (forward β hH h : U) = h) :
    let L := fun R : J => conjugate α K ⊓ conjugate ((σ R : U) * β) H
    let T := fun R : J => conjugate (σ R : U)⁻¹ (L R)
    let transport : ∀ R : J, L R →* T R := fun R =>
      MonoidHom.subgroupMap (conj (σ R : U)⁻¹).toMonoidHom (L R)
    Nonempty ((Ind.{v} (forward β hH) ⋙ Res.{v} (forward α hK)) ≅
      sigmaObj (fun R : J =>
        Res.{v} (backward ((σ R : U) * β) (show L R ≤ _ from inf_le_right)) ⋙
          Ind.{v} (backward α (show L R ≤ _ from inf_le_left)))) →
    ∃ (hKG : K ≤ G) (hHG : H ≤ G) (hLK : ∀ R : J, L R ≤ K)
      (hTH : ∀ R : J, T R ≤ H),
      Nonempty ((Ind.{v} (Subgroup.inclusion hHG) ⋙ Res.{v} (Subgroup.inclusion hKG)) ≅
        sigmaObj (fun R =>
          (Res.{v} (Subgroup.inclusion (hTH R)) ⋙ Res.{v} (transport R)) ⋙
            Ind.{v} (Subgroup.inclusion (hLK R)))) := by
  rintro L T transport ⟨iso⟩
  have eqK := conjugate_eq_of_forward α hK hα
  have eqH := conjugate_eq_of_forward β hH hβ
  have hKG : K ≤ G := eqK ▸ hK
  have hHG : H ≤ G := eqH ▸ hH
  have hLK (R : J) : L R ≤ K := eqK ▸ (show L R ≤ conjugate α K from inf_le_left)
  let l := fun R : J => backward α (show L R ≤ _ from inf_le_left)
  let m := fun R : J => backward ((σ R : U) * β) (show L R ≤ _ from inf_le_right)
  have hα' : forward α hK = Subgroup.inclusion hKG :=
    MonoidHom.ext fun k => Subtype.ext (hα k)
  have hβ' : forward β hH = Subgroup.inclusion hHG :=
    MonoidHom.ext fun h => Subtype.ext (hβ h)
  have hl (R : J) : l R = Subgroup.inclusion (hLK R) := by
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    calc
      (l R t : U) = α * (l R t : U) * α⁻¹ := (hα (l R t)).symm
      _ = t := by
        dsimp only [l]
        rw [backward_val]
        group
  have hm (R : J) (t : L R) : (m R t : U) = (transport R t : U) := by
    calc
      (m R t : U) = β * (m R t : U) * β⁻¹ := (hβ (m R t)).symm
      _ = (transport R t : U) := by
        dsimp only [m]
        rw [backward_val]
        change β * (((σ R : U) * β)⁻¹ * (t : U) * ((σ R : U) * β)) * β⁻¹ =
          (σ R : U)⁻¹ * (t : U) * ((σ R : U)⁻¹)⁻¹
        group
  have hTH (R : J) : T R ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    change (transport R ⟨t, ht⟩ : U) ∈ H
    rw [← hm R ⟨t, ht⟩]
    exact (m R ⟨t, ht⟩).property
  have hfactor (R : J) : m R = (Subgroup.inclusion (hTH R)).comp (transport R) :=
    MonoidHom.ext fun t => Subtype.ext (hm R t)
  -- The inclusion case factors the very same maps on the group algebra.
  -- Restriction of scalars in the resulting order uses Mathlib's comparison.
  have summand (R : J) : (Res.{v} (m R) ⋙ Ind.{v} (l R)) ≅
      (Res.{v} (Subgroup.inclusion (hTH R)) ⋙ Res.{v} (transport R)) ⋙
        Ind.{v} (Subgroup.inclusion (hLK R)) := by
    rw [hl R]
    apply Functor.isoWhiskerRight
    apply ModuleCat.restrictScalarsComp'
    change (MonoidAlgebra.mapDomainAlgHom Complex Complex (m R)).toRingHom =
      (MonoidAlgebra.mapDomainAlgHom Complex Complex (Subgroup.inclusion (hTH R))).toRingHom.comp
        (MonoidAlgebra.mapDomainAlgHom Complex Complex (transport R)).toRingHom
    rw [hfactor R]
    exact congrArg AlgHom.toRingHom
      (MonoidAlgebra.mapDomainAlgHom_comp (transport R) (Subgroup.inclusion (hTH R)))
  change (Ind.{v} (forward β hH) ⋙ Res.{v} (forward α hK)) ≅
    sigmaObj (fun R => Res.{v} (m R) ⋙ Ind.{v} (l R)) at iso
  rw [hα', hβ'] at iso
  exact ⟨hKG, hHG, hLK, hTH, ⟨iso ≪≫ Sigma.mapIso summand⟩⟩

private def cosetCongr {G : Type} [Group G] {K H K' H' : Subgroup G}
    (hK : K = K') (hH : H = H') :
    DoubleCoset.Quotient (K : Set G) (H : Set G) ≃
      DoubleCoset.Quotient (K' : Set G) (H' : Set G) := by
  subst K'
  subst H'
  exact Equiv.refl _

private theorem cosetCongr_mk {G : Type} [Group G] {K H K' H' : Subgroup G}
    (hK : K = K') (hH : H = H') (s : G) :
    cosetCongr hK hH (DoubleCoset.mk K H s) = DoubleCoset.mk K' H' s := by
  subst K'
  subst H'
  rfl

end ParabolicMackeyAssembly
