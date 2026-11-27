import MackeyDiagrams
import Proofs.ConjugationEmbeddingCentralizerCoset
import Proofs.SurvivingCosetRepresentative

set_option maxHeartbeats 2000000

namespace TransportToMackeyRepresentativeAux

open MackeyDiagrams

universe u v

section Quotients

variable {U : Type u} [Group U]

private theorem conjugate_mul (c d : U) (S : Subgroup U) :
    (S.map (MulAut.conj d).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      S.map (MulAut.conj (c * d)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change c * (d * x * d⁻¹) * c⁻¹ = (c * d) * x * (c * d)⁻¹
  group

private theorem coset_card_of_map (e : U ≃* U) (S T : Subgroup U) :
    Cardinal.mk (Quotient (QuotientGroup.leftRel (T.subgroupOf S))) =
      Cardinal.mk (Quotient (QuotientGroup.leftRel
        ((T.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)))) := by
  let f := e.subgroupMap S
  apply Cardinal.mk_congr
  refine Quotient.congr f.toEquiv (fun x y => ?_)
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
  change x⁻¹ * y ∈ T.subgroupOf S ↔
    (f x)⁻¹ * f y ∈ (T.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)
  rw [← map_inv, ← map_mul]
  change ((x : U)⁻¹ * (y : U)) ∈ T ↔
    e ((x : U)⁻¹ * (y : U)) ∈ T.map e.toMonoidHom
  rw [Subgroup.mem_map_equiv, e.symm_apply_apply]

end Quotients

section Transport

variable {U : Type u} [Group U] {K H G L L' : Subgroup U}
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (l' : ConjEmbedding L' K) (r' : ConjEmbedding L' H)
variable (k : K) (h : H) (f : L ≃ L')

private def shiftBasis
    (hl : ∀ t, l'.toHom (f t) = k⁻¹ * l.toHom t * k)
    (hr : ∀ t, r'.toHom (f t) = h * r.toHom t * h⁻¹) :
    ((Biset.induction l).tensor (Biset.restriction r)).carrier ≃
      ((Biset.induction l').tensor (Biset.restriction r')).carrier := by
  refine Quotient.congr ((Equiv.mulRight k).prodCongr (Equiv.mulLeft h)) (fun x y => ?_)
  change
    (∃ t : L, 1 * x.1 * (l.toHom t)⁻¹ = y.1 ∧
      r.toHom t * x.2 * (1 : H)⁻¹ = y.2) ↔
    (∃ t : L', 1 * (x.1 * k) * (l'.toHom t)⁻¹ = y.1 * k ∧
      r'.toHom t * (h * x.2) * (1 : H)⁻¹ = h * y.2)
  simp only [one_mul, inv_one, mul_one]
  have left (t : L) : (x.1 * k) * (l'.toHom (f t))⁻¹ =
      (x.1 * (l.toHom t)⁻¹) * k := by
    rw [hl]
    group
  have right (t : L) : r'.toHom (f t) * (h * x.2) = h * (r.toHom t * x.2) := by
    rw [hr]
    group
  constructor
  · rintro ⟨t, hx, hy⟩
    exact ⟨f t, (left t).trans (congrArg (· * k) hx), (right t).trans (congrArg (h * ·) hy)⟩
  · rintro ⟨t, hx, hy⟩
    obtain ⟨t, rfl⟩ := f.surjective t
    exact ⟨t, mul_right_cancel ((left t).symm.trans hx),
      mul_left_cancel ((right t).symm.trans hy)⟩

private theorem shiftBasis_equivariant
    (hl : ∀ t, l'.toHom (f t) = k⁻¹ * l.toHom t * k)
    (hr : ∀ t, r'.toHom (f t) = h * r.toHom t * h⁻¹)
    (g : K × H) (w : ((Biset.induction l).tensor (Biset.restriction r)).carrier) :
    shiftBasis l r l' r' k h f hl hr
        (((Biset.induction l).tensor (Biset.restriction r)).act g w) =
      ((Biset.induction l').tensor (Biset.restriction r')).act g
        (shiftBasis l r l' r' k h f hl hr w) := by
  refine Quotient.inductionOn w (fun ⟨x, y⟩ => ?_)
  change (Biset.induction l').pair (Biset.restriction r')
      ((g.1 * x * (l.toHom 1)⁻¹) * k) (h * (r.toHom 1 * y * g.2⁻¹)) =
    (Biset.induction l').pair (Biset.restriction r')
      (g.1 * (x * k) * (l'.toHom 1)⁻¹) (r'.toHom 1 * (h * y) * g.2⁻¹)
  simp only [map_one, inv_one, mul_one, one_mul, mul_assoc]

end Transport

section Linear

variable {K H : Type u} [Group K] [Group H]
variable {X X' Y : Biset K H} {R : Type v} [CommSemiring R]
variable (e : X.carrier ≃ X'.carrier)
variable (he : ∀ g x, e (X.act g x) = X'.act g (e x))
variable (q : X.carrier → Y.carrier) (q' : X'.carrier → Y.carrier)
variable (hq : ∀ g x, q (X.act g x) = Y.act g (q x))
variable (hq' : ∀ g x, q' (X'.act g x) = Y.act g (q' x))

private theorem multiplication_commutes (hcomm : ∀ x, q' (e x) = q x) :
    (Biset.Hom.ofFunction e he : Biset.Hom R X X').vertical (Biset.Hom.ofFunction q' hq') =
      Biset.Hom.ofFunction q hq := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  simp only [Biset.Hom.vertical, LinearMap.comp_apply, Biset.Hom.ofFunction_single, hcomm]

private theorem projection_commutes (hcomm : ∀ x, q' (e x) = q x)
    (hf : ∀ z, Set.Finite {w | q w = z}) (hf' : ∀ z, Set.Finite {w | q' w = z}) :
    (Biset.Hom.transfer R q hq hf).vertical (Biset.Hom.ofFunction e he) =
      Biset.Hom.transfer R q' hq' hf' := by
  classical
  -- Each finite transfer has coefficient one at a preimage. Comparing
  -- coefficients at corresponding preimages avoids choosing a fiber order.
  have hpush : (Biset.Hom.ofFunction e he : Biset.Hom R X X').toLinearMap =
      Finsupp.lmapDomain R R e := by
    apply Finsupp.lhom_ext
    intro x c
    simp
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z c
  simp only [Biset.Hom.vertical, LinearMap.comp_apply, Biset.Hom.transfer_single, map_smul]
  congr 1
  apply Finsupp.ext
  intro x'
  obtain ⟨x, rfl⟩ := e.surjective x'
  rw [hpush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply_of_injective e.injective,
    Biset.Hom.transferBasis_apply, Biset.Hom.transferBasis_apply, hcomm]

end Linear

section Drawings

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]
variable (a : ConjEmbedding K G) (b : ConjEmbedding H G)
variable (l : ConjEmbedding L K) (r : ConjEmbedding L H)
variable (d : Dot (a.comp l) (b.comp r))

private theorem eval_multiplication_singleton :
    (LabelledDrawing.mixedMultiplication (R := R) a b l r [(1, d)]).interpret.eval =
      Generator.mixedMultiplication a b l r d R := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval, Diagram.eval]

private theorem eval_projection_singleton
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (LabelledDrawing.compactProjection (R := R) a b l r [(1, ⟨d, hf⟩)]).interpret.eval =
      Generator.mixedProjection a b l r d R hf := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval, Diagram.eval]

end Drawings

end TransportToMackeyRepresentativeAux

theorem TransportToMackeyRepresentative : (∀ {U : Type u} [Group U] (K H G L : Subgroup U) (α β a b : U),
  let conjSubgroup := fun (c : U) (S : Subgroup U) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj c)) S
  let Kα := conjSubgroup α K
  let Hβ := conjSubgroup β H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G)
    (ha : conjSubgroup a L ≤ K) (hb : conjSubgroup b L ≤ H)
    (hs : (α * a) * (β * b)⁻¹ ∈ G),
    let eα := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun x => hK ⟨(x : U), x.property, rfl⟩)
    let eβ := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun y => hH ⟨(y : U), y.property, rfl⟩)
    let ea := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L) (G := K) a
      (fun ℓ => ha ⟨(ℓ : U), ℓ.property, rfl⟩)
    let eb := MackeyDiagrams.ConjEmbedding.ofConjugator (H := L) (G := H) b
      (fun ℓ => hb ⟨(ℓ : U), ℓ.property, rfl⟩)
    let d : MackeyDiagrams.Dot
        (MackeyDiagrams.ConjEmbedding.comp eα ea)
        (MackeyDiagrams.ConjEmbedding.comp eβ eb) :=
      MackeyDiagrams.Dot.ofRepresentatives (α * a) (β * b)
        (by
          intro ℓ
          change α * (a * (ℓ : U) * a⁻¹) * α⁻¹ = _
          group)
        (by
          intro ℓ
          change β * (b * (ℓ : U) * b⁻¹) * β⁻¹ = _
          group) hs
    let s := MackeyDiagrams.Dot.element d
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ i : J, DoubleCoset.mk A B (σ i) = i)
      (j : J) (_ : DoubleCoset.mk A B s = j) (k : K) (h : H)
      (_ : s = MackeyDiagrams.ConjEmbedding.toHom eα k * σ j *
        MackeyDiagrams.ConjEmbedding.toHom eβ h),
      let Lj := Kα ⊓ conjSubgroup ((σ j : U) * β) H
      let Ls := Kα ⊓ conjSubgroup ((s : U) * β) H
      let Limage := conjSubgroup (α * a) L
      let Lprime := conjSubgroup (α * (k : U)⁻¹ * a) L
      let leftJ := MackeyDiagrams.ConjEmbedding.ofConjugator (H := Lj) (G := K) α⁻¹
        (by
          intro ℓ
          obtain ⟨x, hx, he⟩ := ℓ.property.1
          change α * x * α⁻¹ = (ℓ : U) at he
          rw [← he]
          change x ∈ K at hx
          convert hx using 1
          group)
      let rightJ := MackeyDiagrams.ConjEmbedding.ofConjugator (H := Lj) (G := H)
        (β⁻¹ * (σ j : U)⁻¹)
        (by
          intro ℓ
          obtain ⟨y, hy, he⟩ := ℓ.property.2
          change ((σ j : U) * β) * y * ((σ j : U) * β)⁻¹ = (ℓ : U) at he
          rw [← he]
          change y ∈ H at hy
          convert hy using 1
          group)
      ∃ hSub : Lprime ≤ Lj,
        let leftPrime := MackeyDiagrams.ConjEmbedding.ofConjugator
          (H := Lprime) (G := K) α⁻¹ (fun ℓ =>
            (MackeyDiagrams.ConjEmbedding.toHom leftJ ⟨(ℓ : U), hSub ℓ.property⟩).property)
        let rightPrime := MackeyDiagrams.ConjEmbedding.ofConjugator
          (H := Lprime) (G := H) (β⁻¹ * (σ j : U)⁻¹) (fun ℓ =>
            (MackeyDiagrams.ConjEmbedding.toHom rightJ ⟨(ℓ : U), hSub ℓ.property⟩).property)
        let dprime : MackeyDiagrams.Dot
            (MackeyDiagrams.ConjEmbedding.comp eα leftPrime)
            (MackeyDiagrams.ConjEmbedding.comp eβ rightPrime) :=
          ⟨σ j, by
            intro ℓ
            apply Subtype.ext
            change α * (α⁻¹ * (ℓ : U) * (α⁻¹)⁻¹) * α⁻¹ * (σ j : U) =
              (σ j : U) * (β * ((β⁻¹ * (σ j : U)⁻¹) * (ℓ : U) *
                (β⁻¹ * (σ j : U)⁻¹)⁻¹) * β⁻¹)
            group⟩
        let X := MackeyDiagrams.Biset.induction ea
        let Y := MackeyDiagrams.Biset.restriction eb
        let Xprime := MackeyDiagrams.Biset.induction leftPrime
        let Yprime := MackeyDiagrams.Biset.restriction rightPrime
        let W := MackeyDiagrams.Biset.tensor X Y
        let Wprime := MackeyDiagrams.Biset.tensor Xprime Yprime
        let q := MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ ea eb d
        let qprime :=
          MackeyDiagrams.Generator.mixedMultiplicationBasis eα eβ leftPrime rightPrime dprime
        let ι := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex)
          eα eβ ea eb [(1, d)]
        let ιprime := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex)
          eα eβ leftPrime rightPrime [(1, dprime)]
        ∃ (e : W.carrier ≃ Wprime.carrier)
          (he : ∀ (g : K × H) (w : W.carrier),
            e (MackeyDiagrams.Biset.act W g w) = MackeyDiagrams.Biset.act Wprime g (e w)),
          let transport : MackeyDiagrams.Biset.Hom Complex W Wprime :=
            MackeyDiagrams.Biset.Hom.ofFunction e he
          (∀ (x : K) (y : H),
            e (MackeyDiagrams.Biset.pair X Y x y) =
              MackeyDiagrams.Biset.pair Xprime Yprime (x * k) (h * y)) ∧
          MackeyDiagrams.Biset.Hom.vertical transport (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret ιprime)) =
            MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret ι) ∧
          (∀ (hf : ∀ z, Set.Finite {w | q w = z})
              (hfprime : ∀ z, Set.Finite {w | qprime w = z}),
            let p := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex)
              eα eβ ea eb [(1, ⟨d, hf⟩)]
            let pprime := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex)
              eα eβ leftPrime rightPrime [(1, ⟨dprime, hfprime⟩)]
            MackeyDiagrams.Biset.Hom.vertical (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret p)) transport =
              MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret pprime)) ∧
          Cardinal.mk (Quotient (QuotientGroup.leftRel (Subgroup.subgroupOf Lprime Lj))) =
            Cardinal.mk (Quotient (QuotientGroup.leftRel (Subgroup.subgroupOf Limage Ls)))) :=
(by
  open MackeyDiagrams TransportToMackeyRepresentativeAux in
  intro U _ K H G L α β a b conjSubgroup Kα Hβ hK hH ha hb hs
    eα eβ ea eb d s A B J σ hσ j hj k h hsplit Lj Ls Limage Lprime leftJ rightJ
  -- Ian Xiao, Lemma 5.2 (p. 16), starts from the displayed factorization
  -- of s. Its proof has no separately numbered steps. Equations (2.1)
  -- and (2.2) specify the representative and its intersection subgroup.
  -- The hypothesis hsplit supplies the two multipliers. DoubleCoset.eq
  -- would recover a factorization from membership, and
  -- SurvivingCosetRepresentative requires a right-coset transversal
  -- to select a surviving term. Here the factorization is explicit.
  -- ConjugationEmbeddingCentralizerCoset compares presentations of
  -- embeddings. The typed embeddings here already come with their
  -- conjugation formulas. The index comparison uses ordinary left cosets,
  -- while the candidate FLT result concerns double cosets.
  have hs_val : (s : U) = (α * a) * (β * b)⁻¹ := rfl
  have hsplit_val : (s : U) =
      (α * (k : U) * α⁻¹) * (σ j : U) * (β * (h : U) * β⁻¹) :=
    congrArg Subtype.val hsplit
  let c : U := α * (k : U)⁻¹ * α⁻¹
  let t : U := α * (k : U)⁻¹ * a
  have ht : t = (σ j : U) * β * (h : U) * b := by
    calc
      t = c * ((s : U) * (β * b)) := by
        rw [hs_val]
        dsimp only [c, t]
        group
      _ = _ := by
        rw [hsplit_val]
        dsimp only [c]
        group
  -- The two expressions for t give the two inclusions into the intersection.
  have hSub : Lprime ≤ Lj := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    change t * ℓ * t⁻¹ ∈ Kα ⊓ conjSubgroup ((σ j : U) * β) H
    constructor
    · have haℓ : a * ℓ * a⁻¹ ∈ K := ha ⟨ℓ, hℓ, rfl⟩
      refine ⟨(k : U)⁻¹ * (a * ℓ * a⁻¹) * (k : U),
        K.mul_mem (K.mul_mem (K.inv_mem k.property) haℓ) k.property, ?_⟩
      change α * ((k : U)⁻¹ * (a * ℓ * a⁻¹) * (k : U)) * α⁻¹ = t * ℓ * t⁻¹
      dsimp only [t]
      group
    · have hbℓ : b * ℓ * b⁻¹ ∈ H := hb ⟨ℓ, hℓ, rfl⟩
      refine ⟨(h : U) * (b * ℓ * b⁻¹) * (h : U)⁻¹,
        H.mul_mem (H.mul_mem h.property hbℓ) (H.inv_mem h.property), ?_⟩
      change ((σ j : U) * β) * ((h : U) * (b * ℓ * b⁻¹) * (h : U)⁻¹) *
        ((σ j : U) * β)⁻¹ = t * ℓ * t⁻¹
      rw [ht]
      group
  -- Conjugation by c carries both subgroup pairs to each other. Work
  -- with the actual left-coset quotient to include infinite indices.
  have hc : c ∈ Kα := ⟨(k : U)⁻¹, K.inv_mem k.property, rfl⟩
  have hleft : conjSubgroup c Kα = Kα :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Kα.le_normalizer hc)
  have hrightFixed : conjSubgroup (h : U) H = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer h.property)
  have hcRight : c * ((s : U) * β) = ((σ j : U) * β) * (h : U) := by
    rw [hsplit_val]
    dsimp only [c]
    group
  have hright : conjSubgroup c (conjSubgroup ((s : U) * β) H) =
      conjSubgroup ((σ j : U) * β) H := calc
    _ = conjSubgroup (c * ((s : U) * β)) H := conjugate_mul _ _ _
    _ = conjSubgroup (((σ j : U) * β) * (h : U)) H := by rw [hcRight]
    _ = conjSubgroup ((σ j : U) * β) (conjSubgroup (h : U) H) :=
      (conjugate_mul _ _ _).symm
    _ = _ := congrArg (conjSubgroup ((σ j : U) * β)) hrightFixed
  have hmapJ : conjSubgroup c Ls = Lj := by
    change (Kα ⊓ conjSubgroup ((s : U) * β) H).map (MulAut.conj c).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective]
    change conjSubgroup c Kα ⊓ conjSubgroup c (conjSubgroup ((s : U) * β) H) = Lj
    rw [hleft, hright]
  have hmapImage : conjSubgroup c Limage = Lprime := by
    calc
      _ = conjSubgroup (c * (α * a)) L := conjugate_mul _ _ _
      _ = conjSubgroup t L := by
        apply congrArg (fun z => conjSubgroup z L)
        dsimp only [c, t]
        group
      _ = _ := rfl
  have hindex :
      Cardinal.mk (Quotient (QuotientGroup.leftRel (Lprime.subgroupOf Lj))) =
        Cardinal.mk (Quotient (QuotientGroup.leftRel (Limage.subgroupOf Ls))) := by
    let cosetCard (S T : Subgroup U) :=
      Cardinal.mk (Quotient (QuotientGroup.leftRel (T.subgroupOf S)))
    change cosetCard Lj Lprime = cosetCard Ls Limage
    rw [← hmapJ, ← hmapImage]
    exact (coset_card_of_map (MulAut.conj c) Ls Limage).symm
  refine ⟨hSub, ?_⟩
  intro leftPrime rightPrime dprime X Y Xprime Yprime W Wprime q qprime ι ιprime
  -- Lemma 5.2 computes the restricted embeddings on t ℓ t⁻¹.
  -- These two formulas transport the generating balance relation both ways.
  let f : L ≃ Lprime := ((MulAut.conj t).subgroupMap L).toEquiv
  have hf_val (ℓ : L) : (f ℓ : U) = t * (ℓ : U) * t⁻¹ := rfl
  have hl (ℓ : L) : leftPrime.toHom (f ℓ) = k⁻¹ * ea.toHom ℓ * k := by
    apply Subtype.ext
    change α⁻¹ * (f ℓ : U) * (α⁻¹)⁻¹ =
      (k : U)⁻¹ * (a * (ℓ : U) * a⁻¹) * (k : U)
    rw [hf_val]
    dsimp only [t]
    group
  have hr (ℓ : L) : rightPrime.toHom (f ℓ) = h * eb.toHom ℓ * h⁻¹ := by
    apply Subtype.ext
    change (β⁻¹ * (σ j : U)⁻¹) * (f ℓ : U) * (β⁻¹ * (σ j : U)⁻¹)⁻¹ =
      (h : U) * (b * (ℓ : U) * b⁻¹) * (h : U)⁻¹
    rw [hf_val, ht]
    group
  let e : W.carrier ≃ Wprime.carrier := shiftBasis ea eb leftPrime rightPrime k h f hl hr
  have he : ∀ g w, e (W.act g w) = Wprime.act g (e w) :=
    shiftBasis_equivariant ea eb leftPrime rightPrime k h f hl hr
  have he_pair (x : K) (y : H) :
      e (X.pair Y x y) = Xprime.pair Yprime (x * k) (h * y) := rfl
  -- Crossing values agree on the balanced-pair representatives. The
  -- equality identifies the fibers, which suffices for finite transfers.
  have hcomm (w : W.carrier) : qprime (e w) = q w := by
    refine Quotient.inductionOn w (fun ⟨x, y⟩ => ?_)
    change qprime (e (X.pair Y x y)) = q (X.pair Y x y)
    rw [he_pair]
    change Generator.mixedPair eα eβ (eα.toHom (x * k) * σ j * eβ.toHom (h * y)) =
      Generator.mixedPair eα eβ (eα.toHom x * s * eβ.toHom y)
    apply congrArg (Generator.mixedPair eα eβ)
    rw [map_mul, map_mul, hsplit]
    group
  refine ⟨e, he, he_pair, ?_, ?_, hindex⟩
  · -- The reviewed syntax interprets a coefficient-one singleton drawing
    -- as the associated basis pushforward.
    rw [show ιprime.interpret.eval = _ from eval_multiplication_singleton
          eα eβ leftPrime rightPrime dprime,
      show ι.interpret.eval = _ from eval_multiplication_singleton eα eβ ea eb d]
    exact multiplication_commutes e he q qprime
      (Generator.mixedMultiplication_equivariant eα eβ ea eb d)
      (Generator.mixedMultiplication_equivariant eα eβ leftPrime rightPrime dprime) hcomm
  · -- The paper uses the inverse trace labels. The compact drawings
    -- implement those projections by transfer along the forward maps.
    intro hf hfprime p pprime
    rw [show p.interpret.eval = _ from eval_projection_singleton eα eβ ea eb d hf,
      show pprime.interpret.eval = _ from eval_projection_singleton
          eα eβ leftPrime rightPrime dprime hfprime]
    exact projection_commutes e he q qprime
      (Generator.mixedMultiplication_equivariant eα eβ ea eb d)
      (Generator.mixedMultiplication_equivariant eα eβ leftPrime rightPrime dprime)
      hcomm hf hfprime)
