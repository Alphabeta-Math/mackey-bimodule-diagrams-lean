namespace CurlWithCentralizingDotSupport

open MackeyDiagrams

universe u

noncomputable section

variable {U : Type u} [Group U] {K H G : Subgroup U}

private abbrev basis {A : Subgroup U} (x : A) : MonoidAlgebra Complex A :=
  MonoidAlgebra.single x 1

private abbrev lift {A B : Subgroup U} (p : ConjEmbedding A B) :=
  MonoidAlgebra.mapDomainAlgHom Complex Complex p.toHom

private theorem basis_mul {A : Subgroup U} (x y : A) :
    basis (x * y) = basis x * basis y := by
  simp only [basis, MonoidAlgebra.single_mul_single, mul_one]

private theorem lift_basis {A B : Subgroup U} (p : ConjEmbedding A B) (x : A) :
    lift p (basis x) = basis (p.toHom x) :=
  MonoidAlgebra.mapDomain_single

private def summand (a : MonoidAlgebra Complex H) (t : H) :=
  basis t⁻¹ * a * basis t

private theorem summand_mul (a : MonoidAlgebra Complex H) (s t : H) :
    summand a (s * t) = basis t⁻¹ * summand a s * basis t := by
  simp only [summand, mul_inv_rev, basis_mul, mul_assoc]

private theorem summand_invariant (inner : ConjEmbedding K H)
    (a : MonoidAlgebra Complex H)
    (ha : ∀ y : MonoidAlgebra Complex K, Commute (lift inner y) a)
    (t : H) (ℓ : inner.toHom.range) :
    summand a ((ℓ : H) * t) = summand a t := by
  obtain ⟨k, hk⟩ := ℓ.property
  have comm : basis (ℓ : H) * a = a * basis (ℓ : H) := by
    simpa only [lift_basis, hk] using (ha (basis k)).eq
  have cancel : summand a (ℓ : H) = a := by
    rw [summand, mul_assoc, ← comm, ← mul_assoc, ← basis_mul, inv_mul_cancel]
    change (1 : MonoidAlgebra Complex H) * a = a
    exact one_mul a
  rw [summand_mul, cancel]
  rfl

private abbrev IsTransversal (S : Subgroup H) (T : Finset H) :=
  ∀ h : H, ∃! t : {t : H // t ∈ T}, h * t.val⁻¹ ∈ S

-- Right multiplication transports each coset. The two directions of
-- transport are inverse by the uniqueness in the chosen transversal.
private theorem sum_transversal_mul (S : Subgroup H) (T : Finset H)
    (hT : IsTransversal S T) {M : Type*} [AddCommMonoid M] (f : H → M)
    (hf : ∀ (t : H) (ℓ : S), f ((ℓ : H) * t) = f t) (g : H) :
    (∑ t ∈ T, f (t * g)) = ∑ t ∈ T, f t := by
  classical
  let rep (x : H) := Classical.choose (hT x)
  have hrep (x : H) : x * (rep x : H)⁻¹ ∈ S := (Classical.choose_spec (hT x)).1
  have huniq (x : H) (t : {t : H // t ∈ T}) (ht : x * (t : H)⁻¹ ∈ S) :
      t = rep x := (Classical.choose_spec (hT x)).2 t ht
  have back (g : H) (t : {t : H // t ∈ T}) :
      rep ((rep ((t : H) * g) : H) * g⁻¹) = t := by
    apply (huniq _ t _).symm
    have he : (rep ((t : H) * g) : H) * g⁻¹ * (t : H)⁻¹ =
        ((t : H) * g * (rep ((t : H) * g) : H)⁻¹)⁻¹ := by group
    rw [he]
    exact S.inv_mem (hrep _)
  refine Finset.sum_bij (fun t _ => (rep (t * g) : H)) (fun t _ => (rep (t * g)).property)
    ?_ ?_ ?_
  · intro t ht s hs he
    have hs' : rep (t * g) = rep (s * g) := Subtype.ext he
    have hb : (⟨t, ht⟩ : {x : H // x ∈ T}) = ⟨s, hs⟩ :=
      (back g ⟨t, ht⟩).symm.trans ((congrArg (fun r : {x : H // x ∈ T} =>
        rep ((r : H) * g⁻¹)) hs').trans (back g ⟨s, hs⟩))
    exact congrArg Subtype.val hb
  · intro t ht
    refine ⟨rep (t * g⁻¹), (rep (t * g⁻¹)).property, ?_⟩
    have ht' : rep ((rep (t * g⁻¹) : H) * g) = ⟨t, ht⟩ := by
      simpa only [inv_inv] using back g⁻¹ ⟨t, ht⟩
    exact congrArg Subtype.val ht'
  · intro t _
    let ℓ : S := ⟨t * g * (rep (t * g) : H)⁻¹, hrep _⟩
    have hℓ : (ℓ : H) * (rep (t * g) : H) = t * g := by
      dsimp [ℓ]
      group
    exact (congrArg f hℓ).symm.trans (hf _ ℓ)

private theorem trace_central (inner : ConjEmbedding K H) (a : MonoidAlgebra Complex H)
    (ha : ∀ y : MonoidAlgebra Complex K, Commute (lift inner y) a)
    (T : Finset H) (hT : IsTransversal inner.toHom.range T) :
    ∀ y : MonoidAlgebra Complex H, Commute y (∑ t ∈ T, summand a t) := by
  let trace := ∑ t ∈ T, summand a t
  have conjugate (g : H) : basis g⁻¹ * trace * basis g = trace := by
    change basis g⁻¹ * (∑ t ∈ T, summand a t) * basis g = _
    rw [Finset.mul_sum, Finset.sum_mul]
    simp_rw [← summand_mul]
    exact sum_transversal_mul _ T hT (summand a) (summand_invariant inner a ha) g
  have central_basis (g : H) : basis g * trace = trace * basis g := by
    calc
      basis g * trace = basis g * (basis g⁻¹ * trace * basis g) :=
        congrArg (basis g * ·) (conjugate g).symm
      _ = trace * basis g := by
        rw [← mul_assoc, ← mul_assoc, ← basis_mul, mul_inv_cancel]
        change (1 : MonoidAlgebra Complex H) * trace * basis g = trace * basis g
        rw [one_mul]
  intro y
  change y * trace = trace * y
  refine MonoidAlgebra.induction_on (motive := fun z => z * trace = trace * z) y ?_ ?_ ?_
  · intro g
    exact central_basis g
  · intro x y hx hy
    rw [add_mul, mul_add, hx, hy]
  · intro r x hx
    rw [smul_mul_assoc, mul_smul_comm, hx]

private abbrev pair {A B C : Subgroup U} (p : Word A B) (q : Word B C) :=
  Biset.pairLinear Complex p.basis q.basis

private abbrev ev {A B : Subgroup U} {p q : Word A B} (d : Diagram Complex p q) :=
  d.eval.toLinearMap

variable (outer : ConjEmbedding H G) (inner : ConjEmbedding K H)

local notation "up" => Word.up outer
local notation "hk" => Word.up inner
local notation "kh" => Word.down inner
local notation "merged" => Word.up (outer.comp inner)
local notation "emptyH" => Word.empty H

private theorem dot_curl_tail_single (z : G) (t : H) (c : Complex) :
    ev (Diagram.rightUnit up)
      (ev (Diagram.horizontal (Diagram.id up) (Diagram.multiplicationCap inner))
        (ev (Diagram.associate up hk kh)
          (ev (Diagram.horizontal (Diagram.splitUp outer inner) (Diagram.id kh))
            (pair merged kh (Finsupp.single z c) (Finsupp.single t 1))))) =
      (MonoidAlgebra.single z c * basis (outer.toHom t)).coeff := by
  simp only [ev, pair]
  rw [Biset.pairLinear_single (R := Complex) (merged).basis (kh).basis z t c 1, mul_one]
  rw [Diagram.eval_horizontal_single (Diagram.splitUp outer inner) (Diagram.id kh),
    Diagram.eval_splitUp_single, Diagram.eval_id_apply,
    Biset.pairLinear_single (R := Complex) (Word.tensor up hk).basis (kh).basis _ t 1 1, one_mul]
  simp only [map_smul]
  rw [Diagram.eval_associate_single up hk kh,
    Diagram.eval_horizontal_single (Diagram.id up) (Diagram.multiplicationCap inner),
    one_smul, Diagram.eval_id_apply, Diagram.eval_multiplicationCap_single,
    one_mul, Biset.pairLinear_single (R := Complex) (up).basis (emptyH).basis z t 1 1,
    one_mul, Diagram.eval_rightUnit_single]
  have action : (up).basis.act (1, t⁻¹) z = z * outer.toHom t := by
    change 1 * z * (outer.toHom t⁻¹)⁻¹ = z * outer.toHom t
    simp
  rw [action]
  simp only [Finsupp.smul_single, smul_eq_mul, MonoidAlgebra.single_mul_single,
    mul_one, MonoidAlgebra.coeff_single]

private theorem dot_curl_tail (x : G →₀ Complex) (t : H) :
    ev (Diagram.rightUnit up)
      (ev (Diagram.horizontal (Diagram.id up) (Diagram.multiplicationCap inner))
        (ev (Diagram.associate up hk kh)
          (ev (Diagram.horizontal (Diagram.splitUp outer inner) (Diagram.id kh))
            (pair merged kh x (Finsupp.single t 1))))) =
      (MonoidAlgebra.ofCoeff x * basis (outer.toHom t)).coeff := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    have hpair :
        pair merged kh (x + y) (Finsupp.single t 1) =
          pair merged kh x (Finsupp.single t 1) + pair merged kh y (Finsupp.single t 1) :=
      LinearMap.congr_fun ((pair merged kh).map_add x y) _
    rw [hpair, map_add, map_add, map_add, map_add, hx, hy,
      MonoidAlgebra.ofCoeff_add, add_mul, MonoidAlgebra.coeff_add]
  | single z c => exact dot_curl_tail_single outer inner z t c


private def curlTail (middle : AlgebraUpDot Complex inner inner) :
    ScopedDiagram Complex (Word.tensor up (Word.tensor hk kh)) up :=
  .vertical (.ordinary (.unassociate up hk kh))
    (.vertical (.ordinary (.horizontal (.mergeUp outer inner) (.id kh)))
      (.vertical (.horizontal (.algebraUpDot (middle.whisker outer)) (.ordinary (.id kh)))
        (.vertical (.ordinary (.horizontal (.splitUp outer inner) (.id kh)))
          (.vertical (.ordinary (.associate up hk kh))
            (.vertical (.ordinary (.horizontal (.id up) (.multiplicationCap inner)))
              (.ordinary (.rightUnit up)))))))

-- The generator computation inserts the algebra-intertwiner evaluator
-- between the merge and split, with the downward factor carried through.
private theorem curl_term (middle : AlgebraUpDot Complex inner inner)
    (g : G) (t : H) :
    (curlTail outer inner middle).eval.toLinearMap
      (pair up (Word.tensor hk kh) (Finsupp.single g 1)
        (pair hk kh (Finsupp.single t⁻¹ 1) (Finsupp.single t 1))) =
      (basis g * lift outer (summand middle.label t)).coeff := by
  simp only [curlTail, ScopedDiagram.eval, Biset.Hom.vertical, LinearMap.comp_apply]
  rw [show (Diagram.horizontal (Diagram.mergeUp outer inner) (Diagram.id kh) :
      Diagram Complex _ _).eval =
      (Diagram.mergeUp outer inner : Diagram Complex _ _).eval.horizontal
        (Diagram.id kh).eval from rfl]
  simp only [pair]
  rw [Biset.pairLinear_single (R := Complex) (hk).basis (kh).basis t⁻¹ t 1 1, one_mul,
    Biset.pairLinear_single (R := Complex) (up).basis (Word.tensor hk kh).basis g _ 1 1, one_mul,
    Diagram.eval_unassociate_single up hk kh]
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_mergeUp_single, Diagram.eval_id_apply]
  rw [Biset.pairLinear_single (R := Complex) (merged).basis (kh).basis _ t 1 1, one_mul]
  rw [Biset.Hom.horizontal_single, one_smul, AlgebraUpDot.eval_apply, Diagram.eval_id_apply]
  rw [dot_curl_tail outer inner]
  simp only [MonoidAlgebra.ofCoeff_coeff, summand, map_mul, lift_basis]
  change (basis (g * outer.toHom t⁻¹) * lift outer middle.label *
    basis (outer.toHom t)).coeff = _
  simp only [basis_mul, mul_assoc]

private theorem curl_basis (middle : AlgebraUpDot Complex inner inner)
    (finite : inner.toHom.range.FiniteIndex) (T : Finset H)
    (cup : ev (Diagram.reverseCup inner finite) (Finsupp.single 1 1) =
      ∑ t ∈ T, pair hk kh (Finsupp.single t⁻¹ 1) (Finsupp.single t 1))
    (g : G) :
    (ScopedDiagram.rightCurlUp (RightCurlLabel.algebraDot outer middle) finite).eval.toLinearMap
      (Finsupp.single g 1) = (basis g * lift outer (∑ t ∈ T, summand middle.label t)).coeff := by
  have insert : ev (Diagram.insertRightUnit up) (Finsupp.single g 1) =
      Finsupp.single ((up).basis.pair (emptyH).basis g 1) 1 := by
    change (Biset.insertRightUnit (up).basis Complex).toLinearMap _ = _
    rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]
  change (curlTail outer inner middle).eval.toLinearMap
    (ev (Diagram.horizontal (Diagram.id up) (Diagram.reverseCup inner finite))
      (ev (Diagram.insertRightUnit up) (Finsupp.single g 1))) = _
  rw [insert, Diagram.eval_horizontal_single (Diagram.id up) (Diagram.reverseCup inner finite),
    one_smul, Diagram.eval_id_apply]
  change (curlTail outer inner middle).eval.toLinearMap
    (pair up (Word.tensor hk kh) (Finsupp.single g 1)
      (ev (Diagram.reverseCup inner finite) (Finsupp.single 1 1))) = _
  rw [cup, map_sum, map_sum, map_sum, Finset.mul_sum]
  change _ = (MonoidAlgebra.coeffLinearEquiv Complex) (∑ t ∈ T, basis g *
    lift outer (summand middle.label t))
  rw [map_sum]
  exact Finset.sum_congr rfl (fun t _ => curl_term outer inner middle g t)

private theorem groupDot_intertwines_algebra {p q : ConjEmbedding H G}
    (d : Dot p q) (b : MonoidAlgebra Complex H) :
    lift p b * basis d.element = basis d.element * lift q b := by
  induction b using MonoidAlgebra.induction_on with
  | of h =>
    change lift p (basis h) * basis d.element = basis d.element * lift q (basis h)
    rw [lift_basis, lift_basis, ← basis_mul, ← basis_mul, d.intertwines]
  | add x y hx hy => rw [map_add, map_add, add_mul, mul_add, hx, hy]
  | smul r x hx =>
    rw [map_smul, map_smul, smul_mul_assoc, mul_smul_comm, hx]

-- Each supported term of the sliding label intertwines the two lifted
-- algebra traces. Linearity assembles the equality at the fixed boundary.
private theorem trace_slide {p q : ConjEmbedding H G}
    (trace : AlgebraUpDot Complex (ConjEmbedding.id H) (ConjEmbedding.id H))
    (d : DotLabel Complex p q) :
    let dot := (DotLabel.upDrawing d).interpret
    let straight := fun r : ConjEmbedding H G => ScopedDiagram.algebraUpDot (trace.whisker r)
    (dot.vertical (straight q)).eval = ((straight p).vertical dot).eval := by
  dsimp only
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change (trace.whisker q).eval.toLinearMap
      ((DotLabel.upDrawing d).interpret.eval.toLinearMap x) =
    (DotLabel.upDrawing d).interpret.eval.toLinearMap
      ((trace.whisker p).eval.toLinearMap x)
  rw [DotLabel.eval_upDrawing, Diagram.linearUpDot, Diagram.eval_finiteSum,
    Diagram.eval_finiteSum, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  change (trace.whisker q).eval.toLinearMap (d e • ev (Diagram.upDot e) x) =
    d e • ev (Diagram.upDot e) ((trace.whisker p).eval.toLinearMap x)
  rw [map_smul]
  simp only [ev, ← AlgebraUpDot.eval_ofGroupDot]
  change d e • (MonoidAlgebra.ofCoeff x * basis e.element * lift q trace.label).coeff =
    d e • (MonoidAlgebra.ofCoeff x * lift p trace.label * basis e.element).coeff
  rw [mul_assoc, mul_assoc, groupDot_intertwines_algebra e]

end

end CurlWithCentralizingDotSupport
