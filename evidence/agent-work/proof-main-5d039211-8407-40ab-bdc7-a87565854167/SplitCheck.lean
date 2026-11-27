import MackeyDiagrams
import Proofs.EvaluationForTwoProjections

set_option maxHeartbeats 2000000

namespace CaseOneRightProjectionAux

open MackeyDiagrams
open scoped BigOperators
universe u
noncomputable section

-- The registered supplier proves the index formula for arbitrary crossing
-- types, and verifies the individual backward coordinates for the right
-- shape. Its implementation lemmas are private. These local aliases name
-- the exact compiled declarations; Lean checks the resulting proof terms.
open Lean Elab Tactic in
private abbrev crossingIndex := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "index_formula"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

private abbrev conjImage {P H : Type u} [Group P] [Group H] (q : P) (b : H →* P) :=
  Subgroup.map (MulAut.conj q).toMonoidHom b.range

section Crossings
variable {U : Type u} [Group U] {K H P L : Subgroup U}

private abbrev crossingUpper (a : ConjEmbedding K P) (b : ConjEmbedding H P) (q : P) :=
  a.toHom.range ⊓ conjImage q b.toHom

private theorem fiber_card {a : ConjEmbedding K P} {b : ConjEmbedding H P}
    {d : ConjEmbedding L K} {e : ConjEmbedding L H} (p : ProjectionDot.Mixed a b d e)
    (z : P)
    (hz : z ∈ Set.range (Generator.mixedProduct a b ∘
      Generator.mixedMultiplicationBasis a b d e p.dot)) :
    Nat.card {w // Generator.mixedMultiplicationBasis a b d e p.dot w =
      Generator.mixedPair a b z} =
      (a.comp d).toHom.range.relIndex (crossingUpper a b p.dot.element) := by
  have heq (w : ((Word.up d).tensor (.down e)).basis.carrier) :
      Generator.mixedMultiplicationBasis a b d e p.dot w = Generator.mixedPair a b z ↔
      Generator.mixedProduct a b (Generator.mixedMultiplicationBasis a b d e p.dot w) = z :=
    calc
      _ ↔ (Generator.mixedEquiv a b) (Generator.mixedMultiplicationBasis a b d e p.dot w) =
          (Generator.mixedEquiv a b) (Generator.mixedPair a b z) :=
        (Generator.mixedEquiv a b).apply_eq_iff_eq.symm
      _ ↔ _ := by
        change _ = (Generator.mixedEquiv a b) ((Generator.mixedEquiv a b).symm z) ↔ _
        rw [(Generator.mixedEquiv a b).apply_symm_apply z]
        rfl
  exact (Nat.card_congr (Equiv.subtypeEquivRight heq)).trans
    ((crossingIndex a b d e p.dot).2 z hz p.finite)

private theorem fiber_card_le {a : ConjEmbedding K P} {b : ConjEmbedding H P}
    {d : ConjEmbedding L K} {e : ConjEmbedding L H} (p : ProjectionDot.Mixed a b d e)
    (z : P) :
    Nat.card {w // Generator.mixedMultiplicationBasis a b d e p.dot w =
      Generator.mixedPair a b z} ≤
      (a.comp d).toHom.range.relIndex (crossingUpper a b p.dot.element) := by
  by_cases hz : z ∈ Set.range (Generator.mixedProduct a b ∘
      Generator.mixedMultiplicationBasis a b d e p.dot)
  · exact (fiber_card p z hz).le
  · have : IsEmpty {w // Generator.mixedMultiplicationBasis a b d e p.dot w =
      Generator.mixedPair a b z} := ⟨fun ⟨w, hw⟩ => hz ⟨w, by
        change Generator.mixedProduct a b (Generator.mixedMultiplicationBasis a b d e p.dot w) = z
        rw [hw]
        exact (Generator.mixedEquiv a b).apply_symm_apply z⟩⟩
    exact (Nat.card_eq_zero.mpr (Or.inl inferInstance)).le.trans (Nat.zero_le _)

private theorem relIndex_nonzero {a : ConjEmbedding K P} {b : ConjEmbedding H P}
    {d : ConjEmbedding L K} {e : ConjEmbedding L H} (p : ProjectionDot.Mixed a b d e) :
    (a.comp d).toHom.range.relIndex (crossingUpper a b p.dot.element) ≠ 0 :=
  Subgroup.finiteIndex_iff.mp ((crossingIndex a b d e p.dot).1.mp p.finite)

private def projectionOfIndex {a : ConjEmbedding K P} {b : ConjEmbedding H P}
    {d : ConjEmbedding L K} {e : ConjEmbedding L H} (p : Dot (a.comp d) (b.comp e))
    (hp : (a.comp d).toHom.range.relIndex (crossingUpper a b p.element) ≠ 0) :
    ProjectionDot.Mixed a b d e :=
  ⟨p, (crossingIndex a b d e p).1.mpr (Subgroup.finiteIndex_iff.mpr hp)⟩

end Crossings

private theorem conjImage_one {P H : Type u} [Group P] [Group H] (b : H →* P) :
    conjImage (1 : P) b = b.range := by
  ext z
  simp [conjImage, Subgroup.mem_map]

private theorem map_conjImage {P H T : Type u} [Group P] [Group H] [Group T]
    (j : P →* T) (q : P) (b : H →* P) :
    (conjImage q b).map j = conjImage (j q) (j.comp b) := by
  have hrange : b.range.map j = (j.comp b).range := MonoidHom.map_range j b
  unfold conjImage
  rw [← hrange, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

section Transport
variable {U : Type u} [Group U] {A G F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (bc : ConjEmbedding F A) (d : ConjEmbedding C G)
  (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev PP := ProjectionDot.Mixed a bc (d.comp e) f

private abbrev joinGroup (p : PP a bc d e f) :=
  (a.comp d).toHom.range ⊔ conjImage p.dot.element bc.toHom

private abbrev middleOK (p : PP a bc d e f) :=
  ((a.comp d).toHom.range.subgroupOf (a.toHom.range ⊓ joinGroup a bc d e f p)).FiniteIndex

private abbrev pIndex (p : PP a bc d e f) :=
  (a.comp (d.comp e)).toHom.range.relIndex (crossingUpper a bc p.dot.element)

private def restrictCodomain {H P : Subgroup U} (a : ConjEmbedding H P)
    (S : Subgroup P) (h : ∀ k, a.toHom k ∈ S) :
    ConjEmbedding H (S.map P.subtype) where
  toHom :=
    { toFun := fun k => ⟨(a.toHom k : U), ⟨a.toHom k, h k, rfl⟩⟩
      map_one' := Subtype.ext (congrArg (fun z : P => (z : U)) (map_one a.toHom))
      map_mul' x y := Subtype.ext (congrArg (fun z : P => (z : U)) (map_mul a.toHom x y)) }
  hasRepresentative := a.hasRepresentative

private def inclusion {P : Subgroup U} (S : Subgroup P) :
    ConjEmbedding (S.map P.subtype) P :=
  ConjEmbedding.ofConjugator 1 (by
    rintro ⟨z, x, _, rfl⟩
    simp [x.property])

private theorem inclusion_coe {P : Subgroup U} (S : Subgroup P) (x : S.map P.subtype) :
    ((inclusion S).toHom x : U) = (x : U) := by
  simp [inclusion]

private theorem inclusion_range {P : Subgroup U} (S : Subgroup P) :
    (inclusion S).toHom.range = S := by
  ext z
  constructor
  · rintro ⟨⟨x, y, hy, rfl⟩, hz⟩
    have he : y = z := Subtype.ext
      ((inclusion_coe S ⟨(y : U), y, hy, rfl⟩).symm.trans (congrArg (fun z : P => (z : U)) hz))
    exact he ▸ hy
  · intro hz
    exact ⟨⟨(z : U), z, hz, rfl⟩, Subtype.ext (inclusion_coe S _)⟩

private theorem inclusion_restrict {H P : Subgroup U} (a : ConjEmbedding H P)
    (S : Subgroup P) (h : ∀ k, a.toHom k ∈ S) :
    (inclusion S).comp (restrictCodomain a S h) = a :=
  ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (inclusion_coe S ⟨(a.toHom x : U), a.toHom x, h x, rfl⟩))

private def conjugate {H P : Subgroup U} (a : ConjEmbedding H P) (q : P) : ConjEmbedding H P where
  toHom := (MulAut.conj q).toMonoidHom.comp a.toHom
  hasRepresentative := by
    obtain ⟨t, ht⟩ := a.hasRepresentative
    refine ⟨(q : U) * t, ?_⟩
    intro x
    change (q : U) * (a.toHom x : U) * (q : U)⁻¹ = _
    rw [ht]
    group

private theorem upperIndexLe (p : PP a bc d e f)
    (j : ConjEmbedding B A) (v : ConjEmbedding C B) (w : ConjEmbedding F B)
    (q : B) (hv : j.comp v = a.comp d)
    (hw : conjImage (j.toHom q) (j.comp w).toHom = conjImage p.dot.element bc.toHom) :
    (v.comp e).toHom.range.relIndex (crossingUpper v w q) ≤ pIndex a bc d e f p ∧
    (v.comp e).toHom.range.relIndex (crossingUpper v w q) ≠ 0 := by
  have hlo : (v.comp e).toHom.range.map j.toHom = (a.comp (d.comp e)).toHom.range := by
    rw [MonoidHom.map_range]
    exact congrArg (fun k : ConjEmbedding C A => (k.comp e).toHom.range) hv
  have hup : (crossingUpper v w q).map j.toHom =
      (a.comp d).toHom.range ⊓ conjImage p.dot.element bc.toHom := by
    rw [crossingUpper, Subgroup.map_inf _ _ _ j.injective, MonoidHom.map_range, map_conjImage]
    exact congrArg₂ (· ⊓ ·) (congrArg (fun k : ConjEmbedding C A => k.toHom.range) hv) hw
  have hindex := Subgroup.relIndex_map_map_of_injective (v.comp e).toHom.range
    (crossingUpper v w q) j.injective
  rw [hlo, hup] at hindex
  have hle : (a.comp d).toHom.range ⊓ conjImage p.dot.element bc.toHom ≤
      crossingUpper a bc p.dot.element :=
    inf_le_inf_right _ (by rintro _ ⟨x, rfl⟩; exact ⟨d.toHom x, rfl⟩)
  rw [← hindex]
  exact ⟨Subgroup.relIndex_le_of_le_right hle (relIndex_nonzero p),
    fun h => relIndex_nonzero p (Subgroup.relIndex_eq_zero_of_le_right hle h)⟩


-- Theorem 6.4(1), sufficiency. The join initially lives inside A. Map it
-- into U to obtain an internal region of the project's common ambient type.
private theorem joinCrossings (p : PP a bc d e f) (hp : middleOK a bc d e f p) :
    let S := joinGroup a bc d e f p
    let B' := S.map A.subtype
    ∃ (j : ConjEmbedding B' A) (v : ConjEmbedding C B') (w : ConjEmbedding F B')
      (ell : Dot bc (j.comp w)) (m : ProjectionDot.Mixed a j d v)
      (n : ProjectionDot.Mixed v w e f),
      (∀ k : B', (j.toHom k : U) = (k : U)) ∧
      j.comp v = a.comp d ∧ j.comp w = conjugate bc p.dot.element ∧
      ell.element = p.dot.element⁻¹ ∧ m.dot.element = 1 ∧ n.dot.element = 1 ∧
      (∀ z : B', Nat.card {y // Generator.mixedMultiplicationBasis v w e f n.dot y =
        Generator.mixedPair v w z} ≤ pIndex a bc d e f p) := by
  intro S B'
  let p₀ := p.dot.element
  let j := inclusion S
  have hvm (x : C) : (a.comp d).toHom x ∈ S :=
    (show (a.comp d).toHom.range ≤ S from le_sup_left) ⟨x, rfl⟩
  have hwm (x : F) : (conjugate bc p₀).toHom x ∈ S :=
    (show conjImage p₀ bc.toHom ≤ S from le_sup_right) ⟨bc.toHom x, ⟨x, rfl⟩, rfl⟩
  let v := restrictCodomain (a.comp d) S hvm
  let w := restrictCodomain (conjugate bc p₀) S hwm
  have hv : j.comp v = a.comp d := inclusion_restrict _ _ _
  have hw : j.comp w = conjugate bc p₀ := inclusion_restrict _ _ _
  let ell : Dot bc (j.comp w) := ⟨p₀⁻¹, by
    intro x
    rw [hw]
    change bc.toHom x * p₀⁻¹ = p₀⁻¹ * (p₀ * bc.toHom x * p₀⁻¹)
    group⟩
  let md : Dot (a.comp d) (j.comp v) := ⟨1, by intro x; rw [hv, mul_one, one_mul]⟩
  have hm : (a.comp d).toHom.range.relIndex (crossingUpper a j md.element) ≠ 0 := by
    change (a.comp d).toHom.range.relIndex (a.toHom.range ⊓ conjImage 1 j.toHom) ≠ 0
    rw [conjImage_one, inclusion_range]
    exact Subgroup.finiteIndex_iff.mp hp
  let m := projectionOfIndex md hm
  let nd : Dot (v.comp e) (w.comp f) := ⟨1, by
    intro x
    rw [one_mul, mul_one]
    apply j.injective
    change (j.comp v).toHom (e.toHom x) = (j.comp w).toHom (f.toHom x)
    rw [hv, hw]
    change a.toHom (d.toHom (e.toHom x)) = p₀ * bc.toHom (f.toHom x) * p₀⁻¹
    have hi := p.dot.intertwines x
    change a.toHom (d.toHom (e.toHom x)) * p₀ = p₀ * bc.toHom (f.toHom x) at hi
    rw [← hi, mul_inv_cancel_right]⟩
  have hwMap : conjImage (j.toHom nd.element) (j.comp w).toHom = conjImage p₀ bc.toHom := by
    change conjImage (j.toHom 1) (j.comp w).toHom = _
    rw [map_one, conjImage_one, hw]
    exact (MonoidHom.map_range (MulAut.conj p₀).toMonoidHom bc.toHom).symm
  have hn := upperIndexLe a bc d e f p j v w nd.element hv hwMap
  let n := projectionOfIndex nd hn.2
  exact ⟨j, v, w, ell, m, n, inclusion_coe S, hv, hw, rfl, rfl, rfl,
    fun z => (fiber_card_le n z).trans hn.1⟩

-- Theorem 6.4(1), the common internal region A. The middle map is
-- surjective, so every fiber has the same size, including for z = 1.
private theorem commonCrossings (hd : d.toHom.range.FiniteIndex) :
    let j := ConjEmbedding.id A
    ∃ (ell : Dot bc (j.comp bc)) (m : ProjectionDot.Mixed a j d (a.comp d))
      (n : PP a bc d e f → ProjectionDot.Mixed (a.comp d) bc e f),
      ell.element = 1 ∧ m.dot.element = 1 ∧
      (∀ z : A, Nat.card {y // Generator.mixedMultiplicationBasis a j d (a.comp d) m.dot y =
        Generator.mixedPair a j z} = d.toHom.range.index) ∧
      (∀ p, (n p).dot.element = p.dot.element ∧
        ∀ z : A, Nat.card {y // Generator.mixedMultiplicationBasis (a.comp d) bc e f (n p).dot y =
          Generator.mixedPair (a.comp d) bc z} ≤ pIndex a bc d e f p) := by
  intro j
  let ell : Dot bc (j.comp bc) := ⟨1, by intro x; change _ * 1 = 1 * bc.toHom x; simp⟩
  let md : Dot (a.comp d) (j.comp (a.comp d)) :=
    ⟨1, by intro x; change _ * 1 = 1 * (a.comp d).toHom x; simp⟩
  have hr : j.toHom.range = ⊤ := by
    change (MonoidHom.id A).range = ⊤
    ext x
    simp
  have hindex : (a.comp d).toHom.range.relIndex (crossingUpper a j md.element) =
      d.toHom.range.index := by
    change (a.comp d).toHom.range.relIndex (a.toHom.range ⊓ conjImage 1 j.toHom) = _
    rw [conjImage_one, hr, inf_top_eq]
    change (a.toHom.comp d.toHom).range.relIndex a.toHom.range = _
    rw [← MonoidHom.map_range a.toHom d.toHom]
    have he := Subgroup.relIndex_map_map_of_injective d.toHom.range ⊤ a.injective
    rw [Subgroup.map_top] at he
    exact he.trans (Subgroup.relIndex_top_right _)
  let m := projectionOfIndex md (hindex ▸ Subgroup.finiteIndex_iff.mp hd)
  have hcard (z : A) : Nat.card {y // Generator.mixedMultiplicationBasis a j d (a.comp d) m.dot y =
      Generator.mixedPair a j z} = d.toHom.range.index := by
    refine (fiber_card m z ⟨(Biset.induction d).pair (Biset.restriction (a.comp d)) 1 z, ?_⟩).trans hindex
    change Generator.mixedProduct a j (Generator.mixedPair a j (a.toHom 1 * 1 * z)) = z
    simp
  let nd (p : PP a bc d e f) : Dot ((a.comp d).comp e) (bc.comp f) :=
    ⟨p.dot.element, p.dot.intertwines⟩
  have hn (p : PP a bc d e f) :=
    upperIndexLe a bc d e f p j (a.comp d) bc (nd p).element rfl rfl
  let n (p : PP a bc d e f) := projectionOfIndex (nd p) (hn p).2
  exact ⟨ell, m, n, rfl, rfl, hcard, fun p => ⟨rfl, fun z =>
    (fiber_card_le (n p) z).trans (hn p).1⟩⟩

end Transport

open Lean Elab Tactic in
private abbrev rightDot := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "rightDot"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev pulls_right := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "pulls_right"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev pulls_mixed := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "pulls_mixed"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev mergedEval := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "mergedEval"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev leftDrawing := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "leftDrawing"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev rightDrawing := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "rightDrawing"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev ev := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "ev"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev atRight := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "atRight"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev atLeft := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "atLeft"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev splitBottom := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "splitBottom"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev mergeTop := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "mergeTop"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev weighted := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "weighted"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev weighted_parallel := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "weighted_parallel"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev weighted_compact := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "weighted_compact"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev weighted_atLeft := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "weighted_atLeft"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev weighted_atRight := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "weighted_atRight"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev weighted_stack_mem := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "weighted_stack_mem"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev composeAround := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "composeAround"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev map_weighted := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "map_weighted"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

open Lean Elab Tactic in
private abbrev combination_injective := by
  run_tac
    let n := Name.str (Name.str (Name.num `_private.Proofs.EvaluationForTwoProjections 0)
      "EvaluationForTwoProjectionsAux") "combination_injective"
    evalTactic (← `(tactic| exact @$(mkIdent n)))

section Evaluation
variable {U : Type u} [Group U] {G A D F C E B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev Param := PP a (b.comp c) d e f

private abbrev Qstar (p : Param a b c d e f) :=
  (Diagram.mixedProjection (R := Complex) a (b.comp c) (d.comp e) f p.dot p.finite).eval.toLinearMap

private abbrev comb := Finsupp.linearCombination Complex (Qstar a b c d e f)

private theorem traceRight {j : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f)
    (x : ((Word.down a).tensor (.up (b.comp c))).basis.carrier →₀ Complex)
    (y : ((Word.up (d.comp e)).tensor (.down f)).basis.carrier) :
    mergedEval a b c d e f (rightDrawing a b c d e f j v w [(1,ell)] [(1,m)] [(1,n)]) x y =
      x (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f
        (rightDot a b c d e f ell m n) y) := by
  exact Quotient.inductionOn y (fun ⟨g,h⟩ => pulls_right a b c d e f ell m n g h x)

-- Lemma 6.3 gives p = m j(n) ell⁻¹. Retain that parameter, including the
-- proof that its fibers are finite, to apply the subgroup test termwise.
private def compositeParameter {j : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f) :
    Param a b c d e f := by
  classical
  refine ⟨rightDot a b c d e f ell m n, fun z => ?_⟩
  let L := mergedEval a b c d e f (rightDrawing a b c d e f j v w [(1,ell)] [(1,m)] [(1,n)])
  apply (L (Finsupp.single z 1)).support.finite_toSet.subset
  intro y hy
  change Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f
    (rightDot a b c d e f ell m n) y = z at hy
  exact Finsupp.mem_support_iff.mpr (by
    change L (Finsupp.single z 1) y ≠ 0
    rw [traceRight, hy, Finsupp.single_eq_same]
    exact one_ne_zero)

private theorem right_singleton {j : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f)
    (p : Param a b c d e f)
    (hp : m.dot.element * j.toHom n.dot.element * ell.element⁻¹ = p.dot.element) :
    mergedEval a b c d e f (rightDrawing a b c d e f j v w [(1,ell)] [(1,m)] [(1,n)]) =
      Qstar a b c d e f p := by
  have hdot : rightDot a b c d e f ell m n = p.dot := Dot.ext hp
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro y
  rw [traceRight, hdot]
  exact (pulls_mixed a (b.comp c) (d.comp e) f p y x).symm

-- Theorem 6.4(1), necessity for a singleton triple. Both generators of
-- the join lie in m j(B') m⁻¹. Use the index tower at the actual middle
-- crossing, whose finite-fiber witness supplies the nonzero index.
private theorem composite_middle {j : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f) :
    middleOK a (b.comp c) d e f (compositeParameter a b c d e f ell m n) := by
  let p := compositeParameter a b c d e f ell m n
  let J := conjImage m.dot.element j.toHom
  have hl : (a.comp d).toHom.range ≤ J := by
    rintro _ ⟨x, rfl⟩
    have hm := m.dot.intertwines x
    change a.toHom (d.toHom x) * m.dot.element =
      m.dot.element * j.toHom (v.toHom x) at hm
    refine ⟨j.toHom (v.toHom x), ⟨v.toHom x, rfl⟩, ?_⟩
    change m.dot.element * j.toHom (v.toHom x) * m.dot.element⁻¹ = a.toHom (d.toHom x)
    rw [← hm, mul_inv_cancel_right]
  have hr : conjImage p.dot.element (b.comp c).toHom ≤ J := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    let ell₀ := ell.element
    let m₀ := m.dot.element
    let n₀ := n.dot.element
    have he := ell.intertwines x
    change (b.comp c).toHom x * ell₀ = ell₀ * j.toHom (w.toHom x) at he
    have he' : ell₀⁻¹ * (b.comp c).toHom x * ell₀ = j.toHom (w.toHom x) := by
      rw [mul_assoc, he, inv_mul_cancel_left]
    refine ⟨j.toHom (n₀ * w.toHom x * n₀⁻¹), ⟨_, rfl⟩, ?_⟩
    change m₀ * j.toHom (n₀ * w.toHom x * n₀⁻¹) * m₀⁻¹ =
      (m₀ * j.toHom n₀ * ell₀⁻¹) * (b.comp c).toHom x * (m₀ * j.toHom n₀ * ell₀⁻¹)⁻¹
    rw [map_mul, map_mul, map_inv, ← he']
    group
  let low := (a.comp d).toHom.range
  let mid := a.toHom.range ⊓ joinGroup a (b.comp c) d e f p
  let high := a.toHom.range ⊓ J
  have hlow : low ≤ mid := le_inf (by rintro _ ⟨x, rfl⟩; exact ⟨d.toHom x, rfl⟩) le_sup_left
  have hmid : mid ≤ high := inf_le_inf_left _ (sup_le hl hr)
  have ht := Subgroup.relIndex_mul_relIndex low mid high hlow hmid
  apply Subgroup.finiteIndex_iff.mpr
  intro hz
  change low.relIndex mid = 0 at hz
  rw [hz, zero_mul] at ht
  exact relIndex_nonzero m ht.symm

private def labelTerms {X : Type u} (xs : X →₀ Complex) : List (Complex × X) :=
  xs.support.toList.map fun x => (xs x, x)

private theorem labelTerms_single {X : Type u} (x : X) {weight : Complex} (h : weight ≠ 0) :
    labelTerms (Finsupp.single x weight) = [(weight,x)] := by
  simp [labelTerms, Finsupp.support_single _ h]

private theorem weighted_labelTerms {X : Type u} {M : Type*} [AddCommMonoid M] [Module Complex M]
    (s : X → M) (xs : X →₀ Complex) :
    weighted s (labelTerms xs) = Finsupp.linearCombination Complex s xs := by
  change ((xs.support.toList.map fun x => (xs x, x)).map
    fun t : Complex × X => t.1 • s t.2).sum = _
  rw [List.map_map, Finsupp.linearCombination_apply]
  exact Finset.sum_map_toList xs.support (fun i => xs i • s i)


section RightStages
variable (j : ConjEmbedding B' A) (v : ConjEmbedding C B') (w : ConjEmbedding F B')

private abbrev stageOne (xs : List (Complex × Dot (b.comp c) (j.comp w))) :=
  atRight (.down a) (.parallelUp b c j w xs)

private abbrev stageTwo (ys : List (Complex × ProjectionDot.Mixed a j d v)) :=
  atLeft (.compactProjection a j d v ys) (.up w)

private abbrev stageThree (zs : List (Complex × ProjectionDot.Mixed v w e f)) :=
  atRight (.up d) (.compactProjection v w e f zs)

private theorem stageOne_weighted (xs : List (Complex × Dot (b.comp c) (j.comp w))) :
    ev (stageOne a b c j w xs) = weighted (fun x => ev (stageOne a b c j w [(1,x)])) xs :=
  weighted_atRight (.down a) _ _ xs (weighted_parallel b c j w xs)

private theorem stageTwo_weighted (ys : List (Complex × ProjectionDot.Mixed a j d v)) :
    ev (stageTwo a d j v w ys) = weighted (fun y => ev (stageTwo a d j v w [(1,y)])) ys :=
  weighted_atLeft _ _ ys (weighted_compact a j d v ys)

private theorem stageThree_weighted (zs : List (Complex × ProjectionDot.Mixed v w e f)) :
    ev (stageThree d e f v w zs) = weighted (fun z => ev (stageThree d e f v w [(1,z)])) zs :=
  weighted_atRight (.up d) _ _ zs (weighted_compact v w e f zs)

private theorem right_linear_top (xs : List (Complex × Dot (b.comp c) (j.comp w)))
    (ys : List (Complex × ProjectionDot.Mixed a j d v)) (zs : ProjectionDot.Mixed v w e f →₀ Complex) :
    mergedEval a b c d e f (rightDrawing a b c d e f j v w xs ys (labelTerms zs)) =
      Finsupp.linearCombination Complex
        (fun n => mergedEval a b c d e f (rightDrawing a b c d e f j v w xs ys [(1,n)])) zs := by
  rw [← weighted_labelTerms]
  let pre := (ev (stageTwo a d j v w ys)).comp
    ((ev (stageOne a b c j w xs)).comp (ev (splitBottom a b c)))
  let frame := composeAround pre (ev (mergeTop d e f))
  change frame (ev (stageThree d e f v w (labelTerms zs))) = _
  rw [stageThree_weighted, map_weighted]
  rfl

end RightStages

private abbrev allowed (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F) :=
  Finsupp.supported Complex Complex {p : Param a b c d e f | middleOK a (b.comp c) d e f p}

private abbrev allowedEvals := (allowed a b c d e f).map (comb a b c d e f)

-- Theorem 6.4(1), finite sums. Linearity puts the evaluation in the image of
-- the submodule of coefficients supported on admissible middle indices.
-- This permits cancellations while retaining the condition on final support.
private theorem right_supported (j : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B') (xs : List (Complex × Dot (b.comp c) (j.comp w)))
    (ys : List (Complex × ProjectionDot.Mixed a j d v)) (zs : List (Complex × ProjectionDot.Mixed v w e f)) :
    mergedEval a b c d e f (rightDrawing a b c d e f j v w xs ys zs) ∈ allowedEvals a b c d e f := by
  let pre := ev (splitBottom a b c)
  let post := ev (mergeTop d e f)
  change post.comp ((ev (stageThree d e f v w zs)).comp ((ev (stageTwo a d j v w ys)).comp
    ((ev (stageOne a b c j w xs)).comp pre))) ∈ allowedEvals a b c d e f
  rw [stageOne_weighted, stageTwo_weighted, stageThree_weighted]
  apply weighted_stack_mem
  intro ell m n
  let p := compositeParameter a b c d e f ell m n
  change mergedEval a b c d e f (rightDrawing a b c d e f j v w [(1,ell)] [(1,m)] [(1,n)]) ∈ _
  rw [right_singleton a b c d e f ell m n p rfl]
  apply Submodule.mem_map.mpr
  refine ⟨Finsupp.single p 1, ?_, ?_⟩
  · rw [allowed, Finsupp.mem_supported, Finsupp.support_single p one_ne_zero]
    intro q hq
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact composite_middle a b c d e f ell m n
  · rw [Finsupp.linearCombination_single, one_smul]

private theorem mergedEval_add
    (x y : LabelledDrawing Complex (((Word.down a).tensor (.up b)).tensor (.up c))
      (((Word.up d).tensor (.up e)).tensor (.down f))) :
    mergedEval a b c d e f (.add x y) =
      mergedEval a b c d e f x + mergedEval a b c d e f y := by
  let frame := composeAround (ev (splitBottom a b c)) (ev (mergeTop d e f))
  change frame (ev x + ev y) = frame (ev x) + frame (ev y)
  exact map_add frame _ _

private theorem mergedEval_zero :
    mergedEval a b c d e f (.ordinary (.zero
      (((Word.down a).tensor (.up b)).tensor (.up c))
      (((Word.up d).tensor (.up e)).tensor (.down f)))) = 0 := by
  let frame := composeAround (ev (splitBottom a b c)) (ev (mergeTop d e f))
  change frame 0 = 0
  exact map_zero frame

private theorem evaluate_sumDrawings
    (ds : List (LabelledDrawing Complex (((Word.down a).tensor (.up b)).tensor (.up c))
      (((Word.up d).tensor (.up e)).tensor (.down f)))) :
    (mergedEval a b c d e f (match ds with
      | [] => .ordinary (.zero _ _)
      | first :: rest => rest.foldl LabelledDrawing.add first)) =
      (ds.map (mergedEval a b c d e f)).sum := by
  have hf (first : LabelledDrawing Complex (((Word.down a).tensor (.up b)).tensor (.up c))
      (((Word.up d).tensor (.up e)).tensor (.down f))) (rest : List _) :
      mergedEval a b c d e f (rest.foldl LabelledDrawing.add first) =
        mergedEval a b c d e f first + (rest.map (mergedEval a b c d e f)).sum := by
    induction rest generalizing first with
    | nil => simp
    | cons second rest ih =>
      rw [List.foldl_cons, ih, mergedEval_add, List.map_cons, List.sum_cons, add_assoc]
  cases ds with
  | nil => exact mergedEval_zero a b c d e f
  | cons first rest => exact hf first rest


private abbrev Drawing :=
  LabelledDrawing Complex (((Word.down a).tensor (.up b)).tensor (.up c))
    (((Word.up d).tensor (.up e)).tensor (.down f))

private def sumDrawings (ds : List (Drawing a b c d e f)) : Drawing a b c d e f :=
  match ds with
  | [] => .ordinary (.zero _ _)
  | first :: rest => rest.foldl LabelledDrawing.add first

private abbrev rightLabels (j : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B') (xs : DotLabel Complex (b.comp c) (j.comp w))
    (ys : ProjectionDot.Mixed a j d v →₀ Complex) (zs : ProjectionDot.Mixed v w e f →₀ Complex) :=
  rightDrawing a b c d e f j v w (labelTerms xs) (labelTerms ys) (labelTerms zs)

private def IsRight (drawing : Drawing a b c d e f) : Prop :=
  ∃ (B' : Subgroup U) (j : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B') (xs : DotLabel Complex (b.comp c) (j.comp w))
    (ys : ProjectionDot.Mixed a j d v →₀ Complex) (zs : ProjectionDot.Mixed v w e f →₀ Complex),
    drawing = rightLabels a b c d e f j v w xs ys zs

private theorem right_weight {j : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f)
    (p : Param a b c d e f) (z : Complex)
    (hp : m.dot.element * j.toHom n.dot.element * ell.element⁻¹ = p.dot.element) :
    mergedEval a b c d e f (rightLabels a b c d e f j v w (Finsupp.single ell 1)
      (Finsupp.single m 1) (Finsupp.single n z)) = z • Qstar a b c d e f p := by
  unfold rightLabels
  rw [labelTerms_single ell one_ne_zero, labelTerms_single m one_ne_zero,
    right_linear_top, Finsupp.linearCombination_single, right_singleton a b c d e f ell m n p hp]

private theorem realize_weight (p : Param a b c d e f) (hp : middleOK a (b.comp c) d e f p) (z : Complex) :
    ∃ drawing : Drawing a b c d e f, IsRight a b c d e f drawing ∧
      mergedEval a b c d e f drawing = z • Qstar a b c d e f p := by
  obtain ⟨j,v,w,ell,m,n,_,_,_,he,hm,hn,_⟩ := joinCrossings a (b.comp c) d e f p hp
  refine ⟨rightLabels a b c d e f j v w (Finsupp.single ell 1) (Finsupp.single m 1)
    (Finsupp.single n z), ⟨_,j,v,w,_,_,_,rfl⟩, ?_⟩
  apply right_weight a b c d e f ell m n p z
  simp only [he, hm, hn, map_one, one_mul, inv_inv]

private theorem right_sum_supported (ds : List (Drawing a b c d e f))
    (hds : ∀ drawing ∈ ds, IsRight a b c d e f drawing) :
    mergedEval a b c d e f (sumDrawings a b c d e f ds) ∈ allowedEvals a b c d e f := by
  have hs : mergedEval a b c d e f (sumDrawings a b c d e f ds) =
      (ds.map (mergedEval a b c d e f)).sum := evaluate_sumDrawings a b c d e f ds
  rw [hs]
  apply list_sum_mem
  intro val hval
  obtain ⟨drawing, hd, rfl⟩ := List.mem_map.mp hval
  obtain ⟨_,j,v,w,xs,ys,zs,rfl⟩ := hds drawing hd
  exact right_supported a b c d e f j v w (labelTerms xs) (labelTerms ys) (labelTerms zs)

private theorem finite_replacement (target : Drawing a b c d e f)
    (coeff : Param a b c d e f →₀ Complex)
    (hleft : mergedEval a b c d e f target = coeff.sum (fun p z => z • Qstar a b c d e f p)) :
    (∃ ds : List (Drawing a b c d e f), (∀ drawing ∈ ds, IsRight a b c d e f drawing) ∧
      mergedEval a b c d e f (sumDrawings a b c d e f ds) = mergedEval a b c d e f target) ↔
    ∀ p ∈ coeff.support, middleOK a (b.comp c) d e f p := by
  classical
  rw [← Finsupp.linearCombination_apply] at hleft
  constructor
  · rintro ⟨ds, hds, hvalue⟩
    obtain ⟨weights, hw, he⟩ := Submodule.mem_map.mp (right_sum_supported a b c d e f ds hds)
    have eq : weights = coeff :=
      combination_injective a b c d e f (he.trans (hvalue.trans hleft))
    subst weights
    exact (Finsupp.mem_supported Complex coeff).mp hw
  · intro hcoeff
    -- Put each coefficient on the upper mark so every summand is a
    -- complete right diagram at the prescribed boundary.
    let indices := coeff.support.attach.toList
    have hrealize (p : {p // p ∈ coeff.support}) :=
      realize_weight a b c d e f p.1 (hcoeff p.1 p.2) (coeff p.1)
    let chooseDrawing p := Classical.choose (hrealize p)
    let ds := indices.map chooseDrawing
    refine ⟨ds, ?_, ?_⟩
    · intro drawing hd
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hd
      exact (Classical.choose_spec (hrealize p)).1
    · have hs : mergedEval a b c d e f (sumDrawings a b c d e f ds) =
          (ds.map (mergedEval a b c d e f)).sum := evaluate_sumDrawings a b c d e f ds
      rw [hs, hleft]
      change ((indices.map chooseDrawing).map (mergedEval a b c d e f)).sum = _
      rw [List.map_map]
      have hm : indices.map (mergedEval a b c d e f ∘ chooseDrawing) =
          indices.map (fun p => coeff p.1 • Qstar a b c d e f p.1) :=
        List.map_congr_left (fun p _ => (Classical.choose_spec (hrealize p)).2)
      rw [hm]
      have hc : (indices.map (fun p => coeff p.1 • Qstar a b c d e f p.1)).sum =
          ∑ p ∈ coeff.support.attach, coeff p.1 • Qstar a b c d e f p.1 :=
        Finset.sum_map_toList _ _
      rw [hc, Finsupp.linearCombination_apply]
      exact Finset.sum_attach coeff.support (fun p => coeff p • Qstar a b c d e f p)


private theorem joinImplementation (p : Param a b c d e f) (hp : middleOK a (b.comp c) d e f p) :
    let B' := (joinGroup a (b.comp c) d e f p).map A.subtype
    let p₀ := p.dot.element
    ∃ (j : ConjEmbedding B' A) (v : ConjEmbedding C B') (w : ConjEmbedding F B')
      (ell : Dot (b.comp c) (j.comp w)) (m : ProjectionDot.Mixed a j d v)
      (n : ProjectionDot.Mixed v w e f),
      (∀ k : B', (j.toHom k : U) = (k : U)) ∧
      (∀ k : C, j.toHom (v.toHom k) = (a.comp d).toHom k) ∧
      (∀ k : F, j.toHom (w.toHom k) = (MulAut.conj p₀) ((b.comp c).toHom k)) ∧
      ell.element = p₀⁻¹ ∧ m.dot.element = 1 ∧ n.dot.element = 1 ∧
      (∀ z : B', Nat.card {y // Generator.mixedMultiplicationBasis v w e f n.dot y =
        Generator.mixedPair v w z} ≤ pIndex a (b.comp c) d e f p) ∧
      mergedEval a b c d e f (rightLabels a b c d e f j v w (Finsupp.single ell 1)
        (Finsupp.single m 1) (Finsupp.single n 1)) = Qstar a b c d e f p := by
  obtain ⟨j,v,w,ell,m,n,hj,hv,hw,he,hm,hn,hcard⟩ := joinCrossings a (b.comp c) d e f p hp
  refine ⟨j,v,w,ell,m,n,hj, ?_, ?_, he, hm, hn, hcard, ?_⟩
  · intro k
    exact congrArg (fun i : ConjEmbedding C A => i.toHom k) hv
  · intro k
    exact congrArg (fun i : ConjEmbedding F A => i.toHom k) hw
  · simpa only [one_smul] using right_weight a b c d e f ell m n p 1 (by
      simp only [he, hm, hn, map_one, one_mul, inv_inv])

private theorem commonImplementation (hd : d.toHom.range.FiniteIndex) :
    let j := ConjEmbedding.id A
    ∃ (ell : Dot (b.comp c) (j.comp (b.comp c))) (m : ProjectionDot.Mixed a j d (a.comp d))
      (n : Param a b c d e f → ProjectionDot.Mixed (a.comp d) (b.comp c) e f),
      ell.element = 1 ∧ m.dot.element = 1 ∧
      (∀ z : A, Nat.card {y // Generator.mixedMultiplicationBasis a j d (a.comp d) m.dot y =
        Generator.mixedPair a j z} = d.toHom.range.index) ∧
      (∀ p, (n p).dot.element = p.dot.element ∧
        ∀ z : A, Nat.card {y // Generator.mixedMultiplicationBasis (a.comp d) (b.comp c) e f (n p).dot y =
          Generator.mixedPair (a.comp d) (b.comp c) z} ≤ pIndex a (b.comp c) d e f p) ∧
      (∀ coeff : Param a b c d e f →₀ Complex,
        mergedEval a b c d e f (rightLabels a b c d e f j (a.comp d) (b.comp c)
          (Finsupp.single ell 1) (Finsupp.single m 1) (Finsupp.mapDomain n coeff)) =
          coeff.sum (fun p z => z • Qstar a b c d e f p)) := by
  intro j
  obtain ⟨ell,m,n,he,hm,hcard,hn⟩ := commonCrossings a (b.comp c) d e f hd
  refine ⟨ell, m, n, he, hm, hcard, hn, ?_⟩
  intro coeff
  rw [← Finsupp.linearCombination_apply]
  unfold rightLabels
  rw [labelTerms_single ell one_ne_zero, labelTerms_single m one_ne_zero, right_linear_top,
    Finsupp.linearCombination_mapDomain]
  apply congrArg (fun q => Finsupp.linearCombination Complex q coeff)
  funext p
  apply right_singleton a b c d e f ell m (n p) p
  change m.dot.element * (n p).dot.element * ell.element⁻¹ = p.dot.element
  simp only [he, hm, (hn p).1, inv_one, one_mul, mul_one]


end Evaluation
end
end CaseOneRightProjectionAux

namespace CaseOneRightProjectionAux

private theorem joinConnection : (
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let ade := comp a de
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : Drawing) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let fiberSize := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : ProjectionLabel α β η θ) (z : P) =>
    Nat.card {w // MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ
      (MackeyDiagrams.ProjectionDot.dot x) w = MackeyDiagrams.Generator.mixedPair α β z}
  let Parameter := ProjectionLabel a bc de f
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let terms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s (terms xs)) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f (terms ys)))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e (MackeyDiagrams.DotLabel.terms zs))
          (drawId (down f))))
  let right := fun {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c j w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))
  let IsRight := fun (drawing : Drawing) =>
    ∃ (B' : Subgroup U) (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex),
      drawing = right j v w ells ms ns
  let sumDrawings := fun (ds : List Drawing) =>
    match ds with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let conjugatedImage := fun (p : Parameter) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj
      (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p))))
      (MonoidHom.range (hom bc))
  let join := fun (p : Parameter) => MonoidHom.range (hom ad) ⊔ conjugatedImage p
  let middleFinite := fun (p : Parameter) =>
    Subgroup.FiniteIndex (Subgroup.subgroupOf (MonoidHom.range (hom ad))
      (MonoidHom.range (hom a) ⊓ join p))
  let nₚ := fun (p : Parameter) =>
    Subgroup.relIndex (MonoidHom.range (hom ade)) (MonoidHom.range (hom a) ⊓ conjugatedImage p)
  let expansion := fun (coeff : Finsupp Parameter Complex) =>
    Finsupp.sum coeff (fun p weight => weight • Qstar p)
  (∀ (p : Parameter), middleFinite p →
    let B' := Subgroup.map (Subgroup.subtype A) (join p)
    let p₀ := MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p)
    ∃ (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ell : MackeyDiagrams.Dot bc (comp j w))
      (m : ProjectionLabel a j d v) (n : ProjectionLabel v w e f),
      (∀ k : B', (hom j k : U) = (k : U)) ∧
      (∀ k : C, hom j (hom v k) = hom ad k) ∧
      (∀ k : F, hom j (hom w k) = (MulAut.conj p₀) (hom bc k)) ∧
      MackeyDiagrams.Dot.element ell = p₀⁻¹ ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m) = 1 ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot n) = 1 ∧
      (∀ z : B', fiberSize v w e f n z ≤ nₚ p) ∧
      eval (right j v w (Finsupp.single ell 1) (Finsupp.single m 1) (Finsupp.single n 1)) =
        Qstar p)
) := by
  classical
  intro U inst G A D F C E a b c d e f
  exact joinImplementation a b c d e f

private theorem commonConnection : (
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let ade := comp a de
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : Drawing) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let fiberSize := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : ProjectionLabel α β η θ) (z : P) =>
    Nat.card {w // MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ
      (MackeyDiagrams.ProjectionDot.dot x) w = MackeyDiagrams.Generator.mixedPair α β z}
  let Parameter := ProjectionLabel a bc de f
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let terms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s (terms xs)) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f (terms ys)))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e (MackeyDiagrams.DotLabel.terms zs))
          (drawId (down f))))
  let right := fun {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c j w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))
  let IsRight := fun (drawing : Drawing) =>
    ∃ (B' : Subgroup U) (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex),
      drawing = right j v w ells ms ns
  let sumDrawings := fun (ds : List Drawing) =>
    match ds with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let conjugatedImage := fun (p : Parameter) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj
      (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p))))
      (MonoidHom.range (hom bc))
  let join := fun (p : Parameter) => MonoidHom.range (hom ad) ⊔ conjugatedImage p
  let middleFinite := fun (p : Parameter) =>
    Subgroup.FiniteIndex (Subgroup.subgroupOf (MonoidHom.range (hom ad))
      (MonoidHom.range (hom a) ⊓ join p))
  let nₚ := fun (p : Parameter) =>
    Subgroup.relIndex (MonoidHom.range (hom ade)) (MonoidHom.range (hom a) ⊓ conjugatedImage p)
  let expansion := fun (coeff : Finsupp Parameter Complex) =>
    Finsupp.sum coeff (fun p weight => weight • Qstar p)
  (Subgroup.FiniteIndex (MonoidHom.range (hom d)) →
    let j := MackeyDiagrams.ConjEmbedding.id A
    ∃ (ell : MackeyDiagrams.Dot bc (comp j bc)) (m : ProjectionLabel a j d ad)
      (n : Parameter → ProjectionLabel ad bc e f),
      MackeyDiagrams.Dot.element ell = 1 ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m) = 1 ∧
      (∀ z : A, fiberSize a j d ad m z = Subgroup.index (MonoidHom.range (hom d))) ∧
      (∀ (p : Parameter), MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot (n p)) =
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p) ∧
          (∀ z : A, fiberSize ad bc e f (n p) z ≤ nₚ p)) ∧
      (∀ (coeff : Finsupp Parameter Complex),
        eval (right j ad bc (Finsupp.single ell 1) (Finsupp.single m 1)
          (Finsupp.mapDomain n coeff)) = expansion coeff))
) := by
  classical
  intro U inst G A D F C E a b c d e f
  exact commonImplementation a b c d e f

private theorem sumConnection : (
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let ade := comp a de
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : Drawing) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let fiberSize := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : ProjectionLabel α β η θ) (z : P) =>
    Nat.card {w // MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ
      (MackeyDiagrams.ProjectionDot.dot x) w = MackeyDiagrams.Generator.mixedPair α β z}
  let Parameter := ProjectionLabel a bc de f
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let terms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s (terms xs)) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f (terms ys)))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e (MackeyDiagrams.DotLabel.terms zs))
          (drawId (down f))))
  let right := fun {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c j w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))
  let IsRight := fun (drawing : Drawing) =>
    ∃ (B' : Subgroup U) (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex),
      drawing = right j v w ells ms ns
  let sumDrawings := fun (ds : List Drawing) =>
    match ds with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let conjugatedImage := fun (p : Parameter) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj
      (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p))))
      (MonoidHom.range (hom bc))
  let join := fun (p : Parameter) => MonoidHom.range (hom ad) ⊔ conjugatedImage p
  let middleFinite := fun (p : Parameter) =>
    Subgroup.FiniteIndex (Subgroup.subgroupOf (MonoidHom.range (hom ad))
      (MonoidHom.range (hom a) ⊓ join p))
  let nₚ := fun (p : Parameter) =>
    Subgroup.relIndex (MonoidHom.range (hom ade)) (MonoidHom.range (hom a) ⊓ conjugatedImage p)
  let expansion := fun (coeff : Finsupp Parameter Complex) =>
    Finsupp.sum coeff (fun p weight => weight • Qstar p)
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de)
      (coeff : Finsupp Parameter Complex), eval (left r s t xs ys zs) = expansion coeff →
    ((∃ ds : List Drawing,
        (∀ drawing ∈ ds, IsRight drawing) ∧
        eval (sumDrawings ds) = eval (left r s t xs ys zs)) ↔
      ∀ p ∈ Finsupp.support coeff, middleFinite p))
) := by
  classical
  intro U inst G A D F C E a b c d e f
  intro B r s t xs ys zs coeff hleft
  exact finite_replacement a b c d e f
    (leftDrawing a b c d e f r s t (labelTerms xs) (labelTerms ys) (labelTerms zs)) coeff hleft

end CaseOneRightProjectionAux


theorem CaseOneRightProjectionConstruction : (
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
  let bc := comp b c
  let ad := comp a d
  let de := comp d e
  let ade := comp a de
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
    MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
      (drawId (down f))
  let eval := fun (drawing : Drawing) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
  let atRight := fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
  let ProjectionLabel := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ
  let fiberSize := fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H)
      (x : ProjectionLabel α β η θ) (z : P) =>
    Nat.card {w // MackeyDiagrams.Generator.mixedMultiplicationBasis α β η θ
      (MackeyDiagrams.ProjectionDot.dot x) w = MackeyDiagrams.Generator.mixedPair α β z}
  let Parameter := ProjectionLabel a bc de f
  let Qstar := fun (p : Parameter) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
  let terms := fun {X : Type u} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let left := fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.compactProjection a b r s (terms xs)) (drawId (up c)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f (terms ys)))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e (MackeyDiagrams.DotLabel.terms zs))
          (drawId (down f))))
  let right := fun {B' : Subgroup U} (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c j w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a j d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))
  let IsRight := fun (drawing : Drawing) =>
    ∃ (B' : Subgroup U) (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ells : MackeyDiagrams.DotLabel Complex bc (comp j w))
      (ms : Finsupp (ProjectionLabel a j d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex),
      drawing = right j v w ells ms ns
  let sumDrawings := fun (ds : List Drawing) =>
    match ds with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let conjugatedImage := fun (p : Parameter) =>
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj
      (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p))))
      (MonoidHom.range (hom bc))
  let join := fun (p : Parameter) => MonoidHom.range (hom ad) ⊔ conjugatedImage p
  let middleFinite := fun (p : Parameter) =>
    Subgroup.FiniteIndex (Subgroup.subgroupOf (MonoidHom.range (hom ad))
      (MonoidHom.range (hom a) ⊓ join p))
  let nₚ := fun (p : Parameter) =>
    Subgroup.relIndex (MonoidHom.range (hom ade)) (MonoidHom.range (hom a) ⊓ conjugatedImage p)
  let expansion := fun (coeff : Finsupp Parameter Complex) =>
    Finsupp.sum coeff (fun p weight => weight • Qstar p)
  (∀ (p : Parameter), middleFinite p →
    let B' := Subgroup.map (Subgroup.subtype A) (join p)
    let p₀ := MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p)
    ∃ (j : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B')
      (ell : MackeyDiagrams.Dot bc (comp j w))
      (m : ProjectionLabel a j d v) (n : ProjectionLabel v w e f),
      (∀ k : B', (hom j k : U) = (k : U)) ∧
      (∀ k : C, hom j (hom v k) = hom ad k) ∧
      (∀ k : F, hom j (hom w k) = (MulAut.conj p₀) (hom bc k)) ∧
      MackeyDiagrams.Dot.element ell = p₀⁻¹ ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m) = 1 ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot n) = 1 ∧
      (∀ z : B', fiberSize v w e f n z ≤ nₚ p) ∧
      eval (right j v w (Finsupp.single ell 1) (Finsupp.single m 1) (Finsupp.single n 1)) =
        Qstar p) ∧
  (Subgroup.FiniteIndex (MonoidHom.range (hom d)) →
    let j := MackeyDiagrams.ConjEmbedding.id A
    ∃ (ell : MackeyDiagrams.Dot bc (comp j bc)) (m : ProjectionLabel a j d ad)
      (n : Parameter → ProjectionLabel ad bc e f),
      MackeyDiagrams.Dot.element ell = 1 ∧
      MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m) = 1 ∧
      (∀ z : A, fiberSize a j d ad m z = Subgroup.index (MonoidHom.range (hom d))) ∧
      (∀ (p : Parameter), MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot (n p)) =
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p) ∧
          (∀ z : A, fiberSize ad bc e f (n p) z ≤ nₚ p)) ∧
      (∀ (coeff : Finsupp Parameter Complex),
        eval (right j ad bc (Finsupp.single ell 1) (Finsupp.single m 1)
          (Finsupp.mapDomain n coeff)) = expansion coeff)) ∧
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de)
      (coeff : Finsupp Parameter Complex), eval (left r s t xs ys zs) = expansion coeff →
    ((∃ ds : List Drawing,
        (∀ drawing ∈ ds, IsRight drawing) ∧
        eval (sumDrawings ds) = eval (left r s t xs ys zs)) ↔
      ∀ p ∈ Finsupp.support coeff, middleFinite p))
) :=
(by
  open CaseOneRightProjectionAux in
  intro U inst G A D F C E a b c d e f
  -- Xiao, §6.2.1, Lemma 6.3, (6.1)–(6.2), Theorem 6.4(1) and its proof.
  -- The archived original PDF places the proof on p. 23. The revised
  -- published PDF places it on p. 25. The Alphabeta Math page reproduces the
  -- proof in prose. The dependencies implement the backward evaluation on
  -- the typed s₂s₁s₂ diagram. Here the two constructions use the same
  -- singleton transfer identity, with finite index proved at each vertex.
  exact ⟨joinConnection a b c d e f, commonConnection a b c d e f, sumConnection a b c d e f⟩
)

#print axioms CaseOneRightProjectionConstruction
