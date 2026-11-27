import MackeyDiagrams
import Proofs.EvaluationWithOneProjection

set_option maxHeartbeats 2000000

namespace XiaoCaseSixAux
open MackeyDiagrams
noncomputable section

private abbrev U := Multiplicative (ZMod 2)
private abbrev T : Subgroup U := ⊥
private abbrev H : Subgroup U := ⊤
private abbrev pack := fun x : U => (⟨x, Subgroup.mem_top x⟩ : H)
private abbrev g := pack (Multiplicative.ofAdd (1 : ZMod 2))
private abbrev unitEmbedding := MackeyDiagrams.ConjEmbedding.id T
private abbrev inclusion : MackeyDiagrams.ConjEmbedding T H :=
  ⟨Subgroup.inclusion (show T ≤ H from bot_le), ⟨1, fun _ => by simp⟩⟩
private abbrev a := unitEmbedding
private abbrev b := inclusion
private abbrev d := inclusion
private abbrev c := unitEmbedding
private abbrev e := inclusion
private abbrev f := inclusion
private abbrev i := unitEmbedding
private abbrev j := unitEmbedding
private abbrev k := unitEmbedding
private abbrev upW := @MackeyDiagrams.Word.up U _
private abbrev downW := @MackeyDiagrams.Word.down U _
private abbrev tensor := @MackeyDiagrams.Word.tensor U _
private abbrev compE := @MackeyDiagrams.ConjEmbedding.comp U _
private abbrev homE := @MackeyDiagrams.ConjEmbedding.toHom U _
private abbrev bottom := tensor (upW a) (tensor (downW b) (upW d))
private abbrev top := tensor (upW c) (tensor (downW e) (upW f))
private abbrev ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
private abbrev stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
private abbrev beside := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
private abbrev straight := fun {K J : Subgroup U} (p : MackeyDiagrams.Word K J) =>
  ordinary (MackeyDiagrams.Diagram.id p)
private abbrev onLeft := fun {K J J' L M : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
    (w : MackeyDiagrams.Word L M)
    (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
  stack (ordinary (MackeyDiagrams.Diagram.unassociate p q w))
    (stack (beside crossing (straight w)) (ordinary (MackeyDiagrams.Diagram.associate p' q' w)))
private abbrev left := fun {B : Subgroup U}
    (α : MackeyDiagrams.ConjEmbedding T B) (β γ : MackeyDiagrams.ConjEmbedding H B)
    (r : List (Complex × MackeyDiagrams.Dot (compE α a) (compE β b)))
    (t : List (Complex × MackeyDiagrams.Dot (compE β d) (compE γ f)))
    (s : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)) =>
  (stack
    (onLeft (upW d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication α β a b r))
    (stack (beside (straight (downW α)) (MackeyDiagrams.LabelledDrawing.parallelUp β d γ f t))
      (onLeft (upW f) (MackeyDiagrams.LabelledDrawing.compactProjection α γ c e s))) :
    MackeyDiagrams.LabelledDrawing Complex bottom top)
private abbrev IsLeft := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
  ∃ (B : Subgroup U) (α : MackeyDiagrams.ConjEmbedding T B)
    (β γ : MackeyDiagrams.ConjEmbedding H B)
    (r : List (Complex × MackeyDiagrams.Dot (compE α a) (compE β b)))
    (t : List (Complex × MackeyDiagrams.Dot (compE β d) (compE γ f)))
    (s : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)),
    drawing = left α β γ r t s
private abbrev right := fun (r : MackeyDiagrams.ProjectionDot.Mixed b d i j)
    (t : MackeyDiagrams.Dot (compE a i) (compE c k))
    (s : MackeyDiagrams.Dot (compE e k) (compE f j)) =>
  (stack (beside (straight (upW a)) (MackeyDiagrams.LabelledDrawing.compactProjection b d i j [(1, r)]))
    (stack (onLeft (downW j) (MackeyDiagrams.LabelledDrawing.parallelUp a i c k [(1, t)]))
      (beside (straight (upW c)) (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j [(1, s)]))) :
    MackeyDiagrams.LabelledDrawing Complex bottom top)
private abbrev input := fun x : H => Finsupp.single
  (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor (downW b) (upW d))) 1
    (MackeyDiagrams.Generator.mixedPair b d x)) (1 : Complex)
private abbrev output := fun x : H => Finsupp.single
  (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
    (MackeyDiagrams.Word.basis (tensor (downW e) (upW f))) 1
    (MackeyDiagrams.Generator.mixedPair e f x)) (1 : Complex)
private abbrev evaluate := fun {p q : MackeyDiagrams.Word T T}
    (drawing : MackeyDiagrams.LabelledDrawing Complex p q) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
private abbrev translate := fun (a₀ : MackeyDiagrams.ConjEmbedding T T)
    (b₀ d₀ : MackeyDiagrams.ConjEmbedding T H) =>
  let dot : MackeyDiagrams.Dot d₀ d₀ := ⟨g, fun x => mul_comm (homE d₀ x) g⟩
  evaluate (beside (straight (upW a₀))
    (beside (straight (downW b₀)) (MackeyDiagrams.LabelledDrawing.upDot [(1, dot)])))
private abbrev translationIn := translate a b d
private abbrev translationOut := translate c e f
private abbrev Summand := Complex × MackeyDiagrams.LabelledDrawing Complex bottom top
private abbrev sumLeft := fun (terms : List Summand) =>
  (⟨Finset.univ, fun i : Fin terms.length =>
    MackeyDiagrams.LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩ :
    MackeyDiagrams.IndexedDrawing Complex bottom top (Fin terms.length))

-- Example 6.7, step 2. Conjugation acts trivially in the ambient C₂.
private theorem embedding_coe {K J : Subgroup U} (a₀ : ConjEmbedding K J) (x : K) :
    (a₀.toHom x : U) = (x : U) := by
  obtain ⟨u, hu⟩ := a₀.hasRepresentative
  simpa [mul_comm u (x : U), mul_assoc] using hu x

private theorem forced {B : Subgroup U} (β : ConjEmbedding H B) : B = H := by
  apply top_unique
  intro x hx
  have hm := (β.toHom (⟨x, hx⟩ : H)).property
  rwa [embedding_coe] at hm

private theorem embedding_unique {K J : Subgroup U} (a₀ b₀ : ConjEmbedding K J) : a₀ = b₀ := by
  apply ConjEmbedding.ext
  apply MonoidHom.ext
  intro x
  exact Subtype.ext ((embedding_coe a₀ x).trans (embedding_coe b₀ x).symm)

private theorem t_one (x : T) : x = 1 :=
  Subtype.ext (Subgroup.mem_bot.mp x.property)

private def topEquiv : H ≃ U where
  toFun := Subtype.val
  invFun := pack
  left_inv _ := rfl
  right_inv _ := rfl

private theorem index_bounds :
    (0 < Subgroup.index (MonoidHom.range e.toHom) ∧ Subgroup.index (MonoidHom.range e.toHom) ≤ 2) ∧
    (0 < Subgroup.index (MonoidHom.range j.toHom) ∧ Subgroup.index (MonoidHom.range j.toHom) ≤ 2) := by
  have hr : e.toHom.range = ⊥ := by
    apply bot_unique
    rintro x ⟨y, rfl⟩
    rw [t_one y, map_one]
    exact Subgroup.one_mem _
  have ht : j.toHom.range = ⊤ := MonoidHom.range_eq_top.mpr Function.surjective_id
  have hc : Nat.card H = 2 := by
    rw [Nat.card_congr topEquiv]
    change Nat.card (ZMod 2) = 2
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hr, ht, Subgroup.index_bot, Subgroup.index_top, hc]
  decide

private abbrev idH := ConjEmbedding.id H
private abbrev Lr := Dot (inclusion.comp a) (idH.comp b)
private abbrev Lt := Dot (idH.comp d) (idH.comp f)
private abbrev Ls := ProjectionDot.Mixed inclusion idH c e
private abbrev LeftFiber := ((upW c).tensor (downW e)).basis.carrier
private abbrev QL (s : Dot (inclusion.comp c) (idH.comp e)) (w : LeftFiber) :=
  Generator.mixedProduct inclusion idH (Generator.mixedMultiplicationBasis inclusion idH c e s w)
private abbrev LF (y : H) : LeftFiber :=
  (Biset.induction c).pair (Biset.restriction e) 1 y

private theorem leftFiber (s : Dot (inclusion.comp c) (idH.comp e)) (z : H) :
    {w : LeftFiber | QL s w = z} = {LF (s.element⁻¹ * z)} := by
  ext w
  change QL s w = z ↔ w = LF (s.element⁻¹ * z)
  refine Quotient.inductionOn w ?_
  rintro ⟨y, v⟩
  change QL s ((Biset.induction c).pair (Biset.restriction e) y v) = z ↔
    (Biset.induction c).pair (Biset.restriction e) y v = LF (s.element⁻¹ * z)
  rw [t_one y]
  have h (v : H) : QL s (LF v) = s.element * v := by
    change (inclusion.toHom 1 * s.element * v) * 1 = s.element * v
    simp
  rw [h]
  constructor
  · intro he
    rw [← he, inv_mul_cancel_left]
  · intro he
    have he' := congrArg (QL s) he
    rwa [h, h, mul_inv_cancel_left] at he'

private theorem leftFinite (s : Dot (inclusion.comp c) (idH.comp e)) (z : H) :
    Set.Finite {w : LeftFiber | QL s w = z} := by
  rw [leftFiber]
  exact Set.finite_singleton _

private abbrev RightFiber := ((upW i).tensor (downW j)).basis.carrier
private abbrev Rr := Dot (b.comp i) (d.comp j)
private abbrev Rt := Dot (a.comp i) (c.comp k)
private abbrev Rs := Dot (e.comp k) (f.comp j)
private abbrev QR (r : Rr) (w : RightFiber) :=
  Generator.mixedProduct b d (Generator.mixedMultiplicationBasis b d i j r w)
private abbrev RF : RightFiber := (Biset.induction i).pair (Biset.restriction j) 1 1

private theorem rightFiberUnit (w : RightFiber) : w = RF := by
  refine Quotient.inductionOn w ?_
  rintro ⟨x, y⟩
  change (Biset.induction i).pair (Biset.restriction j) x y = RF
  rw [t_one x, t_one y]

private theorem rightProduct (r : Rr) (w : RightFiber) : QR r w = r.element := by
  rw [rightFiberUnit w]
  change (b.toHom 1 * r.element * d.toHom 1) * 1 = _
  simp

private theorem rightFinite (r : Rr) (x : H) : Set.Finite {w : RightFiber | QR r w = x} :=
  (Set.finite_singleton RF).subset (fun w _ => rightFiberUnit w)

private def rOne : Rr := ⟨1, fun y => by rw [t_one y]; simp⟩
private def tOne : Rt := ⟨1, fun y => by rw [t_one y]; simp⟩
private def sOne : Rs := ⟨1, fun y => by rw [t_one y]; simp⟩
private def rightDot : ProjectionDot.Mixed b d i j :=
  ⟨rOne, fun z => (rightFinite rOne (Generator.mixedProduct b d z)).subset
    (fun _ hz => congrArg (Generator.mixedProduct b d) hz)⟩

private theorem g_ne_one : g ≠ 1 := by
  intro h
  have h' : (1 : ZMod 2) = 0 := congrArg (fun x : H => Multiplicative.toAdd (x : U)) h
  exact (by decide : (1 : ZMod 2) ≠ 0) h'


private abbrev nativeLeft (r : Lr) (t : Lt) (s : Ls) :
    LabelledDrawing Complex (tensor (tensor (upW a) (downW b)) (upW d))
      (tensor (tensor (upW c) (downW e)) (upW f)) :=
  stack (beside (LabelledDrawing.mixedMultiplication inclusion idH a b [(1, r)]) (straight (upW d)))
    (stack (ordinary (Diagram.associate (downW inclusion) (upW idH) (upW d)))
      (stack (beside (straight (downW inclusion)) (LabelledDrawing.parallelUp idH d idH f [(1, t)]))
        (stack (ordinary (Diagram.unassociate (downW inclusion) (upW idH) (upW f)))
          (beside (LabelledDrawing.compactProjection inclusion idH c e [(1, s)]) (straight (upW f))))))

-- Example 6.7, step 2. Apply Xiao (6.3) through EvaluationWithOneProjection.
-- The supplier uses left bracketing. Reassociate the same pure triples on
-- both boundaries. The projection certificate is obtained from the exact
-- singleton fiber, and proof irrelevance identifies it with the given one.
private theorem leftColumn (r : Lr) (t : Lt) (s : Ls) (x : H) :
    evaluate (left inclusion idH idH [(1, r)] [(1, t)] [(1, s)]) (input x) =
      output (s.dot.element⁻¹ * r.element * x * t.element) := by
  let z := inclusion.toHom 1 * r.element * idH.toHom x * t.element
  have hz : s.dot.element⁻¹ * z = s.dot.element⁻¹ * r.element * x * t.element := by
    change s.dot.element⁻¹ * (inclusion.toHom 1 * r.element * x * t.element) = _
    simp [mul_assoc]
  let v := s.dot.element⁻¹ * z
  have hfin : (leftFinite s.dot z).toFinset = {LF v} := by
    ext w
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact Set.ext_iff.mp (leftFiber s.dot z) w
  let A := (Diagram.associate (R := Complex) (upW c) (downW e) (upW f)).eval.toLinearMap
  have h := (EvaluationWithOneProjection a b d c e f).1 inclusion idH idH |>.1
    r t s.dot (leftFinite s.dot) 1 x
  change evaluate (nativeLeft r t s)
      (Finsupp.single (((upW a).tensor (downW b)).basis.pair (upW d).basis
        ((upW a).basis.pair (downW b).basis 1 x) 1) 1) =
    ∑ w ∈ (leftFinite s.dot z).toFinset,
      Finsupp.single (((upW c).tensor (downW e)).basis.pair (upW f).basis w 1) (1 : Complex) at h
  change A (evaluate (nativeLeft r t s)
    ((Diagram.unassociate (R := Complex) (upW a) (downW b) (upW d)).eval.toLinearMap (input x))) = _
  change A (evaluate (nativeLeft r t s)
    ((Diagram.unassociate (R := Complex) (upW a) (downW b) (upW d)).eval.toLinearMap
      (Finsupp.single ((upW a).basis.pair ((downW b).tensor (upW d)).basis 1
        ((downW b).basis.pair (upW d).basis x 1)) 1))) = _
  rw [Diagram.eval_unassociate_single, h, hfin, Finset.sum_singleton]
  unfold A
  change (Diagram.associate (R := Complex) (upW c) (downW e) (upW f)).eval.toLinearMap
    (Finsupp.single (((upW c).tensor (downW e)).basis.pair (upW f).basis
      ((upW c).basis.pair (downW e).basis 1 v) 1) 1) = _
  rw [Diagram.eval_associate_single]
  change output v = _
  exact congrArg output hz

private theorem leftColumnGeneral {B : Subgroup U}
    (α : ConjEmbedding T B) (β γ : ConjEmbedding H B)
    (r : Dot (α.comp a) (β.comp b)) (t : Dot (β.comp d) (γ.comp f))
    (s : ProjectionDot.Mixed α γ c e) (x : H) :
    evaluate (left α β γ [(1, r)] [(1, t)] [(1, s)]) (input x) =
    output ((pack (s.dot.element : U))⁻¹ * pack (r.element : U) * x * pack (t.element : U)) := by
  have hB := forced β
  change B = (⊤ : Subgroup U) at hB
  subst B
  have hα : α = inclusion := embedding_unique α inclusion
  have hβ : β = idH := embedding_unique β idH
  have hγ : γ = idH := embedding_unique γ idH
  subst α
  subst β
  subst γ
  exact leftColumn r t s x

-- Example 6.7, step 1. In (6.4) the sole possible pair in the lower
-- projection is (1,1), and its multiplication value is 1.
private theorem rightColumn (x : H) :
    evaluate (right rightDot tOne sOne) (input x) =
      if x = 1 then output 1 else 0 := by
  classical
  have h := (EvaluationWithOneProjection a b d c e f).2 T i j k |>.1
    rOne (rightFinite rOne) tOne sOne 1 x
  change evaluate (right rightDot tOne sOne) (input x) =
    ∑ w ∈ (rightFinite rOne x).toFinset,
      (let rep : T × T := Quotient.out w
       Finsupp.single ((Biset.induction c).pair ((downW e).tensor (upW f)).basis
          (1 * a.toHom rep.1 * tOne.element)
          (Generator.mixedPair e f (sOne.element * f.toHom rep.2))) (1 : Complex)) at h
  rw [h]
  have hv (w : RightFiber) : w ∈ (rightFinite rOne x).toFinset ↔ x = 1 := by
    rw [Set.Finite.mem_toFinset]
    change QR rOne w = x ↔ x = 1
    rw [rightProduct]
    exact eq_comm
  by_cases hx : x = 1
  · rw [ite_eq_left hx]
    have hs : (rightFinite rOne x).toFinset = {RF} := by
      ext w
      rw [hv, Finset.mem_singleton]
      exact ⟨fun _ => rightFiberUnit w, fun _ => hx⟩
    rw [hs, Finset.sum_singleton]
    have hrep : (Quotient.out RF : T × T) = (1, 1) :=
      Prod.ext (t_one _) (t_one _)
    simp only [hrep, map_one, one_mul, mul_one]
    rfl
  · rw [ite_eq_right hx]
    have hs : (rightFinite rOne x).toFinset = ∅ := by
      ext w
      simp [hv, hx]
    rw [hs, Finset.sum_empty]

section WeightedFrames

variable {V : Type*} [Group V] {K J M : Subgroup V}
variable {p p' : Word K J} {q q' : Word J M}

private theorem apply_list_sum {X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y]
    [Module Complex X] [Module Complex Y] (fs : List (X →ₗ[Complex] Y)) (v : X) :
    fs.sum v = (fs.map (fun f => f v)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change f v + fs.sum v = f v + _
    rw [ih]
    rfl

private theorem frame_list_left (terms : List (Complex × ScopedDiagram Complex p p'))
    (h : Biset.Hom Complex q.basis q'.basis) :
    ((ScopedDiagram.linearCombination terms).eval.horizontal h).toLinearMap =
      (terms.map fun (c, d) => c • (d.eval.horizontal h).toLinearMap).sum := by
  apply Finsupp.lhom_ext
  intro w k
  refine Quotient.inductionOn w ?_
  rintro ⟨u, v⟩
  rw [apply_list_sum, List.map_map]
  change ((ScopedDiagram.linearCombination terms).eval.horizontal h).toLinearMap
    (Finsupp.single (p.basis.pair q.basis u v) k) = _
  rw [Biset.Hom.horizontal_single, ScopedDiagram.eval_linearCombination_apply]
  let F := (Biset.pairLinear Complex p'.basis q'.basis).flip (h.toLinearMap (Finsupp.single v 1))
  change k • F ((terms.map fun (c,d) => c • d.eval.toLinearMap (Finsupp.single u 1)).sum) = _
  rw [map_list_sum, List.smul_sum, List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c,d⟩ _
  simp only [Function.comp_apply, map_smul, LinearMap.smul_apply]
  change k • c • F _ = c • (_ : Biset.Hom Complex _ _).toLinearMap
    (Finsupp.single (p.basis.pair q.basis u v) k)
  rw [Biset.Hom.horizontal_single]
  change k • c • F _ = c • k • F _
  rw [smul_comm k c]

private theorem frame_list_right (h : Biset.Hom Complex p.basis p'.basis)
    (terms : List (Complex × ScopedDiagram Complex q q')) :
    (h.horizontal (ScopedDiagram.linearCombination terms).eval).toLinearMap =
      (terms.map fun (c, d) => c • (h.horizontal d.eval).toLinearMap).sum := by
  apply Finsupp.lhom_ext
  intro w k
  refine Quotient.inductionOn w ?_
  rintro ⟨u, v⟩
  rw [apply_list_sum, List.map_map]
  change (h.horizontal (ScopedDiagram.linearCombination terms).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis u v) k) = _
  rw [Biset.Hom.horizontal_single, ScopedDiagram.eval_linearCombination_apply]
  let F := Biset.pairLinear Complex p'.basis q'.basis (h.toLinearMap (Finsupp.single u 1))
  change k • F ((terms.map fun (c,d) => c • d.eval.toLinearMap (Finsupp.single v 1)).sum) = _
  rw [map_list_sum, List.smul_sum, List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c,d⟩ _
  simp only [Function.comp_apply, map_smul, LinearMap.smul_apply]
  change k • c • F _ = c • (_ : Biset.Hom Complex _ _).toLinearMap
    (Finsupp.single (p.basis.pair q.basis u v) k)
  rw [Biset.Hom.horizontal_single]
  change k • c • F _ = c • k • F _
  rw [smul_comm k c]

end WeightedFrames

private theorem translated_column (x : H) :
    translationIn (input x) = input (x * g) := by
  let dot : Dot d d := ⟨g, fun y => mul_comm (d.toHom y) g⟩
  let Y := (downW b).basis
  let Z := (upW d).basis
  let X := (upW a).basis
  let V := (ScopedDiagram.weightedUpDot (R := Complex) [(1, dot)]).eval
  have hv : V.toLinearMap (Finsupp.single (1 : H) 1) = Finsupp.single g 1 := by
    change (Diagram.finiteSum [Diagram.scale 1 (Diagram.upDot dot)]).eval.toLinearMap
      (Finsupp.single (1 : H) 1) = _
    rw [Diagram.eval_finiteSum]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    change (1 : Complex) • (Diagram.upDot dot).eval.toLinearMap (Finsupp.single (1 : H) 1) + 0 = _
    rw [one_smul, add_zero, Diagram.eval_upDot_single, one_mul]
  change ((Diagram.id (R := Complex) (upW a)).eval.horizontal
      ((Diagram.id (R := Complex) (downW b)).eval.horizontal V)).toLinearMap
      (Finsupp.single (X.pair (Y.tensor Z) 1 (Y.pair Z x 1)) 1) = _
  rw [Biset.Hom.horizontal_single, Biset.Hom.horizontal_single, Diagram.eval_id_apply,
    Diagram.eval_id_apply, hv, one_smul, Biset.pairLinear_single, one_mul, one_smul,
    Biset.pairLinear_single, one_mul]
  have he : Y.pair Z x g = Generator.mixedPair b d (x * g) :=
    (Generator.mixedPair_mixedProduct b d (Y.pair Z x g)).symm
  rw [he]

private theorem basis_input (w : bottom.basis.carrier) :
    ∃ x : H, w = (upW a).basis.pair ((downW b).tensor (upW d)).basis 1
      (Generator.mixedPair b d x) := by
  refine Quotient.inductionOn w ?_
  rintro ⟨y, v⟩
  refine ⟨Generator.mixedProduct b d v, ?_⟩
  change (upW a).basis.pair ((downW b).tensor (upW d)).basis y v = _
  rw [t_one y, Generator.mixedPair_mixedProduct]

private abbrev Llow (rs : List (Complex × Lr)) :=
  onLeft (upW d) (LabelledDrawing.mixedMultiplication inclusion idH a b rs)
private abbrev Lmid (ts : List (Complex × Lt)) :=
  beside (straight (downW inclusion)) (LabelledDrawing.parallelUp idH d idH f ts)
private abbrev Lhigh (ss : List (Complex × Ls)) :=
  onLeft (upW f) (LabelledDrawing.compactProjection inclusion idH c e ss)

private abbrev lowTerm (r : Lr) := ScopedDiagram.ordinary
  (Diagram.mixedMultiplication (R := Complex) inclusion idH a b r)
private abbrev midTerm (t : Lt) := ScopedDiagram.ordinary
  (Diagram.parallelUp (R := Complex) idH d idH f t)
private abbrev highTerm (s : Ls) := ScopedDiagram.ordinary
  (Diagram.mixedProjection (R := Complex) inclusion idH c e s.dot s.finite)

private theorem frame_onLeft {K J J' L M : Subgroup U}
    {p : Word K J} {q : Word J L} {p' : Word K J'} {q' : Word J' L} (w : Word L M)
    (terms : List (Complex × ScopedDiagram Complex (p.tensor q) (p'.tensor q')))
    (x : ((p.tensor (q.tensor w)).basis.carrier →₀ Complex)) :
    (Diagram.associate (R := Complex) p' q' w).eval.toLinearMap
        (((ScopedDiagram.linearCombination terms).eval.horizontal (Diagram.id w).eval).toLinearMap
          ((Diagram.unassociate p q w).eval.toLinearMap x)) =
      (terms.map fun (c,d) =>
        c • (Diagram.associate (R := Complex) p' q' w).eval.toLinearMap
          ((d.eval.horizontal (Diagram.id w).eval).toLinearMap
            ((Diagram.unassociate p q w).eval.toLinearMap x))).sum := by
  rw [frame_list_left (q := w) (q' := w), apply_list_sum, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c,d⟩ _
  simp only [Function.comp_apply, LinearMap.smul_apply, map_smul]

private theorem low_list (rs : List (Complex × Lr)) (x : bottom.basis.carrier →₀ Complex) :
    evaluate (Llow rs) x =
      (rs.map fun (c,r) => c • evaluate (Llow [(1,r)]) x).sum := by
  change (Diagram.associate (R := Complex) (downW inclusion) (upW idH) (upW d)).eval.toLinearMap
    (((ScopedDiagram.linearCombination (rs.map fun (c,r) => (c, lowTerm r))).eval.horizontal
      (Diagram.id (upW d)).eval).toLinearMap
      ((Diagram.unassociate (upW a) (downW b) (upW d)).eval.toLinearMap x)) = _
  rw [frame_onLeft, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c,r⟩ _
  simp only [Function.comp_apply]
  apply congrArg (fun z => c • z)
  have h := frame_onLeft (upW d) [(1, lowTerm r)] x
  change evaluate (Llow [(1,r)]) x = _ at h
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] using h.symm

private theorem mid_list (ts : List (Complex × Lt))
    (x : ((downW inclusion).tensor ((upW idH).tensor (upW d))).basis.carrier →₀ Complex) :
    evaluate (Lmid ts) x =
      (ts.map fun (c,t) => c • evaluate (Lmid [(1,t)]) x).sum := by
  change ((Diagram.id (R := Complex) (downW inclusion)).eval.horizontal
    (ScopedDiagram.linearCombination (ts.map fun (c,t) => (c, midTerm t))).eval).toLinearMap x = _
  rw [frame_list_right (p := downW inclusion) (p' := downW inclusion), apply_list_sum, List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c,t⟩ _
  simp only [Function.comp_apply, LinearMap.smul_apply]
  congr 1
  have h := frame_list_right (p := downW inclusion) (p' := downW inclusion)
    (Diagram.id (R := Complex) (downW inclusion)).eval [(1, midTerm t)]
  have hx := LinearMap.congr_fun h x
  change evaluate (Lmid [(1,t)]) x = _ at hx
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] using hx.symm

private theorem high_list (ss : List (Complex × Ls))
    (x : ((downW inclusion).tensor ((upW idH).tensor (upW f))).basis.carrier →₀ Complex) :
    evaluate (Lhigh ss) x =
      (ss.map fun (c,s) => c • evaluate (Lhigh [(1,s)]) x).sum := by
  change (Diagram.associate (R := Complex) (upW c) (downW e) (upW f)).eval.toLinearMap
    (((ScopedDiagram.linearCombination (ss.map fun (c,s) => (c, highTerm s))).eval.horizontal
      (Diagram.id (upW f)).eval).toLinearMap
      ((Diagram.unassociate (downW inclusion) (upW idH) (upW f)).eval.toLinearMap x)) = _
  rw [frame_onLeft, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c,s⟩ _
  simp only [Function.comp_apply]
  apply congrArg (fun z => c • z)
  have h := frame_onLeft (upW f) [(1, highTerm s)] x
  change evaluate (Lhigh [(1,s)]) x = _ at h
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] using h.symm

-- Example 6.7, step 3. The three finite labels are expanded by the
-- linearity of evaluation at the marked crossings. The displayed
-- indexed sum over whole drawings remains a separate scope.
private theorem left_list (rs : List (Complex × Lr)) (ts : List (Complex × Lt))
    (ss : List (Complex × Ls)) (v : bottom.basis.carrier →₀ Complex) :
    evaluate (left inclusion idH idH rs ts ss) v =
      (rs.map fun (cr,r) => cr • (ts.map fun (ct,t) => ct •
        (ss.map fun (cs,s) => cs •
          evaluate (left inclusion idH idH [(1,r)] [(1,t)] [(1,s)]) v).sum).sum).sum := by
  change evaluate (Lhigh ss) (evaluate (Lmid ts) (evaluate (Llow rs) v)) = _
  rw [low_list, map_list_sum, map_list_sum, List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨cr,r⟩ _
  simp only [Function.comp_apply, map_smul]
  apply congrArg (fun z => cr • z)
  rw [mid_list, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨ct,t⟩ _
  simp only [Function.comp_apply, map_smul]
  apply congrArg (fun z => ct • z)
  exact high_list ss _

private def weighted {I V : Type*} [AddCommMonoid V] [Module Complex V]
    (terms : List (Complex × I)) (f : I → V) : V :=
  (terms.map fun (c,i) => c • f i).sum

private theorem map_weighted {I V W : Type*} [AddCommMonoid V] [Module Complex V]
    [AddCommMonoid W] [Module Complex W] (F : V →ₗ[Complex] W)
    (terms : List (Complex × I)) (f : I → V) :
    F (weighted terms f) = weighted terms (fun i => F (f i)) := by
  rw [weighted, weighted, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨c,i⟩ _
  exact map_smul F c (f i)

private theorem weighted_congr {I V : Type*} [AddCommMonoid V] [Module Complex V]
    (terms : List (Complex × I)) (f g : I → V) (h : ∀ i, f i = g i) :
    weighted terms f = weighted terms g := by
  rw [show f = g from funext h]

private theorem left_commutes_on_input (rs : List (Complex × Lr)) (ts : List (Complex × Lt))
    (ss : List (Complex × Ls)) (x : H) :
    evaluate (left inclusion idH idH rs ts ss) (translationIn (input x)) =
      translationOut (evaluate (left inclusion idH idH rs ts ss) (input x)) := by
  let column (y : H) (r : Lr) (t : Lt) (s : Ls) :=
    evaluate (left inclusion idH idH [(1,r)] [(1,t)] [(1,s)]) (input y)
  have h (r : Lr) (t : Lt) (s : Ls) :
      column (x * g) r t s = translationOut (column x r t s) := by
    change evaluate (left inclusion idH idH [(1,r)] [(1,t)] [(1,s)]) (input (x * g)) =
      translationOut (evaluate (left inclusion idH idH [(1,r)] [(1,t)] [(1,s)]) (input x))
    rw [leftColumn, leftColumn]
    change input (s.dot.element⁻¹ * r.element * (x * g) * t.element) =
      translationIn (input (s.dot.element⁻¹ * r.element * x * t.element))
    rw [translated_column]
    apply congrArg input
    ac_rfl
  rw [translated_column, left_list rs ts ss (input (x * g)), left_list rs ts ss (input x)]
  change weighted rs (fun r => weighted ts (fun t => weighted ss (column (x * g) r t))) =
    translationOut (weighted rs (fun r => weighted ts (fun t => weighted ss (column x r t))))
  rw [map_weighted]
  apply weighted_congr
  intro r
  rw [map_weighted]
  apply weighted_congr
  intro t
  rw [map_weighted]
  exact weighted_congr _ _ _ (h r t)

private theorem left_commutes (D : LabelledDrawing Complex bottom top) (hD : IsLeft D) :
    (evaluate D).comp translationIn = translationOut.comp (evaluate D) := by
  obtain ⟨B, α, β, γ, rs, ts, ss, rfl⟩ := hD
  have hB := forced β
  change B = (⊤ : Subgroup U) at hB
  subst B
  have hα : α = inclusion := embedding_unique α inclusion
  have hβ : β = idH := embedding_unique β idH
  have hγ : γ = idH := embedding_unique γ idH
  subst α
  subst β
  subst γ
  apply Finsupp.lhom_ext
  intro w k
  obtain ⟨x, rfl⟩ := basis_input w
  have hk : Finsupp.single ((upW a).basis.pair ((downW b).tensor (upW d)).basis 1
        (Generator.mixedPair b d x)) k = k • input x := by
    change _ = k • Finsupp.single _ 1
    simp [Finsupp.smul_single]
  rw [hk]
  simp only [map_smul, LinearMap.comp_apply]
  rw [left_commutes_on_input]

-- Example 6.7, step 3. Each position of the original finite indexed
-- drawing contributes its own summand and coefficient.
private theorem indexed_commutes (terms : List Summand) (h : ∀ term ∈ terms, IsLeft term.2) :
    ((sumLeft terms).eval).comp translationIn =
      translationOut.comp ((sumLeft terms).eval) := by
  classical
  apply LinearMap.ext
  intro v
  have heval (z : bottom.basis.carrier →₀ Complex) :
      (sumLeft terms).eval z = ∑ idx ∈ (sumLeft terms).indices,
        (terms.get idx).1 • evaluate (terms.get idx).2 z :=
    IndexedDrawing.eval_apply (sumLeft terms) z
  simp only [LinearMap.comp_apply]
  rw [heval (translationIn v), heval v, map_sum]
  apply Finset.sum_congr rfl
  intro idx _
  let term := terms.get idx
  change term.1 • evaluate term.2 (translationIn v) =
    translationOut (term.1 • evaluate term.2 v)
  rw [map_smul]
  exact congrArg (fun z => term.1 • z)
    (LinearMap.congr_fun (left_commutes term.2 (h term (List.get_mem terms idx))) v)

private theorem right_noncommutes :
    (evaluate (right rightDot tOne sOne)).comp translationIn ≠
      translationOut.comp (evaluate (right rightDot tOne sOne)) := by
  classical
  let R := evaluate (right rightDot tOne sOne)
  have h1 : R (input 1) = output 1 := by
    have h := rightColumn 1
    rw [ite_eq_left rfl] at h
    exact h
  have hg : R (input g) = 0 := by
    rw [show R (input g) = _ from rightColumn g, ite_eq_right g_ne_one]
  -- Example 6.7, steps 4–5. The commutator is detected on the unit vector.
  intro he
  have hv := LinearMap.congr_fun he (input 1)
  change R (translationIn (input 1)) = translationOut (R (input 1)) at hv
  rw [translated_column, one_mul, hg, h1] at hv
  have ht : translationOut (output 1) = output g := by
    change translationIn (input 1) = input g
    rw [translated_column, one_mul]
  rw [ht] at hv
  have hne : output g ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
  exact hne hv.symm

end
end XiaoCaseSixAux

theorem CaseSixProjectionNoLeftReplacement : (
let U := Multiplicative (ZMod 2)
let T : Subgroup U := ⊥
let H : Subgroup U := ⊤
let pack := fun x : U => (⟨x, Subgroup.mem_top x⟩ : H)
let g := pack (Multiplicative.ofAdd (1 : ZMod 2))
let unitEmbedding := MackeyDiagrams.ConjEmbedding.id T
let inclusion : MackeyDiagrams.ConjEmbedding T H :=
  ⟨Subgroup.inclusion (show T ≤ H from bot_le), ⟨1, fun _ => by simp⟩⟩
let a := unitEmbedding
let b := inclusion
let d := inclusion
let c := unitEmbedding
let e := inclusion
let f := inclusion
let i := unitEmbedding
let j := unitEmbedding
let k := unitEmbedding
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let hom := @MackeyDiagrams.ConjEmbedding.toHom U _
let bottom := tensor (up a) (tensor (down b) (up d))
let top := tensor (up c) (tensor (down e) (up f))
let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let beside := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let straight := fun {K J : Subgroup U} (p : MackeyDiagrams.Word K J) =>
  ordinary (MackeyDiagrams.Diagram.id p)
let onLeft := fun {K J J' L M : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
    (w : MackeyDiagrams.Word L M)
    (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
  stack (ordinary (MackeyDiagrams.Diagram.unassociate p q w))
    (stack (beside crossing (straight w)) (ordinary (MackeyDiagrams.Diagram.associate p' q' w)))
let left := fun {B : Subgroup U}
    (α : MackeyDiagrams.ConjEmbedding T B) (β γ : MackeyDiagrams.ConjEmbedding H B)
    (r : List (Complex × MackeyDiagrams.Dot (comp α a) (comp β b)))
    (t : List (Complex × MackeyDiagrams.Dot (comp β d) (comp γ f)))
    (s : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)) =>
  (stack
    (onLeft (up d) (MackeyDiagrams.LabelledDrawing.mixedMultiplication α β a b r))
    (stack (beside (straight (down α)) (MackeyDiagrams.LabelledDrawing.parallelUp β d γ f t))
      (onLeft (up f) (MackeyDiagrams.LabelledDrawing.compactProjection α γ c e s))) :
    MackeyDiagrams.LabelledDrawing Complex bottom top)
let IsLeft := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
  ∃ (B : Subgroup U) (α : MackeyDiagrams.ConjEmbedding T B)
    (β γ : MackeyDiagrams.ConjEmbedding H B)
    (r : List (Complex × MackeyDiagrams.Dot (comp α a) (comp β b)))
    (t : List (Complex × MackeyDiagrams.Dot (comp β d) (comp γ f)))
    (s : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)),
    drawing = left α β γ r t s
let right := fun (r : MackeyDiagrams.ProjectionDot.Mixed b d i j)
    (t : MackeyDiagrams.Dot (comp a i) (comp c k))
    (s : MackeyDiagrams.Dot (comp e k) (comp f j)) =>
  (stack (beside (straight (up a)) (MackeyDiagrams.LabelledDrawing.compactProjection b d i j [(1, r)]))
    (stack (onLeft (down j) (MackeyDiagrams.LabelledDrawing.parallelUp a i c k [(1, t)]))
      (beside (straight (up c)) (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j [(1, s)]))) :
    MackeyDiagrams.LabelledDrawing Complex bottom top)
let input := fun x : H => Finsupp.single
  (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor (down b) (up d))) 1
    (MackeyDiagrams.Generator.mixedPair b d x)) (1 : Complex)
let output := fun x : H => Finsupp.single
  (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
    (MackeyDiagrams.Word.basis (tensor (down e) (up f))) 1
    (MackeyDiagrams.Generator.mixedPair e f x)) (1 : Complex)
let evaluate := fun {p q : MackeyDiagrams.Word T T}
    (drawing : MackeyDiagrams.LabelledDrawing Complex p q) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing))
let translate := fun (a₀ : MackeyDiagrams.ConjEmbedding T T)
    (b₀ d₀ : MackeyDiagrams.ConjEmbedding T H) =>
  let dot : MackeyDiagrams.Dot d₀ d₀ := ⟨g, fun x => mul_comm (hom d₀ x) g⟩
  evaluate (beside (straight (up a₀))
    (beside (straight (down b₀)) (MackeyDiagrams.LabelledDrawing.upDot [(1, dot)])))
let translationIn := translate a b d
let translationOut := translate c e f
let Summand := Complex × MackeyDiagrams.LabelledDrawing Complex bottom top
let sumLeft := fun (terms : List Summand) =>
  (⟨Finset.univ, fun i : Fin terms.length =>
    MackeyDiagrams.LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩ :
    MackeyDiagrams.IndexedDrawing Complex bottom top (Fin terms.length))
(0 < Subgroup.index (MonoidHom.range (hom e)) ∧ Subgroup.index (MonoidHom.range (hom e)) ≤ 2) ∧
(0 < Subgroup.index (MonoidHom.range (hom j)) ∧ Subgroup.index (MonoidHom.range (hom j)) ≤ 2) ∧
(∀ (B : Subgroup U) (α : MackeyDiagrams.ConjEmbedding T B)
    (β γ : MackeyDiagrams.ConjEmbedding H B),
  B = H ∧
  (∀ x : H, (hom β x : U) = (x : U) ∧ (hom γ x : U) = (x : U)) ∧
  (∀ (r : MackeyDiagrams.Dot (comp α a) (comp β b))
      (t : MackeyDiagrams.Dot (comp β d) (comp γ f))
      (s : MackeyDiagrams.ProjectionDot.Mixed α γ c e) (x : H),
    evaluate (left α β γ [(1, r)] [(1, t)] [(1, s)]) (input x) =
      output ((pack (MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot s) : U))⁻¹ *
        pack (MackeyDiagrams.Dot.element r : U) * x * pack (MackeyDiagrams.Dot.element t : U)))) ∧
∃ (r : MackeyDiagrams.ProjectionDot.Mixed b d i j)
    (t : MackeyDiagrams.Dot (comp a i) (comp c k))
    (s : MackeyDiagrams.Dot (comp e k) (comp f j)),
  MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot r) = 1 ∧
  MackeyDiagrams.Dot.element t = 1 ∧ MackeyDiagrams.Dot.element s = 1 ∧
  let R := evaluate (right r t s)
  R (input 1) = output 1 ∧ R (input g) = 0 ∧
  translationOut (R (input 1)) = output g ∧
  LinearMap.comp R translationIn ≠ LinearMap.comp translationOut R ∧
  (∀ (terms : List Summand), (∀ term ∈ terms, IsLeft term.2) →
    LinearMap.comp ((sumLeft terms).eval) translationIn =
      LinearMap.comp translationOut ((sumLeft terms).eval)) ∧
  (∀ (terms : List Summand), (∀ term ∈ terms, IsLeft term.2) → (sumLeft terms).eval ≠ R)
) :=
(by
  classical
  -- Xiao, Example 6.7, archived printed p. 28 and published 28 November
  -- revision printed p. 30. The rendered inequality compares evaluated maps.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  refine ⟨XiaoCaseSixAux.index_bounds.1, XiaoCaseSixAux.index_bounds.2, ?_, ?_⟩
  · intro B α β γ
    exact ⟨XiaoCaseSixAux.forced β,
      fun x => ⟨XiaoCaseSixAux.embedding_coe β x, XiaoCaseSixAux.embedding_coe γ x⟩,
      XiaoCaseSixAux.leftColumnGeneral α β γ⟩
  · refine ⟨XiaoCaseSixAux.rightDot, XiaoCaseSixAux.tOne, XiaoCaseSixAux.sOne,
      rfl, rfl, rfl, ?_, ?_, ?_, XiaoCaseSixAux.right_noncommutes,
      XiaoCaseSixAux.indexed_commutes, ?_⟩
    · have h := XiaoCaseSixAux.rightColumn 1
      rw [ite_eq_left rfl] at h
      exact h
    · have h := XiaoCaseSixAux.rightColumn XiaoCaseSixAux.g
      rw [ite_eq_right XiaoCaseSixAux.g_ne_one] at h
      exact h
    · have h := XiaoCaseSixAux.rightColumn 1
      rw [ite_eq_left rfl] at h
      rw [h]
      change XiaoCaseSixAux.translationIn (XiaoCaseSixAux.input 1) =
        XiaoCaseSixAux.input XiaoCaseSixAux.g
      rw [XiaoCaseSixAux.translated_column, one_mul]
    · intro terms h he
      have hc := XiaoCaseSixAux.indexed_commutes terms h
      change (XiaoCaseSixAux.sumLeft terms).eval =
        XiaoCaseSixAux.evaluate
          (XiaoCaseSixAux.right XiaoCaseSixAux.rightDot XiaoCaseSixAux.tOne XiaoCaseSixAux.sOne) at he
      rw [he] at hc
      exact XiaoCaseSixAux.right_noncommutes hc)
