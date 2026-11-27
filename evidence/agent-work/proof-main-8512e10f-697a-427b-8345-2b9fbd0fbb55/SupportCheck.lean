import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
import Proofs.CaseTwoLeftProjectionConstruction
import Mathlib.GroupTheory.SemidirectProduct

set_option linter.unusedVariables false
namespace CaseTwoAudit

noncomputable abbrev swap : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (1 : ZMod 2)

noncomputable abbrev action : Multiplicative (ZMod 2) →* MulAut (Multiplicative Int × Multiplicative Int) :=
  let act := fun i : Multiplicative (ZMod 2) =>
    if i = 1 then 1 else (MulEquiv.prodComm : MulAut (Multiplicative Int × Multiplicative Int))
  { toFun := act
    map_one' := ite_eq_left rfl
    map_mul' := by
      have cases₂ : ∀ i : Multiplicative (ZMod 2), i = 1 ∨ i = swap := by
        intro i
        change (Multiplicative.toAdd i : Fin 2) = 0 ∨ Multiplicative.toAdd i = (1 : ZMod 2)
        exact (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) (Multiplicative.toAdd i)
      have hs : swap * swap = 1 := by decide
      have hn : swap ≠ 1 := by decide
      intro i j
      rcases cases₂ i with rfl | rfl <;> rcases cases₂ j with rfl | rfl <;>
        simp only [act, one_mul, mul_one, hs, ite_eq_left rfl, ite_eq_right hn]
      rfl }

noncomputable abbrev U :=
  SemidirectProduct (Multiplicative Int × Multiplicative Int) (Multiplicative (ZMod 2)) action

noncomputable abbrev A : Subgroup U :=
  ⊤

noncomputable abbrev G : Subgroup U :=
  MonoidHom.range (MonoidHom.comp
    (SemidirectProduct.inl (φ := action))
    (MonoidHom.inl (Multiplicative Int) (Multiplicative Int)))

noncomputable abbrev D :=
  G

noncomputable abbrev T : Subgroup U :=
  ⊥

noncomputable abbrev C :=
  T

noncomputable abbrev E :=
  T

noncomputable abbrev F :=
  T

noncomputable abbrev B' :=
  T

noncomputable abbrev τ : A :=
  ⟨SemidirectProduct.inr (φ := action) swap, Subgroup.mem_top _⟩

noncomputable abbrev incl :=
  fun {H K : Subgroup U} (h : H ≤ K) =>
    ({ toHom := Subgroup.inclusion h
       hasRepresentative := ⟨1, fun _ => by simp⟩ } : MackeyDiagrams.ConjEmbedding H K)

noncomputable abbrev a : MackeyDiagrams.ConjEmbedding G A :=
  incl le_top

noncomputable abbrev b : MackeyDiagrams.ConjEmbedding D A :=
  incl le_top

noncomputable abbrev c : MackeyDiagrams.ConjEmbedding F D :=
  incl bot_le

noncomputable abbrev d : MackeyDiagrams.ConjEmbedding C G :=
  incl bot_le

noncomputable abbrev e : MackeyDiagrams.ConjEmbedding E C :=
  incl le_rfl

noncomputable abbrev f : MackeyDiagrams.ConjEmbedding E F :=
  incl le_rfl

noncomputable abbrev u : MackeyDiagrams.ConjEmbedding B' A :=
  incl bot_le

noncomputable abbrev v : MackeyDiagrams.ConjEmbedding C B' :=
  incl le_rfl

noncomputable abbrev w : MackeyDiagrams.ConjEmbedding F B' :=
  incl le_rfl

noncomputable abbrev comp :=
  @MackeyDiagrams.ConjEmbedding.comp U _

noncomputable abbrev bc :=
  comp b c

noncomputable abbrev de :=
  comp d e

noncomputable abbrev up :=
  @MackeyDiagrams.Word.up U _

noncomputable abbrev down :=
  @MackeyDiagrams.Word.down U _

noncomputable abbrev tensor :=
  @MackeyDiagrams.Word.tensor U _

noncomputable abbrev bottom :=
  tensor (tensor (down a) (up b)) (up c)

noncomputable abbrev top :=
  tensor (tensor (up d) (up e)) (down f)

noncomputable abbrev mergedBottom :=
  tensor (down a) (up bc)

noncomputable abbrev mergedTop :=
  tensor (up de) (down f)

noncomputable abbrev drawId :=
  fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)

noncomputable abbrev splitBottom : MackeyDiagrams.LabelledDrawing Complex mergedBottom bottom :=
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal (drawId (down a))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp b c)))
    (MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.unassociate (down a) (up b) (up c)))

noncomputable abbrev mergeTop : MackeyDiagrams.LabelledDrawing Complex top mergedTop :=
  MackeyDiagrams.LabelledDrawing.horizontal
    (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp d e))
    (drawId (down f))

noncomputable abbrev eval :=
  fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (MackeyDiagrams.LabelledDrawing.vertical splitBottom
        (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))

noncomputable abbrev atRight :=
  fun {K H J L J' : Subgroup U} (p : MackeyDiagrams.Word K H)
      {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
      {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor q r) (tensor q' r')) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate p q r))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal (drawId p) crossing)
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))

noncomputable abbrev ProjectionLabel :=
  fun {K H P L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K P) (β : MackeyDiagrams.ConjEmbedding H P)
      (η : MackeyDiagrams.ConjEmbedding L K) (θ : MackeyDiagrams.ConjEmbedding L H) =>
    MackeyDiagrams.ProjectionDot.Mixed α β η θ

noncomputable abbrev terms :=
  fun {X : Type} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))

noncomputable abbrev Qstar :=
  fun (p : ProjectionLabel a bc de f) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))

noncomputable abbrev left :=
  fun {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
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

noncomputable abbrev right :=
  fun
      (ells : MackeyDiagrams.DotLabel Complex bc (comp u w))
      (ms : Finsupp (ProjectionLabel a u d v) Complex)
      (ns : Finsupp (ProjectionLabel v w e f) Complex) =>
    MackeyDiagrams.LabelledDrawing.vertical
      (atRight (down a)
        (MackeyDiagrams.LabelledDrawing.parallelUp b c u w (MackeyDiagrams.DotLabel.terms ells)))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.compactProjection a u d v (terms ms)) (drawId (up w)))
        (atRight (up d) (MackeyDiagrams.LabelledDrawing.compactProjection v w e f (terms ns))))

noncomputable abbrev Drawing :=
  MackeyDiagrams.LabelledDrawing Complex bottom top

noncomputable abbrev IsLeftWith :=
  fun (allowed : Set A) (drawing : Drawing) =>
    ∃ (B : Subgroup U) (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de),
      (∀ x ∈ Finsupp.support xs,
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot x) ∈ allowed) ∧
      drawing = left r s t xs ys zs

noncomputable abbrev leftShape :=
  MackeyDiagrams.LabelledDrawing.planarShape
    (left (B := T) d (incl bot_le) (incl le_rfl) 0 0 0)

noncomputable abbrev sumDrawings :=
  fun (drawings : List Drawing) =>
    match drawings with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest

noncomputable abbrev basisVector :=
  fun p : A =>
    Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc p) (1 : Complex)

noncomputable abbrev line :=
  MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)

noncomputable abbrev swapCoset :=
  DoubleCoset.doubleCoset τ (line : Set A) (line : Set A)

noncomputable abbrev intersection :=
  fun x : A => line ⊓
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) line

end CaseTwoAudit


namespace CaseTwoAudit

open MackeyDiagrams

private theorem swap_ne_one : swap ≠ 1 := by decide
private theorem sq_swap : swap * swap = 1 := by decide

theorem line_iff (x : A) : x ∈ line ↔ x.val.left.2 = 1 ∧ x.val.right = 1 := by
  constructor
  · rintro ⟨⟨_, i, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hr⟩
    let g := (SemidirectProduct.inl (φ := action))
      ((MonoidHom.inl (Multiplicative Int) (Multiplicative Int)) x.val.left.1)
    refine ⟨⟨g, ⟨x.val.left.1, rfl⟩⟩, Subtype.ext ?_⟩
    apply SemidirectProduct.ext
    · exact Prod.ext rfl hl.symm
    · exact hr.symm

theorem swapCoset_iff (x : A) : x ∈ swapCoset ↔ x.val.right = swap := by
  constructor
  · intro hx
    obtain ⟨l, hl, r, hr, he⟩ := DoubleCoset.mem_doubleCoset.mp hx
    have h := congrArg (fun a : A => a.val.right) he
    change x.val.right = l.val.right * swap * r.val.right at h
    rw [(line_iff l).mp hl |>.2, (line_iff r).mp hr |>.2, one_mul, mul_one] at h
    exact h
  · intro hx
    let l : A := ⟨⟨(x.val.left.1, 1), 1⟩, Subgroup.mem_top _⟩
    let r : A := ⟨⟨(x.val.left.2, 1), 1⟩, Subgroup.mem_top _⟩
    apply DoubleCoset.mem_doubleCoset.mpr
    refine ⟨l, (line_iff l).mpr ⟨rfl,rfl⟩, r, (line_iff r).mpr ⟨rfl,rfl⟩, ?_⟩
    symm
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change ((x.val.left.1, 1) * action 1 1) * action (1 * swap) (x.val.left.2, 1) = x.val.left
      rw [map_one, one_mul, mul_one]
      change (x.val.left.1, 1) * (if swap = 1 then 1 else
        (MulEquiv.prodComm : MulAut (Multiplicative Int × Multiplicative Int))) (x.val.left.2, 1) = _
      rw [ite_eq_right swap_ne_one]
      exact Prod.ext (mul_one _) (one_mul _)
    · exact (by simpa using hx.symm : (1 : Multiplicative (ZMod 2)) * swap * 1 = x.val.right)

theorem intersect_calc (x : A) : (x ∈ line → intersection x = line) ∧
    (x ∈ swapCoset → intersection x = ⊥) := by
  have conjugation (h : A) (hh : h ∈ line) :
      (x * h * x⁻¹).val.left =
        if x.val.right = 1 then h.val.left else (h.val.left.2, h.val.left.1) := by
    have hr := (line_iff h).mp hh |>.2
    have hx' : action x.val.right h.val.left =
        if x.val.right = 1 then h.val.left else (h.val.left.2, h.val.left.1) := by
      change (if x.val.right = 1 then 1 else MulEquiv.prodComm) h.val.left = _
      split <;> rfl
    change x.val.left * action x.val.right h.val.left *
      action (x.val.right * h.val.right) (action x.val.right⁻¹ x.val.left⁻¹) = _
    rw [hr, mul_one]
    change x.val.left * action x.val.right h.val.left *
      (action x.val.right * action x.val.right⁻¹) x.val.left⁻¹ = _
    rw [← MonoidHom.map_mul, mul_inv_cancel, map_one]
    change x.val.left * action x.val.right h.val.left * x.val.left⁻¹ = _
    rw [mul_comm x.val.left, mul_assoc, mul_inv_cancel, mul_one, hx']
  constructor
  · intro h
    apply le_antisymm inf_le_left
    intro y hy
    have hx := (line_iff x).mp h |>.2
    refine ⟨hy, y, hy, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simpa [MulAut.conj_apply, hx] using conjugation y hy
    · change x.val.right * y.val.right * x.val.right⁻¹ = _
      rw [hx, one_mul, inv_one, mul_one]
  · intro hxcoset
    have hx := (swapCoset_iff x).mp hxcoset
    apply le_antisymm _ bot_le
    rintro y ⟨hy, z, hz, rfl⟩
    change (x * z * x⁻¹) ∈ (⊥ : Subgroup A)
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply SemidirectProduct.ext
    · have hc := conjugation z hz
      rw [hx, ite_eq_right swap_ne_one] at hc
      have hz₂ := (line_iff z).mp hz |>.1
      have hy₂ := (line_iff (x * z * x⁻¹)).mp hy |>.1
      rw [hc] at hy₂
      change z.val.left.1 = 1 at hy₂
      rw [hc, hz₂, hy₂]
      rfl
    · change x.val.right * z.val.right * x.val.right⁻¹ = 1
      rw [(line_iff z).mp hz |>.2, mul_one, mul_inv_cancel]

end CaseTwoAudit

namespace CaseTwoAudit

open MackeyDiagrams

private theorem bot_el (j : T) : j = 1 :=
  Subtype.ext (Subgroup.mem_bot.mp j.property)

private theorem unit_index {J K : Subgroup U} [Subsingleton K]
    (i : ConjEmbedding J K) : i.toHom.range.index = 1 := by
  apply Subgroup.index_eq_one.mpr
  ext g
  change (∃ j, i.toHom j = g) ↔ True
  exact iff_true_intro ⟨1, Subsingleton.elim _ _⟩

theorem cup_indices : v.toHom.range.index = 1 ∧ f.toHom.range.index = 1 := by
  let _ : Subsingleton T := ⟨fun j k => (bot_el j).trans (bot_el k).symm⟩
  exact ⟨unit_index v, unit_index f⟩

theorem forced_bot {B : Subgroup U} (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (x : Dot (comp a r) (comp b s)) (hx : x.element ∈ swapCoset) : B = ⊥ := by
  apply le_antisymm _ bot_le
  intro j hj
  let j' : B := ⟨j, hj⟩
  have h : a.toHom (r.toHom j') ∈ intersection x.element := by
    refine ⟨⟨r.toHom j',rfl⟩, b.toHom (s.toHom j'), ⟨s.toHom j',rfl⟩, ?_⟩
    change x.element * b.toHom (s.toHom j') * x.element⁻¹ = a.toHom (r.toHom j')
    have he := x.intertwines j'
    change a.toHom (r.toHom j') * x.element = x.element * b.toHom (s.toHom j') at he
    rw [← he, mul_assoc, mul_inv_cancel, mul_one]
  rw [(intersect_calc x.element).2 hx, Subgroup.mem_bot] at h
  apply Subgroup.mem_bot.mpr
  have h' : a.toHom (r.toHom j') = a.toHom (r.toHom 1) := by simpa only [map_one] using h
  exact congrArg Subtype.val (r.injective (a.injective h'))

theorem line_infinite : Infinite G := by
  apply Infinite.of_injective
    (f := fun n : Int =>
      let i := Multiplicative.ofAdd n
      (⟨⟨(i, 1), 1⟩, ⟨i, rfl⟩⟩ : G))
  intro j k h
  exact congrArg (fun x : G => Multiplicative.toAdd x.val.left.1) h

theorem line_commutes (x y : A) (hx : x ∈ line) (hy : y ∈ line) :
    x * y = y * x := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change x.val.left * action x.val.right y.val.left = y.val.left * action y.val.right x.val.left
    rw [(line_iff x).mp hx |>.2, (line_iff y).mp hy |>.2, map_one]
    exact mul_comm _ _
  · change x.val.right * y.val.right = y.val.right * x.val.right
    rw [(line_iff x).mp hx |>.2, one_mul, mul_one]

theorem unbounded_line_fiber (r : ConjEmbedding T G) (s : ConjEmbedding T D)
    (y : Dot (comp a r) (comp b s)) (hy : y.element ∈ line) :
    ¬ Set.Finite {j | Generator.mixedMultiplicationBasis a b r s y j =
      Generator.mixedPair a b y.element} := by
  let _ : Infinite G := line_infinite
  apply Set.infinite_of_injective_forall_mem
    (f := fun j : G => (Biset.induction r).pair (Biset.restriction s) j j⁻¹)
  · intro j k hk
    have h : (Biset.balance (Biset.induction r) (Biset.restriction s)).r (j,j⁻¹) (k,k⁻¹) :=
      Quotient.exact hk
    obtain ⟨i, hi, _⟩ := h
    change (1 : G) * j * (r.toHom i)⁻¹ = k at hi
    simpa only [bot_el i, map_one, inv_one, one_mul, mul_one] using hi
  · intro j
    change Generator.mixedPair a b (a.toHom j * y.element * b.toHom j⁻¹) =
      Generator.mixedPair a b y.element
    change Generator.mixedPair a b (a.toHom j * y.element * a.toHom j⁻¹) = _
    rw [line_commutes _ _ ⟨j,rfl⟩ hy, map_inv, mul_assoc, mul_inv_cancel, mul_one]

end CaseTwoAudit

namespace CaseTwoAudit
open MackeyDiagrams
open PlanarCode

private def leftCode : Code :=
  [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp]

private def RigidAt (p : Code) : Prop :=
  (∀ event ∈ p, event = .vertex 0 .mixedProjection ∨ event = .vertex 1 .mixedProjection ∨
    event = .vertex 0 .parallelUp) ∧
  (∀ before after x y, p = before ++ [x, y] ++ after →
    x.outputs.length = 2 ∧ x.inputs.length = 2 ∧ y.outputs.length = 2 ∧ y.inputs.length = 2 ∧
    x.position ≤ 1 ∧ y.position ≤ 1)

private theorem leftCode_rigid : RigidAt leftCode := by
  refine ⟨?_, ?_⟩
  · simp [leftCode]
  intro before after x y h
  rcases before with _ | ⟨a, ⟨_ | ⟨b, more⟩⟩⟩
  · simp [leftCode] at h
    obtain ⟨rfl, rfl, _⟩ := h
    decide
  · simp [leftCode] at h
    obtain ⟨_, rfl, rfl, _⟩ := h
    decide
  · have hlen := congrArg List.length h
    simp [leftCode] at hlen
    omega

-- Any sublist with surrounding context still occupies the same three-wire code.
-- Both adjacent pairs overlap, so no exchange can have either orientation here.
private theorem code_eq_of_equivalent_rigid {x y : Code} (h : Equivalent x y) :
    (∀ lead trail, RigidAt (lead ++ x ++ trail) → x = y) ∧
    (∀ lead trail, RigidAt (lead ++ y ++ trail) → x = y) := by
  induction h with
  | refl => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | symm _ ih => exact ⟨fun p q h => (ih.2 p q h).symm, fun p q h => (ih.1 p q h).symm⟩
  | trans _ _ ih₁ ih₂ =>
      constructor
      · intro p q h
        have h₁ := ih₁.1 p q h
        exact h₁.trans (ih₂.1 p q (h₁ ▸ h))
      · intro p q h
        have h₂ := ih₂.2 p q h
        exact (ih₁.2 p q (h₂.symm ▸ h)).trans h₂
  | context before after _ ih =>
      constructor
      · intro p q h
        have he := ih.1 (p ++ before) (after ++ q) (by simpa only [List.append_assoc] using h)
        rw [he]
      · intro p q h
        have he := ih.2 (p ++ before) (after ++ q) (by simpa only [List.append_assoc] using h)
        rw [he]
  | exchange before after i gap l r =>
      constructor
      · intro p q h
        have hh := h.2 (p ++ before) (after ++ q) (l.place i)
          (r.place (i + l.outputs.length + gap)) (by simp only [List.append_assoc])
        obtain ⟨hsize, _, _, _, _, hpos⟩ := hh
        have sz : (l.place i).outputs.length = l.outputs.length := by cases l <;> rfl
        have hr : (r.place (i + l.outputs.length + gap)).position = i + l.outputs.length + gap := by
          cases r <;> rfl
        omega
      · intro p q h
        have hh := h.2 (p ++ before) (after ++ q) (r.place (i + l.inputs.length + gap))
          (l.place i) (by simp only [List.append_assoc])
        obtain ⟨_, _, _, hsize, hpos, _⟩ := hh
        have sz : (l.place i).inputs.length = l.inputs.length := by cases l <;> rfl
        have hr : (r.place (i + l.inputs.length + gap)).position = i + l.inputs.length + gap := by
          cases r <;> rfl
        omega
  | @scale i b t x y _ _ =>
      constructor
      · intro p q h
        have bad := h.1 (.scale i b t x) (by simp)
        rcases bad with bad | bad | bad <;> cases bad
      · intro p q h
        have bad := h.1 (.scale i b t y) (by simp)
        rcases bad with bad | bad | bad <;> cases bad
  | @add i b t x y z w _ _ _ _ =>
      constructor
      · intro p q h
        have bad := h.1 (.add i b t x z) (by simp)
        rcases bad with bad | bad | bad <;> cases bad
      · intro p q h
        have bad := h.1 (.add i b t y w) (by simp)
        rcases bad with bad | bad | bad <;> cases bad

theorem checked_leftCode {p q : Word G F} (drawing : LabelledDrawing Complex p q)
    (h : drawing.planarShape = leftShape) : encode drawing.erase.geometry = leftCode := by
  have he := congrArg PlanarShape.wiring h
  change Quotient.mk PlanarCode.setoid (encode drawing.erase.geometry) =
    Quotient.mk PlanarCode.setoid leftCode at he
  have hr := Quotient.exact he
  exact (code_eq_of_equivalent_rigid hr).2 [] [] (by simpa using leftCode_rigid)

end CaseTwoAudit

namespace CaseTwoAudit
open MackeyDiagrams

private theorem one_in_line : (1 : A) ∈ line := line.one_mem
private theorem tau_in_swapCoset : τ ∈ swapCoset := DoubleCoset.mem_doubleCoset_self line line τ

theorem subset_self_coset (p : A) (hp : p ∈ line) :
    DoubleCoset.doubleCoset p (line : Set A) (line : Set A) = line := by
  ext x
  constructor
  · rintro h
    obtain ⟨k,hk,l,hl,rfl⟩ := DoubleCoset.mem_doubleCoset.mp h
    exact line.mul_mem (line.mul_mem hk hp) hl
  · intro hx
    apply DoubleCoset.mem_doubleCoset.mpr
    exact ⟨x * p⁻¹, line.mul_mem hx (line.inv_mem hp), 1, line.one_mem, by group⟩

theorem parameters_incompatible {B : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (x y : ProjectionLabel a b r s) :
    x.dot.element ∈ line → y.dot.element ∈ swapCoset → False := by
  intro hx hy
  have hB := forced_bot r s y.dot hy
  subst B
  exact unbounded_line_fiber r s x.dot hx (x.finite _)

private theorem singletonTerms {X : Type} (x : X) :
    terms (Finsupp.single x (1 : Complex)) = [((1 : Complex), x)] := by
  classical
  have hs : (Finsupp.single x (1 : Complex)).support = {x} := by simp
  unfold terms
  rw [hs]
  simp

-- Theorem 6.4(2), first assertion. This uses the full intersection
-- construction term by term. Its common-region specialization needs an
-- additional finite-index hypothesis that the example does not supply.
theorem left_transfer (p : ProjectionLabel a bc de f) (allowed : Set A)
    (hp : p.dot.element ∈ allowed) :
    ∃ l, IsLeftWith allowed l ∧ eval l = Qstar p := by
  classical
  obtain ⟨l, hw, hval⟩ := (CaseTwoLeftProjectionConstruction a b c d e f).1 p
  obtain ⟨r,s,t,_,_,_,_,x,y,z,hx,_,_,_,_,hl⟩ := hw
  refine ⟨l, ⟨_, r, s, t, Finsupp.single x 1, Finsupp.single y 1,
    Finsupp.single z 1, ?_, ?_⟩, hval⟩
  · intro q hq
    have he : q = x := ((Finsupp.mem_support_single q x (1 : Complex)).mp hq).1
    subst q
    exact hx.symm ▸ hp
  · rw [hl]
    dsimp only [left]
    change _ = LabelledDrawing.vertical
      (LabelledDrawing.horizontal (LabelledDrawing.compactProjection a b r s
        (terms (Finsupp.single x 1))) (drawId (up c)))
      (LabelledDrawing.vertical
        (atRight (up r) (LabelledDrawing.compactProjection s c t f
          (terms (Finsupp.single y 1))))
        (LabelledDrawing.horizontal (LabelledDrawing.parallelUp r t d e
          (terms (Finsupp.single z 1))) (drawId (down f))))
    rw [singletonTerms, singletonTerms, singletonTerms]

end CaseTwoAudit

namespace CaseTwoAudit

open MackeyDiagrams

private theorem trivial_dot {P : Subgroup U} (alpha beta : ConjEmbedding T P) (q : P) :
    ∀ h, alpha.toHom h * q = q * beta.toHom h := by
  intro h
  have hh : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.property)
  simp [hh]

noncomputable def proj {J K P : Subgroup U} (alpha : ConjEmbedding J P)
    (beta : ConjEmbedding K P) (eta : ConjEmbedding T J) (theta : ConjEmbedding T K)
    (q : P) (hinj : Function.Injective (fun z : J × K =>
      alpha.toHom z.1 * q * beta.toHom z.2)) : ProjectionLabel alpha beta eta theta := by
  let dot : Dot (alpha.comp eta) (beta.comp theta) :=
    ⟨q, trivial_dot (alpha.comp eta) (beta.comp theta) q⟩
  refine ⟨dot, Generator.finiteFiber_of_injective alpha beta eta theta dot ?_⟩
  intro x y
  refine Quotient.inductionOn₂ x y (fun j k he => ?_)
  change Generator.mixedPair alpha beta (alpha.toHom j.1 * q * beta.toHom j.2) =
    Generator.mixedPair alpha beta (alpha.toHom k.1 * q * beta.toHom k.2) at he
  exact congrArg (Quotient.mk _) (hinj ((Generator.mixedEquiv alpha beta).symm.injective he))

theorem trivial_right_injective {J P : Subgroup U} (alpha : ConjEmbedding J P)
    (beta : ConjEmbedding T P) (q : P) :
    Function.Injective (fun z : J × T => alpha.toHom z.1 * q * beta.toHom z.2) := by
  intro j k he
  have hbot (g : T) : g = 1 := Subtype.ext (Subgroup.mem_bot.mp g.property)
  change alpha.toHom j.1 * q * beta.toHom j.2 =
    alpha.toHom k.1 * q * beta.toHom k.2 at he
  simp only [hbot j.2, hbot k.2, map_one, mul_one] at he
  exact Prod.ext (alpha.injective (mul_right_cancel he)) ((hbot j.2).trans (hbot k.2).symm)

noncomputable def overall (q : A) : ProjectionLabel a bc de f :=
  proj a bc de f q (trivial_right_injective a bc q)

noncomputable def mid (q : A) : ProjectionLabel a u d v :=
  proj a u d v q (trivial_right_injective a u q)

noncomputable def last : ProjectionLabel v w e f :=
  proj v w e f 1 (trivial_right_injective v w 1)

noncomputable def first : Dot bc (comp u w) :=
  ⟨1, trivial_dot bc (comp u w) 1⟩

noncomputable abbrev unitOut :=
  (Biset.induction de).pair (Biset.restriction f) 1 1

theorem transfer_probe (q z : A) :
    Qstar (overall q) (basisVector z) unitOut =
      if q = z then (1 : Complex) else 0 := by
  classical
  let p := overall q
  change
    (Biset.Hom.transfer Complex (Generator.mixedMultiplicationBasis a bc de f p.dot)
        (Generator.mixedMultiplication_equivariant a bc de f p.dot) p.finite).toLinearMap
      (Finsupp.single (Generator.mixedPair a bc z) 1) unitOut = _
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_apply]
  change (if Generator.mixedPair a bc (a.toHom 1 * q * bc.toHom 1) =
      Generator.mixedPair a bc z then 1 else 0) = _
  rw [map_one, map_one, one_mul, mul_one]
  have he : Generator.mixedPair a bc q = Generator.mixedPair a bc z ↔ q = z :=
    (Generator.mixedEquiv a bc).symm.injective.eq_iff
  simp only [he]

end CaseTwoAudit

set_option maxHeartbeats 2000000
namespace CaseTwoFactor
open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {A B C D : Subgroup U}

private theorem inputs_stack {s t : DrawingShape} (h : s.outputs = t.inputs) :
    (s.stack t).inputs = s.inputs := by
  induction s with
  | straight => exact h.symm
  | vertical a b ia ib =>
    cases t <;> rfl
  | vertex | horizontal | zero | add | scale =>
    cases t <;> rfl

private theorem outputs_stack {s t : DrawingShape} (h : s.outputs = t.inputs) :
    (s.stack t).outputs = t.outputs := by
  induction s with
  | straight => rfl
  | vertical a b ia ib =>
    cases t <;> first | exact h | exact ib h
  | vertex | horizontal | zero | add | scale =>
    cases t <;> first | exact h | rfl

private theorem inputs_juxtapose (s t : DrawingShape) :
    (s.juxtapose t).inputs = s.inputs ++ t.inputs := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.inputs]
    | cons x xs =>
      cases t with
      | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.inputs]
      | _ => rfl
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, DrawingShape.inputs, ib, List.append_assoc]
    | _ => simp [DrawingShape.juxtapose, DrawingShape.inputs, ib, List.append_assoc]
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.inputs]
    | _ => rfl

private theorem outputs_juxtapose (s t : DrawingShape) :
    (s.juxtapose t).outputs = s.outputs ++ t.outputs := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.outputs]
    | cons x xs =>
      cases t with
      | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs]
      | _ => rfl
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs, ib, List.append_assoc]
    | _ => simp [DrawingShape.juxtapose, DrawingShape.outputs, ib, List.append_assoc]
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r => cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs]
    | _ => rfl

private theorem shift_append (i : Nat) (a b : PlanarCode.Code) :
    PlanarCode.shift i (a ++ b) = PlanarCode.shift i a ++ PlanarCode.shift i b :=
  List.map_append

private theorem shift_shift (i j : Nat) (a : PlanarCode.Code) :
    PlanarCode.shift i (PlanarCode.shift j a) = PlanarCode.shift (i+j) a := by
  simp only [PlanarCode.shift, List.map_map]
  congr 1
  funext e
  cases e <;> simp [PlanarEvent.place, PlanarEvent.position, Nat.add_assoc]

private theorem shift_zero (a : PlanarCode.Code) : PlanarCode.shift 0 a = a := by
  unfold PlanarCode.shift
  have h : (fun e : PlanarEvent => e.place (0 + e.position)) = id := by
    funext e
    cases e <;> simp [PlanarEvent.place, PlanarEvent.position]
  rw [h, List.map_id]

private theorem encode_stack (s t : DrawingShape) :
    PlanarCode.encode (s.stack t) = PlanarCode.encode s ++ PlanarCode.encode t := by
  induction s with
  | straight => rfl
  | vertical a b ia ib =>
    cases t <;> simp [DrawingShape.stack, PlanarCode.encode, ib, List.append_assoc]
  | vertex | horizontal | zero | add | scale =>
    cases t <;> simp [DrawingShape.stack, PlanarCode.encode]

private theorem encode_juxtapose (s t : DrawingShape) :
    PlanarCode.encode (s.juxtapose t) =
      PlanarCode.encode s ++ PlanarCode.shift s.outputs.length (PlanarCode.encode t) := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.outputs, PlanarCode.encode, shift_zero]
    | cons x xs =>
      cases t with
      | straight r =>
        cases r <;> simp [DrawingShape.juxtapose, PlanarCode.encode, PlanarCode.shift]
      | _ => rfl
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r with
      | nil => simp [DrawingShape.juxtapose, PlanarCode.encode, PlanarCode.shift]
      | cons x xs =>
        simp [DrawingShape.juxtapose, PlanarCode.encode, ib, PlanarCode.shift]
    | _ => simp [DrawingShape.juxtapose, DrawingShape.outputs, PlanarCode.encode,
      ib, shift_append, shift_shift, List.append_assoc, List.length_append, Nat.add_assoc]
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, DrawingShape.outputs, PlanarCode.encode,
        PlanarCode.shift]
    | _ => rfl


private def Fits : DrawingShape → Prop
  | .vertical s t => Fits s ∧ Fits t ∧ s.outputs = t.inputs
  | .horizontal s t => Fits s ∧ Fits t
  | .add s _ | .scale s => Fits s
  | _ => True

private theorem fits_stack {s t : DrawingShape} (hs : Fits s) (ht : Fits t)
    (h : s.outputs = t.inputs) : Fits (s.stack t) := by
  induction s with
  | straight => exact ht
  | vertical a b ia ib =>
    obtain ⟨ha,hb,hab⟩ := hs
    change b.outputs = t.inputs at h
    cases t with
    | straight => exact ⟨ha, hb, hab⟩
    | _ => exact ⟨ha, ib hb h, hab.trans (inputs_stack h).symm⟩
  | vertex | horizontal | zero | add | scale =>
    cases t <;> first | exact hs | exact ⟨hs, ht, h⟩

private theorem fits_juxtapose {s t : DrawingShape} (hs : Fits s) (ht : Fits t) :
    Fits (s.juxtapose t) := by
  induction s with
  | straight l =>
    cases l with
    | nil => exact ht
    | cons x xs =>
      cases t with
      | straight r => cases r <;> trivial
      | _ => exact ⟨hs, ht⟩
  | horizontal a b ia ib =>
    cases t with
    | straight r =>
      cases r with
      | nil => exact hs
      | cons x xs => exact ⟨hs.1, ib hs.2⟩
    | _ => exact ⟨hs.1, ib hs.2⟩
  | vertex | vertical | zero | add | scale =>
    cases t with
    | straight r =>
      cases r with
      | nil => exact hs
      | cons x xs => exact ⟨hs, ht⟩
    | _ => exact ⟨hs, ht⟩

private theorem upward_dirs (n : Nat) :
    (DrawingShape.upwardDots n).inputs = [true] ∧
      (DrawingShape.upwardDots n).outputs = [true] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h : (DrawingShape.vertex .upDot).outputs = (DrawingShape.upwardDots n).inputs := ih.1.symm
    exact ⟨inputs_stack h, (outputs_stack h).trans ih.2⟩

private theorem downward_dirs (n : Nat) :
    (DrawingShape.downwardDots n).inputs = [false] ∧
      (DrawingShape.downwardDots n).outputs = [false] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h : (DrawingShape.vertex .downDot).outputs = (DrawingShape.downwardDots n).inputs := ih.1.symm
    exact ⟨inputs_stack h, (outputs_stack h).trans ih.2⟩

private theorem expanded_dirs (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    (DrawingShape.expandedProjectionGeometry n o c).inputs = [false, true] ∧
    (DrawingShape.expandedProjectionGeometry n o c).outputs = [true, false] := by
  unfold DrawingShape.expandedProjectionGeometry
  dsimp only
  have h₁ : (match o with
    | .junction => (DrawingShape.straight [false]).horizontal (.vertex .bentReverseCup)
    | .cupAndMerge => ((DrawingShape.straight [false, true]).horizontal (.vertex .reverseCup)).stack
        ((DrawingShape.straight [false]).horizontal ((DrawingShape.vertex .mergeUp).horizontal (.straight [false])))).outputs =
      [false, true, false] := by cases o <;> rfl
  have h₂ : (match c with
    | .junction => (DrawingShape.vertex .bentTraceCapOnLeft).horizontal (.straight [false])
    | .splitAndTrace => ((DrawingShape.straight [false]).horizontal
        ((DrawingShape.vertex .splitUp).horizontal (.straight [false]))).stack
          ((DrawingShape.vertex .traceCap).horizontal (.straight [true, false]))).inputs =
      [false, true, false] := by cases c <;> rfl
  let mid := (DrawingShape.straight [false]).horizontal
    ((DrawingShape.upwardDots n).horizontal (.straight [false]))
  have hm₁ : mid.inputs = [false,true,false] := by
    simp [mid, DrawingShape.inputs, upward_dirs]
  have hm₂ : mid.outputs = [false,true,false] := by
    simp [mid, DrawingShape.outputs, upward_dirs]
  have hm := hm₂.trans h₂.symm
  have hh := h₁.trans ((inputs_stack hm).trans hm₁).symm
  constructor
  · exact (inputs_stack hh).trans (by cases o <;> rfl)
  · exact (outputs_stack hh).trans ((outputs_stack hm).trans (by cases c <;> rfl))

private theorem geometry_dirs {s : DrawingShape} (hs : Fits s) :
    s.geometry.inputs = s.inputs ∧ s.geometry.outputs = s.outputs := by
  induction s with
  | straight => exact ⟨rfl,rfl⟩
  | vertex k =>
    cases k <;> try exact ⟨rfl,rfl⟩
    case parallelUpChain n =>
      simp only [DrawingShape.geometry, DrawingShape.inputs, DrawingShape.outputs]
      have h₁ : (.vertex .mergeUp : DrawingShape).outputs = (DrawingShape.upwardDots n).inputs := (upward_dirs n).1.symm
      have h₂ : (DrawingShape.upwardDots n).outputs = (.vertex .splitUp : DrawingShape).inputs := (upward_dirs n).2
      rw [inputs_stack (h₁.trans (inputs_stack h₂).symm), outputs_stack (h₁.trans (inputs_stack h₂).symm),
        outputs_stack h₂]
      exact ⟨rfl,rfl⟩
    case parallelDownChain n =>
      simp only [DrawingShape.geometry, DrawingShape.inputs, DrawingShape.outputs]
      have h₁ : (.vertex .mergeDown : DrawingShape).outputs = (DrawingShape.downwardDots n).inputs := (downward_dirs n).1.symm
      have h₂ : (DrawingShape.downwardDots n).outputs = (.vertex .splitDown : DrawingShape).inputs := (downward_dirs n).2
      rw [inputs_stack (h₁.trans (inputs_stack h₂).symm), outputs_stack (h₁.trans (inputs_stack h₂).symm),
        outputs_stack h₂]
      exact ⟨rfl,rfl⟩
    case expandedMixedProjection o c => exact expanded_dirs 1 o c
    case expandedProjectionChain n o c => exact expanded_dirs n o c
  | vertical s t ihs iht =>
    obtain ⟨hs, ht, hst⟩ := hs
    obtain ⟨hs₁,hs₂⟩ := ihs hs
    obtain ⟨ht₁,ht₂⟩ := iht ht
    have h : s.geometry.outputs = t.geometry.inputs := hs₂.trans (hst.trans ht₁.symm)
    exact ⟨(inputs_stack h).trans hs₁, (outputs_stack h).trans ht₂⟩
  | horizontal s t ihs iht =>
    obtain ⟨hs, ht⟩ := hs
    obtain ⟨hs₁,hs₂⟩ := ihs hs
    obtain ⟨ht₁,ht₂⟩ := iht ht
    exact ⟨by simp [DrawingShape.geometry, inputs_juxtapose, DrawingShape.inputs, hs₁, ht₁],
      by simp [DrawingShape.geometry, outputs_juxtapose, DrawingShape.outputs, hs₂, ht₂]⟩
  | zero => exact ⟨rfl,rfl⟩
  | add l r ihl ihr => exact ihl hs
  | scale d ih => exact ih hs

private def code (s : DrawingShape) : PlanarCode.Code :=
  PlanarCode.encode s.geometry

private theorem code_stack (s t : DrawingShape) : code (s.stack t) = code s ++ code t := by
  induction s generalizing t with
  | straight => rfl
  | vertical a b ia ib =>
    have h (t : DrawingShape) : PlanarCode.encode (b.stack t).geometry =
        PlanarCode.encode b.geometry ++ PlanarCode.encode t.geometry := ib t
    cases t <;>
      simp [DrawingShape.stack, code, DrawingShape.geometry, encode_stack, h, List.append_assoc]
    all_goals rfl
  | vertex | horizontal | zero | add | scale =>
    cases t <;> simp [DrawingShape.stack, code, DrawingShape.geometry, encode_stack] <;> rfl

private theorem code_juxtapose {s t : DrawingShape} (hs : Fits s) (ht : Fits t) :
    code (s.juxtapose t) = code s ++ PlanarCode.shift s.outputs.length (code t) := by
  induction s with
  | straight l =>
    cases l with
    | nil => simp [DrawingShape.juxtapose, DrawingShape.outputs, code, PlanarCode.encode,
        DrawingShape.geometry, shift_zero]
    | cons x xs =>
      cases t with
      | straight r =>
        cases r <;> simp [DrawingShape.juxtapose, code, DrawingShape.geometry, PlanarCode.encode,
          PlanarCode.shift]
      | _ =>
        first | rfl | simp [DrawingShape.juxtapose, code, DrawingShape.geometry, encode_juxtapose]
  | horizontal a b ia ib =>
    have h₁ := (geometry_dirs hs.1).2
    cases t with
    | straight r =>
      cases r with
      | nil =>
        simp [DrawingShape.juxtapose, code, DrawingShape.geometry, PlanarCode.encode, PlanarCode.shift]
      | cons x xs =>
        have hb : PlanarCode.encode (b.juxtapose (.straight (x :: xs))).geometry =
            PlanarCode.encode b.geometry := by
          have h := ib hs.2
          simpa [code, DrawingShape.geometry, PlanarCode.encode, PlanarCode.shift] using h
        simp [DrawingShape.juxtapose, code, DrawingShape.geometry, PlanarCode.encode,
          encode_juxtapose, hb, PlanarCode.shift]
    | _ =>
      have hb := ib hs.2
      unfold code at hb
      simp [DrawingShape.juxtapose, code, DrawingShape.geometry, encode_juxtapose,
        hb, h₁, DrawingShape.outputs, shift_append, shift_shift, List.append_assoc,
        List.length_append, Nat.add_assoc]
  | vertex | vertical | zero | add | scale =>
    have h := (geometry_dirs hs).2
    cases t with
    | straight r =>
      cases r <;> simp [DrawingShape.juxtapose, code, DrawingShape.geometry,
        encode_juxtapose, PlanarCode.encode, PlanarCode.shift]
    | _ =>
      simp [DrawingShape.juxtapose, code, DrawingShape.geometry, encode_juxtapose, ← h] <;> rfl


private theorem diagram_fits {p q : Word A B} (d : Diagram Complex p q) :
    Fits d.drawing ∧ d.drawing.inputs = p.directions ∧ d.drawing.outputs = q.directions := by
  induction d <;> try exact ⟨trivial, rfl, rfl⟩
  case associate p q r =>
    exact ⟨trivial, rfl, List.append_assoc _ _ _⟩
  case unassociate p q r =>
    exact ⟨trivial, List.append_assoc _ _ _, rfl⟩
  case rightUnit p =>
    exact ⟨trivial, (List.append_nil _).symm, rfl⟩
  case insertRightUnit p =>
    exact ⟨trivial, rfl, (List.append_nil _).symm⟩
  case vertical d e hd he =>
    have h := hd.2.2.trans he.2.1.symm
    exact ⟨fits_stack hd.1 he.1 h, (inputs_stack h).trans hd.2.1,
      (outputs_stack h).trans he.2.2⟩
  case horizontal d e hd he =>
    exact ⟨fits_juxtapose hd.1 he.1, (inputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.1 he.2.1), (outputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.2 he.2.2)⟩
  case add d e hd he => exact hd
  case scale r d hd => exact hd

private theorem drawing_fits {p q : Word A B} (d : LabelledDrawing Complex p q) :
    Fits d.erase ∧ d.erase.inputs = p.directions ∧ d.erase.outputs = q.directions := by
  induction d <;> try exact ⟨trivial, rfl, rfl⟩
  case ordinary d => exact diagram_fits d
  case trivalent v => cases v <;> exact ⟨trivial, rfl, rfl⟩
  case bentVertex v => cases v <;> exact ⟨trivial, rfl, rfl⟩
  case add d e hd he => exact hd
  case scale c d hd => exact hd
  case vertical d e hd he =>
    have h := hd.2.2.trans he.2.1.symm
    exact ⟨fits_stack hd.1 he.1 h, (inputs_stack h).trans hd.2.1,
      (outputs_stack h).trans he.2.2⟩
  case horizontal d e hd he =>
    exact ⟨fits_juxtapose hd.1 he.1, (inputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.1 he.2.1), (outputs_juxtapose _ _).trans
      (congrArg₂ (· ++ ·) hd.2.2 he.2.2)⟩

private theorem drawing_code_vert {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) :
    code (d.vertical e).erase = code d.erase ++ code e.erase :=
  code_stack _ _

private theorem drawing_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex p' q') :
    code (d.horizontal e).erase = code d.erase ++ PlanarCode.shift q.directions.length (code e.erase) := by
  have hd := drawing_fits d
  have he := drawing_fits e
  change code (d.erase.juxtapose e.erase) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]

private theorem diagram_code_vert {p q r : Word A B}
    (d : Diagram Complex p q) (e : Diagram Complex q r) :
    code (d.vertical e).drawing = code d.drawing ++ code e.drawing :=
  code_stack _ _

private theorem diagram_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : Diagram Complex p q) (e : Diagram Complex p' q') :
    code (d.horizontal e).drawing = code d.drawing ++ PlanarCode.shift q.directions.length (code e.drawing) := by
  have hd := diagram_fits d
  have he := diagram_fits e
  change code (d.drawing.juxtapose e.drawing) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]


private abbrev drawingCode {p q : Word A B} (d : LabelledDrawing Complex p q) :=
  code d.erase

private theorem drawingCode_vertical {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) :
    drawingCode (d.vertical e) = drawingCode d ++ drawingCode e :=
  drawing_code_vert d e

private theorem drawingCode_horizontal {p q : Word A B} {p' q' : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex p' q') :
    drawingCode (d.horizontal e) =
      drawingCode d ++ PlanarCode.shift q.directions.length (drawingCode e) :=
  drawing_code_horiz d e

private abbrev drawingId (p : Word A B) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private def Factorable {p q : Word A B} (d : LabelledDrawing Complex p q) : Prop :=
  ∀ l r, drawingCode d = l ++ r →
    ∃ (m : Word A B) (below : LabelledDrawing Complex p m)
      (above : LabelledDrawing Complex m q),
      drawingCode below = l ∧ drawingCode above = r ∧
        d.interpret.eval = below.interpret.eval.vertical above.interpret.eval

private theorem factor_atom {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : (drawingCode d).length ≤ 1) : Factorable d := by
  intro l r hc
  have hlen : l.length + r.length ≤ 1 := by simpa only [hc, List.length_append] using h
  have hempty : l = [] ∨ r = [] := by
    by_cases hl : l = []
    · exact .inl hl
    · exact .inr (List.length_eq_zero_iff.mp (by
        have := mt List.length_eq_zero_iff.mp hl
        omega))
  rcases hempty with rfl | rfl
  · exact ⟨p, drawingId p, d, rfl, hc, (Biset.Hom.id_vertical _).symm⟩
  · exact ⟨q, d, drawingId q, by simpa only [List.append_nil] using hc,
      rfl, (Biset.Hom.vertical_id _).symm⟩

private theorem factor_vertical {p q r : Word A B}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex q r}
    (hd : Factorable d) (he : Factorable e) : Factorable (d.vertical e) := by
  intro l t hc
  rw [drawingCode_vertical] at hc
  rcases List.append_eq_append_iff.mp hc with ⟨s, hl, hs⟩ | ⟨s, hs, ht⟩
  · obtain ⟨m, f, g, hf, hg, hev⟩ := he s t hs
    refine ⟨m, d.vertical f, g, ?_, hg, ?_⟩
    · rw [drawingCode_vertical, hf, hl]
    · change d.interpret.eval.vertical e.interpret.eval =
        (d.interpret.eval.vertical f.interpret.eval).vertical g.interpret.eval
      rw [hev, Biset.Hom.vertical_assoc]
  · obtain ⟨m, f, g, hf, hg, hdv⟩ := hd l s hs
    refine ⟨m, f, g.vertical e, hf, ?_, ?_⟩
    · rw [drawingCode_vertical, hg, ht]
    · change d.interpret.eval.vertical e.interpret.eval =
        f.interpret.eval.vertical (g.interpret.eval.vertical e.interpret.eval)
      rw [hdv, Biset.Hom.vertical_assoc]

private theorem factor_horizontal {p q : Word A B} {p' q' : Word B C}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex p' q'}
    (hd : Factorable d) (he : Factorable e) : Factorable (d.horizontal e) := by
  intro l t hc
  rw [drawingCode_horizontal] at hc
  rcases List.append_eq_append_iff.mp hc with ⟨s, hl, hs⟩ | ⟨s, hs, ht⟩
  · obtain ⟨s',t',hec,hs',ht'⟩ := List.map_eq_append_iff.mp hs
    change PlanarCode.shift q.directions.length s' = s at hs'
    change PlanarCode.shift q.directions.length t' = t at ht'
    obtain ⟨m,f,g,hf,hg,hev⟩ := he s' t' hec
    refine ⟨q.tensor m, d.horizontal f, (drawingId q).horizontal g, ?_, ?_, ?_⟩
    · rw [drawingCode_horizontal, hf, hs', hl]
    · rw [drawingCode_horizontal, hg, ht']
      rfl
    · change d.interpret.eval.horizontal e.interpret.eval =
        (d.interpret.eval.horizontal f.interpret.eval).vertical
          ((Biset.Hom.id q.basis).horizontal g.interpret.eval)
      rw [Biset.Hom.horizontal_vertical, Biset.Hom.vertical_id, hev]
  · obtain ⟨m,f,g,hf,hg,hdv⟩ := hd l s hs
    refine ⟨m.tensor p', f.horizontal (drawingId p'), g.horizontal e, ?_, ?_, ?_⟩
    · rw [drawingCode_horizontal, hf]
      exact List.append_nil _
    · rw [drawingCode_horizontal, hg, ht]
    · change d.interpret.eval.horizontal e.interpret.eval =
        (f.interpret.eval.horizontal (Biset.Hom.id p'.basis)).vertical
          (g.interpret.eval.horizontal e.interpret.eval)
      rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical, hdv]

private theorem factor_congr {p q : Word A B} {d e : LabelledDrawing Complex p q}
    (hc : drawingCode d = drawingCode e) (hv : d.interpret.eval = e.interpret.eval)
    (he : Factorable e) : Factorable d := by
  intro l r h
  obtain ⟨m,f,g,hf,hg,hev⟩ := he l r (hc.symm.trans h)
  exact ⟨m,f,g,hf,hg,hv.trans hev⟩

private def isCompactCrossing : PlanarEvent → Prop
  | .vertex _ .mixedProjection | .vertex _ .parallelUp => True
  | _ => False

private def goodCode (c : PlanarCode.Code) : Prop :=
  ∀ e ∈ c, isCompactCrossing e

private theorem good_left {l r : PlanarCode.Code} (h : goodCode (l ++ r)) :
    goodCode l := fun e he => h e (List.mem_append_left _ he)

private theorem good_right {l r : PlanarCode.Code} (h : goodCode (l ++ r)) :
    goodCode r := fun e he => h e (List.mem_append_right _ he)

private theorem good_unshift {n : Nat} {c : PlanarCode.Code}
    (h : goodCode (PlanarCode.shift n c)) : goodCode c := by
  intro e he
  have hp := h (e.place (n + e.position)) (List.mem_map_of_mem he)
  cases e with
  | vertex _ k =>
    cases k <;> try exact hp
  | _ => exact hp

private theorem factor_ordinary {p q : Word A B} (d : Diagram Complex p q)
    (h : goodCode (drawingCode (.ordinary d))) : Factorable (.ordinary d) := by
  induction d with
  | vertical d e hd he =>
    change goodCode (code (d.vertical e).drawing) at h
    rw [diagram_code_vert] at h
    refine factor_congr (d := .ordinary (d.vertical e))
      (e := (LabelledDrawing.ordinary d).vertical (.ordinary e)) ?_ rfl
      (factor_vertical (hd (good_left h)) (he (good_right h)))
    exact (diagram_code_vert d e).trans (drawing_code_vert (.ordinary d) (.ordinary e)).symm
  | horizontal d e hd he =>
    change goodCode (code (d.horizontal e).drawing) at h
    rw [diagram_code_horiz] at h
    refine factor_congr (d := .ordinary (d.horizontal e))
      (e := (LabelledDrawing.ordinary d).horizontal (.ordinary e)) ?_ rfl
      (factor_horizontal (hd (good_left h)) (he (good_unshift (good_right h))))
    exact (diagram_code_horiz d e).trans (drawing_code_horiz (.ordinary d) (.ordinary e)).symm
  | zero p q =>
    exact False.elim (h (.zero 0 p.directions q.directions) List.mem_cons_self)
  | add d e _ _ =>
    let s := d.drawing.geometry
    exact False.elim (h (.add 0 s.inputs s.outputs (PlanarCode.encode s)
      (code e.drawing)) List.mem_cons_self)
  | scale _ d _ =>
    let s := d.drawing.geometry
    exact False.elim (h (.scale 0 s.inputs s.outputs (PlanarCode.encode s)) List.mem_cons_self)
  | _ => exact factor_atom _ (by first | exact Nat.le_refl 1 | exact Nat.zero_le 1)

private theorem no_parallelUpChain (n : Nat) :
    ¬ goodCode (code (.vertex (.parallelUpChain n))) := by
  intro h
  change goodCode (PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack
    ((DrawingShape.upwardDots n).stack (.vertex .splitUp)))) at h
  rw [encode_stack, encode_stack] at h
  exact (good_right (good_right h)) (.vertex 0 (.trivalent .splitUp)) List.mem_cons_self

private theorem no_parallelDownChain (n : Nat) :
    ¬ goodCode (code (.vertex (.parallelDownChain n))) := by
  intro h
  change goodCode (PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack
    ((DrawingShape.downwardDots n).stack (.vertex .splitDown)))) at h
  rw [encode_stack] at h
  exact (good_left h) (.vertex 0 (.trivalent .mergeDown)) List.mem_cons_self

private theorem no_expandedProjection (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    ¬ goodCode (PlanarCode.encode (DrawingShape.expandedProjectionGeometry n o c)) := by
  intro h
  unfold DrawingShape.expandedProjectionGeometry at h
  rw [encode_stack] at h
  have hs := good_left h
  cases o
  · exact hs (.vertex 1 (.trivalent .upToUpDown)) List.mem_cons_self
  · exact hs (.vertex 2 .reverseCup) List.mem_cons_self

private theorem factor_drawing {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : goodCode (drawingCode d)) : Factorable d := by
  induction d with
  | ordinary d => exact factor_ordinary d h
  | vertical d e hd he =>
    rw [drawingCode_vertical] at h
    exact factor_vertical (hd (good_left h)) (he (good_right h))
  | horizontal d e hd he =>
    rw [drawingCode_horizontal] at h
    exact factor_horizontal (hd (good_left h)) (he (good_unshift (good_right h)))
  | parallelUpChain _ _ _ _ labels => exact False.elim (no_parallelUpChain labels.length h)
  | parallelDownChain _ _ _ _ labels => exact False.elim (no_parallelDownChain labels.length h)
  | expandedProjection _ _ _ _ _ o c => exact False.elim (no_expandedProjection 1 o c h)
  | expandedProjectionChain _ _ _ _ labels _ o c =>
    exact False.elim (no_expandedProjection labels.length o c h)
  | expandedLinearDotProjection _ _ _ _ labels _ o c =>
    exact False.elim (no_expandedProjection labels.length o c h)
  | rightCurlUp =>
    exact False.elim (h (.vertex 0 (.trivalent .upToUpDown)) List.mem_cons_self)
  | add d e _ _ =>
    let s := d.erase.geometry
    exact False.elim (h (.add 0 s.inputs s.outputs (PlanarCode.encode s)
      (drawingCode e)) List.mem_cons_self)
  | scale _ d _ =>
    let s := d.erase.geometry
    exact False.elim (h (.scale 0 s.inputs s.outputs (PlanarCode.encode s)) List.mem_cons_self)
  | trivalent v => cases v <;> exact factor_atom _ (Nat.le_refl 1)
  | bentVertex v => cases v <;> exact factor_atom _ (Nat.le_refl 1)
  | _ => exact factor_atom _ (Nat.le_refl 1)


/-- Split the exact left code into the three typed crossing stages.
Use the cut proof from the registered DotSlidePreorderNotSymmetric, replacing
its admitted event kinds by the two compact crossing kinds of Example 6.3. -/
theorem factor_left {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : PlanarCode.encode d.erase.geometry =
      [.vertex 0 .mixedProjection, .vertex 1 .mixedProjection, .vertex 0 .parallelUp]) :
    ∃ (m n : Word A B) (d₁ : LabelledDrawing Complex p m)
      (d₂ : LabelledDrawing Complex m n) (d₃ : LabelledDrawing Complex n q),
      PlanarCode.encode d₁.erase.geometry = [.vertex 0 .mixedProjection] ∧
      PlanarCode.encode d₂.erase.geometry = [.vertex 1 .mixedProjection] ∧
      PlanarCode.encode d₃.erase.geometry = [.vertex 0 .parallelUp] ∧
      d.interpret.eval = d₁.interpret.eval.vertical
        (d₂.interpret.eval.vertical d₃.interpret.eval) := by
  let a : PlanarEvent := .vertex 0 .mixedProjection
  let b : PlanarEvent := .vertex 1 .mixedProjection
  let c : PlanarEvent := .vertex 0 .parallelUp
  change drawingCode d = [a,b,c] at h
  have hg : goodCode (drawingCode d) := by
    rw [h]
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> trivial
  obtain ⟨m,d₁,tail,h₁,ht,he⟩ := factor_drawing d hg [a] [b,c] h
  have htgood : goodCode (drawingCode tail) := by
    rw [ht]
    intro e hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> trivial
  obtain ⟨n,d₂,d₃,h₂,h₃,he'⟩ := factor_drawing tail htgood [b] [c] ht
  exact ⟨m,n,d₁,d₂,d₃,h₁,h₂,h₃,he.trans (congrArg (d₁.interpret.eval.vertical ·) he')⟩

end CaseTwoFactor

#print axioms CaseTwoAudit.cup_indices
#print axioms CaseTwoAudit.intersect_calc
#print axioms CaseTwoAudit.unbounded_line_fiber
#print axioms CaseTwoAudit.checked_leftCode
#print axioms CaseTwoAudit.left_transfer
#print axioms CaseTwoAudit.transfer_probe
