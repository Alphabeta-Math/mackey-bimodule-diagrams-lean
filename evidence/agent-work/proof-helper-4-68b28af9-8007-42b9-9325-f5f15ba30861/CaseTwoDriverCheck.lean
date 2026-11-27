import Mathlib.GroupTheory.SemidirectProduct
import MackeyDiagrams
import Proofs.EvaluationForTwoProjections
import Proofs.CaseTwoLeftProjectionConstruction


set_option maxHeartbeats 2000000
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

/- Coefficient lemmas adapted from Proofs/EvaluationForTwoProjections.lean.
   These local declarations use the public MackeyDiagrams generators and dot APIs. -/
namespace CaseTwoCoefficient

open MackeyDiagrams
open scoped BigOperators

universe u
noncomputable section
set_option maxHeartbeats 1500000

private abbrev Vec (X : Type*) := X →₀ Complex

-- A contravariant basis map acts by precomposition on coefficients.
private def Pulls {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X) : Prop :=
  ∀ v, L v y = v x

private theorem pulls_single {X Y : Type*} (L : Vec X →ₗ[Complex] Vec Y) (y : Y) (x : X)
    (h : ∀ i : X, L (Finsupp.single i 1) y = Finsupp.single i (1 : Complex) x) :
    Pulls L y x := by
  let l := (Finsupp.lapply y : Vec Y →ₗ[Complex] Complex).comp L
  have he : l = (Finsupp.lapply x : Vec X →ₗ[Complex] Complex) := by
    apply Finsupp.lhom_ext
    intro i w
    have hs : Finsupp.single i w = w • Finsupp.single i (1 : Complex) := by
      simp [Finsupp.smul_single]
    rw [hs, map_smul, map_smul]
    exact congrArg (w • ·) (h i)
  exact fun v => LinearMap.congr_fun he v

private theorem pulls_of_single {X Y : Type*} {L : Vec X →ₗ[Complex] Vec Y}
    {forward : X → Y} {x : X} {y : Y} (inv : ∀ i, forward i = y ↔ i = x)
    (h : ∀ i : X, L (Finsupp.single i 1) = Finsupp.single (forward i) 1) :
    Pulls L y x := by
  classical
  apply pulls_single
  intro i
  rw [h i]
  simp only [Finsupp.single_apply, inv]

private theorem pulls_mixed {U : Type u} [Group U] {K H P L : Subgroup U}
    (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (d : ConjEmbedding L K) (e : ConjEmbedding L H)
    (p : ProjectionDot.Mixed a b d e)
    (y : ((Word.up d).tensor (.down e)).basis.carrier) :
    Pulls (Diagram.mixedProjection (R := Complex) a b d e p.dot p.finite).eval.toLinearMap
      y (Generator.mixedMultiplicationBasis a b d e p.dot y) := by
  classical
  apply pulls_single
  intro i
  change (Biset.Hom.transfer Complex (Generator.mixedMultiplicationBasis a b d e p.dot)
    (Generator.mixedMultiplication_equivariant a b d e p.dot) p.finite).toLinearMap
      (Finsupp.single i 1) y = _
  rw [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_apply, Finsupp.single_apply]
  by_cases h : i = Generator.mixedMultiplicationBasis a b d e p.dot y
  · simp [h]
  · simp [h, Ne.symm h]

section Balanced
variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {X X' : Biset K H} {Y Y' : Biset H J}

-- The unchanged strand makes the balancing parameter unique at a fixed output
-- representative. Thus no orbit multiplicity is introduced by tensoring a pullback.
private theorem pulls_horizontal_right (L : Biset.Hom Complex X X')
    (free : ∀ (s : Y.carrier) (h : H), Y.act (h, 1) s = s → h = 1)
    {x' : X'.carrier} {x : X.carrier} (hx : Pulls L.toLinearMap x' x) (s : Y.carrier) :
    Pulls (L.horizontal (Biset.Hom.id Y)).toLinearMap (X'.pair Y x' s) (X.pair Y x s) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨i,t⟩ => ?_)
  change (L.horizontal (Biset.Hom.id Y)).toLinearMap (Finsupp.single (X.pair Y i t) 1)
    (X'.pair Y x' s) = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
    (Finsupp.single t 1) (X'.pair Y x' s) = Finsupp.single (X.pair Y i t) 1 (X.pair Y x s)
  by_cases ht : ∃ h : H, Y.act (h, 1) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y i t = X.pair Y (X.act (1,h) i) s := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single s 1) (X'.pair Y x' s) = v x' := by
      apply pulls_single ((Biset.pairLinear Complex X' Y).flip (Finsupp.single s 1))
      intro j
      change Biset.pairLinear Complex X' Y (Finsupp.single j 1) (Finsupp.single s 1)
        (X'.pair Y x' s) = _
      rw [Biset.pairLinear_single, mul_one]
      have hi : X'.pair Y j s = X'.pair Y x' s ↔ j = x' := by
        constructor
        · intro hp
          obtain ⟨k, hk, hs⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (X'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    -- Rechoose the input representative before using the horizontal basis formula.
    have hre := congrArg (fun w => (L.horizontal (Biset.Hom.id Y)).toLinearMap
      (Finsupp.single w 1) (X'.pair Y x' s)) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single i 1))
      (Finsupp.single t 1) (X'.pair Y x' s) =
      Biset.pairLinear Complex X' Y (L.toLinearMap (Finsupp.single (X.act (1,h) i) 1))
      (Finsupp.single s 1) (X'.pair Y x' s) at hre
    rw [hre, heval, hx _ , he]
    have hi : X.pair Y (X.act (1,h) i) s = X.pair Y x s ↔ X.act (1,h) i = x := by
      constructor
      · intro hp
        obtain ⟨k, hk, hs⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (X.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec X'.carrier,
        Biset.pairLinear Complex X' Y v (Finsupp.single t 1) (X'.pair Y x' s) = 0 := by
      have he : (Finsupp.lapply (X'.pair Y x' s) : Vec (X'.tensor Y).carrier →ₗ[Complex] Complex).comp
          ((Biset.pairLinear Complex X' Y).flip (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X' Y (Finsupp.single j r) (Finsupp.single t 1)
          (X'.pair Y x' s) = 0
        rw [Biset.pairLinear_single, mul_one, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, _, hk⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, _, hk⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

private theorem pulls_horizontal_left (L : Biset.Hom Complex Y Y')
    (free : ∀ (s : X.carrier) (h : H), X.act (1, h) s = s → h = 1)
    {y' : Y'.carrier} {y : Y.carrier} (hy : Pulls L.toLinearMap y' y) (s : X.carrier) :
    Pulls ((Biset.Hom.id X).horizontal L).toLinearMap (X.pair Y' s y') (X.pair Y s y) := by
  classical
  apply pulls_single
  refine fun z => Quotient.inductionOn z (fun ⟨t,i⟩ => ?_)
  change ((Biset.Hom.id X).horizontal L).toLinearMap (Finsupp.single (X.pair Y t i) 1)
    (X.pair Y' s y') = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
    (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') = Finsupp.single (X.pair Y t i) 1 (X.pair Y s y)
  by_cases ht : ∃ h : H, X.act (1, h) t = s
  · obtain ⟨h, hh⟩ := ht
    have he : X.pair Y t i = X.pair Y s (Y.act (h,1) i) := by
      rw [← hh, Biset.pair_orbit]
    have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single s 1) v (X.pair Y' s y') = v y' := by
      apply pulls_single (Biset.pairLinear Complex X Y' (Finsupp.single s 1))
      intro j
      rw [Biset.pairLinear_single, one_mul]
      have hi : X.pair Y' s j = X.pair Y' s y' ↔ j = y' := by
        constructor
        · intro hp
          obtain ⟨k, hs, hk⟩ := Quotient.exact hp
          have hk1 := free s k hs
          subst k
          exact (Y'.one_act j).symm.trans hk
        · intro hp
          rw [hp]
      simp only [Finsupp.single_apply, hi]
    have hre := congrArg (fun w => ((Biset.Hom.id X).horizontal L).toLinearMap
      (Finsupp.single w 1) (X.pair Y' s y')) he
    rw [Biset.Hom.horizontal_single, one_smul, Biset.Hom.horizontal_single, one_smul] at hre
    change Biset.pairLinear Complex X Y' (Finsupp.single t 1)
      (L.toLinearMap (Finsupp.single i 1)) (X.pair Y' s y') =
      Biset.pairLinear Complex X Y' (Finsupp.single s 1)
      (L.toLinearMap (Finsupp.single (Y.act (h,1) i) 1)) (X.pair Y' s y') at hre
    rw [hre, heval, hy _ , he]
    have hi : X.pair Y s (Y.act (h,1) i) = X.pair Y s y ↔ Y.act (h,1) i = y := by
      constructor
      · intro hp
        obtain ⟨k, hs, hk⟩ := Quotient.exact hp
        have hk1 := free s k hs
        subst k
        exact (Y.one_act _).symm.trans hk
      · intro hp
        rw [hp]
    simp only [Finsupp.single_apply, hi]
  · have heval : ∀ v : Vec Y'.carrier,
        Biset.pairLinear Complex X Y' (Finsupp.single t 1) v (X.pair Y' s y') = 0 := by
      have he : (Finsupp.lapply (X.pair Y' s y') : Vec (X.tensor Y').carrier →ₗ[Complex] Complex).comp
          (Biset.pairLinear Complex X Y' (Finsupp.single t 1)) = 0 := by
        apply Finsupp.lhom_ext
        intro j r
        change Biset.pairLinear Complex X Y' (Finsupp.single t 1) (Finsupp.single j r)
          (X.pair Y' s y') = 0
        rw [Biset.pairLinear_single, one_mul, Finsupp.single_apply, ite_eq_right]
        intro hp
        obtain ⟨k, hk, _⟩ := Quotient.exact hp
        exact ht ⟨k, hk⟩
      exact fun v => LinearMap.congr_fun he v
    rw [heval, Finsupp.single_apply, ite_eq_right]
    intro hp
    obtain ⟨k, hk, _⟩ := Quotient.exact hp
    exact ht ⟨k, hk⟩

end Balanced

end
end CaseTwoCoefficient

namespace CaseTwoCoefficient
open MackeyDiagrams
open scoped BigOperators
universe u
noncomputable section
set_option maxHeartbeats 2000000

variable {U : Type u} [Group U]
variable {K H J L M : Subgroup U}

private abbrev ev {p q : Word K H} (d : LabelledDrawing Complex p q) := d.interpret.eval.toLinearMap

private abbrev drawId (p : Word K H) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private abbrev before {p q r : Word K H} (d : LabelledDrawing Complex p q)
    (e : LabelledDrawing Complex q r) := LabelledDrawing.vertical d e

private abbrev atLeft {p q : Word K H} (d : LabelledDrawing Complex p q)
    (r : Word H J) := LabelledDrawing.horizontal d (drawId r)

private abbrev atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :=
  before (.ordinary (.associate p q r))
    (before (.horizontal (drawId p) d) (.ordinary (.unassociate p q' r')))

private abbrev pair (p : Word K H) (q : Word H J) := p.basis.pair q.basis

private abbrev triple (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :=
  pair (p.tensor q) r (pair p q x y) z

private theorem pulls_before {p q r : Word K H}
    {d : LabelledDrawing Complex p q} {e : LabelledDrawing Complex q r}
    {z : r.basis.carrier} {y : q.basis.carrier} {x : p.basis.carrier}
    (he : Pulls (ev e) z y) (hd : Pulls (ev d) y x) : Pulls (ev (before d e)) z x := by
  intro v
  change ev e (ev d v) z = _
  rw [he _, hd _]

private theorem pulls_assoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.associate p q r))) (pair p (q.tensor r) x (pair q r y z))
      (triple p q r x y z) := by
  let i := Biset.associateBasisEquiv p.basis q.basis r.basis
  have hi : ∀ v : _, i v = i (triple p q r x y z) ↔ v = triple p q r x y z :=
    fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨xy,t⟩ => ?_)
  exact Quotient.inductionOn xy (fun ⟨s,w⟩ => Diagram.eval_associate_single p q r s w t 1)

private theorem pulls_unassoc (p : Word K H) (q : Word H J) (r : Word J L)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier) :
    Pulls (ev (.ordinary (.unassociate p q r))) (triple p q r x y z)
      (pair p (q.tensor r) x (pair q r y z)) := by
  let i := (Biset.associateBasisEquiv p.basis q.basis r.basis).symm
  have hi : ∀ v : _, i v = i (pair p (q.tensor r) x (pair q r y z)) ↔
      v = pair p (q.tensor r) x (pair q r y z) := fun _ => i.apply_eq_iff_eq
  apply pulls_of_single hi
  intro v
  refine Quotient.inductionOn v (fun ⟨s,yz⟩ => ?_)
  exact Quotient.inductionOn yz (fun ⟨w,t⟩ => Diagram.eval_unassociate_single p q r s w t 1)

private theorem pulls_atRight (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    {d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')}
    (free : ∀ (s : p.basis.carrier) (h : H), p.basis.act (1, h) s = s → h = 1)
    (s : p.basis.carrier) {x : q'.basis.carrier} {y : r'.basis.carrier}
    {x' : q.basis.carrier} {y' : r.basis.carrier}
    (hd : Pulls (ev d) (pair q' r' x y) (pair q r x' y')) :
    Pulls (ev (atRight p d)) (triple p q' r' s x y) (triple p q r s x' y') := by
  apply pulls_before (pulls_before (pulls_unassoc p q' r' s x y) ?_)
    (pulls_assoc p q r s x' y')
  exact pulls_horizontal_left d.interpret.eval free hd s

private theorem free_up_left (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.induction a).act (h, 1) s = s) : h = 1 := by
  change h * s * (a.toHom 1)⁻¹ = s at eq
  simpa using mul_right_cancel (show h * s = 1 * s by simpa using eq)

private theorem free_up_right (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.induction a).act (1, h) s = s) : h = 1 := by
  change 1 * s * (a.toHom h)⁻¹ = s at eq
  apply a.injective
  have he : (a.toHom h)⁻¹ = 1 :=
    mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_right (a : ConjEmbedding H K) (s : K) (h : K)
    (eq : (Biset.restriction a).act (1, h) s = s) : h = 1 := by
  change a.toHom 1 * s * h⁻¹ = s at eq
  have he : h⁻¹ = 1 := mul_left_cancel (a := s) (by simpa using eq)
  simpa using congrArg Inv.inv he

private theorem free_down_left (a : ConjEmbedding H K) (s : K) (h : H)
    (eq : (Biset.restriction a).act (h, 1) s = s) : h = 1 := by
  change a.toHom h * s * (1 : K)⁻¹ = s at eq
  apply a.injective
  exact mul_right_cancel (show a.toHom h * s = a.toHom 1 * s by simpa using eq)

private theorem up_balance (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    pair (Word.up a) (Word.up b) (x * a.toHom y) 1 = pair (Word.up a) (Word.up b) x y := by
  simpa [pair, Word.basis, Biset.induction] using
    (Biset.induction a).pair_balance (Biset.induction b) y x 1

private theorem pulls_merge (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) :
    Pulls (ev (.trivalent (.mergeUp a b))) x (pair (Word.up a) (Word.up b) x 1) := by
  have hi (w : ((Word.up a).tensor (.up b)).basis.carrier) (z : K) :
      Generator.mergeUpBasis a b w = z ↔ w = pair (Word.up a) (Word.up b) z 1 := by
    refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
    change s * a.toHom t = z ↔ pair (Word.up a) (Word.up b) s t = _
    constructor
    · rintro rfl
      exact (up_balance a b s t).symm
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom t = z * a.toHom 1 at eq
      simpa using eq
  apply pulls_of_single (fun w => hi w x)
  intro w
  refine Quotient.inductionOn w (fun ⟨s,t⟩ => ?_)
  exact Diagram.eval_mergeUp_single a b s t 1

private theorem pulls_split (a : ConjEmbedding H K) (b : ConjEmbedding J H) (x : K) (y : H) :
    Pulls (ev (.trivalent (.splitUp a b))) (pair (Word.up a) (Word.up b) x y) (x * a.toHom y) := by
  apply pulls_single
  intro s
  change (Diagram.splitUp (R := Complex) a b).eval.toLinearMap (Finsupp.single s 1)
    (pair (Word.up a) (Word.up b) x y) = _
  rw [Diagram.eval_splitUp_single]
  classical
  have hi : pair (Word.up a) (Word.up b) s 1 = pair (Word.up a) (Word.up b) x y ↔
      s = x * a.toHom y := by
    constructor
    · intro he
      have eq := congrArg (Generator.mergeUpBasis a b) he
      change s * a.toHom 1 = x * a.toHom y at eq
      simpa using eq
    · rintro rfl
      exact up_balance a b x y
  simp only [Finsupp.single_apply, hi]

private theorem sum_eval (p q : Word K H) (xs : List (Complex × Diagram Complex p q)) :
    (ScopedDiagram.linearCombination (xs.map fun (c,d) => (c, ScopedDiagram.ordinary d))).eval.toLinearMap =
      (xs.map fun (c,d) => c • d.eval.toLinearMap).sum := by
  apply LinearMap.ext
  intro v
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c,d⟩
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply]
    rw [ih]
    rfl

private theorem singleton_mixed (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d) :
    ev (.compactProjection a b c d [(1,p)]) =
      (Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem singleton_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) :
    ev (.parallelUp a b c d [(1,p)]) =
      (Diagram.parallelUp (R := Complex) a b c d p).eval.toLinearMap := by
  change (ScopedDiagram.linearCombination
    (([(1, Diagram.parallelUp (R := Complex) a b c d p)]).map
      fun (r,t) => (r, ScopedDiagram.ordinary t))).eval.toLinearMap = _
  rw [sum_eval]
  simp

private theorem pulls_compact (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (p : ProjectionDot.Mixed a b c d)
    (x : K) (y : J) :
    Pulls (ev (.compactProjection a b c d [(1,p)])) (pair (Word.up c) (Word.down d) x y)
      (Generator.mixedPair a b (a.toHom x * p.dot.element * b.toHom y)) := by
  rw [singleton_mixed]
  exact pulls_mixed a b c d p _

private theorem pulls_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (p : Dot (a.comp b) (c.comp d)) (x : K) (y : J) :
    Pulls (ev (.parallelUp a b c d [(1,p)])) (pair (Word.up c) (Word.up d) x y)
      (pair (Word.up a) (Word.up b) (x * c.toHom y * p.element⁻¹) 1) := by
  rw [singleton_parallel]
  intro v
  change ev (.trivalent (.splitUp c d))
    ((Diagram.upDot (R := Complex) p).eval.toLinearMap (ev (.trivalent (.mergeUp a b)) v))
    (pair (Word.up c) (Word.up d) x y) = _
  rw [pulls_split c d x y _]
  have he : Pulls (Diagram.upDot (R := Complex) p).eval.toLinearMap
      (x * c.toHom y) (x * c.toHom y * p.element⁻¹) := by
    refine pulls_of_single (forward := fun z : K => z * p.element)
      ?_ (fun z => Diagram.eval_upDot_single p z 1)
    intro s
    exact eq_mul_inv_iff_mul_eq.symm
  rw [he _, pulls_merge a b _ _]

end
end CaseTwoCoefficient

namespace CaseTwoCoefficient
open MackeyDiagrams
universe u
noncomputable section
set_option maxHeartbeats 2400000

variable {U : Type u} [Group U] {G A D F C E B B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A)
  (c : ConjEmbedding F D) (d : ConjEmbedding C G)
  (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev bottom := ((Word.down a).tensor (.up b)).tensor (.up c)
private abbrev top := ((Word.up d).tensor (.up e)).tensor (.down f)
private abbrev mergedBottom := (Word.down a).tensor (.up (b.comp c))
private abbrev mergedTop := (Word.up (d.comp e)).tensor (.down f)

private abbrev splitBottom : LabelledDrawing Complex (mergedBottom a b c) (bottom a b c) :=
  before (.horizontal (drawId (.down a)) (.trivalent (.splitUp b c)))
    (.ordinary (.unassociate (.down a) (.up b) (.up c)))

private abbrev mergeTop : LabelledDrawing Complex (top d e f) (mergedTop d e f) :=
  .horizontal (.trivalent (.mergeUp d e)) (drawId (.down f))

private abbrev mergedEval (drawing : LabelledDrawing Complex (bottom a b c) (top d e f)) :=
  ev (before (splitBottom a b c) (before drawing (mergeTop d e f)))

private abbrev leftDrawing (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B)
    (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × Dot (r.comp t) (d.comp e))) :=
  before (atLeft (.compactProjection a b r s xs) (.up c))
    (before (atRight (.up r) (.compactProjection s c t f ys))
      (atLeft (.parallelUp r t d e zs) (.down f)))

private abbrev rightDrawing (u' : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B')
    (ells : List (Complex × Dot (b.comp c) (u'.comp w)))
    (ms : List (Complex × ProjectionDot.Mixed a u' d v))
    (ns : List (Complex × ProjectionDot.Mixed v w e f)) :=
  before (atRight (.down a) (.parallelUp b c u' w ells))
    (before (atLeft (.compactProjection a u' d v ms) (.up w))
      (atRight (.up d) (.compactProjection v w e f ns)))

private theorem pulls_splitBottom (x y : A) (z : D) :
    Pulls (ev (splitBottom a b c)) (triple (.down a) (.up b) (.up c) x y z)
      (pair (.down a) (.up (b.comp c)) x (y * b.toHom z)) := by
  apply pulls_before (pulls_unassoc (.down a) (.up b) (.up c) x y z)
  exact pulls_horizontal_left (X := Biset.restriction a) (Diagram.splitUp (R := Complex) b c).eval (free_down_right a)
    (pulls_split b c y z) x

private theorem pulls_mergeTop (g : G) (h : F) :
    Pulls (ev (mergeTop d e f)) (pair (.up (d.comp e)) (.down f) g h)
      (triple (.up d) (.up e) (.down f) g 1 h) := by
  exact pulls_horizontal_right (Y := Biset.restriction f) (Diagram.mergeUp (R := Complex) d e).eval
    (free_down_left f) (pulls_merge d e g) h

private theorem mixedPair_coord {K H P : Subgroup U}
    (α : ConjEmbedding K P) (β : ConjEmbedding H P) (x y : P) :
    pair (.down α) (.up β) x y = Generator.mixedPair α β (x * y) := by
  apply (Generator.mixedEquiv α β).injective
  change x * y = Generator.mixedProduct α β (Generator.mixedPair α β (x * y))
  rw [Generator.mixedProduct_mixedPair]

private def leftDot {r : ConjEmbedding B G} {s : ConjEmbedding B D} {t : ConjEmbedding E B}
    (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) : Dot (a.comp (d.comp e)) ((b.comp c).comp f) where
  element := a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element
  intertwines := by
    intro j
    have hz := congrArg a.toHom (z.inverse.intertwines j)
    have hx := x.dot.intertwines (t.toHom j)
    have hy := congrArg b.toHom (y.dot.intertwines j)
    simp only [Dot.inverse, ConjEmbedding.comp_apply, map_mul] at hz hx hy
    simp only [ConjEmbedding.comp_apply]
    calc
      a.toHom (d.toHom (e.toHom j)) * (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element) =
          (a.toHom (d.toHom (e.toHom j)) * a.toHom z.element⁻¹) *
            x.dot.element * b.toHom y.dot.element := by simp only [mul_assoc]
      _ = (a.toHom z.element⁻¹ * a.toHom (r.toHom (t.toHom j))) *
            x.dot.element * b.toHom y.dot.element := by rw [hz]
      _ = a.toHom z.element⁻¹ * (a.toHom (r.toHom (t.toHom j)) * x.dot.element) *
            b.toHom y.dot.element := by simp only [mul_assoc]
      _ = a.toHom z.element⁻¹ * x.dot.element *
            (b.toHom (s.toHom (t.toHom j)) * b.toHom y.dot.element) := by rw [hx]; simp only [mul_assoc]
      _ = (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element) *
            b.toHom (c.toHom (f.toHom j)) := by rw [hy]; simp only [mul_assoc]

private def rightDot {u' : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'}
    (ell : Dot (b.comp c) (u'.comp w))
    (m : ProjectionDot.Mixed a u' d v) (n : ProjectionDot.Mixed v w e f) :
    Dot (a.comp (d.comp e)) ((b.comp c).comp f) where
  element := m.dot.element * u'.toHom n.dot.element * ell.element⁻¹
  intertwines := by
    intro j
    have hm := m.dot.intertwines (e.toHom j)
    have hn := congrArg u'.toHom (n.dot.intertwines j)
    have hl := ell.inverse.intertwines (f.toHom j)
    simp only [Dot.inverse, ConjEmbedding.comp_apply, map_mul] at hm hn hl
    simp only [ConjEmbedding.comp_apply]
    calc
      a.toHom (d.toHom (e.toHom j)) * (m.dot.element * u'.toHom n.dot.element * ell.element⁻¹) =
          (a.toHom (d.toHom (e.toHom j)) * m.dot.element) *
            u'.toHom n.dot.element * ell.element⁻¹ := by simp only [mul_assoc]
      _ = m.dot.element * (u'.toHom (v.toHom (e.toHom j)) * u'.toHom n.dot.element) *
            ell.element⁻¹ := by rw [hm]; simp only [mul_assoc]
      _ = m.dot.element * u'.toHom n.dot.element *
            (u'.toHom (w.toHom (f.toHom j)) * ell.element⁻¹) := by rw [hn]; simp only [mul_assoc]
      _ = (m.dot.element * u'.toHom n.dot.element * ell.element⁻¹) *
            b.toHom (c.toHom (f.toHom j)) := by rw [hl]; simp only [mul_assoc]

-- Lemma 6.3, left backward calculation. At each stage the linear coefficient
-- is evaluated at its unique backwards coordinate. The fixed strands act
-- freely at the balancing interfaces, so rebracketing retains the fiber sum.
private theorem pulls_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f (leftDot a b c d e f x y z)
        (pair (.up (d.comp e)) (.down f) g h)) := by
  let g' := g * z.element⁻¹
  let y' := y.dot.element * c.toHom h
  let x' := a.toHom g' * x.dot.element * b.toHom y'
  have step₃ : Pulls (ev (atLeft (.parallelUp r t d e [(1,z)]) (.down f)))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up r) (.up t) (.down f) g' 1 h) := by
    have hp := pulls_parallel r t d e z g 1
    simp only [map_one, mul_one] at hp
    exact pulls_horizontal_right (Y := Biset.restriction f) _ (free_down_left f) hp h
  have step₂ : Pulls (ev (atRight (.up r) (.compactProjection s c t f [(1,y)])))
      (triple (.up r) (.up t) (.down f) g' 1 h) (triple (.up r) (.down s) (.up c) g' y' 1) := by
    apply pulls_atRight (.up r) (free_up_right r) g'
    have hp := pulls_compact s c t f y 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₁ : Pulls (ev (atLeft (.compactProjection a b r s [(1,x)]) (.up c)))
      (triple (.up r) (.down s) (.up c) g' y' 1) (triple (.down a) (.up b) (.up c) x' 1 1) :=
    pulls_horizontal_right _ (free_up_left c) (pulls_compact a b r s x g' y') _
  have step₀ := pulls_splitBottom a b c x' 1 1
  simp only [map_one, mul_one] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * (leftDot a b c d e f x y z).element * (b.comp c).toHom h))
  have hc : x' = a.toHom g * (leftDot a b c d e f x y z).element * (b.comp c).toHom h := by
    simp only [x', g', y', leftDot, ConjEmbedding.comp_apply, map_mul, mul_assoc]
  rw [← hc]
  exact out

-- Lemma 6.3, right backward calculation. The parallel vertex contributes
-- right multiplication by ell⁻¹. Its reversed intertwining equation
-- moves that factor through the right boundary action.
private theorem pulls_right {u' : ConjEmbedding B' A} {v : ConjEmbedding C B'}
    {w : ConjEmbedding F B'} (ell : Dot (b.comp c) (u'.comp w))
    (m : ProjectionDot.Mixed a u' d v) (n : ProjectionDot.Mixed v w e f)
    (g : G) (h : F) :
    Pulls (mergedEval a b c d e f (rightDrawing a b c d e f u' v w [(1,ell)] [(1,m)] [(1,n)]))
      (pair (.up (d.comp e)) (.down f) g h)
      (Generator.mixedMultiplicationBasis a (b.comp c) (d.comp e) f (rightDot a b c d e f ell m n)
        (pair (.up (d.comp e)) (.down f) g h)) := by
  let n' := n.dot.element * w.toHom h
  let m' := a.toHom g * m.dot.element * u'.toHom n'
  have step₃ : Pulls (ev (atRight (.up d) (.compactProjection v w e f [(1,n)])))
      (triple (.up d) (.up e) (.down f) g 1 h) (triple (.up d) (.down v) (.up w) g n' 1) := by
    apply pulls_atRight (.up d) (free_up_right d) g
    have hp := pulls_compact v w e f n 1 h
    simp only [map_one, one_mul] at hp
    exact hp
  have step₂ : Pulls (ev (atLeft (.compactProjection a u' d v [(1,m)]) (.up w)))
      (triple (.up d) (.down v) (.up w) g n' 1) (triple (.down a) (.up u') (.up w) m' 1 1) :=
    pulls_horizontal_right _ (free_up_left w) (pulls_compact a u' d v m g n') _
  have step₁ : Pulls (ev (atRight (.down a) (.parallelUp b c u' w [(1,ell)])))
      (triple (.down a) (.up u') (.up w) m' 1 1)
      (triple (.down a) (.up b) (.up c) m' ell.element⁻¹ 1) := by
    apply pulls_atRight (.down a) (free_down_right a) m'
    simpa only [map_one, mul_one, one_mul] using pulls_parallel b c u' w ell 1 1
  have step₀ := pulls_splitBottom a b c m' ell.element⁻¹ 1
  simp only [map_one, mul_one] at step₀
  rw [mixedPair_coord a (b.comp c) m' ell.element⁻¹] at step₀
  have out := pulls_before (pulls_before (pulls_mergeTop d e f g h)
      (pulls_before (pulls_before step₃ step₂) step₁)) step₀
  change Pulls _ _ (Generator.mixedPair a (b.comp c)
    (a.toHom g * (rightDot a b c d e f ell m n).element * (b.comp c).toHom h))
  have hel := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at hel
  have hc : m' * ell.element⁻¹ =
      a.toHom g * (rightDot a b c d e f ell m n).element * (b.comp c).toHom h := by
    simp only [m', n', rightDot, ConjEmbedding.comp_apply, map_mul, mul_assoc, hel]
  rw [← hc]
  exact out

end
end CaseTwoCoefficient

namespace CaseTwoCoefficient
open MackeyDiagrams
universe u
noncomputable section
set_option maxHeartbeats 2400000

private def weighted {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (s : I → M) (xs : List (Complex × I)) : M :=
  (xs.map fun x => x.1 • s x.2).sum

private theorem map_weighted {I M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (L : M →ₗ[Complex] N) (s : I → M) (xs : List (Complex × I)) :
    L (weighted s xs) = weighted (fun i => L (s i)) xs := by
  unfold weighted
  rw [map_list_sum, List.map_map]
  simp only [Function.comp_def, map_smul]

private theorem weighted_mem {I M : Type*} [AddCommMonoid M] [Module Complex M]
    (S : Submodule Complex M) (s : I → M) (xs : List (Complex × I))
    (hs : ∀ i, s i ∈ S) : weighted s xs ∈ S := by
  unfold weighted
  apply list_sum_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact S.smul_mem t.1 (hs t.2)

private def preapply {M N : Type*} [AddCommMonoid M] [Module Complex M]
    [AddCommMonoid N] [Module Complex N] (x : M) : (M →ₗ[Complex] N) →ₗ[Complex] N where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def composeAround
    {M N P Q : Type*} [AddCommMonoid M] [Module Complex M] [AddCommMonoid N] [Module Complex N]
    [AddCommMonoid P] [Module Complex P] [AddCommMonoid Q] [Module Complex Q]
    (pre : M →ₗ[Complex] N) (post : P →ₗ[Complex] Q) :
    (N →ₗ[Complex] P) →ₗ[Complex] (M →ₗ[Complex] Q) where
  toFun f := post.comp (f.comp pre)
  map_add' g h := by
    change post.comp ((g + h).comp pre) = post.comp (g.comp pre) + post.comp (h.comp pre)
    rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r g := by
    change post.comp ((r • g).comp pre) = r • post.comp (g.comp pre)
    rw [LinearMap.smul_comp, LinearMap.comp_smul]

section WeightedCrossings
variable {U : Type u} [Group U] {K H J L M : Subgroup U}

private theorem weighted_compact (a : ConjEmbedding K H) (b : ConjEmbedding J H)
    (c : ConjEmbedding L K) (d : ConjEmbedding L J) (xs : List (Complex × ProjectionDot.Mixed a b c d)) :
    ev (.compactProjection a b c d xs) =
      weighted (fun p => ev (.compactProjection a b c d [(1,p)])) xs := by
  have hs := sum_eval ((Word.down a).tensor (.up b)) ((Word.up c).tensor (.down d))
    (xs.map fun t => (t.1, Diagram.mixedProjection (R := Complex) a b c d t.2.dot t.2.finite))
  simp only [List.map_map] at hs
  rw [show weighted (fun p => ev (.compactProjection a b c d [(1,p)])) xs =
      weighted (fun p => (Diagram.mixedProjection (R := Complex) a b c d p.dot p.finite).eval.toLinearMap)
        xs from congrArg (fun s => weighted s xs) (funext (singleton_mixed a b c d))]
  exact hs

private theorem weighted_parallel (a : ConjEmbedding H K) (b : ConjEmbedding L H)
    (c : ConjEmbedding J K) (d : ConjEmbedding L J) (xs : List (Complex × Dot (a.comp b) (c.comp d))) :
    ev (.parallelUp a b c d xs) =
      weighted (fun p => ev (.parallelUp a b c d [(1,p)])) xs := by
  have hs := sum_eval ((Word.up a).tensor (.up b)) ((Word.up c).tensor (.up d))
    (xs.map fun t => (t.1, Diagram.parallelUp (R := Complex) a b c d t.2))
  simp only [List.map_map] at hs
  rw [show weighted (fun p => ev (.parallelUp a b c d [(1,p)])) xs =
      weighted (fun p => (Diagram.parallelUp (R := Complex) a b c d p).eval.toLinearMap)
        xs from congrArg (fun s => weighted s xs) (funext (singleton_parallel a b c d))]
  exact hs

private theorem weighted_atLeft {I : Type*} {p q : Word K H} {r : Word H J}
    (S : LabelledDrawing Complex p q) (s : I → LabelledDrawing Complex p q) (xs : List (Complex × I))
    (he : ev S = weighted (fun i => ev (s i)) xs) :
    ev (atLeft S r) = weighted (fun i => ev (atLeft (s i) r)) xs := by
  apply Finsupp.lhom_ext
  intro w c
  refine Quotient.inductionOn w (fun ⟨x,y⟩ => ?_)
  let T := c • (((Biset.pairLinear Complex q.basis r.basis).flip
    (Finsupp.single y 1)).comp (preapply (Finsupp.single x (1 : Complex))))
  have col (d : LabelledDrawing Complex p q) :
      ev (atLeft d r) (Finsupp.single (pair p r x y) c) = T (ev d) := by
    exact Biset.Hom.horizontal_single d.interpret.eval (Biset.Hom.id r.basis) x y c
  change ev (atLeft S r) (Finsupp.single (pair p r x y) c) =
    preapply (Finsupp.single (pair p r x y) c) (weighted (fun i => ev (atLeft (s i) r)) xs)
  rw [col S, he, map_weighted T, map_weighted]
  exact congrArg (fun v => weighted v xs) (funext fun i => (col (s i)).symm)

private theorem weighted_atRight {I : Type*} (p : Word K H) {q : Word H J} {r : Word J L}
    {q' : Word H M} {r' : Word M L}
    (S : LabelledDrawing Complex (q.tensor r) (q'.tensor r'))
    (s : I → LabelledDrawing Complex (q.tensor r) (q'.tensor r')) (xs : List (Complex × I))
    (he : ev S = weighted (fun i => ev (s i)) xs) :
    ev (atRight p S) = weighted (fun i => ev (atRight p (s i))) xs := by
  let first := ev (.ordinary (.associate p q r))
  let last := ev (.ordinary (.unassociate p q' r'))
  let frame := composeAround first last
  have mid : ev (.horizontal (drawId p) S) =
      weighted (fun i => ev (.horizontal (drawId p) (s i))) xs := by
    apply Finsupp.lhom_ext
    intro w c
    refine Quotient.inductionOn w (fun ⟨x,y⟩ => ?_)
    let T := c • ((Biset.pairLinear Complex p.basis (q'.tensor r').basis
      (Finsupp.single x 1)).comp (preapply (Finsupp.single y (1 : Complex))))
    have col (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :
        ev (.horizontal (drawId p) d) (Finsupp.single (pair p (q.tensor r) x y) c) = T (ev d) := by
      exact Biset.Hom.horizontal_single (Biset.Hom.id p.basis) d.interpret.eval x y c
    change ev (.horizontal (drawId p) S) (Finsupp.single (pair p (q.tensor r) x y) c) =
      preapply (Finsupp.single (pair p (q.tensor r) x y) c)
        (weighted (fun i => ev (.horizontal (drawId p) (s i))) xs)
    rw [col S, he, map_weighted T, map_weighted]
    exact congrArg (fun v => weighted v xs) (funext fun i => (col (s i)).symm)
  have hframe (d : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :
      ev (atRight p d) = frame (ev (.horizontal (drawId p) d)) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hframe S, mid, map_weighted frame]
  exact congrArg (fun v => weighted v xs) (funext fun i => (hframe (s i)).symm)

end WeightedCrossings

-- Lemma 6.3, finite label expansion. Three applications of linearity group
-- the products of the weights in the range of the finitely supported
-- coefficient map. In particular an empty label contributes the zero map.
private theorem weighted_stack_mem {I J K M N P Q S T : Type*}
    [AddCommMonoid M] [Module Complex M] [AddCommMonoid N] [Module Complex N]
    [AddCommMonoid P] [Module Complex P] [AddCommMonoid Q] [Module Complex Q]
    [AddCommMonoid S] [Module Complex S] [AddCommMonoid T] [Module Complex T]
    (V : Submodule Complex (M →ₗ[Complex] T)) (pre : M →ₗ[Complex] N) (post : S →ₗ[Complex] T)
    (x : I → (N →ₗ[Complex] P)) (y : J → (P →ₗ[Complex] Q)) (z : K → (Q →ₗ[Complex] S))
    (xs : List (Complex × I)) (ys : List (Complex × J)) (zs : List (Complex × K))
    (h : ∀ i j k, post.comp ((z k).comp ((y j).comp ((x i).comp pre))) ∈ V) :
    post.comp ((weighted z zs).comp ((weighted y ys).comp ((weighted x xs).comp pre))) ∈ V := by
  let tail := post.comp ((weighted z zs).comp (weighted y ys))
  change composeAround pre tail (weighted x xs) ∈ V
  rw [map_weighted]
  apply weighted_mem
  intro i
  let head := (x i).comp pre
  let tail' := post.comp (weighted z zs)
  change composeAround head tail' (weighted y ys) ∈ V
  rw [map_weighted]
  apply weighted_mem
  intro j
  change composeAround ((y j).comp head) post (weighted z zs) ∈ V
  rw [map_weighted]
  apply weighted_mem
  intro k
  exact h i j k
end
end CaseTwoCoefficient

namespace CaseTwoAudit
set_option maxHeartbeats 2500000
open MackeyDiagrams
open CaseTwoCoefficient (rightDot pulls_right pulls_mixed rightDrawing ev atLeft before
  weighted weighted_compact weighted_atLeft map_weighted composeAround)

private theorem singletonTermsRight {X : Type} (x : X) :
    terms (Finsupp.single x (1 : Complex)) = [((1 : Complex), x)] := by
  classical
  have hs := Finsupp.support_single x (one_ne_zero : (1 : Complex) ≠ 0)
  unfold terms
  rw [hs]
  simp

private theorem right_unit (q : A) :
    eval (rightDrawing a b c d e f u v w [(1,first)] [(1,mid q)] [(1,last)]) =
      Qstar (overall q) := by
  classical
  apply LinearMap.ext
  intro vec
  apply Finsupp.ext
  intro i
  refine Quotient.inductionOn i (fun ⟨g,h⟩ => ?_)
  have he : rightDot a b c d e f first (mid q) last = (overall q).dot := by
    apply Dot.ext
    change q * u.toHom 1 * (1 : A)⁻¹ = q
    rw [map_one, inv_one, mul_one, mul_one]
  have hp := pulls_right a b c d e f first (mid q) last g h
  rw [he] at hp
  exact (hp vec).trans ((pulls_mixed a bc de f (overall q) _ vec).symm)

noncomputable abbrev rhs :=
  right (Finsupp.single first 1) (Finsupp.single (mid 1) 1 + Finsupp.single (mid τ) 1)
    (Finsupp.single last 1)

theorem right_sum : eval rhs = Qstar (overall 1) + Qstar (overall τ) := by
  classical
  let S := Finsupp.single (mid 1) (1 : Complex) + Finsupp.single (mid τ) 1
  let stage (x : ProjectionLabel a u d v) :=
    atLeft (LabelledDrawing.compactProjection a u d v [(1,x)]) (up w)
  let D := atLeft (LabelledDrawing.compactProjection a u d v (terms S)) (up w)
  have hD : ev D = weighted (fun x => ev (stage x)) (terms S) :=
    weighted_atLeft _ _ _ (weighted_compact a u d v (terms S))
  have hpre : DotLabel.terms (Finsupp.single first (1 : Complex)) = [(1,first)] :=
    singletonTermsRight first
  have hlast := singletonTermsRight last
  have h0 : eval rhs = eval (rightDrawing a b c d e f u v w [(1,first)] (terms S) [(1,last)]) := by
    change eval (right (Finsupp.single first 1) S (Finsupp.single last 1)) = _
    unfold right
    rw [hpre, hlast]
  rw [h0]
  let pre := (ev (atRight (down a) (LabelledDrawing.parallelUp b c u w [(1,first)]))).comp
    (ev splitBottom)
  let post := (ev mergeTop).comp
    (ev (atRight (up d) (LabelledDrawing.compactProjection v w e f [(1,last)])))
  let frame := composeAround pre post
  change frame (ev D) = _
  rw [hD, map_weighted]
  have hs (x : ProjectionLabel a u d v) :
      frame (ev (stage x)) = eval (rightDrawing a b c d e f u v w [(1,first)] [(1,x)] [(1,last)]) := rfl
  simp only [hs]
  have as_sum {I M : Type} [AddCommMonoid M] [Module Complex M]
      (f : I → M) (l : I →₀ Complex) :
      weighted f (terms l) = l.sum (fun i c => c • f i) := by
    unfold weighted terms Finsupp.sum
    rw [List.map_map, Finset.sum_map_toList]
    rfl
  rw [as_sum]
  rw [← Finsupp.linearCombination_apply Complex]
  dsimp only [S]
  rw [map_add, Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  simp only [one_smul, right_unit]

end CaseTwoAudit

namespace CaseTwoAudit
open MackeyDiagrams
open CaseTwoCoefficient (leftDot pulls_left leftDrawing ev atLeft
  weighted weighted_compact weighted_parallel weighted_atLeft weighted_atRight weighted_stack_mem preapply)

private abbrev EvalMap :=
  ((Word.basis mergedBottom).carrier →₀ Complex) →ₗ[Complex]
    ((Word.basis mergedTop).carrier →₀ Complex)

private noncomputable abbrev probe (q : A) : EvalMap →ₗ[Complex] Complex :=
  (Finsupp.lapply unitOut).comp (preapply (basisVector q))

private theorem atom_zero {B : Subgroup U}
    {r : ConjEmbedding B G} {s : ConjEmbedding B D} {t : ConjEmbedding T B}
    (x : ProjectionLabel a b r s) (y : ProjectionLabel s c t f)
    (z : Dot (comp r t) de) (q : A)
    (hq : q ∉ DoubleCoset.doubleCoset x.dot.element (line : Set A) (line : Set A)) :
    probe q (eval (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)])) = 0 := by
  classical
  have hp := pulls_left a b c d e f x y z (1 : G) (1 : F) (basisVector q)
  have hne : q ≠ a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element := by
    intro he
    exact hq (DoubleCoset.mem_doubleCoset.mpr
      ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, he⟩)
  change probe q (eval (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)])) =
    basisVector q (Generator.mixedPair a bc (a.toHom 1 * (leftDot a b c d e f x y z).element * bc.toHom 1)) at hp
  rw [hp, map_one, map_one, one_mul, mul_one]
  change Finsupp.single (Generator.mixedPair a bc q) (1 : Complex)
    (Generator.mixedPair a bc (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element)) = _
  have hne' : Generator.mixedPair a bc q ≠
      Generator.mixedPair a bc (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element) :=
    fun eq => hne ((Generator.mixedEquiv a bc).symm.injective eq)
  rw [Finsupp.single_apply, ite_eq_right hne']

theorem canonical_zero {B : Subgroup U}
    (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding T B)
    (xs : Finsupp (ProjectionLabel a b r s) Complex)
    (ys : Finsupp (ProjectionLabel s c t f) Complex)
    (zs : DotLabel Complex (comp r t) de) (q : A)
    (hq : ∀ x ∈ xs.support, q ∉ DoubleCoset.doubleCoset x.dot.element (line : Set A) (line : Set A)) :
    probe q (eval (left r s t xs ys zs)) = 0 := by
  classical
  let S := {x // x ∈ xs.support}
  let xs' : List (Complex × S) := xs.support.attach.toList.map (fun x => (xs x.val, x))
  let X (x : ProjectionLabel a b r s) :=
    atLeft (LabelledDrawing.compactProjection a b r s [(1,x)]) (up c)
  let Y (y : ProjectionLabel s c t f) :=
    atRight (up r) (LabelledDrawing.compactProjection s c t f [(1,y)])
  let Z (z : Dot (comp r t) de) :=
    atLeft (LabelledDrawing.parallelUp r t d e [(1,z)]) (down f)
  let Xsum := atLeft (LabelledDrawing.compactProjection a b r s (terms xs)) (up c)
  let Ysum := atRight (up r) (LabelledDrawing.compactProjection s c t f (terms ys))
  let Zsum := atLeft (LabelledDrawing.parallelUp r t d e (DotLabel.terms zs)) (down f)
  have hx : ev Xsum = weighted (fun x => ev (X x)) (terms xs) :=
    weighted_atLeft _ _ _ (weighted_compact a b r s (terms xs))
  have hy : ev Ysum = weighted (fun y => ev (Y y)) (terms ys) :=
    weighted_atRight _ _ _ _ (weighted_compact s c t f (terms ys))
  have hz : ev Zsum = weighted (fun z => ev (Z z)) (DotLabel.terms zs) :=
    weighted_atLeft _ _ _ (weighted_parallel r t d e (DotLabel.terms zs))
  have hx' : ev Xsum = weighted (fun x : S => ev (X x.val)) xs' := by
    rw [hx]
    unfold weighted xs' terms
    simp only [List.map_map, Function.comp_def]
    rw [Finset.sum_map_toList, Finset.sum_map_toList]
    exact (Finset.sum_attach xs.support (fun x => xs x • ev (X x))).symm
  change (ev mergeTop).comp ((ev Zsum).comp ((ev Ysum).comp ((ev Xsum).comp (ev splitBottom)))) ∈
    LinearMap.ker (probe q)
  rw [hx', hy, hz]
  refine weighted_stack_mem _ _ _ _ _ _ xs' (terms ys) (DotLabel.terms zs) ?_
  intro x y z
  exact atom_zero x.val y z q (hq x.val x.property)

end CaseTwoAudit

namespace CaseTwoAudit
open MackeyDiagrams

theorem elem_nontrivial : (τ : A) ≠ 1 := by
  intro h
  have he := congrArg (fun x : A => x.val.right) h
  exact (by decide : swap ≠ 1) he

theorem rhs_probe_one : eval rhs (basisVector 1) unitOut = 1 := by
  classical
  rw [right_sum, LinearMap.add_apply, Finsupp.add_apply, transfer_probe, transfer_probe]
  simp only [ite_true, ite_eq_right elem_nontrivial, add_zero]

theorem rhs_probe_swap : eval rhs (basisVector τ) unitOut = 1 := by
  classical
  rw [right_sum, LinearMap.add_apply, Finsupp.add_apply, transfer_probe, transfer_probe]
  simp only [ite_true, ite_eq_right (Ne.symm elem_nontrivial), zero_add]

theorem eval_add (x y : Drawing) : eval (LabelledDrawing.add x y) = eval x + eval y := by
  ext v out
  change (mergeTop.interpret.eval.toLinearMap
    ((x.interpret.eval.toLinearMap + y.interpret.eval.toLinearMap)
      (splitBottom.interpret.eval.toLinearMap (Finsupp.single v 1)))) out = _
  simp only [LinearMap.add_apply, map_add, Finsupp.add_apply]
  rfl

private theorem eval_zero :
    eval (LabelledDrawing.ordinary (Diagram.zero bottom top)) = 0 := by
  ext v out
  change (mergeTop.interpret.eval.toLinearMap (0 : Finsupp _ Complex)) out = _
  simp

private theorem member_swap_coset_reverse {x z : A}
    (h : z ∈ DoubleCoset.doubleCoset x (line : Set A) (line : Set A)) :
    x ∈ DoubleCoset.doubleCoset z (line : Set A) (line : Set A) := by
  obtain ⟨l,hl,r,hr,he⟩ := DoubleCoset.mem_doubleCoset.mp h
  apply DoubleCoset.mem_doubleCoset.mpr
  exact ⟨l⁻¹, line.inv_mem hl, r⁻¹, line.inv_mem hr, by rw [he]; group⟩

private theorem sum_drawings_zero_at (drawings : List Drawing) (q : A)
    (hall : ∀ x ∈ drawings, eval x (basisVector q) unitOut = 0) :
    eval (sumDrawings drawings) (basisVector q) unitOut = 0 := by
  have fold_zero (ds : List Drawing) :
      ∀ (s : Drawing), eval s (basisVector q) unitOut = 0 →
        (∀ x ∈ ds, eval x (basisVector q) unitOut = 0) →
        eval (ds.foldl LabelledDrawing.add s) (basisVector q) unitOut = 0 := by
    induction ds with
    | nil => exact fun _ h _ => h
    | cons d rest ih =>
      intro s hs h
      apply ih
      · rw [eval_add, LinearMap.add_apply, Finsupp.add_apply, hs, h d List.mem_cons_self, add_zero]
      · exact fun x hx => h x (List.mem_cons_of_mem d hx)
  cases drawings with
  | nil =>
    change eval (LabelledDrawing.ordinary (Diagram.zero bottom top)) (basisVector q) unitOut = _
    rw [eval_zero]
    rfl
  | cons d ds =>
    exact fold_zero ds d (hall d List.mem_cons_self) (fun x hx => hall x (List.mem_cons_of_mem d hx))

end CaseTwoAudit

namespace CaseTwoAudit
open MackeyDiagrams

private theorem candidate_zero (allowed : Set A) (drawing : Drawing)
    (hd : IsLeftWith allowed drawing) (q : A)
    (hq : ∀ x ∈ allowed, x ∉ DoubleCoset.doubleCoset q (line : Set A) (line : Set A)) :
    eval drawing (basisVector q) unitOut = 0 := by
  obtain ⟨_, r, s, t, xs, ys, zs, ha, rfl⟩ := hd
  exact canonical_zero r s t xs ys zs q (fun x hx hh =>
    hq x.dot.element (ha x hx) (member_swap_coset_reverse hh))

theorem allowed_crossings (allowed : Set A) (drawings : List Drawing)
    (hd : ∀ drawing ∈ drawings, IsLeftWith allowed drawing)
    (he : eval (sumDrawings drawings) = eval rhs) :
    (∃ x ∈ allowed, x ∈ line) ∧ (∃ x ∈ allowed, x ∈ swapCoset) := by
  constructor
  · by_contra! h
    have hz := sum_drawings_zero_at drawings 1 (fun d hd' =>
      candidate_zero allowed d (hd d hd') 1 (by
        rw [subset_self_coset 1 line.one_mem]
        exact h))
    rw [he, rhs_probe_one] at hz
    exact one_ne_zero hz
  · by_contra! h
    have hz := sum_drawings_zero_at drawings τ (fun d hd' =>
      candidate_zero allowed d (hd d hd') τ h)
    rw [he, rhs_probe_swap] at hz
    exact one_ne_zero hz

theorem two_left_drawings :
    ∃ l₁ lτ, IsLeftWith (line : Set A) l₁ ∧ IsLeftWith swapCoset lτ ∧
      eval l₁ = Qstar (overall 1) ∧ eval lτ = Qstar (overall τ) ∧
      eval (MackeyDiagrams.LabelledDrawing.add l₁ lτ) = eval rhs := by
  obtain ⟨l₁, h₁, hval₁⟩ := left_transfer (overall 1) line line.one_mem
  obtain ⟨lτ, hτ, hvalτ⟩ := left_transfer (overall τ) swapCoset
    (DoubleCoset.mem_doubleCoset_self line line τ)
  exact ⟨l₁,lτ,h₁,hτ,hval₁,hvalτ,by rw [eval_add, hval₁, hvalτ, right_sum]⟩

theorem canonical_ne {B : Subgroup U}
    (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding T B)
    (xs : Finsupp (ProjectionLabel a b r s) Complex)
    (ys : Finsupp (ProjectionLabel s c t f) Complex)
    (zs : DotLabel Complex (comp r t) de) :
    eval (left r s t xs ys zs) ≠ eval rhs := by
  intro he
  let allowed := {q : A | ∃ x ∈ xs.support, (x : ProjectionLabel a b r s).dot.element = q}
  have ha : IsLeftWith allowed (left r s t xs ys zs) :=
    ⟨B, r,s,t,xs,ys,zs,fun x hx => ⟨x,hx,rfl⟩,rfl⟩
  have hh := allowed_crossings allowed [left r s t xs ys zs] (by simpa) he
  obtain ⟨_, ⟨x, _, rfl⟩, hx⟩ := hh.1
  obtain ⟨_, ⟨y, _, rfl⟩, hy⟩ := hh.2
  exact parameters_incompatible r s x y hx hy

end CaseTwoAudit

noncomputable def CaseTwoReviewedType : Prop :=
  let swap : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
  let action : Multiplicative (ZMod 2) →* MulAut (Multiplicative Int × Multiplicative Int) :=
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
  let U := SemidirectProduct (Multiplicative Int × Multiplicative Int) (Multiplicative (ZMod 2)) action
  let A : Subgroup U := ⊤
  let G : Subgroup U := MonoidHom.range (MonoidHom.comp
    (SemidirectProduct.inl (φ := action))
    (MonoidHom.inl (Multiplicative Int) (Multiplicative Int)))
  let D := G
  let T : Subgroup U := ⊥
  let C := T
  let E := T
  let F := T
  let B' := T
  let τ : A := ⟨SemidirectProduct.inr (φ := action) swap, Subgroup.mem_top _⟩
  let incl := fun {H K : Subgroup U} (h : H ≤ K) =>
    ({ toHom := Subgroup.inclusion h
       hasRepresentative := ⟨1, fun _ => by simp⟩ } : MackeyDiagrams.ConjEmbedding H K)
  let a : MackeyDiagrams.ConjEmbedding G A := incl le_top
  let b : MackeyDiagrams.ConjEmbedding D A := incl le_top
  let c : MackeyDiagrams.ConjEmbedding F D := incl bot_le
  let d : MackeyDiagrams.ConjEmbedding C G := incl bot_le
  let e : MackeyDiagrams.ConjEmbedding E C := incl le_rfl
  let f : MackeyDiagrams.ConjEmbedding E F := incl le_rfl
  let u : MackeyDiagrams.ConjEmbedding B' A := incl bot_le
  let v : MackeyDiagrams.ConjEmbedding C B' := incl le_rfl
  let w : MackeyDiagrams.ConjEmbedding F B' := incl le_rfl
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let bc := comp b c
  let de := comp d e
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let bottom := tensor (tensor (down a) (up b)) (up c)
  let top := tensor (tensor (up d) (up e)) (down f)
  let mergedBottom := tensor (down a) (up bc)
  let mergedTop := tensor (up de) (down f)
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
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
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
  let terms := fun {X : Type} (label : Finsupp X Complex) =>
    List.map (fun x => (label x, x)) (Finset.toList (Finsupp.support label))
  let Qstar := fun (p : ProjectionLabel a bc de f) =>
    MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval
      (MackeyDiagrams.Diagram.mixedProjection (R := Complex) a bc de f
        (MackeyDiagrams.ProjectionDot.dot p) (MackeyDiagrams.ProjectionDot.finite p)))
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
  let right := fun
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
  let Drawing := MackeyDiagrams.LabelledDrawing Complex bottom top
  let IsLeftWith := fun (allowed : Set A) (drawing : Drawing) =>
    ∃ (B : Subgroup U) (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : Finsupp (ProjectionLabel a b r s) Complex)
      (ys : Finsupp (ProjectionLabel s c t f) Complex)
      (zs : MackeyDiagrams.DotLabel Complex (comp r t) de),
      (∀ x ∈ Finsupp.support xs,
        MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot x) ∈ allowed) ∧
      drawing = left r s t xs ys zs
  let leftShape := MackeyDiagrams.LabelledDrawing.planarShape
    (left (B := T) d (incl bot_le) (incl le_rfl) 0 0 0)
  let sumDrawings := fun (drawings : List Drawing) =>
    match drawings with
    | [] => MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.zero bottom top)
    | first :: rest => List.foldl MackeyDiagrams.LabelledDrawing.add first rest
  let basisVector := fun p : A =>
    Finsupp.single (MackeyDiagrams.Generator.mixedPair a bc p) (1 : Complex)
  let line := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)
  let swapCoset := DoubleCoset.doubleCoset τ (line : Set A) (line : Set A)
  let intersection := fun x : A => line ⊓
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) line
  Subgroup.index (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom v)) = 1 ∧
  Subgroup.index (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom f)) = 1 ∧
  (∀ x : A, (x ∈ line → intersection x = line) ∧
    (x ∈ swapCoset → intersection x = ⊥)) ∧
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D)
      (x : MackeyDiagrams.Dot (comp a r) (comp b s)),
      MackeyDiagrams.Dot.element x ∈ swapCoset →
      B = ⊥ ∧ ∀ y : MackeyDiagrams.Dot (comp a r) (comp b s),
        MackeyDiagrams.Dot.element y ∈ line →
        ¬ Set.Finite {j | MackeyDiagrams.Generator.mixedMultiplicationBasis a b r s y j =
          MackeyDiagrams.Generator.mixedPair a b (MackeyDiagrams.Dot.element y)}) ∧
  ∃ (ell : MackeyDiagrams.Dot bc (comp u w))
    (m₁ mτ : ProjectionLabel a u d v) (n : ProjectionLabel v w e f)
    (p₁ pτ : ProjectionLabel a bc de f),
    MackeyDiagrams.Dot.element ell = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot m₁) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot mτ) = τ ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot n) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot p₁) = 1 ∧
    MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot pτ) = τ ∧
    let rhs := right (Finsupp.single ell 1) (Finsupp.single m₁ 1 + Finsupp.single mτ 1)
      (Finsupp.single n 1)
    eval rhs = Qstar p₁ + Qstar pτ ∧
    eval rhs (basisVector 1) ≠ 0 ∧
    eval rhs (basisVector τ) ≠ 0 ∧
    (∀ (allowed : Set A) (drawings : List Drawing),
      (∀ drawing ∈ drawings, IsLeftWith allowed drawing) →
      eval (sumDrawings drawings) = eval rhs →
      (∃ x ∈ allowed, x ∈ line) ∧ (∃ x ∈ allowed, x ∈ swapCoset)) ∧
    (∃ l₁ lτ, IsLeftWith (line : Set A) l₁ ∧ IsLeftWith swapCoset lτ ∧
      eval l₁ = Qstar p₁ ∧ eval lτ = Qstar pτ ∧
      eval (MackeyDiagrams.LabelledDrawing.add l₁ lτ) = eval rhs) ∧
    (∀ replacement : MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex
        (MackeyDiagrams.Word.boundary bottom) (MackeyDiagrams.Word.boundary top) leftShape,
      MackeyDiagrams.ScopedDiagram.eval
        (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret replacement) ≠
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.ScopedDiagram.atBoundary
        (MackeyDiagrams.LabelledDrawing.interpret rhs)))


namespace CaseTwoAudit
open MackeyDiagrams

/-- Exact remaining connection. It identifies evaluation in the full planar fibre
with evaluation of the three typed compact stages. The Lean theorem below checks
only the assembly conditional on a proof of this proposition. -/
def CaseTwoLeftInversion : Prop :=
    ∀ replacement : LabelledDrawing.PlanarAtBoundary Complex bottom.boundary top.boundary leftShape,
      ∃ (B : Subgroup U) (r : ConjEmbedding B G) (s : ConjEmbedding B D)
        (t : ConjEmbedding T B) (xs : Finsupp (ProjectionLabel a b r s) Complex)
        (ys : Finsupp (ProjectionLabel s c t f) Complex)
        (zs : DotLabel Complex (comp r t) de),
        replacement.interpret.eval = (left r s t xs ys zs).interpret.atBoundary.eval

end CaseTwoAudit

namespace CaseTwoAudit

open MackeyDiagrams

theorem frame_eq_of_atBoundary_eq
    {V : Type*} [Group V] {K H : Subgroup V}
    {R : Type*} [CommSemiring R] {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing R p₀ p) (post : LabelledDrawing R q q₀)
    (x y : LabelledDrawing R p q)
    (h : x.interpret.atBoundary.eval = y.interpret.atBoundary.eval) :
    (LabelledDrawing.vertical pre (LabelledDrawing.vertical x post)).interpret.eval.toLinearMap =
      (LabelledDrawing.vertical pre (LabelledDrawing.vertical y post)).interpret.eval.toLinearMap := by
  have he := (ScopedDiagram.eval_atBoundary_eq_iff x.interpret y.interpret).mp h
  exact congrArg
    (fun m => (pre.interpret.eval.vertical (m.vertical post.interpret.eval)).toLinearMap) he

theorem no_replacement_of_canonical (normal : CaseTwoLeftInversion)
    (replacement : LabelledDrawing.PlanarAtBoundary Complex bottom.boundary top.boundary leftShape) :
    replacement.interpret.eval ≠ rhs.interpret.atBoundary.eval := by
  intro hrep
  obtain ⟨B, r, s, t, xs, ys, zs, hval⟩ := normal replacement
  exact canonical_ne r s t xs ys zs
    (frame_eq_of_atBoundary_eq splitBottom mergeTop _ _ (hval.symm.trans hrep))

end CaseTwoAudit

#print axioms CaseTwoAudit.right_sum
#print axioms CaseTwoAudit.rhs_probe_one
#print axioms CaseTwoAudit.rhs_probe_swap
#print axioms CaseTwoAudit.canonical_zero
#print axioms CaseTwoAudit.frame_eq_of_atBoundary_eq
#print axioms CaseTwoAudit.no_replacement_of_canonical
