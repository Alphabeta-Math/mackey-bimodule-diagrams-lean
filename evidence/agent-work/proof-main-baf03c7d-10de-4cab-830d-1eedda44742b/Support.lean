/-
Ian Xiao, Example 6.3 and the Case 2 figure, archived source PDF pp. 24 and 22
(SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2).
The separately checked published 28 November revision places the same example
and figure on pp. 26 and 24
(SHA-256 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
https://getcurious.cc/downloads/mackey-bimodules.pdf#page=26

The figure has three marked crossings on each side and the fixed boundary
cosets. The middle right dot is the finite label 1 + τ at one mark. The
example gives Q₁^! + Qτ^! as a sum of maps. The list fold in the reviewed
type appears under evaluation only. The empty list gives the zero map and
the singleton has its sole map's evaluation. The separate witness of two
left terms uses the binary addition constructor on the complete drawings.
The obstruction quantifies over the single left planar shape at the common
ordered boundary. The explicit scopes and orientations therefore agree
with the source and the revision's evaluation convention.

Alphabeta Math's canonical semidirect subgroup steps 1.2 and 2.1 give the
coordinate factorization and conjugation-action calculation. Here the base
is abelian, so conjugation on it only depends on the C₂ coordinate. This
makes the intersection the full line in G and trivial in GτG.
https://alphabetamath.cc/item/prop-canonical-subgroups-of-an-external-semidirect-product

Lemma 6.3 and (6.1) motivate the coefficient calculation. The public
EvaluationForTwoProjections gives existence and uniqueness of the overall
parameter. The left and right basis calculations below give the explicit
parameter and support of each weighted term, which is needed for the two
probes. The calculation uses
DoubleCoset.mem_doubleCoset on the first projection's basis coordinates.
CaseTwoLeftProjectionConstruction .1 (Theorem 6.4(2)) applies separately
to the two overall ProjectionDot.Mixed witnesses, whose finite fibers
are proved below. Each use gives its own internal subgroup.
https://getcurious.cc/articles/math-bimodule-string-diagrams#lem:three-projections
https://getcurious.cc/articles/math-bimodule-string-diagrams#thm:three-projections

For the universal shape clause we prove rigidity of the positioned event
sequence, since event count alone does not determine the crossing order.
The factorization isolates each actual singleton. Alphabeta Math's Morita
coherence steps 1.1–1.3 motivate the associator, unitor and whiskering
identities. Here the local boundary-coherence proof works on balanced
basis elements, extends linearly and removes only empty-code padding.
It adapts the project's DotSlidePreorderNotSymmetric support to the
existing driver imports. The normal forms identify the same B, r, s, t
and restriction suffix across the cuts. Collecting coefficients keeps
the same projection and parallel-crossing marks and uses the finite
fiber proof carried by each projection term. The fixed-boundary
comparison then follows by composition and the two coefficient probes.
https://alphabetamath.cc/item/lem-bimodule-tensor-associators-and-unitors-satisfy-bicategory-coherence
-/


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
  fun {X : Type*} (label : Finsupp X Complex) =>
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

/-- Evaluation in the full planar fibre agrees with a composite of three typed
compact crossings at the common ordered boundaries. -/
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

theorem encode_stack (s t : DrawingShape) :
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

def code (s : DrawingShape) : PlanarCode.Code :=
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

theorem drawing_code_vert {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) :
    code (d.vertical e).erase = code d.erase ++ code e.erase :=
  code_stack _ _

theorem drawing_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex p' q') :
    code (d.horizontal e).erase = code d.erase ++ PlanarCode.shift q.directions.length (code e.erase) := by
  have hd := drawing_fits d
  have he := drawing_fits e
  change code (d.erase.juxtapose e.erase) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]

theorem diagram_code_vert {p q r : Word A B}
    (d : Diagram Complex p q) (e : Diagram Complex q r) :
    code (d.vertical e).drawing = code d.drawing ++ code e.drawing :=
  code_stack _ _

theorem diagram_code_horiz {p q : Word A B} {p' q' : Word B C}
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

def isCompactCrossing : PlanarEvent → Prop
  | .vertex _ .mixedProjection | .vertex _ .parallelUp => True
  | _ => False

def goodCode (c : PlanarCode.Code) : Prop :=
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

theorem no_expandedProjection (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
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

namespace CaseTwoStructural

open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {A B C D : Subgroup U}

private abbrev join (n : Nat) : PlanarEvent := .vertex n (.trivalent .mergeUp)
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

theorem shift_zero (a : PlanarCode.Code) : PlanarCode.shift 0 a = a := by
  unfold PlanarCode.shift
  have h : (fun e : PlanarEvent => e.place (0 + e.position)) = id := by
    funext e
    cases e <;> simp [PlanarEvent.place, PlanarEvent.position]
  rw [h, List.map_id]

theorem encode_stack (s t : DrawingShape) :
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

def code (s : DrawingShape) : PlanarCode.Code :=
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

theorem drawing_code_vert {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r) :
    code (d.vertical e).erase = code d.erase ++ code e.erase :=
  code_stack _ _

theorem drawing_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex p' q') :
    code (d.horizontal e).erase = code d.erase ++ PlanarCode.shift q.directions.length (code e.erase) := by
  have hd := drawing_fits d
  have he := drawing_fits e
  change code (d.erase.juxtapose e.erase) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]

theorem diagram_code_vert {p q r : Word A B}
    (d : Diagram Complex p q) (e : Diagram Complex q r) :
    code (d.vertical e).drawing = code d.drawing ++ code e.drawing :=
  code_stack _ _

theorem diagram_code_horiz {p q : Word A B} {p' q' : Word B C}
    (d : Diagram Complex p q) (e : Diagram Complex p' q') :
    code (d.horizontal e).drawing = code d.drawing ++ PlanarCode.shift q.directions.length (code e.drawing) := by
  have hd := diagram_fits d
  have he := diagram_fits e
  change code (d.drawing.juxtapose e.drawing) = _
  rw [code_juxtapose hd.1 he.1, hd.2.2]



end CaseTwoStructural
namespace CaseTwoBoundaryCoherence

open MackeyDiagrams

universe u v

section Basis

variable {K H J F : Type u} [Group K] [Group H] [Group J] [Group F]
variable {R : Type v} [CommSemiring R]
variable {X X' X'' : Biset K H} {Y Y' : Biset H J}

/-- Equivariant maps taking each basis element to a basis element. -/
private structure BasisMap (X X' : Biset K H) where
  run : X.carrier → X'.carrier
  commute : ∀ g x, run (X.act g x) = X'.act g (run x)

namespace BasisMap

private noncomputable def linear (f : BasisMap X X') : Biset.Hom R X X' :=
  Biset.Hom.ofFunction f.run f.commute

private theorem linear_single (f : BasisMap X X') (x : X.carrier) (c : R) :
    (f.linear (R := R)).toLinearMap (Finsupp.single x c) = Finsupp.single (f.run x) c :=
  Biset.Hom.ofFunction_single _ _ _ _

private def ident (X : Biset K H) : BasisMap X X := ⟨id, fun _ _ => rfl⟩

private def vert (f : BasisMap X X') (g : BasisMap X' X'') : BasisMap X X'' :=
  ⟨g.run ∘ f.run, fun k x => by simp only [Function.comp_apply, f.commute, g.commute]⟩

private def hor (f : BasisMap X X') (g : BasisMap Y Y') :
    BasisMap (X.tensor Y) (X'.tensor Y') where
  run := Quotient.lift (fun z => X'.pair Y' (f.run z.1) (g.run z.2)) (by
    intro x y h
    obtain ⟨k, hk, hk'⟩ := h
    rw [← hk, ← hk', f.commute, g.commute, Biset.pair_orbit])
  commute := by
    intro k z
    refine Quotient.inductionOn z ?_
    rintro ⟨x,y⟩
    change X'.pair Y' (f.run (X.act (k.1,1) x)) (g.run (Y.act (1,k.2) y)) =
      X'.pair Y' (X'.act (k.1,1) (f.run x)) (Y'.act (1,k.2) (g.run y))
    rw [f.commute, g.commute]

private theorem linear_ident (X : Biset K H) : ((ident X).linear (R := R)) = Biset.Hom.id X := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  exact linear_single _ _ _

private theorem linear_vert (f : BasisMap X X') (g : BasisMap X' X'') :
    ((f.vert g).linear (R := R)) = f.linear.vertical g.linear := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  change ((f.vert g).linear (R := R)).toLinearMap (Finsupp.single x c) =
    g.linear.toLinearMap (f.linear.toLinearMap (Finsupp.single x c))
  rw [linear_single, linear_single, linear_single]
  rfl

private theorem linear_hor (f : BasisMap X X') (g : BasisMap Y Y') :
    ((f.hor g).linear (R := R)) = f.linear.horizontal g.linear := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z c
  refine Quotient.inductionOn z ?_
  rintro ⟨x,y⟩
  change ((f.hor g).linear (R := R)).toLinearMap (Finsupp.single (X.pair Y x y) c) =
    (f.linear.horizontal g.linear).toLinearMap (Finsupp.single (X.pair Y x y) c)
  rw [linear_single, Biset.Hom.horizontal_single, linear_single, linear_single,
    Biset.pairLinear_single, one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

private def assoc (X : Biset K H) (Y : Biset H J) (Z : Biset J F) :
    BasisMap ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z)) :=
  ⟨Biset.associateBasis X Y Z, by
    intro g w
    refine Quotient.inductionOn w (fun ⟨xy,z⟩ => ?_)
    exact Quotient.inductionOn xy (fun _ => rfl)⟩

private def left (X : Biset K H) : BasisMap ((Biset.regular K).tensor X) X :=
  ⟨Biset.leftUnitBasis X, by
    intro g z
    refine Quotient.inductionOn z ?_
    rintro ⟨k,x⟩
    change X.act (g.1 * k * (1 : K)⁻¹, 1) (X.act (1,g.2) x) =
      X.act g (X.act (k,1) x)
    rw [← X.mul_act, ← X.mul_act]
    rcases g with ⟨a,b⟩
    simp⟩

private def insRight (X : Biset K H) : BasisMap X (X.tensor (Biset.regular H)) :=
  ⟨fun x => X.pair (Biset.regular H) x 1, by
    intro g x
    change X.pair (Biset.regular H) (X.act g x) 1 =
      X.pair (Biset.regular H) (X.act (g.1,1) x) (1 * 1 * g.2⁻¹)
    have e := X.pair_balance (Biset.regular H) g.2⁻¹ (X.act (g.1,1) x) 1
    rw [← X.mul_act] at e
    rcases g with ⟨k,h⟩
    simpa [Biset.regular] using e⟩

end BasisMap

end Basis


section Words

variable {U : Type u} [Group U] {A B C D : Subgroup U}
variable {R : Type v} [CommSemiring R]

private def appendBasis : {A B C : Subgroup U} →
    (a : Boundary A B) → (b : Boundary B C) →
    BasisMap (a.word.basis.tensor b.word.basis) (a.append b).word.basis
  | _, _, _, .empty _, b => BasisMap.left b.word.basis
  | _, _, _, .cons s t, b => (BasisMap.assoc s.word.basis t.word.basis b.word.basis).vert
      ((BasisMap.ident s.word.basis).hor (appendBasis t b))

private def join (a : Boundary A B) (b : Boundary B C)
    (x : a.word.basis.carrier) (y : b.word.basis.carrier) :
    (a.append b).word.basis.carrier :=
  (appendBasis a b).run (a.word.basis.pair b.word.basis x y)

private theorem join_cons (s : Strand A B) (t : Boundary B C) (b : Boundary C D)
    (x : s.word.basis.carrier) (y : t.word.basis.carrier) (z : b.word.basis.carrier) :
    join (.cons s t) b (s.word.basis.pair t.word.basis x y) z =
      s.word.basis.pair (t.append b).word.basis x (join t b y z) := rfl

private theorem join_left_action (a : Boundary A B) (b : Boundary B C)
    (g : A) (x : a.word.basis.carrier) (y : b.word.basis.carrier) :
    join a b (a.word.basis.act (g,1) x) y =
      (a.append b).word.basis.act (g,1) (join a b x y) := by
  have h := (appendBasis a b).commute (g,1) (a.word.basis.pair b.word.basis x y)
  rw [Biset.act_pair] at h
  change (appendBasis a b).run
    (a.word.basis.pair b.word.basis (a.word.basis.act (g,1) x) (b.word.basis.act 1 y)) = _ at h
  rwa [Biset.one_act] at h

private def reindex {a b : Boundary A B} (h : a = b) :
    a.word.basis.carrier → b.word.basis.carrier :=
  fun x => h ▸ x

private theorem reindex_cons (s : Strand A B) {a b : Boundary B C}
    (h : a = b) (x : s.word.basis.carrier) (y : a.word.basis.carrier) :
    reindex (congrArg (Boundary.cons s) h) (s.word.basis.pair a.word.basis x y) =
      s.word.basis.pair b.word.basis x (reindex h y) := by
  cases h
  rfl

private theorem join_assoc (a : Boundary A B) (b : Boundary B C) (c : Boundary C D)
    (x : a.word.basis.carrier) (y : b.word.basis.carrier) (z : c.word.basis.carrier) :
    reindex (Boundary.append_assoc a b c) (join (a.append b) c (join a b x y) z) =
      join a (b.append c) x (join b c y z) := by
  induction a with
  | empty => exact join_left_action b c x y z
  | cons s t ih =>
    refine Quotient.inductionOn x ?_
    rintro ⟨x',x''⟩
    change reindex (congrArg (Boundary.cons s) (Boundary.append_assoc t b c))
      (join (.cons s (t.append b)) c (join (.cons s t) b (s.word.basis.pair t.word.basis x' x'') y) z) =
      join (.cons s t) (b.append c) (s.word.basis.pair t.word.basis x' x'') (join b c y z)
    simp only [join_cons, reindex_cons s (Boundary.append_assoc t b c), ih]
    rfl

private theorem join_empty (a : Boundary A B) (x : a.word.basis.carrier) (y : B) :
    reindex (Boundary.append_empty a) (join a (.empty B) x y) =
      a.word.basis.act (1,y⁻¹) x := by
  induction a with
  | @empty K =>
    change ↥K at x
    change x * y * (1 : K)⁻¹ = 1 * x * (y⁻¹)⁻¹
    simp
  | @cons K H J s t ih =>
    refine Quotient.inductionOn x ?_
    rintro ⟨x',x''⟩
    change reindex (congrArg (Boundary.cons s) (Boundary.append_empty t))
      (join (.cons s t) (.empty J) (s.word.basis.pair t.word.basis x' x'') y) =
      (s.word.basis.tensor t.word.basis).act (1,y⁻¹) (s.word.basis.pair t.word.basis x' x'')
    have step := congrArg (reindex (congrArg (Boundary.cons s) (Boundary.append_empty t)))
      (join_cons s t (.empty J) x' x'' y)
    refine step.trans ((reindex_cons s (Boundary.append_empty t) x' _).trans ?_)
    rw [ih, Biset.act_pair]
    change s.word.basis.pair t.word.basis x' _ =
      s.word.basis.pair t.word.basis (s.word.basis.act 1 x') _
    rw [Biset.one_act]

private theorem eval_appendBasis (a : Boundary A B) (b : Boundary B C) :
    ((appendBasis a b).linear (R := R)) = (a.appendDiagram b).eval := by
  induction a with
  | empty => rfl
  | cons s t ih =>
    change (((BasisMap.assoc s.word.basis t.word.basis b.word.basis).vert
      ((BasisMap.ident s.word.basis).hor (appendBasis t b))).linear (R := R)) =
      (Biset.associate _ _ _ R).vertical ((Biset.Hom.id _).horizontal (t.appendDiagram b).eval)
    rw [BasisMap.linear_vert, BasisMap.linear_hor, BasisMap.linear_ident, ih]
    rfl

private def normBasis : {A B : Subgroup U} →
    (p : Word A B) → BasisMap p.basis p.boundary.word.basis
  | _, _, .empty A => BasisMap.ident (Biset.regular A)
  | _, _, .up a => BasisMap.insRight (Biset.induction a)
  | _, _, .down a => BasisMap.insRight (Biset.restriction a)
  | _, _, .tensor p q => ((normBasis p).hor (normBasis q)).vert (appendBasis p.boundary q.boundary)

private theorem eval_normBasis (p : Word A B) :
    ((normBasis p).linear (R := R)) = (p.reorderToBoundary (R := R)).eval := by
  induction p with
  | empty => exact BasisMap.linear_ident (R := R) _
  | up => rfl
  | down => rfl
  | tensor p q ihp ihq =>
    change ((((normBasis p).hor (normBasis q)).vert
      (appendBasis p.boundary q.boundary)).linear (R := R)) =
      ((p.reorderToBoundary (R := R)).eval.horizontal (q.reorderToBoundary (R := R)).eval).vertical
        (p.boundary.appendDiagram q.boundary).eval
    rw [BasisMap.linear_vert, BasisMap.linear_hor, ihp, ihq, eval_appendBasis]


/-- Transport the target of a map across equality of ordered strand data. -/
def transport {X : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X a.word.basis) : Biset.Hom R X b.word.basis :=
  h ▸ f

private theorem transport_single {X : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X a.word.basis) (x : X.carrier) (y : a.word.basis.carrier) (c : R)
    (hf : f.toLinearMap (Finsupp.single x c) = Finsupp.single y c) :
    (transport h f).toLinearMap (Finsupp.single x c) = Finsupp.single (reindex h y) c := by
  cases h
  exact hf

private theorem transport_trans {X : Biset A B} {a b c : Boundary A B}
    (h : a = b) (k : b = c) (f : Biset.Hom R X a.word.basis) :
    transport (h.trans k) f = transport k (transport h f) := by
  cases h
  cases k
  rfl

private theorem transport_vertical {X Y : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X Y) (g : Biset.Hom R Y a.word.basis) :
    transport h (f.vertical g) = f.vertical (transport h g) := by
  cases h
  rfl

private theorem transport_append {X : Biset A B} {Y : Biset B C}
    {a a' : Boundary A B} {b b' : Boundary B C} (ha : a = a') (hb : b = b')
    (f : Biset.Hom R X a.word.basis) (g : Biset.Hom R Y b.word.basis) :
    transport (congrArg₂ Boundary.append ha hb) ((f.horizontal g).vertical (a.appendDiagram b).eval) =
      ((transport ha f).horizontal (transport hb g)).vertical (a'.appendDiagram b').eval := by
  cases ha
  cases hb
  rfl

private def Coherent {p q : Word A B} (f : Biset.Hom R p.basis q.basis) : Prop :=
  ∃ h : p.boundary = q.boundary, transport h (p.reorderToBoundary (R := R)).eval =
    f.vertical (q.reorderToBoundary (R := R)).eval

private theorem coherent_of_single {p q : Word A B} (f : Biset.Hom R p.basis q.basis)
    (h : p.boundary = q.boundary) (g : p.basis.carrier → q.basis.carrier)
    (hf : ∀ x c, f.toLinearMap (Finsupp.single x c) = Finsupp.single (g x) c)
    (hg : ∀ x, reindex h ((normBasis p).run x) = (normBasis q).run (g x)) :
    Coherent (p := p) (q := q) f := by
  refine ⟨h, ?_⟩
  rw [← eval_normBasis p, ← eval_normBasis q]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  change (transport h (normBasis p).linear).toLinearMap (Finsupp.single x c) =
    (normBasis q).linear.toLinearMap (f.toLinearMap (Finsupp.single x c))
  rw [transport_single h _ x _ c (BasisMap.linear_single _ _ _), hf, BasisMap.linear_single, hg]

private theorem coherent_id (p : Word A B) : Coherent (p := p) (q := p) (Biset.Hom.id (R := R) _) :=
  ⟨rfl, rfl⟩

private theorem coherent_vertical {p q t : Word A B}
    {f : Biset.Hom R p.basis q.basis} {g : Biset.Hom R q.basis t.basis}
    (hf : Coherent (p := p) (q := q) f) (hg : Coherent (p := q) (q := t) g) :
    Coherent (p := p) (q := t) (f.vertical g) := by
  obtain ⟨h, hf⟩ := hf
  obtain ⟨k, hg⟩ := hg
  exact ⟨h.trans k, by rw [transport_trans h k, hf, transport_vertical k, hg, Biset.Hom.vertical_assoc]⟩

private theorem coherent_horizontal {p p' : Word A B} {q q' : Word B C}
    {f : Biset.Hom R p.basis p'.basis} {g : Biset.Hom R q.basis q'.basis}
    (hf : Coherent (p := p) (q := p') f) (hg : Coherent (p := q) (q := q') g) :
    Coherent (p := p.tensor q) (q := p'.tensor q') (f.horizontal g) := by
  obtain ⟨h, hf⟩ := hf
  obtain ⟨k, hg⟩ := hg
  refine ⟨congrArg₂ Boundary.append h k, ?_⟩
  change transport (congrArg₂ Boundary.append h k)
    (((p.reorderToBoundary (R := R)).eval.horizontal (q.reorderToBoundary (R := R)).eval).vertical
      (p.boundary.appendDiagram q.boundary).eval) =
    (f.horizontal g).vertical
      (((p'.reorderToBoundary (R := R)).eval.horizontal (q'.reorderToBoundary (R := R)).eval).vertical
        (p'.boundary.appendDiagram q'.boundary).eval)
  rw [transport_append h k, hf, hg, ← Biset.Hom.horizontal_vertical, Biset.Hom.vertical_assoc]

private theorem coherent_inverse {p q : Word A B}
    {f : Biset.Hom R p.basis q.basis} {g : Biset.Hom R q.basis p.basis}
    (hf : Coherent (p := p) (q := q) f) (hg : g.vertical f = Biset.Hom.id _) :
    Coherent (p := q) (q := p) g := by
  obtain ⟨h, hf⟩ := hf
  have hc := congrArg (transport h.symm) hf
  rw [← transport_trans h h.symm] at hc
  change (p.reorderToBoundary (R := R)).eval = transport h.symm
    (f.vertical (q.reorderToBoundary (R := R)).eval) at hc
  refine ⟨h.symm, ?_⟩
  rw [hc, transport_vertical h.symm, ← Biset.Hom.vertical_assoc, hg, Biset.Hom.id_vertical]

private theorem coherent_associate (p : Word A B) (q : Word B C) (t : Word C D) :
    Coherent (p := (p.tensor q).tensor t) (q := p.tensor (q.tensor t))
      (Diagram.associate (R := R) p q t).eval := by
  refine coherent_of_single _ (Word.boundary_associate p q t)
    (Biset.associateBasis p.basis q.basis t.basis) ?_ ?_
  · intro x c
    change (Biset.associate p.basis q.basis t.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.associate, Biset.Hom.ofFunction_single]
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨xy,z⟩
    refine Quotient.inductionOn xy ?_
    rintro ⟨x,y⟩
    change reindex (Boundary.append_assoc p.boundary q.boundary t.boundary)
      ((normBasis ((p.tensor q).tensor t)).run ((p.basis.tensor q.basis).pair t.basis (p.basis.pair q.basis x y) z)) =
      (normBasis (p.tensor (q.tensor t))).run (p.basis.pair (q.basis.tensor t.basis) x (q.basis.pair t.basis y z))
    exact join_assoc p.boundary q.boundary t.boundary _ _ _

private theorem coherent_leftUnit (p : Word A B) :
    Coherent (p := (Word.empty A).tensor p) (q := p) (Diagram.leftUnit (R := R) p).eval := by
  refine coherent_of_single _ (Word.boundary_leftUnit p) (Biset.leftUnitBasis p.basis) ?_ ?_
  · intro x c
    change (Biset.leftUnit p.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.leftUnit, Biset.Hom.ofFunction_single]
  · intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨k,x⟩
    change p.boundary.word.basis.act (k,1) ((normBasis p).run x) =
      (normBasis p).run (p.basis.act (k,1) x)
    exact ((normBasis p).commute _ _).symm

private theorem coherent_rightUnit (p : Word A B) :
    Coherent (p := p.tensor (.empty B)) (q := p) (Diagram.rightUnit (R := R) p).eval := by
  refine coherent_of_single _ (Word.boundary_rightUnit p) (Biset.rightUnitBasis p.basis) ?_ ?_
  · intro x c
    change (Biset.rightUnit p.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.rightUnit, Biset.Hom.ofFunction_single]
  · intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨x,k⟩
    change reindex (Boundary.append_empty p.boundary) (join p.boundary (.empty B) ((normBasis p).run x) k) =
      (normBasis p).run (p.basis.act (1,k⁻¹) x)
    exact (join_empty p.boundary _ k).trans ((normBasis p).commute _ _).symm

end Words

end CaseTwoBoundaryCoherence

namespace CaseTwoStructural

open MackeyDiagrams CaseTwoBoundaryCoherence

universe u
variable {U : Type u} [Group U] {A B : Subgroup U}

private theorem expanded_code_ne_nil (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry n o c) ≠ [] := by
  cases o <;> cases c <;>
    simp [DrawingShape.expandedProjectionGeometry, encode_stack, PlanarCode.encode, PlanarCode.shift]

private theorem vertex_code_ne_nil (k : VertexKind) : code (.vertex k) ≠ [] := by
  cases k <;> try (exact List.cons_ne_nil _ _)
  case parallelUpChain n =>
    simp [code, DrawingShape.geometry, encode_stack, PlanarCode.encode]
  case parallelDownChain n =>
    simp [code, DrawingShape.geometry, encode_stack, PlanarCode.encode]
  case expandedMixedProjection o c => exact expanded_code_ne_nil 1 o c
  case expandedProjectionChain n o c => exact expanded_code_ne_nil n o c

private theorem code_split_horizontal {a b : PlanarCode.Code} {n : Nat}
    (h : a ++ PlanarCode.shift n b = []) : a = [] ∧ b = [] := by
  obtain ⟨ha, hb⟩ := List.append_eq_nil_iff.mp h
  exact ⟨ha, List.map_eq_nil_iff.mp hb⟩

private theorem emptyDiagram_coherent {p q : Word A B} (d : Diagram Complex p q)
    (h : code d.drawing = []) : Coherent (p := p) (q := q) d.eval := by
  induction d <;> try (exact (List.cons_ne_nil _ _ h).elim)
  case id p => exact coherent_id p
  case associate p q r => exact coherent_associate p q r
  case unassociate p q r =>
    exact coherent_inverse (coherent_associate p q r) Biset.unassociate_associate
  case leftUnit p => exact coherent_leftUnit p
  case rightUnit p => exact coherent_rightUnit p
  case insertLeftUnit p =>
    exact coherent_inverse (coherent_leftUnit p) Biset.insertLeftUnit_leftUnit
  case insertRightUnit p =>
    exact coherent_inverse (coherent_rightUnit p) Biset.insertRightUnit_rightUnit
  case vertical d e ihd ihe =>
    have ⟨hd, he⟩ := List.append_eq_nil_iff.mp ((diagram_code_vert d e).symm.trans h)
    exact coherent_vertical (ihd hd) (ihe he)
  case horizontal d e ihd ihe =>
    have ⟨hd, he⟩ := code_split_horizontal ((diagram_code_horiz d e).symm.trans h)
    exact coherent_horizontal (ihd hd) (ihe he)

private theorem emptyDrawing_coherent {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : code d.erase = []) : Coherent (p := p) (q := q) d.interpret.eval := by
  induction d <;> try (exact (vertex_code_ne_nil _ h).elim)
  case ordinary d => exact emptyDiagram_coherent d h
  case add | scale =>
    simp only [code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, List.cons_ne_nil] at h
  case vertical d e ihd ihe =>
    have ⟨hd, he⟩ := List.append_eq_nil_iff.mp ((drawing_code_vert d e).symm.trans h)
    exact coherent_vertical (ihd hd) (ihe he)
  case horizontal d e ihd ihe =>
    have ⟨hd, he⟩ := code_split_horizontal ((drawing_code_horiz d e).symm.trans h)
    exact coherent_horizontal (ihd hd) (ihe he)

/-- At the canonical boundary the evaluated map is the transported identity. -/
theorem empty_geometry_atBoundary {p q : Word A B} (d : LabelledDrawing Complex p q)
    (h : PlanarCode.encode d.erase.geometry = []) :
    ∃ he : p.boundary = q.boundary,
      d.interpret.atBoundary.eval = transport he (Biset.Hom.id (R := Complex) p.boundary.word.basis) := by
  obtain ⟨he, hc⟩ := emptyDrawing_coherent d h
  refine ⟨he, ?_⟩
  change (p.reorderFromBoundary (R := Complex)).eval.vertical
    (d.interpret.eval.vertical (q.reorderToBoundary (R := Complex)).eval) = _
  rw [← hc, ← transport_vertical he]
  have hp : (p.reorderFromBoundary (R := Complex)).eval.vertical
      (p.reorderToBoundary (R := Complex)).eval = Biset.Hom.id p.boundary.word.basis :=
    Word.eval_reorderFromTo p
  rw [hp]

end CaseTwoStructural
namespace CaseTwoStructural

open MackeyDiagrams
open Biset.Hom

universe u
variable {U : Type u} [Group U] {A B C : Subgroup U}

def boundaryDirections : {A B : Subgroup U} → Boundary A B → List Bool
  | _, _, .empty _ => []
  | _, _, .cons (.up _) rest => true :: boundaryDirections rest
  | _, _, .cons (.down _) rest => false :: boundaryDirections rest

private theorem boundaryDirections_append (p : Boundary A B) (q : Boundary B C) :
    boundaryDirections (p.append q) = boundaryDirections p ++ boundaryDirections q := by
  induction p with
  | empty => rfl
  | cons s rest ih => cases s <;> simp only [Boundary.append, boundaryDirections, List.cons_append, ih]

theorem boundaryDirections_word (p : Word A B) :
    boundaryDirections p.boundary = p.directions := by
  induction p with
  | empty | up | down => rfl
  | tensor p q ihp ihq => rw [Word.boundary, boundaryDirections_append, ihp, ihq, Word.directions]

noncomputable def canon {p q : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) :
    Biset.Hom Complex p.boundary.word.basis q.boundary.word.basis :=
  (p.reorderFromBoundary (R := Complex)).eval.vertical
    (f.vertical (q.reorderToBoundary (R := Complex)).eval)

theorem canon_vertical {p q r : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) (g : Biset.Hom Complex q.basis r.basis) :
    canon (f.vertical g) = (canon f).vertical (canon g) := by
  unfold canon
  simp only [vertical_assoc]
  have h := Word.eval_reorderToFrom (R := Complex) q
  change ((q.reorderToBoundary (R := Complex)).eval.vertical q.reorderFromBoundary.eval) = Biset.Hom.id _ at h
  rw [← vertical_assoc (q.reorderToBoundary (R := Complex)).eval, h, id_vertical]

private abbrev BoundaryMap {A B : Subgroup U} (p q : Boundary A B) :=
  Biset.Hom Complex p.word.basis q.word.basis

private noncomputable def boundaryId {p q : Boundary A B} (h : p = q) : BoundaryMap p q :=
  h ▸ (Biset.Hom.id p.word.basis : BoundaryMap p p)

/-- Empty code preserves the ordered labelled boundary, and its evaluation there is
the identity transported along the boundary equality. -/
def EmptyCodeCoherence (U : Type u) [Group U] : Prop :=
  ∀ {A B : Subgroup U} {p q : Word A B} (d : LabelledDrawing Complex p q),
    code d.erase = [] →
      ∃ h : p.boundary = q.boundary, canon d.interpret.eval = boundaryId h

def Wire (p q : Word A B) :=
  {d : LabelledDrawing Complex p q // code d.erase = []}

noncomputable def Wire.eval {p q : Word A B} (d : Wire p q) :=
  d.val.interpret.eval

private def Wire.id (p : Word A B) : Wire p p := ⟨.ordinary (.id p), rfl⟩

private def Wire.vertical {p q r : Word A B} (d : Wire p q) (e : Wire q r) : Wire p r :=
  ⟨d.val.vertical e.val, by rw [drawing_code_vert, d.property, e.property]; rfl⟩

private def Wire.horizontal {p q : Word A B} {r s : Word B C}
    (d : Wire p q) (e : Wire r s) : Wire (p.tensor r) (q.tensor s) :=
  ⟨d.val.horizontal e.val, by rw [drawing_code_horiz, d.property, e.property]; rfl⟩

theorem Wire.boundary (hc : EmptyCodeCoherence U)
    {p q : Word A B} (d : Wire p q) : p.boundary = q.boundary :=
  (hc d.val d.property).choose

theorem Wire.directions (hc : EmptyCodeCoherence U)
    {p q : Word A B} (d : Wire p q) : p.directions = q.directions := by
  simpa only [boundaryDirections_word] using congrArg boundaryDirections (d.boundary hc)

private theorem appendCode (p : Boundary A B) (q : Boundary B C) :
    code (p.appendDiagram (R := Complex) q).drawing = [] ∧
    code (p.splitDiagram (R := Complex) q).drawing = [] := by
  induction p with
  | empty => exact ⟨rfl, rfl⟩
  | cons s rest ih =>
    constructor
    · change code ((Diagram.associate (R := Complex) s.word rest.word q.word).vertical
        ((Diagram.id s.word).horizontal (rest.appendDiagram q))).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, (ih q).1]
      rfl
    · change code (((Diagram.id (R := Complex) s.word).horizontal (rest.splitDiagram q)).vertical
        (Diagram.unassociate s.word rest.word q.word)).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, (ih q).2]
      rfl

private theorem reorderCode (p : Word A B) :
    code (p.reorderToBoundary (R := Complex)).drawing = [] ∧
    code (p.reorderFromBoundary (R := Complex)).drawing = [] := by
  induction p with
  | empty | up | down => exact ⟨rfl, rfl⟩
  | tensor p q hp hq =>
    constructor
    · change code (((p.reorderToBoundary (R := Complex)).horizontal q.reorderToBoundary).vertical
        (p.boundary.appendDiagram q.boundary)).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, hp.1, hq.1, (appendCode _ _).1]
      rfl
    · change code (((p.boundary.splitDiagram (R := Complex) q.boundary)).vertical
        (p.reorderFromBoundary.horizontal q.reorderFromBoundary)).drawing = []
      rw [diagram_code_vert, diagram_code_horiz, hp.2, hq.2, (appendCode _ _).2]
      rfl

private def Wire.between (p q : Word A B) (h : p.boundary = q.boundary) : Wire p q :=
  (show Wire p p.boundary.word from ⟨.ordinary p.reorderToBoundary, (reorderCode p).1⟩).vertical
    (show Wire p.boundary.word q from h.symm ▸
      (show Wire q.boundary.word q from ⟨.ordinary q.reorderFromBoundary, (reorderCode q).2⟩))

def Framed {p q r s : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) (g : Biset.Hom Complex r.basis s.basis) : Prop :=
  ∃ (pre : Wire p r) (post : Wire s q), f = pre.eval.vertical (g.vertical post.eval)

theorem Framed.self {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) :
    Framed f f := by
  refine ⟨Wire.id p, Wire.id q, ?_⟩
  change f = (Biset.Hom.id _).vertical (f.vertical (Biset.Hom.id _))
  rw [id_vertical, vertical_id]

theorem Framed.vertLeft {p q r s t : Word A B}
    (d : Wire p q) {f : Biset.Hom Complex q.basis r.basis}
    {g : Biset.Hom Complex s.basis t.basis} (h : Framed f g) : Framed (d.eval.vertical f) g := by
  obtain ⟨pre, post, rfl⟩ := h
  exact ⟨d.vertical pre, post, (vertical_assoc _ _ _).symm⟩

theorem Framed.vertRight {p q r s t : Word A B}
    (d : Wire q r) {f : Biset.Hom Complex p.basis q.basis}
    {g : Biset.Hom Complex s.basis t.basis} (h : Framed f g) : Framed (f.vertical d.eval) g := by
  obtain ⟨pre, post, rfl⟩ := h
  refine ⟨pre, post.vertical d, ?_⟩
  simp only [Wire.vertical, Wire.eval, Subtype.coe_mk, LabelledDrawing.interpret, ScopedDiagram.eval, vertical_assoc]

theorem Framed.trans {p q r s t z : Word A B}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    {k : Biset.Hom Complex t.basis z.basis} (h : Framed f g) (h' : Framed g k) : Framed f k := by
  obtain ⟨pre, post, rfl⟩ := h
  obtain ⟨pre', post', rfl⟩ := h'
  refine ⟨pre.vertical pre', post'.vertical post, ?_⟩
  simp only [Wire.vertical, Wire.eval, Subtype.coe_mk, LabelledDrawing.interpret, ScopedDiagram.eval, vertical_assoc]

theorem Framed.horizontal {p q r s : Word A B} {p' q' r' s' : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    {f' : Biset.Hom Complex p'.basis q'.basis} {g' : Biset.Hom Complex r'.basis s'.basis}
    (h : Framed f g) (h' : Framed f' g') :
    Framed (p := p.tensor p') (q := q.tensor q') (r := r.tensor r') (s := s.tensor s')
      (f.horizontal f') (g.horizontal g') := by
  obtain ⟨pre, post, rfl⟩ := h
  obtain ⟨pre', post', rfl⟩ := h'
  refine ⟨pre.horizontal pre', post.horizontal post', ?_⟩
  change _ = (pre.eval.horizontal pre'.eval).vertical ((g.horizontal g').vertical (post.eval.horizontal post'.eval))
  simp only [horizontal_vertical]

theorem Framed.boundaries (hc : EmptyCodeCoherence U) {p q r s : Word A B}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    (h : Framed f g) : p.boundary = r.boundary ∧ q.boundary = s.boundary :=
  ⟨h.choose.boundary hc, (h.choose_spec.choose.boundary hc).symm⟩

private theorem boundaryId_cancel {P Q R S : Boundary A B}
    (hp : P = R) (hq : S = Q) (m : BoundaryMap R S) :
    HEq ((boundaryId hp).vertical (m.vertical (boundaryId hq))) m := by
  subst P
  subst Q
  simp only [boundaryId, id_vertical, vertical_id]
  rfl

theorem Framed.canonical (hc : EmptyCodeCoherence U) {p q r s : Word A B}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    (h : Framed f g) : HEq (canon f) (canon g) := by
  obtain ⟨pre, post, rfl⟩ := h
  obtain ⟨hp, ep⟩ := hc pre.val pre.property
  obtain ⟨hq, eq⟩ := hc post.val post.property
  change canon pre.eval = _ at ep
  change canon post.eval = _ at eq
  rw [canon_vertical, canon_vertical, ep, eq]
  exact boundaryId_cancel hp hq (canon g)

private theorem Wire.eval_eq (hc : EmptyCodeCoherence U) {p q : Word A B}
    (d e : Wire p q) : d.eval = e.eval := by
  obtain ⟨hp, hd⟩ := hc d.val d.property
  obtain ⟨hq, he⟩ := hc e.val e.property
  apply (ScopedDiagram.eval_atBoundary_eq_iff d.val.interpret e.val.interpret).mp
  exact hd.trans he.symm

theorem frameStraight (hc : EmptyCodeCoherence U) {p q r : Word A B}
    (d : Wire p q) (h : p.boundary = r.boundary) :
    Framed d.eval (Biset.Hom.id (R := Complex) r.basis) := by
  let pre := Wire.between p r h
  let post := Wire.between r q (h.symm.trans (d.boundary hc))
  refine ⟨pre, post, ?_⟩
  rw [id_vertical]
  exact Wire.eval_eq hc d (pre.vertical post)

private theorem insertLeft_natural {p q : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) :
    (Biset.insertLeftUnit p.basis Complex).vertical
      ((Biset.Hom.id (Biset.regular A)).horizontal f) =
    f.vertical (Biset.insertLeftUnit q.basis Complex) := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  change (((Biset.Hom.id (Biset.regular A)).horizontal f).toLinearMap
      ((Biset.insertLeftUnit p.basis Complex).toLinearMap (Finsupp.single x r))) = _
  rw [Biset.insertLeftUnit, Biset.Hom.ofFunction_single, horizontal_single]
  change r • Biset.pairLinear Complex (Biset.regular A) q.basis (Finsupp.single 1 1)
      (f.toLinearMap (Finsupp.single x 1)) =
    (Biset.insertLeftUnit q.basis Complex).toLinearMap (f.toLinearMap (Finsupp.single x r))
  have aux (z : q.basis.carrier →₀ Complex) :
      Biset.pairLinear Complex (Biset.regular A) q.basis (Finsupp.single 1 1) z =
        (Biset.insertLeftUnit q.basis Complex).toLinearMap z := by
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro y s
    rw [Biset.pairLinear_single, one_mul, Biset.insertLeftUnit, Biset.Hom.ofFunction_single]
  rw [aux, ← map_smul, ← map_smul]
  simp [Finsupp.smul_single, smul_eq_mul]

private theorem insertRight_natural {p q : Word A B}
    (f : Biset.Hom Complex p.basis q.basis) :
    (Biset.insertRightUnit p.basis Complex).vertical
      (f.horizontal (Biset.Hom.id (Biset.regular B))) =
    f.vertical (Biset.insertRightUnit q.basis Complex) := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  change ((f.horizontal (Biset.Hom.id (Biset.regular B))).toLinearMap
      ((Biset.insertRightUnit p.basis Complex).toLinearMap (Finsupp.single x r))) = _
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single, horizontal_single]
  change r • Biset.pairLinear Complex q.basis (Biset.regular B)
      (f.toLinearMap (Finsupp.single x 1)) (Finsupp.single 1 1) =
    (Biset.insertRightUnit q.basis Complex).toLinearMap (f.toLinearMap (Finsupp.single x r))
  have aux (z : q.basis.carrier →₀ Complex) :
      Biset.pairLinear Complex q.basis (Biset.regular B) z (Finsupp.single 1 1) =
        (Biset.insertRightUnit q.basis Complex).toLinearMap z := by
    change (Biset.pairLinear Complex q.basis (Biset.regular B)).flip (Finsupp.single 1 1) z = _
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro y s
    simp only [LinearMap.flip_apply, Biset.insertRightUnit, Biset.Hom.ofFunction_single]
    exact (Biset.pairLinear_single (R := Complex) q.basis (Biset.regular B) y 1 s 1).trans (by rw [mul_one])
  rw [aux, ← map_smul, ← map_smul]
  simp [Finsupp.smul_single, smul_eq_mul]

theorem stripLeft {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) :
    Framed (p := (Word.empty A).tensor p) (q := (Word.empty A).tensor q)
      ((Biset.Hom.id (Biset.regular A)).horizontal f) f := by
  refine ⟨⟨.ordinary (.leftUnit p), rfl⟩, ⟨.ordinary (.insertLeftUnit q), rfl⟩, ?_⟩
  change _ = (Biset.leftUnit p.basis Complex).vertical (f.vertical (Biset.insertLeftUnit q.basis Complex))
  rw [← insertLeft_natural, ← vertical_assoc, Biset.leftUnit_insertLeftUnit, id_vertical]

theorem stripRight {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) :
    Framed (p := p.tensor (Word.empty B)) (q := q.tensor (Word.empty B))
      (f.horizontal (Biset.Hom.id (Biset.regular B))) f := by
  refine ⟨⟨.ordinary (.rightUnit p), rfl⟩, ⟨.ordinary (.insertRightUnit q), rfl⟩, ?_⟩
  change _ = (Biset.rightUnit p.basis Complex).vertical (f.vertical (Biset.insertRightUnit q.basis Complex))
  rw [← insertRight_natural, ← vertical_assoc, Biset.rightUnit_insertRightUnit, id_vertical]


theorem splitSingleton {c d : PlanarCode.Code} {e : PlanarEvent}
    (h : c ++ d = [e]) : (c = [] ∧ d = [e]) ∨ (c = [e] ∧ d = []) := by
  cases c with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons x xs =>
    simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, rfl⟩

theorem shiftEmpty {i : Nat} {c : PlanarCode.Code}
    (h : PlanarCode.shift i c = []) : c = [] := by
  simpa only [PlanarCode.shift, List.map_eq_nil_iff] using h


end CaseTwoStructural
namespace CaseTwoStructural

open MackeyDiagrams

universe u
variable {U : Type u} [Group U]
variable {G H K : Subgroup U}

private abbrev MergeBoundaryMap (p q : Boundary G K) :=
  Biset.Hom Complex p.word.basis q.word.basis

noncomputable abbrev normalize {p q : Word G K} (d : ScopedDiagram Complex p q) :
    MergeBoundaryMap p.boundary q.boundary := d.atBoundary.eval

private abbrev upPair (l : ConjEmbedding H G) (a : ConjEmbedding K H) :=
  (Word.up l).tensor (.up a)

inductive StraightAt : (p q : Boundary G K) → MergeBoundaryMap p q → Prop
  | id (p : Boundary G K) : StraightAt p p (Biset.Hom.id _)

private inductive MergeAt : (p q : Boundary G K) → MergeBoundaryMap p q → Prop
  | vertex (H : Subgroup U) (l : ConjEmbedding H G) (a : ConjEmbedding K H) :
    MergeAt (upPair l a).boundary (Word.up (l.comp a)).boundary
      (normalize (.ordinary (.mergeUp l a)))

/-- The only coherence input. Empty code evaluates to the identity at the
common ordered labelled boundary. -/
private def EmptyCodeStraight (U : Type u) [Group U] : Prop :=
  ∀ {G K : Subgroup U} {p q : Word G K} (d : LabelledDrawing Complex p q),
    code d.erase = [] → StraightAt p.boundary q.boundary (normalize d.interpret)

noncomputable def juxtaposeMap
    {p q : Boundary G H} {r s : Boundary H K}
    (f : MergeBoundaryMap p q) (g : MergeBoundaryMap r s) : MergeBoundaryMap (p.append r) (q.append s) :=
  (p.splitDiagram r).eval.vertical ((f.horizontal g).vertical (q.appendDiagram s).eval)

theorem normalize_vertical {p q r : Word G K}
    (d : ScopedDiagram Complex p q) (e : ScopedDiagram Complex q r) :
    normalize (d.vertical e) = (normalize d).vertical (normalize e) := by
  let fp := (p.reorderFromBoundary (R := Complex)).eval
  let tq := (q.reorderToBoundary (R := Complex)).eval
  let fq := (q.reorderFromBoundary (R := Complex)).eval
  let tr := (r.reorderToBoundary (R := Complex)).eval
  change fp.vertical ((d.eval.vertical e.eval).vertical tr) =
    (fp.vertical (d.eval.vertical tq)).vertical (fq.vertical (e.eval.vertical tr))
  have h : tq.vertical fq = Biset.Hom.id _ := Word.eval_reorderToFrom q
  simp only [Biset.Hom.vertical_assoc]
  rw [← Biset.Hom.vertical_assoc tq, h, Biset.Hom.id_vertical]

theorem normalize_horizontal {p q : Word G H} {r s : Word H K}
    (d : ScopedDiagram Complex p q) (e : ScopedDiagram Complex r s) :
    normalize (d.horizontal e) = juxtaposeMap (normalize d) (normalize e) := by
  change ((p.boundary.splitDiagram (R := Complex) r.boundary).eval.vertical
      ((p.reorderFromBoundary (R := Complex)).eval.horizontal r.reorderFromBoundary.eval)).vertical
      ((d.eval.horizontal e.eval).vertical
        (((q.reorderToBoundary (R := Complex)).eval.horizontal s.reorderToBoundary.eval).vertical
          (q.boundary.appendDiagram s.boundary).eval)) = _
  unfold juxtaposeMap
  change _ = (p.boundary.splitDiagram (R := Complex) r.boundary).eval.vertical
    ((((p.reorderFromBoundary (R := Complex)).eval.vertical
        (d.eval.vertical q.reorderToBoundary.eval)).horizontal
      ((r.reorderFromBoundary (R := Complex)).eval.vertical
        (e.eval.vertical s.reorderToBoundary.eval))).vertical
      (q.boundary.appendDiagram s.boundary).eval)
  rw [← Biset.Hom.horizontal_vertical, ← Biset.Hom.horizontal_vertical]
  simp only [Biset.Hom.vertical_assoc]

theorem normalize_id (p : Word G K) :
    normalize (.ordinary (.id p)) = Biset.Hom.id _ := Word.eval_reorderFromTo p

theorem straight_boundary_eq {p q : Boundary G K} {f : MergeBoundaryMap p q}
    (h : StraightAt p q f) : p = q := by
  cases h
  rfl

private theorem vertical_straight_left
    {p q r : Boundary G K} {f : MergeBoundaryMap p q} {g : MergeBoundaryMap q r}
    (hf : StraightAt p q f) (hg : MergeAt q r g) :
    MergeAt p r (f.vertical g) := by
  cases hf
  simpa only [Biset.Hom.id_vertical] using hg

private theorem vertical_straight_right
    {p q r : Boundary G K} {f : MergeBoundaryMap p q} {g : MergeBoundaryMap q r}
    (hf : MergeAt p q f) (hg : StraightAt q r g) :
    MergeAt p r (f.vertical g) := by
  cases hg
  simpa only [Biset.Hom.vertical_id] using hf

theorem pad_left_eval {X Y : Biset G K} (f : Biset.Hom Complex X Y) :
    ((Biset.insertLeftUnit X Complex).vertical
      ((Biset.Hom.id (Biset.regular G)).horizontal f)).vertical
        (Biset.leftUnit Y Complex) = f := by
  have h (Z : Biset G K) (w : Z.carrier →₀ Complex) :
      (Biset.insertLeftUnit Z Complex).toLinearMap w =
        Biset.pairLinear Complex (Biset.regular G) Z (Finsupp.single 1 1) w := by
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro z c
    rw [Biset.pairLinear_single, one_mul]
    exact Biset.Hom.ofFunction_single _ _ _ _
  have commute : (Biset.insertLeftUnit X Complex).vertical
      ((Biset.Hom.id (Biset.regular G)).horizontal f) =
      f.vertical (Biset.insertLeftUnit Y Complex) := by
    apply Biset.Hom.ext
    apply LinearMap.ext
    intro w
    change (((Biset.Hom.id (Biset.regular G)).horizontal f).toLinearMap
        ((Biset.insertLeftUnit X Complex).toLinearMap w)) =
      (Biset.insertLeftUnit Y Complex).toLinearMap (f.toLinearMap w)
    rw [h, h, Biset.Hom.horizontal_pairLinear]
    rfl
  rw [commute, Biset.Hom.vertical_assoc, Biset.insertLeftUnit_leftUnit, Biset.Hom.vertical_id]

theorem pad_right_eval {X Y : Biset G K} (f : Biset.Hom Complex X Y) :
    ((Biset.insertRightUnit X Complex).vertical
      (f.horizontal (Biset.Hom.id (Biset.regular K)))).vertical
        (Biset.rightUnit Y Complex) = f := by
  have h (Z : Biset G K) (w : Z.carrier →₀ Complex) :
      (Biset.insertRightUnit Z Complex).toLinearMap w =
        Biset.pairLinear Complex Z (Biset.regular K) w (Finsupp.single 1 1) := by
    change (Biset.insertRightUnit Z Complex).toLinearMap w =
      ((Biset.pairLinear Complex Z (Biset.regular K)).flip (Finsupp.single 1 1)) w
    apply LinearMap.congr_fun
    apply Finsupp.lhom_ext
    intro z c
    change (Biset.insertRightUnit Z Complex).toLinearMap (Finsupp.single z c) =
      Biset.pairLinear Complex Z (Biset.regular K) (Finsupp.single z c) (Finsupp.single 1 1)
    rw [Biset.pairLinear_single, mul_one]
    exact Biset.Hom.ofFunction_single _ _ _ _
  have commute : (Biset.insertRightUnit X Complex).vertical
      (f.horizontal (Biset.Hom.id (Biset.regular K))) =
      f.vertical (Biset.insertRightUnit Y Complex) := by
    apply Biset.Hom.ext
    apply LinearMap.ext
    intro w
    change ((f.horizontal (Biset.Hom.id (Biset.regular K))).toLinearMap
        ((Biset.insertRightUnit X Complex).toLinearMap w)) =
      (Biset.insertRightUnit Y Complex).toLinearMap (f.toLinearMap w)
    rw [h, h, Biset.Hom.horizontal_pairLinear]
    rfl
  rw [commute, Biset.Hom.vertical_assoc, Biset.insertRightUnit_rightUnit, Biset.Hom.vertical_id]

def boundaryDirs : {G K : Subgroup U} → Boundary G K → List Bool
  | _, _, .empty _ => []
  | _, _, .cons (.up _) rest => true :: boundaryDirs rest
  | _, _, .cons (.down _) rest => false :: boundaryDirs rest

theorem boundaryDirs_append (p : Boundary G H) (q : Boundary H K) :
    boundaryDirs (p.append q) = boundaryDirs p ++ boundaryDirs q := by
  induction p with
  | empty => rfl
  | cons s rest ih => cases s <;> simp only [Boundary.append, boundaryDirs, ih, List.cons_append]

theorem word_boundaryDirs (p : Word G K) : boundaryDirs p.boundary = p.directions := by
  induction p with
  | empty | up | down => rfl
  | tensor p q hp hq => simp only [Word.boundary, Word.directions, boundaryDirs_append, hp, hq]

theorem append_singleton {x y : PlanarCode.Code} {v : PlanarEvent}
    (h : x ++ y = [v]) : (x = [] ∧ y = [v]) ∨ (x = [v] ∧ y = []) := by
  cases x with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons w xs =>
    have ⟨hw, ht⟩ := List.cons.inj h
    have ⟨hx, hy⟩ := List.append_eq_nil_iff.mp ht
    exact Or.inr ⟨by rw [hw, hx], hy⟩

theorem shift_eq_nil {n : Nat} {x : PlanarCode.Code}
    (h : PlanarCode.shift n x = []) : x = [] := by
  cases x with
  | nil => rfl
  | cons e es => cases h

private theorem expanded_no_singleton_merge (n : Nat) (opening : ProjectionOpening)
    (closing : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry n opening closing) ≠ [join 0] := by
  cases opening <;>
    simp only [DrawingShape.expandedProjectionGeometry, encode_stack]
  all_goals
    intro h
    have hh := congrArg List.head? h
    cases hh

private theorem straightAt_of_eq {p q : Boundary G K} {f : MergeBoundaryMap p q}
    (h : p = q)
    (he : cast (congrArg (fun b => MergeBoundaryMap p b) h.symm) f = Biset.Hom.id _) :
    StraightAt p q f := by
  subst q
  change f = Biset.Hom.id _ at he
  subst f
  exact StraightAt.id p


end CaseTwoStructural
namespace CaseTwoStructural

open MackeyDiagrams

universe u
variable {U : Type u} [Group U]

private theorem transport_id_eq_boundaryId {G K : Subgroup U}
    {P Q : Boundary G K} (h : P = Q) :
    CaseTwoBoundaryCoherence.transport h
      (Biset.Hom.id (R := Complex) P.word.basis) = boundaryId h := by
  subst Q
  rfl

private theorem cast_boundaryId {G K : Subgroup U} {P Q : Boundary G K} (h : P = Q) :
    cast (congrArg (fun b => BoundaryMap P b) h.symm) (boundaryId h) =
      Biset.Hom.id (R := Complex) P.word.basis := by
  subst Q
  rfl

theorem dot_empty_coherence : EmptyCodeCoherence U := by
  intro G K p q d h
  obtain ⟨he, hev⟩ := empty_geometry_atBoundary d h
  exact ⟨he, hev.trans (transport_id_eq_boundaryId he)⟩

theorem merge_empty_coherence : EmptyCodeStraight U := by
  intro G K p q d h
  obtain ⟨he, hev⟩ := dot_empty_coherence (U := U) d h
  apply straightAt_of_eq he
  change cast _ (canon d.interpret.eval) = _
  rw [hev]
  exact cast_boundaryId he

end CaseTwoStructural

namespace CaseTwoFirstStage

open MackeyDiagrams Biset.Hom
set_option linter.unusedSimpArgs false
open CaseTwoStructural (code diagram_code_vert diagram_code_horiz drawing_code_vert
  drawing_code_horiz boundaryDirections boundaryDirections_word
  Wire Wire.eval Wire.directions
  Framed Framed.self Framed.boundaries Framed.canonical Framed.vertLeft
  Framed.vertRight Framed.horizontal Framed.trans frameStraight stripLeft stripRight
  splitSingleton shiftEmpty shift_zero encode_stack)

universe u
variable {U : Type u} [Group U] {K H J P : Subgroup U}

private theorem coherence : CaseTwoStructural.EmptyCodeCoherence U :=
  fun d h => CaseTwoStructural.empty_geometry_atBoundary d h

private abbrev inputPair (a : ConjEmbedding K P) (b : ConjEmbedding H P) :=
  (Word.down a).tensor (.up b)

private abbrev outputPair (r : ConjEmbedding P K) (s : ConjEmbedding P H) :=
  (Word.up r).tensor (.down s)

private def cross (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    {B : Subgroup U} (r : ConjEmbedding B K) (s : ConjEmbedding B H)
    (ts : List (Complex × ProjectionDot.Mixed a b r s)) :=
  LabelledDrawing.compactProjection a b r s ts

private def straight (p : Word K H) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private inductive Core : {K H : Subgroup U} → Word K H → Word K H → Type u
  | atom {K H P B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P) (r : ConjEmbedding B K) (s : ConjEmbedding B H)
      (ts : List (Complex × ProjectionDot.Mixed a b r s)) :
      Core (inputPair a b) (outputPair r s)
  | tail {K H J P B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P) (r : ConjEmbedding B K) (s : ConjEmbedding B H)
      (ts : List (Complex × ProjectionDot.Mixed a b r s)) (t : Strand H J) :
      Core ((inputPair a b).tensor t.word) ((outputPair r s).tensor t.word)

private def Core.drawing {p q : Word K H} : Core p q → LabelledDrawing Complex p q
  | .atom a b r s ts => cross a b r s ts
  | .tail a b r s ts t => (cross a b r s ts).horizontal (straight t.word)

private theorem Core.width {p q : Word K H} (d : Core p q) :
    2 ≤ p.directions.length := by
  cases d with
  | atom => exact Nat.le_refl 2
  | tail _ _ _ _ _ t => cases t <;> exact Nat.le_succ 2

private inductive Short : {K H : Subgroup U} → Word K H → Type u
  | empty (K : Subgroup U) : Short (.empty K)
  | one {K H : Subgroup U} (s : Strand K H) : Short s.word

private theorem shortBoundary (p : Boundary K H) (h : (boundaryDirections p).length ≤ 1) :
    ∃ q : Word K H, Nonempty (Short q) ∧ p = q.boundary := by
  cases p with
  | empty => exact ⟨_, ⟨.empty _⟩, rfl⟩
  | cons s t =>
    cases t with
    | empty =>
      cases s with
      | up a => exact ⟨.up a, ⟨.one (.up a)⟩, rfl⟩
      | down a => exact ⟨.down a, ⟨.one (.down a)⟩, rfl⟩
    | cons s' t => cases s <;> cases s' <;> simp [boundaryDirections] at h

private theorem emptyBoundary (p : Boundary K H) (h : (boundaryDirections p).length = 0) :
    ∃ e : K = H, p = e ▸ Boundary.empty K := by
  cases p with
  | empty => exact ⟨rfl, rfl⟩
  | cons s t => cases s <;> simp [boundaryDirections] at h

private def Normal {p q : Word K H} (f : Biset.Hom Complex p.basis q.basis) : Prop :=
  ∃ (p' q' : Word K H) (x : Core p' q'),
    Framed (p := p) (q := q) f x.drawing.interpret.eval

private theorem Core.withTail {p q : Word K H} (d : Core p q) {t : Word H J}
    (s : Short t) (hw : (p.directions ++ t.directions).length ≤ 3) :
    Normal (p := p.tensor t) (q := q.tensor t)
      (d.drawing.interpret.eval.horizontal (Biset.Hom.id t.basis)) := by
  cases s with
  | empty => exact ⟨_, _, d, stripRight _⟩
  | one t =>
    cases d with
    | atom a b r s ts => exact ⟨_, _, .tail a b r s ts t, Framed.self _⟩
    | tail a b r s ts z => cases z <;> cases t <;> simp [Strand.word, Word.directions] at hw

private theorem normalTail {p q : Word K H} {r s : Word H J}
    {f : Biset.Hom Complex p.basis q.basis} (hn : Normal (p := p) (q := q) f)
    (w : Wire r s) (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor s) (f.horizontal (Wire.eval w)) := by
  obtain ⟨p', q', d, hd⟩ := hn
  have hp : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using
      congrArg boundaryDirections (Framed.boundaries coherence hd).1
  rw [hp, List.length_append] at hw
  have hr : r.directions.length ≤ 1 := by have := d.width; omega
  obtain ⟨t, ⟨st⟩, ht⟩ := shortBoundary r.boundary (by rwa [boundaryDirections_word])
  have ht' : r.directions = t.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections ht
  obtain ⟨x, y, z, hz⟩ := d.withTail st (by rw [List.length_append, ← ht']; exact hw)
  exact ⟨x, y, z, Framed.trans (Framed.horizontal hd (frameStraight coherence w ht)) hz⟩

private theorem normalPrefix {p q : Word K H} {r s : Word H J}
    (w : Wire p q) (hw : q.directions.length = 0)
    {f : Biset.Hom Complex r.basis s.basis} (hn : Normal (p := r) (q := s) f) :
    Normal (p := p.tensor r) (q := q.tensor s) ((Wire.eval w).horizontal f) := by
  have hp : p.directions.length = 0 := by rwa [Wire.directions coherence w]
  obtain ⟨e, he⟩ := emptyBoundary p.boundary (by rwa [boundaryDirections_word])
  subst H
  obtain ⟨x, y, z, hz⟩ := hn
  have hi := frameStraight coherence (r := Word.empty K) w he
  exact ⟨x, y, z, Framed.trans (Framed.horizontal hi hz) (stripLeft _)⟩

private abbrev mark : PlanarEvent := .vertex 0 .mixedProjection

private theorem splitShift {n : Nat} {c : PlanarCode.Code} (h : PlanarCode.shift n c = [mark]) :
    n = 0 ∧ c = [mark] := by
  cases c with
  | nil => simp [PlanarCode.shift] at h
  | cons e es =>
    have hpos := congrArg PlanarEvent.position (List.cons.inj h).1
    have placePos : (e.place (n + e.position)).position = n + e.position := by
      cases e <;> rfl
    change (e.place (n + e.position)).position = 0 at hpos
    rw [placePos] at hpos
    have hn : n = 0 := by omega
    subst n
    exact ⟨rfl, (shift_zero _).symm.trans h⟩

private theorem verticalStep {p q t : Word K H}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q t)
    (h : CaseTwoStructural.code d.erase ++ CaseTwoStructural.code e.erase = [mark]) (hw : p.directions.length ≤ 3)
    (hd : CaseTwoStructural.code d.erase = [mark] → p.directions.length ≤ 3 → Normal (p := p) (q := q) d.interpret.eval)
    (he : CaseTwoStructural.code e.erase = [mark] → q.directions.length ≤ 3 → Normal (p := q) (q := t) e.interpret.eval) :
    Normal (p := p) (q := t) (d.vertical e).interpret.eval := by
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · let w : Wire p q := ⟨d, hd0⟩
    obtain ⟨x, y, z, hz⟩ := he he1 (by rwa [← Wire.directions coherence w])
    exact ⟨x, y, z, Framed.vertLeft w hz⟩
  · obtain ⟨x, y, z, hz⟩ := hd hd1 hw
    exact ⟨x, y, z, Framed.vertRight ⟨e, he0⟩ hz⟩

private theorem horizontalStep {p q : Word K H} {r s : Word H J}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex r s)
    (h : CaseTwoStructural.code d.erase ++ PlanarCode.shift q.directions.length (CaseTwoStructural.code e.erase) = [mark])
    (hw : (p.directions ++ r.directions).length ≤ 3)
    (hd : CaseTwoStructural.code d.erase = [mark] → p.directions.length ≤ 3 → Normal (p := p) (q := q) d.interpret.eval)
    (he : CaseTwoStructural.code e.erase = [mark] → r.directions.length ≤ 3 → Normal (p := r) (q := s) e.interpret.eval) :
    Normal (p := p.tensor r) (q := q.tensor s) (d.horizontal e).interpret.eval := by
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · obtain ⟨hz, he1⟩ := splitShift he1
    exact normalPrefix ⟨d, hd0⟩ hz (he he1 (by rw [List.length_append] at hw; omega))
  · exact normalTail (hd hd1 (by rw [List.length_append] at hw; omega)) ⟨e, shiftEmpty he0⟩ hw

private theorem eval_atom {B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (r : ConjEmbedding B K) (s : ConjEmbedding B H)
    (d : Dot (a.comp r) (b.comp s))
    (hf : ∀ y, Set.Finite {x | Generator.mixedMultiplicationBasis a b r s d x = y}) :
    (Diagram.mixedProjection (R := Complex) a b r s d hf).eval =
      (cross a b r s [(1, ⟨d, hf⟩)]).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change _ = (ScopedDiagram.linearCombination
    [(1, .ordinary (.mixedProjection a b r s d hf))]).eval.toLinearMap z
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp [ScopedDiagram.eval]

private theorem ordinaryNormal {p q : Word K H} (d : Diagram Complex p q) :
    CaseTwoStructural.code d.drawing = [mark] → p.directions.length ≤ 3 →
      Normal (p := p) (q := q) d.eval := by
  induction d <;> intro h hw
  case vertical d e hd he =>
    rw [diagram_code_vert] at h
    exact verticalStep (.ordinary d) (.ordinary e) h hw hd he
  case horizontal d e hd he =>
    rw [diagram_code_horiz] at h
    exact horizontalStep (.ordinary d) (.ordinary e) h hw hd he
  case mixedProjection a b r s d hf =>
    refine ⟨_, _, .atom a b r s [(1, ⟨d, hf⟩)], ?_⟩
    rw [eval_atom]
    exact Framed.self (cross a b r s [(1, ⟨d, hf⟩)]).interpret.eval
  all_goals
    simp [CaseTwoStructural.code, mark, Diagram.drawing, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h

private theorem expandedNotMark (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry n o c) ≠ [mark] := by
  unfold DrawingShape.expandedProjectionGeometry
  rw [encode_stack]
  cases o <;> simp [DrawingShape.stack, PlanarCode.encode, PlanarCode.shift,
    DrawingShape.outputs, VertexKind.outputs, VertexKind.canonical, PlanarEvent.place,
    PlanarEvent.position, mark]

private theorem drawingNormal {p q : Word K H} (d : LabelledDrawing Complex p q) :
    CaseTwoStructural.code d.erase = [mark] → p.directions.length ≤ 3 →
      Normal (p := p) (q := q) d.interpret.eval := by
  induction d <;> intro h hw
  case ordinary d => exact ordinaryNormal d h hw
  case vertical d e hd he =>
    rw [drawing_code_vert] at h
    exact verticalStep d e h hw hd he
  case horizontal d e hd he =>
    rw [drawing_code_horiz] at h
    exact horizontalStep d e h hw hd he
  case compactProjection a b r s ts =>
    exact ⟨_, _, .atom a b r s ts, Framed.self (cross a b r s ts).interpret.eval⟩
  case trivalent v => cases v <;> simp [CaseTwoStructural.code, LabelledDrawing.erase, DrawingShape.geometry,
    PlanarCode.encode, VertexKind.canonical, TrivalentVertex.kind, mark] at h
  case bentVertex v => cases v <;> simp [CaseTwoStructural.code, LabelledDrawing.erase, DrawingShape.geometry,
    PlanarCode.encode, VertexKind.canonical, BentVertex.kind, mark] at h
  case parallelUpChain labels =>
    change PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack _) = _ at h
    rw [encode_stack] at h
    simp [mark, PlanarCode.encode, VertexKind.canonical] at h
  case parallelDownChain labels =>
    change PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack _) = _ at h
    rw [encode_stack] at h
    simp [mark, PlanarCode.encode, VertexKind.canonical] at h
  case expandedProjection _ _ _ _ _ o c => exact False.elim (expandedNotMark 1 o c h)
  case expandedProjectionChain _ _ _ _ labels _ o c =>
    exact False.elim (expandedNotMark labels.length o c h)
  case expandedLinearDotProjection _ _ _ _ labels _ o c =>
    exact False.elim (expandedNotMark labels.length o c h)
  case rightCurlUp =>
    simp [CaseTwoStructural.code, LabelledDrawing.erase, DrawingShape.geometry, DrawingShape.rightCurlGeometry,
      DrawingShape.stack, PlanarCode.encode, VertexKind.canonical, PlanarCode.shift,
      DrawingShape.outputs, PlanarEvent.place, PlanarEvent.position, mark] at h
  all_goals
    simp [CaseTwoStructural.code, mark, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h

private theorem sameInput {M M' N N' : Subgroup U}
    (a : ConjEmbedding K M) (b : ConjEmbedding N M) (c : Strand N H)
    (a' : ConjEmbedding K M') (b' : ConjEmbedding N' M') (c' : ConjEmbedding H N')
    (h : ((inputPair a b).tensor c.word).boundary =
      ((inputPair a' b').tensor (.up c')).boundary) :
    ∃ _e : M = M', ∃ _e' : N = N',
      HEq a a' ∧ HEq b b' ∧ HEq c (.up c' : Strand N' H) := by
  cases c with
  | up c =>
    change Boundary.cons (.down a) (.cons (.up b) (.cons (.up c) (.empty H))) =
      Boundary.cons (.down a') (.cons (.up b') (.cons (.up c') (.empty H))) at h
    injection h with _ hm _ ha ht
    subst M'
    have haa : a = a' := by injection ha
    have ht' := eq_of_heq ht
    injection ht' with _ hn _ hb hu
    subst N'
    have hbb : b = b' := by injection hb
    have hu' := eq_of_heq hu
    injection hu' with _ _ _ hc _
    exact ⟨rfl, rfl, heq_of_eq haa, heq_of_eq hbb, heq_of_eq hc⟩
  | down c =>
    change Boundary.cons (.down a) (.cons (.up b) (.cons (.down c) (.empty H))) =
      Boundary.cons (.down a') (.cons (.up b') (.cons (.up c') (.empty H))) at h
    injection h with _ hm _ _ ht
    subst M'
    have ht' := eq_of_heq ht
    injection ht' with _ hn _ _ hu
    subst N'
    have hu' := eq_of_heq hu
    injection hu' with _ _ _ hc _
    injection hc

private abbrev BMap (p q : Boundary K H) :=
  Biset.Hom Complex p.word.basis q.word.basis

/-- Transport along the recovered equality of the ordered source and target. -/
def castBoundary {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (f : BMap p q) : BMap p' q' := by
  cases hp
  cases hq
  exact f

private theorem castBoundary_eq {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (f : BMap p q) (g : BMap p' q') (h : HEq f g) : castBoundary hp hq f = g := by
  cases hp
  cases hq
  exact eq_of_heq h

set_option maxHeartbeats 800000 in
/-- The exact leftmost projection stage, with the third strand fixed by the input boundary. -/
theorem normalizeFirst {M N : Subgroup U} (a : ConjEmbedding K M) (b : ConjEmbedding N M)
    (c : ConjEmbedding H N) {p q : Word K H} (d : LabelledDrawing Complex p q)
    (hc : PlanarCode.encode d.erase.geometry = [.vertex 0 .mixedProjection])
    (hp : p.boundary = ((inputPair a b).tensor (.up c)).boundary) :
    ∃ (B : Subgroup U) (r : ConjEmbedding B K) (s : ConjEmbedding B N)
      (ts : List (Complex × ProjectionDot.Mixed a b r s))
      (hq : q.boundary = ((outputPair r s).tensor (.up c)).boundary),
      castBoundary hp hq d.interpret.atBoundary.eval =
        ((LabelledDrawing.compactProjection a b r s ts).horizontal
          (.ordinary (.id (.up c)))).interpret.atBoundary.eval := by
  have hw : p.directions.length = 3 := by
    have hd := congrArg boundaryDirections hp
    simpa [boundaryDirections_word, Word.directions] using congrArg List.length hd
  obtain ⟨v, w, x, hx⟩ := drawingNormal d hc (Nat.le_of_eq hw)
  obtain ⟨hv, hq⟩ := Framed.boundaries coherence hx
  have hcanon := Framed.canonical coherence hx
  have hd := hv.symm.trans hp
  cases x with
  | atom a₀ b₀ r s ts =>
    have bad := congrArg (List.length ∘ boundaryDirections) hd
    simp [Function.comp_apply, boundaryDirections_word, Word.directions] at bad
  | tail a₀ b₀ r s ts t =>
    obtain ⟨hM, hN, ha, hb, ht⟩ := sameInput a₀ b₀ t a b c hd
    cases hM
    cases hN
    cases eq_of_heq ha
    cases eq_of_heq hb
    cases eq_of_heq ht
    refine ⟨_, r, s, ts, hq, ?_⟩
    apply castBoundary_eq
    exact hcanon

/-- Combine repeated projection entries by adding their complex coefficients. -/
noncomputable def collectProjection {X : Type u} (ts : List (Complex × X)) : X →₀ Complex :=
  (ts.map fun (z, x) => Finsupp.single x z).sum

private theorem eval_collect {X : Type u} {Y : Type*} [AddCommMonoid Y] [Module Complex Y]
    (f : X → Y) (ts : List (Complex × X)) :
    freeLift Complex f (collectProjection ts) = (ts.map fun t => t.1 • f t.2).sum := by
  induction ts with
  | nil => simp [collectProjection]
  | cons t ts ih =>
    rcases t with ⟨z, x⟩
    change freeLift Complex f (Finsupp.single x z + collectProjection ts) = _
    rw [map_add, freeLift_single, ih]
    rfl

/-- Evaluation factors through the collected coefficients, including repeated and cancelling terms. -/
theorem eval_collectProjection {B : Subgroup U} (a : ConjEmbedding K P) (b : ConjEmbedding H P)
    (r : ConjEmbedding B K) (s : ConjEmbedding B H)
    (ts : List (Complex × ProjectionDot.Mixed a b r s))
    (z : (inputPair a b).basis.carrier →₀ Complex) :
    (LabelledDrawing.compactProjection a b r s ts).interpret.eval.toLinearMap z =
      freeLift Complex
        (fun x : ProjectionDot.Mixed a b r s =>
          (Diagram.mixedProjection (R := Complex) a b r s x.dot x.finite).eval.toLinearMap z)
        (collectProjection ts) := by
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply, eval_collect, List.map_map]
  rfl

end CaseTwoFirstStage

namespace CaseTwoAudit

open MackeyDiagrams

/-- Normalize stage one of the exact left Case 2 drawing. -/
theorem first_stage_at_boundary {p q : Word G F} (drawing : LabelledDrawing Complex p q)
    (h : PlanarCode.encode drawing.erase.geometry = [.vertex 0 .mixedProjection])
    (hp : p.boundary = bottom.boundary) :
    ∃ (B : Subgroup U) (r : ConjEmbedding B G) (s : ConjEmbedding B D)
      (xs : List (Complex × ProjectionDot.Mixed a b r s))
      (hq : q.boundary = (tensor (tensor (up r) (down s)) (up c)).boundary),
      CaseTwoFirstStage.castBoundary hp hq drawing.interpret.atBoundary.eval =
        (((LabelledDrawing.compactProjection a b r s xs).horizontal
          (drawId (up c))).interpret.atBoundary).eval :=
  CaseTwoFirstStage.normalizeFirst a b c drawing h hp

end CaseTwoAudit


set_option maxHeartbeats 2000000

namespace CaseTwoStage
open CaseTwoFactor (drawing_code_vert drawing_code_horiz diagram_code_vert diagram_code_horiz encode_stack no_expandedProjection goodCode isCompactCrossing)
open CaseTwoStructural (Wire Wire.eval Wire.boundary Wire.directions Framed Framed.self Framed.vertLeft
  Framed.vertRight Framed.horizontal Framed.trans Framed.boundaries Framed.canonical
  canon canon_vertical frameStraight stripLeft stripRight dot_empty_coherence boundaryDirections
  boundaryDirections_word splitSingleton shiftEmpty
 )


open MackeyDiagrams Biset.Hom
universe u
variable {U : Type u} [Group U] {A B C D : Subgroup U}

private inductive ShortWord : {A B : Subgroup U} → Word A B → Type u
  | empty (A : Subgroup U) : ShortWord (.empty A)
  | strand {A B : Subgroup U} (s : Strand A B) : ShortWord s.word

private theorem shortBoundary (p : Boundary A B) (h : (boundaryDirections p).length ≤ 1) :
    ∃ r : Word A B, Nonempty (ShortWord r) ∧ p = r.boundary := by
  cases p with
  | empty => exact ⟨.empty _, ⟨.empty _⟩, rfl⟩
  | cons s t =>
    cases t with
    | empty => exact ⟨s.word, ⟨.strand s⟩, by cases s <;> rfl⟩
    | cons t rest => cases s <;> cases t <;> simp [boundaryDirections] at h

private inductive Atom : {A B : Subgroup U} → VertexKind → Word A B → Word A B → Type u
  | project {K H G L : Subgroup U}
      (a : ConjEmbedding K G) (b : ConjEmbedding H G) (l : ConjEmbedding L K)
      (r : ConjEmbedding L H) (xs : List (Complex × ProjectionDot.Mixed a b l r)) :
      Atom .mixedProjection ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r))
  | parallel {K H H' G : Subgroup U}
      (b : ConjEmbedding H G) (a : ConjEmbedding K H)
      (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
      (zs : List (Complex × Dot (b.comp a) (b'.comp a'))) :
      Atom .parallelUp ((Word.up b).tensor (.up a)) ((Word.up b').tensor (.up a'))

private abbrev drawingId (p : Word A B) : LabelledDrawing Complex p p := .ordinary (.id p)

private def Atom.drawing {k : VertexKind} {p q : Word A B} :
    Atom k p q → LabelledDrawing Complex p q
  | .project a b l r xs => .compactProjection a b l r xs
  | .parallel b a b' a' zs => .parallelUp b a b' a' zs

private theorem Atom.width {k : VertexKind} {p q : Word A B} (a : Atom k p q) :
    p.directions.length = 2 := by cases a <;> rfl

private inductive Core : {A B : Subgroup U} → VertexKind → Nat →
    Word A B → Word A B → Type u
  | bare {A B : Subgroup U} {k : VertexKind} {p q : Word A B} (a : Atom k p q) : Core k 0 p q
  | left {A B C : Subgroup U} {k : VertexKind} {p q : Word B C} (s : Strand A B) (a : Atom k p q) :
      Core k 1 (s.word.tensor p) (s.word.tensor q)
  | right {A B C : Subgroup U} {k : VertexKind} {p q : Word A B} (a : Atom k p q) (s : Strand B C) :
      Core k 0 (p.tensor s.word) (q.tensor s.word)

private def Core.drawing {k : VertexKind} {n : Nat} {p q : Word A B} :
    Core k n p q → LabelledDrawing Complex p q
  | .bare a => a.drawing
  | .left s a => (drawingId s.word).horizontal a.drawing
  | .right a s => a.drawing.horizontal (drawingId s.word)

private theorem strandWidth (s : Strand A B) : s.word.directions.length = 1 := by cases s <;> rfl

private theorem Core.width {k : VertexKind} {n : Nat} {p q : Word A B} (c : Core k n p q) :
    2 ≤ p.directions.length := by
  cases c with
  | bare a => rw [a.width]
  | left s a => simp [Word.directions, strandWidth, a.width]
  | right a s => simp [Word.directions, strandWidth, a.width]

private def Normal {p q : Word A B} (k : VertexKind) (n : Nat)
    (f : Biset.Hom Complex p.basis q.basis) : Prop :=
  ∃ (r s : Word A B) (c : Core k n r s), Framed (p := p) (q := q) f c.drawing.interpret.eval

private theorem ShortWord.padLeft {k : VertexKind} {n : Nat} {p : Word A B}
    {r s : Word B C} (w : ShortWord p) (c : Core k n r s)
    (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := p.tensor s) k (p.directions.length + n)
      ((Biset.Hom.id p.basis).horizontal c.drawing.interpret.eval) := by
  cases w with
  | empty =>
    simp only [Word.directions, List.length_nil, Nat.zero_add]
    exact ⟨_, _, c, stripLeft _⟩
  | strand t =>
    rw [strandWidth]
    cases c with
    | bare a => exact ⟨_, _, .left t a, Framed.self _⟩
    | left t' a => simp [Word.directions, strandWidth, a.width] at hw
    | right a t' => simp [Word.directions, strandWidth, a.width] at hw

private theorem ShortWord.padRight {k : VertexKind} {n : Nat} {p q : Word A B}
    {r : Word B C} (c : Core k n p q) (w : ShortWord r)
    (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor r) k n
      (c.drawing.interpret.eval.horizontal (Biset.Hom.id r.basis)) := by
  cases w with
  | empty => exact ⟨_, _, c, stripRight _⟩
  | strand t =>
    cases c with
    | bare a => exact ⟨_, _, .right a t, Framed.self _⟩
    | left t' a => simp [Word.directions, strandWidth, a.width] at hw
    | right a t' => simp [Word.directions, strandWidth, a.width] at hw

private theorem padLeft {k : VertexKind} {n : Nat}
    {p q : Word A B} {r s : Word B C} (d : Wire p q)
    {f : Biset.Hom Complex r.basis s.basis} (h : Normal (p := r) (q := s) k n f)
    (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor s) k (q.directions.length + n)
      ((Wire.eval d).horizontal f) := by
  let hc : CaseTwoStructural.EmptyCodeCoherence U := dot_empty_coherence
  obtain ⟨r', s', c, hf⟩ := h
  have hr : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (Framed.boundaries hc hf).1
  have hp : p.directions.length ≤ 1 := by
    rw [List.length_append, hr] at hw
    have := c.width
    omega
  obtain ⟨p', ⟨w⟩, hb⟩ := shortBoundary p.boundary (by rwa [boundaryDirections_word])
  have hp' : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  rw [← Wire.directions hc d, hp']
  rw [hp', hr] at hw
  obtain ⟨v, z, c', h'⟩ := w.padLeft c hw
  exact ⟨v, z, c', Framed.trans (Framed.horizontal (frameStraight hc d hb) hf) h'⟩

private theorem padRight {k : VertexKind} {n : Nat}
    {p q : Word A B} {r s : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} (h : Normal (p := p) (q := q) k n f)
    (d : Wire r s) (hw : (p.directions ++ r.directions).length ≤ 3) :
    Normal (p := p.tensor r) (q := q.tensor s) k n (f.horizontal (Wire.eval d)) := by
  let hc : CaseTwoStructural.EmptyCodeCoherence U := dot_empty_coherence
  obtain ⟨p', q', c, hf⟩ := h
  have hp : p.directions = p'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections (Framed.boundaries hc hf).1
  have hr : r.directions.length ≤ 1 := by
    rw [List.length_append, hp] at hw
    have := c.width
    omega
  obtain ⟨r', ⟨w⟩, hb⟩ := shortBoundary r.boundary (by rwa [boundaryDirections_word])
  have hr' : r.directions = r'.directions := by
    simpa only [boundaryDirections_word] using congrArg boundaryDirections hb
  rw [hp, hr'] at hw
  obtain ⟨v, z, c', h'⟩ := w.padRight c hw
  exact ⟨v, z, c', Framed.trans (Framed.horizontal hf (frameStraight hc d hb)) h'⟩

private theorem shiftSingleton {k : VertexKind} {i n : Nat} {c : PlanarCode.Code}
    (h : PlanarCode.shift i c = [.vertex n k]) :
    ∃ m : Nat, c = [.vertex m k] ∧ i + m = n := by
  cases c with
  | nil => simp [PlanarCode.shift] at h
  | cons e es =>
    have ht := congrArg List.length h
    simp only [PlanarCode.shift, List.length_map, List.length_cons, List.length_nil] at ht
    have hz : es = [] := List.length_eq_zero_iff.mp (by omega)
    subst es
    cases e <;> simp [PlanarCode.shift, PlanarEvent.place, PlanarEvent.position] at h
    next m k' =>
      obtain ⟨hm, rfl⟩ := h
      exact ⟨m, rfl, hm⟩

private def Supported (k : VertexKind) : Prop := k = .mixedProjection ∨ k = .parallelUp

private abbrev Normalizes {p q : Word A B} (d : LabelledDrawing Complex p q) (k : VertexKind) :=
  ∀ n, CaseTwoFactor.code d.erase = [.vertex n k] → p.directions.length ≤ 3 →
    Normal (p := p) (q := q) k n d.interpret.eval

private theorem normalVertical {k : VertexKind} {p q r : Word A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r)
    (hd : Normalizes d k) (he : Normalizes e k) : Normalizes (d.vertical e) k := by
  intro n h hw
  rw [drawing_code_vert] at h
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · let w : Wire p q := ⟨d, hd0⟩
    have hew : q.directions.length ≤ 3 := by rw [← Wire.directions dot_empty_coherence w]; exact hw
    obtain ⟨s, t, c, hf⟩ := he n he1 hew
    exact ⟨s, t, c, Framed.vertLeft w hf⟩
  · obtain ⟨s, t, c, hf⟩ := hd n hd1 hw
    exact ⟨s, t, c, Framed.vertRight ⟨e, he0⟩ hf⟩

private theorem normalHorizontal {k : VertexKind} {p q : Word A B} {r s : Word B C}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex r s)
    (hd : Normalizes d k) (he : Normalizes e k) : Normalizes (d.horizontal e) k := by
  intro n h hw
  rw [drawing_code_horiz] at h
  change (p.directions ++ r.directions).length ≤ 3 at hw
  have hw' := hw
  rw [List.length_append] at hw'
  rcases splitSingleton h with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
  · obtain ⟨m, hm, rfl⟩ := shiftSingleton he1
    exact padLeft ⟨d, hd0⟩ (he m hm (by omega)) hw
  · exact padRight (hd n hd1 (by omega)) ⟨e, shiftEmpty he0⟩ hw

private theorem ordinaryProjection_eval {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (x : ProjectionDot.Mixed a b l r) :
    (Diagram.mixedProjection (R := Complex) a b l r x.dot x.finite).eval =
      (LabelledDrawing.compactProjection a b l r [(1, x)]).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change _ = (ScopedDiagram.linearCombination
    [(1, ScopedDiagram.ordinary (.mixedProjection a b l r x.dot x.finite))]).eval.toLinearMap z
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul]
  rfl

private theorem ordinarySingleton {k : VertexKind} (hk : Supported k)
    {p q : Word A B} (d : Diagram Complex p q) : Normalizes (.ordinary d) k := by
  induction d
  case vertical d e hd he => exact normalVertical (.ordinary d) (.ordinary e) hd he
  case horizontal d e hd he => exact normalHorizontal (.ordinary d) (.ordinary e) hd he
  case mixedProjection a b l r x hf =>
    intro n h _
    have h' : (.vertex 0 .mixedProjection : PlanarEvent) = .vertex n k := (List.cons.inj h).1
    cases h'
    let z : ProjectionDot.Mixed a b l r := ⟨x, hf⟩
    refine ⟨_, _, .bare (.project a b l r [(1, z)]), ?_⟩
    change Framed (Diagram.mixedProjection (R := Complex) a b l r x hf).eval
      (LabelledDrawing.compactProjection a b l r [(1, z)]).interpret.eval
    rw [← ordinaryProjection_eval a b l r z]
    exact Framed.self _
  all_goals
    intro n h _
    rcases hk with rfl | rfl <;>
      simp [CaseTwoFactor.code, LabelledDrawing.erase, Diagram.drawing, DrawingShape.geometry,
        PlanarCode.encode, VertexKind.canonical] at h

private theorem expanded_no_mark {k : VertexKind} (hk : Supported k) (n count : Nat)
    (opening : ProjectionOpening) (closing : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry count opening closing) ≠
      [.vertex n k] := by
  intro h
  apply (no_expandedProjection count opening closing).elim
  rw [h]
  rcases hk with rfl | rfl <;> simp [goodCode, isCompactCrossing]

private theorem drawingSingleton {k : VertexKind} (hk : Supported k)
    {p q : Word A B} (d : LabelledDrawing Complex p q) : Normalizes d k := by
  induction d
  case ordinary d => exact ordinarySingleton hk d
  case vertical d e hd he => exact normalVertical d e hd he
  case horizontal d e hd he => exact normalHorizontal d e hd he
  case compactProjection a b l r xs =>
    intro n h _
    have h' : (.vertex 0 .mixedProjection : PlanarEvent) = .vertex n k := (List.cons.inj h).1
    cases h'
    exact ⟨_, _, .bare (.project a b l r xs), Framed.self _⟩
  case parallelUp b a b' a' zs =>
    intro n h _
    have h' : (.vertex 0 .parallelUp : PlanarEvent) = .vertex n k := (List.cons.inj h).1
    cases h'
    exact ⟨_, _, .bare (.parallel b a b' a' zs), Framed.self _⟩
  case trivalent v =>
    intro n h _
    cases v <;> rcases hk with rfl | rfl <;>
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode,
        VertexKind.canonical, TrivalentVertex.kind] at h
  case bentVertex v =>
    intro n h _
    cases v <;> rcases hk with rfl | rfl <;>
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode,
        VertexKind.canonical, BentVertex.kind] at h
  case parallelUpChain labels =>
    intro n h _
    change PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack _) = _ at h
    rw [encode_stack] at h
    rcases hk with rfl | rfl <;> simp [PlanarCode.encode, VertexKind.canonical] at h
  case parallelDownChain labels =>
    intro n h _
    change PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack _) = _ at h
    rw [encode_stack] at h
    rcases hk with rfl | rfl <;> simp [PlanarCode.encode, VertexKind.canonical] at h
  case rightCurlUp =>
    intro n h _
    rcases hk with rfl | rfl <;>
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, DrawingShape.rightCurlGeometry,
        DrawingShape.stack, PlanarCode.encode, VertexKind.canonical, PlanarCode.shift,
        DrawingShape.outputs, PlanarEvent.place, PlanarEvent.position] at h
  case expandedProjection _ _ _ _ xs opening closing =>
    intro n h _
    exact (expanded_no_mark hk n 1 opening closing h).elim
  case expandedProjectionChain _ _ _ _ xs _ opening closing =>
    intro n h _
    exact (expanded_no_mark hk n xs.length opening closing h).elim
  case expandedLinearDotProjection _ _ _ _ xs _ opening closing =>
    intro n h _
    exact (expanded_no_mark hk n xs.length opening closing h).elim
  all_goals
    intro n h _
    rcases hk with rfl | rfl <;>
      simp [CaseTwoFactor.code, LabelledDrawing.erase, DrawingShape.geometry, PlanarCode.encode, VertexKind.canonical] at h


abbrev upDownUp {G B D F : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) : Word G F :=
  ((Word.up r).tensor (.down s)).tensor (.up c)

abbrev upUpDown {G B L F : Subgroup U} (r : ConjEmbedding B G)
    (t : ConjEmbedding L B) (j : ConjEmbedding L F) : Word G F :=
  ((Word.up r).tensor (.up t)).tensor (.down j)

def rightProjection {G B D F L : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) (t : ConjEmbedding L B)
    (j : ConjEmbedding L F) (xs : List (Complex × ProjectionDot.Mixed s c t j)) :
    LabelledDrawing Complex (upDownUp r s c) (upUpDown r t j) :=
  LabelledDrawing.vertical (.ordinary (.associate (.up r) (.down s) (.up c)))
    (((drawingId (.up r)).horizontal (.compactProjection s c t j xs)).vertical
      (.ordinary (.unassociate (.up r) (.up t) (.down j))))

/-- Evaluate at the specified, ordered labelled boundaries. -/
noncomputable def evalAt {p q : Word A B} {P Q : Boundary A B}
    (d : LabelledDrawing Complex p q) (hp : p.boundary = P) (hq : q.boundary = Q) :
    Biset.Hom Complex P.word.basis Q.word.basis := by
  subst P
  subst Q
  exact d.interpret.atBoundary.eval

/-- Canonical evaluation composes at a shared labelled intermediate boundary. -/
theorem evalAt_vertical {p q v : Word A B} {P Q V : Boundary A B}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q v)
    (hp : p.boundary = P) (hq : q.boundary = Q) (hv : v.boundary = V) :
    evalAt (d.vertical e) hp hv = (evalAt d hp hq).vertical (evalAt e hq hv) := by
  cases hp
  cases hq
  cases hv
  exact canon_vertical d.interpret.eval e.interpret.eval

private theorem evalAt_heq {p q : Word A B} {P Q : Boundary A B}
    (d : LabelledDrawing Complex p q) (hp : p.boundary = P) (hq : q.boundary = Q) :
    HEq (evalAt d hp hq) (canon d.interpret.eval) := by
  cases hp
  cases hq
  rfl

private theorem rightProjection_canon {G B D F L : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) (t : ConjEmbedding L B)
    (j : ConjEmbedding L F) (xs : List (Complex × ProjectionDot.Mixed s c t j)) :
    HEq (canon (rightProjection r s c t j xs).interpret.eval)
      (canon ((drawingId (.up r)).horizontal
        (.compactProjection s c t j xs)).interpret.eval) := by
  let cross := (drawingId (.up r)).horizontal (.compactProjection s c t j xs)
  have h : Framed (rightProjection r s c t j xs).interpret.eval cross.interpret.eval :=
    ⟨⟨.ordinary (.associate (.up r) (.down s) (.up c)), rfl⟩,
     ⟨.ordinary (.unassociate (.up r) (.up t) (.down j)), rfl⟩, rfl⟩
  exact Framed.canonical dot_empty_coherence h

private theorem upDownUp_inj {G B B' D D' F : Subgroup U}
    {r : ConjEmbedding B G} {s : ConjEmbedding B D} {c : ConjEmbedding F D}
    {r' : ConjEmbedding B' G} {s' : ConjEmbedding B' D'} {c' : ConjEmbedding F D'}
    (h : (upDownUp r' s' c').boundary = (upDownUp r s c).boundary) :
    B' = B ∧ D' = D ∧ HEq r' r ∧ HEq s' s ∧ HEq c' c := by
  change Boundary.cons (.up r') (Boundary.cons (.down s') (Boundary.cons (.up c') (.empty F))) =
    Boundary.cons (.up r) (Boundary.cons (.down s) (Boundary.cons (.up c) (.empty F))) at h
  injection h with _ eB _ hr htail
  subst B'
  have ht := eq_of_heq htail
  injection ht with _ eD _ hs htail'
  subst D'
  have hlast := eq_of_heq htail'
  injection hlast with _ _ _ hc _
  have rr := eq_of_heq hr
  have ss := eq_of_heq hs
  have er : r' = r := by injection rr
  have es : s' = s := by injection ss
  have ec : c' = c := by injection hc
  exact ⟨rfl, rfl, heq_of_eq er, heq_of_eq es, heq_of_eq ec⟩

/-- Normalize stage two at the shared input and its actual ordered output.
Each retained list entry carries its termwise finite-fibre proof. -/
theorem secondStage {G B D F : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D) {p q : Word G F}
    (draw : LabelledDrawing Complex p q)
    (hcode : PlanarCode.encode draw.erase.geometry = [.vertex 1 .mixedProjection])
    (hin : p.boundary = (upDownUp r s c).boundary) :
    ∃ (L : Subgroup U) (t : ConjEmbedding L B) (j : ConjEmbedding L F)
      (ys : List (Complex × ProjectionDot.Mixed s c t j))
      (hout : (upUpDown r t j).boundary = q.boundary),
      evalAt draw hin rfl = evalAt (rightProjection r s c t j ys) rfl hout := by
  have hdirs : p.directions = [true, false, true] := by
    have hh := congrArg boundaryDirections hin
    rw [boundaryDirections_word] at hh
    exact hh
  have hwidth : p.directions.length ≤ 3 := by rw [hdirs]; decide
  obtain ⟨_, _, core, hf⟩ := drawingSingleton (.inl rfl) draw 1 hcode hwidth
  cases core with
  | left head atom =>
    obtain ⟨hb, ht⟩ := Framed.boundaries dot_empty_coherence hf
    cases atom with
    | project s' c' t j ys =>
      have hb' := hb.symm.trans hin
      cases head with
      | down r' =>
        have bad := congrArg boundaryDirections hb'
        change [false, false, true] = [true, false, true] at bad
        contradiction
      | up r' =>
        rename_i B' D' L
        obtain ⟨eB, eD, er, es, ec⟩ :=
          upDownUp_inj (r := r) (s := s) (c := c)
            (r' := r') (s' := s') (c' := c') hb'
        subst B'
        subst D'
        have er' := eq_of_heq er
        have es' := eq_of_heq es
        have ec' := eq_of_heq ec
        subst r'
        subst s'
        subst c'
        have hout : (upUpDown r t j).boundary = q.boundary := ht.symm
        refine ⟨_, t, j, ys, hout, ?_⟩
        exact eq_of_heq ((evalAt_heq draw hin rfl).trans
          ((Framed.canonical dot_empty_coherence hf).trans
            ((rightProjection_canon r s c t j ys).symm.trans
              (evalAt_heq (rightProjection r s c t j ys) rfl hout).symm)))


/-- Retain the actual last strand, including its starting subgroup and label. -/
def suffix : {G F : Subgroup U} → Boundary G F → Option (Σ L : Subgroup U, Strand L F)
  | _, _, .empty _ => none
  | _, _, .cons s (.empty _) => some ⟨_, s⟩
  | _, _, .cons _ (.cons t rest) => suffix (.cons t rest)

/-- A left parallel crossing on a three-strand input preserves the labelled suffix. -/
theorem parallelSuffix {p q : Word A B} (draw : LabelledDrawing Complex p q)
    (hcode : PlanarCode.encode draw.erase.geometry = [.vertex 0 .parallelUp])
    (hwidth : p.directions.length = 3) :
    suffix p.boundary = suffix q.boundary := by
  obtain ⟨_, _, core, hf⟩ :=
    drawingSingleton (.inr rfl) draw 0 hcode (by rw [hwidth])
  obtain ⟨hb, ht⟩ := Framed.boundaries dot_empty_coherence hf
  cases core with
  | bare atom =>
    have hd := congrArg (fun b => (boundaryDirections b).length) hb
    simp only [boundaryDirections_word, hwidth, atom.width] at hd
    contradiction
  | right atom s =>
    refine (congrArg suffix hb).trans (Eq.trans ?_ (congrArg suffix ht.symm))
    cases atom
    cases s <;> rfl

/-- The exact top boundary fixes both the common subgroup and the outgoing restriction. -/
theorem secondStage_fixedSuffix {G B D F C T : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (c : ConjEmbedding F D)
    (d : ConjEmbedding C G) (e : ConjEmbedding T C) (f : ConjEmbedding T F)
    {p q v : Word G F} (stage₂ : LabelledDrawing Complex p q)
    (stage₃ : LabelledDrawing Complex q v)
    (hc₂ : PlanarCode.encode stage₂.erase.geometry = [.vertex 1 .mixedProjection])
    (hc₃ : PlanarCode.encode stage₃.erase.geometry = [.vertex 0 .parallelUp])
    (hin : p.boundary = (upDownUp r s c).boundary)
    (htop : v.boundary = (upUpDown d e f).boundary) :
    ∃ (t : ConjEmbedding T B) (ys : List (Complex × ProjectionDot.Mixed s c t f))
      (hout : (upUpDown r t f).boundary = q.boundary),
      evalAt stage₂ hin rfl = evalAt (rightProjection r s c t f ys) rfl hout := by
  obtain ⟨L, t, j, ys, hout, heval⟩ := secondStage r s c stage₂ hc₂ hin
  have hwidth : q.directions.length = 3 := by
    have h := congrArg (fun b => (boundaryDirections b).length) hout.symm
    rw [boundaryDirections_word] at h
    exact h
  have hsuff := (congrArg suffix hout).trans
    ((parallelSuffix stage₃ hc₃ hwidth).trans (congrArg suffix htop))
  change some (⟨L, Strand.down j⟩ : Σ X : Subgroup U, Strand X F) =
    some ⟨T, Strand.down f⟩ at hsuff
  have hpair := Option.some.inj hsuff
  have hgroup : L = T := congrArg Sigma.fst hpair
  subst L
  have hstrand := eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
  have hj : j = f := by injection hstrand
  subst j
  exact ⟨t, ys, hout, heval⟩


end CaseTwoStage

open MackeyDiagrams
open CaseTwoStructural (code drawing_code_vert drawing_code_horiz diagram_code_vert diagram_code_horiz
  encode_stack shift_zero StraightAt normalize normalize_vertical normalize_horizontal
  normalize_id juxtaposeMap pad_left_eval pad_right_eval boundaryDirs boundaryDirs_append word_boundaryDirs
  append_singleton shift_eq_nil merge_empty_coherence straight_boundary_eq
 )

namespace CaseTwoStageThree

universe u
variable {V : Type u} [Group V]
variable {G H K J : Subgroup V}

private abbrev pair (r : ConjEmbedding H G) (t : ConjEmbedding K H) :=
  (Word.up r).tensor (.up t)

private abbrev HomAt (P Q : Boundary G K) :=
  Biset.Hom Complex P.word.basis Q.word.basis

private abbrev par (r : ConjEmbedding H G) (t : ConjEmbedding K H)
    (d : ConjEmbedding J G) (e : ConjEmbedding K J)
    (zs : List (Complex × Dot (r.comp t) (d.comp e))) :=
  LabelledDrawing.parallelUp r t d e zs

private abbrev IdDraw (p : Word G K) : LabelledDrawing Complex p p :=
  .ordinary (.id p)

private inductive Stage : (P Q : Boundary G K) → HomAt P Q → Prop
  | bare {B C : Subgroup V}
      (r : ConjEmbedding B G) (t : ConjEmbedding K B)
      (d : ConjEmbedding C G) (e : ConjEmbedding K C)
      (zs : List (Complex × Dot (r.comp t) (d.comp e))) :
      Stage (pair r t).boundary (pair d e).boundary (normalize (par r t d e zs).interpret)
  | tail {B C E : Subgroup V}
      (r : ConjEmbedding B G) (t : ConjEmbedding E B)
      (d : ConjEmbedding C G) (e : ConjEmbedding E C)
      (zs : List (Complex × Dot (r.comp t) (d.comp e))) (s : Strand E K) :
      Stage ((pair r t).tensor s.word).boundary ((pair d e).tensor s.word).boundary
        (normalize ((par r t d e zs).horizontal (IdDraw s.word)).interpret)

private theorem Stage.left {P Q S : Boundary G K} {f : HomAt P Q} {g : HomAt Q S}
    (hf : StraightAt P Q f) (hg : Stage Q S g) : Stage P S (f.vertical g) := by
  cases hf
  simpa only [Biset.Hom.id_vertical] using hg

private theorem Stage.right {P Q S : Boundary G K} {f : HomAt P Q} {g : HomAt Q S}
    (hf : Stage P Q f) (hg : StraightAt Q S g) : Stage P S (f.vertical g) := by
  cases hg
  simpa only [Biset.Hom.vertical_id] using hf

private theorem Stage.unframe {P Q P' Q' : Boundary G K}
    {f : HomAt P P'} {g : HomAt P' Q'} {h : HomAt Q' Q}
    (hf : StraightAt P P' f) (hh : StraightAt Q' Q h)
    (hs : Stage P Q ((f.vertical g).vertical h)) : Stage P' Q' g := by
  cases hf
  cases hh
  simpa only [Biset.Hom.id_vertical, Biset.Hom.vertical_id] using hs

private theorem Stage.padLeft {p q : Word G K} (d : LabelledDrawing Complex p q)
    (hs : Stage p.boundary q.boundary (normalize d.interpret)) :
    Stage ((Boundary.empty G).append p.boundary) ((Boundary.empty G).append q.boundary)
      (juxtaposeMap (Biset.Hom.id (R := Complex) (Boundary.empty G).word.basis)
        (normalize d.interpret)) := by
  change Stage p.boundary q.boundary
    (((Biset.insertLeftUnit p.boundary.word.basis Complex).vertical
      ((Biset.Hom.id (Biset.regular G)).horizontal (normalize d.interpret))).vertical
      (Biset.leftUnit q.boundary.word.basis Complex))
  rwa [pad_left_eval]

private theorem Stage.padRight {p q : Word G K} (d : LabelledDrawing Complex p q)
    (hs : Stage p.boundary q.boundary (normalize d.interpret)) :
    Stage (p.boundary.append (.empty K)) (q.boundary.append (.empty K))
      (juxtaposeMap (normalize d.interpret)
        (Biset.Hom.id (R := Complex) (Boundary.empty K).word.basis)) := by
  let padded := d.interpret.horizontal (ScopedDiagram.ordinary (Diagram.id (R := Complex) (Word.empty K)))
  let ins : Diagram Complex p (p.tensor (.empty K)) := .insertRightUnit p
  let rem : Diagram Complex (q.tensor (.empty K)) q := .rightUnit q
  let framed := ((ScopedDiagram.ordinary ins).vertical padded).vertical (.ordinary rem)
  have he : framed.eval = d.interpret.eval := pad_right_eval d.interpret.eval
  have hn : normalize framed = normalize d.interpret := (ScopedDiagram.eval_atBoundary_eq_iff _ _).2 he
  have hm : Stage p.boundary q.boundary (normalize framed) := hn.symm ▸ hs
  dsimp only [framed] at hm
  rw [normalize_vertical, normalize_vertical] at hm
  have hpad := Stage.unframe (merge_empty_coherence (.ordinary ins) rfl)
    (merge_empty_coherence (.ordinary rem) rfl) hm
  dsimp only [padded] at hpad
  rw [normalize_horizontal, normalize_id] at hpad
  exact hpad

private theorem Stage.nonemptyRight
    {P Q : Boundary G H} {f : HomAt P Q}
    (hs : Stage P Q f) (s : Strand H J) (rest : Boundary J K)
    (hw : (boundaryDirs P).length + (boundaryDirs (.cons s rest)).length ≤ 3) :
    Stage (P.append (.cons s rest)) (Q.append (.cons s rest))
      (juxtaposeMap f (Biset.Hom.id (R := Complex) (Boundary.cons s rest).word.basis)) := by
  cases hs with
  | bare r t d e zs =>
    cases rest with
    | empty =>
      cases s with
      | up a =>
        simpa only [LabelledDrawing.interpret, normalize_horizontal, normalize_id,
          Strand.word, Word.boundary] using
          (Stage.tail r t d e zs (Strand.up a))
      | down a =>
        simpa only [LabelledDrawing.interpret, normalize_horizontal, normalize_id,
          Strand.word, Word.boundary] using
          (Stage.tail r t d e zs (Strand.down a))
    | cons s' rest =>
      cases s <;> cases s' <;>
        simp only [Word.boundary, Boundary.append, boundaryDirs, List.length_cons,
          List.length_nil] at hw <;> omega
  | tail r t d e zs w =>
    cases s <;> cases w <;>
      simp only [Strand.word, Word.boundary, Boundary.append, boundaryDirs, List.length_cons,
        List.length_nil] at hw <;> omega

private theorem Stage.horizontalLeft {p q : Word G H} (d : LabelledDrawing Complex p q)
    {S T : Boundary H K} {g : HomAt S T}
    (hs : Stage p.boundary q.boundary (normalize d.interpret)) (hg : StraightAt S T g)
    (hw : (boundaryDirs p.boundary).length + (boundaryDirs S).length ≤ 3) :
    Stage (p.boundary.append S) (q.boundary.append T)
      (juxtaposeMap (normalize d.interpret) g) := by
  cases hg
  rename_i S
  cases S with
  | empty => exact Stage.padRight d hs
  | cons s rest => exact Stage.nonemptyRight hs s rest hw

private theorem Stage.horizontalRight {P Q : Boundary G H} {f : HomAt P Q}
    {r s : Word H K} (e : LabelledDrawing Complex r s)
    (hf : StraightAt P Q f) (hQ : boundaryDirs Q = [])
    (hs : Stage r.boundary s.boundary (normalize e.interpret)) :
    Stage (P.append r.boundary) (Q.append s.boundary)
      (juxtaposeMap f (normalize e.interpret)) := by
  cases hf
  rename_i P
  cases P with
  | empty => exact Stage.padLeft e hs
  | cons s rest => cases s <;> cases hQ

private abbrev event : PlanarEvent := .vertex 0 .parallelUp

private theorem unshift {n : Nat} {x : PlanarCode.Code}
    (h : PlanarCode.shift n x = [event]) : n = 0 ∧ x = [event] := by
  cases x with
  | nil => cases h
  | cons e es =>
    have he := (List.cons.inj h).1
    have hn : n + e.position = 0 := by
      have hh := congrArg PlanarEvent.position he
      cases e <;> exact hh
    have hn' : n = 0 := by omega
    exact ⟨hn', by simpa only [hn', shift_zero] using h⟩

private def Claim {p q : Word G K} (d : LabelledDrawing Complex p q) : Prop :=
  code d.erase = [event] → p.directions.length ≤ 3 →
    Stage p.boundary q.boundary (normalize d.interpret)

private theorem verticalStep {p q r : Word G K}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex q r)
    (hd : Claim d) (he : Claim e) : Claim (d.vertical e) := by
  intro hc hw
  rw [drawing_code_vert] at hc
  change Stage p.boundary r.boundary (normalize (d.interpret.vertical e.interpret))
  rw [normalize_vertical]
  rcases append_singleton hc with ⟨hd₀, he₁⟩ | ⟨hd₁, he₀⟩
  · have h := merge_empty_coherence d hd₀
    have hdirs := congrArg boundaryDirs (straight_boundary_eq h)
    rw [word_boundaryDirs, word_boundaryDirs] at hdirs
    exact Stage.left h (he he₁ (hdirs ▸ hw))
  · exact Stage.right (hd hd₁ hw) (merge_empty_coherence e he₀)

private theorem horizontalStep {p q : Word G H} {r s : Word H K}
    (d : LabelledDrawing Complex p q) (e : LabelledDrawing Complex r s)
    (hd : Claim d) (he : Claim e) : Claim (d.horizontal e) := by
  intro hc hw
  rw [drawing_code_horiz] at hc
  change (p.directions ++ r.directions).length ≤ 3 at hw
  rw [List.length_append] at hw
  change Stage (p.boundary.append r.boundary) (q.boundary.append s.boundary)
    (normalize (d.interpret.horizontal e.interpret))
  rw [normalize_horizontal]
  rcases append_singleton hc with ⟨hd₀, he₁⟩ | ⟨hd₁, he₀⟩
  · obtain ⟨hlen, he₁⟩ := unshift he₁
    have h := merge_empty_coherence d hd₀
    have hq : boundaryDirs q.boundary = [] := by
      rw [word_boundaryDirs]
      exact List.length_eq_zero_iff.mp hlen
    exact Stage.horizontalRight e h hq (he he₁ (by omega))
  · exact Stage.horizontalLeft d (hd hd₁ (by omega))
      (merge_empty_coherence e (shift_eq_nil he₀))
      (by simpa only [word_boundaryDirs] using hw)

private theorem ordinary {p q : Word G K} (d : Diagram Complex p q) :
    Claim (.ordinary d) := by
  induction d with
  | vertical d e hd he => exact verticalStep (.ordinary d) (.ordinary e) hd he
  | horizontal d e hd he => exact horizontalStep (.ordinary d) (.ordinary e) hd he
  | _ => intro hc; cases hc

private theorem notExpanded (n : Nat) (opening : ProjectionOpening)
    (closing : ProjectionClosing) :
    PlanarCode.encode (DrawingShape.expandedProjectionGeometry n opening closing) ≠ [event] := by
  cases opening <;> simp only [DrawingShape.expandedProjectionGeometry, encode_stack]
  all_goals
    intro h
    have hh := congrArg List.head? h
    cases hh

private theorem drawing {p q : Word G K} (d : LabelledDrawing Complex p q) : Claim d := by
  induction d with
  | ordinary d => exact ordinary d
  | vertical d e hd he => exact verticalStep d e hd he
  | horizontal d e hd he => exact horizontalStep d e hd he
  | parallelUp r t d e zs => exact fun _ _ => Stage.bare r t d e zs
  | trivalent v => cases v <;> intro hc <;> cases hc
  | bentVertex v => cases v <;> intro hc <;> cases hc
  | expandedProjection _ _ _ _ _ opening closing =>
    exact fun h => (notExpanded _ opening closing h).elim
  | expandedProjectionChain _ _ _ _ _ _ opening closing =>
    exact fun h => (notExpanded _ opening closing h).elim
  | expandedLinearDotProjection _ _ _ _ _ _ opening closing =>
    exact fun h => (notExpanded _ opening closing h).elim
  | parallelUpChain _ _ _ _ labels =>
    intro h
    change PlanarCode.encode ((DrawingShape.vertex .mergeUp).stack
      ((DrawingShape.upwardDots labels.length).stack (.vertex .splitUp))) = [event] at h
    rw [encode_stack] at h
    have hh := congrArg List.head? h
    cases hh
  | parallelDownChain _ _ _ _ labels =>
    intro h
    change PlanarCode.encode ((DrawingShape.vertex .mergeDown).stack
      ((DrawingShape.downwardDots labels.length).stack (.vertex .splitDown))) = [event] at h
    rw [encode_stack] at h
    have hh := congrArg List.head? h
    cases hh
  | _ => intro hc; cases hc

private noncomputable def collect (r : ConjEmbedding H G) (t : ConjEmbedding K H)
    (d : ConjEmbedding J G) (e : ConjEmbedding K J)
    (zs : List (Complex × Dot (r.comp t) (d.comp e))) : DotLabel Complex (r.comp t) (d.comp e) :=
  (zs.map fun (c, z) => Finsupp.single z c).sum

theorem eval_collect (r : ConjEmbedding H G) (t : ConjEmbedding K H)
    (d : ConjEmbedding J G) (e : ConjEmbedding K J)
    (zs : List (Complex × Dot (r.comp t) (d.comp e))) :
    (par r t d e zs).interpret.eval =
      (par r t d e (DotLabel.terms (collect r t d e zs))).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  let L := freeLift Complex
    (fun z => (Diagram.parallelUp (R := Complex) r t d e z).eval.toLinearMap x)
  have he (ts : List (Complex × Dot (r.comp t) (d.comp e))) :
      (par r t d e ts).interpret.eval.toLinearMap x = L (collect r t d e ts) := by
    change (ScopedDiagram.linearCombination
      (ts.map fun (c, z) => (c, .ordinary (.parallelUp r t d e z)))).eval.toLinearMap x = _
    rw [ScopedDiagram.eval_linearCombination_apply, List.map_map]
    unfold collect
    induction ts with
    | nil => exact (map_zero L).symm
    | cons a ts ih =>
      obtain ⟨c, z⟩ := a
      simp only [List.map_cons, List.sum_cons, map_add, ← ih]
      congr 1
      exact (freeLift_single Complex
        (fun z => (Diagram.parallelUp (R := Complex) r t d e z).eval.toLinearMap x) z c).symm
  have hterms (Z : DotLabel Complex (r.comp t) (d.comp e)) :
      collect r t d e (DotLabel.terms Z) = Z := by
    unfold collect DotLabel.terms
    rw [List.map_map, Finset.sum_map_toList]
    exact Finsupp.sum_single Z
  rw [he, he, hterms]

private abbrev triple {E : Subgroup V} {B : Subgroup V}
    (r : ConjEmbedding B G) (t : ConjEmbedding E B) (s : Strand E K) :=
  (pair r t).tensor s.word

private theorem triple_inj {B B' E E' : Subgroup V}
    (r' : ConjEmbedding B' G) (t' : ConjEmbedding E' B') (s' : Strand E' K)
    (r : ConjEmbedding B G) (t : ConjEmbedding E B) (s : Strand E K)
    (h : (triple r' t' s').boundary = (triple r t s).boundary) :
    B' = B ∧ E' = E ∧ HEq r' r ∧ HEq t' t ∧ HEq s' s := by
  have word_boundary (s : Strand E K) : s.word.boundary = .cons s (.empty K) := by
    cases s <;> rfl
  have word_boundary' (s : Strand E' K) : s.word.boundary = .cons s (.empty K) := by
    cases s <;> rfl
  change Boundary.cons (.up r') (.cons (.up t') s'.word.boundary) =
    Boundary.cons (.up r) (.cons (.up t) s.word.boundary) at h
  rw [word_boundary s, word_boundary' s'] at h
  injection h with _ hB _ hR htail
  subst B'
  have hr : r' = r := by
    have h' := eq_of_heq hR
    injection h'
  have ht' := eq_of_heq htail
  injection ht' with _ hE _ hT hs
  subst E'
  have ht : t' = t := by
    have h' := eq_of_heq hT
    injection h'
  have hs' : s' = s := by
    have h' := eq_of_heq hs
    injection h'
  exact ⟨rfl, rfl, heq_of_eq hr, heq_of_eq ht, heq_of_eq hs'⟩

private theorem witness {P Q : Boundary G K} {m : HomAt P Q}
    (h : Stage P Q m) (hP : (boundaryDirs P).length = 3)
    {C E : Subgroup V} (d : ConjEmbedding C G) (e : ConjEmbedding E C)
    (f : ConjEmbedding E K) (hQ : Q = (triple d e (.down f)).boundary) :
    ∃ (B : Subgroup V) (r : ConjEmbedding B G) (t : ConjEmbedding E B)
      (Z : DotLabel Complex (r.comp t) (d.comp e))
      (hp : P = (triple r t (.down f)).boundary),
      cast (congrArg₂ (fun X Y : Boundary G K => HomAt X Y) hp hQ) m =
        (par r t d e (DotLabel.terms Z) |>.horizontal (IdDraw (.down f))).interpret.atBoundary.eval := by
  cases h with
  | bare r t x y zs => cases hP
  | tail r t x y zs s =>
    obtain ⟨hC, hE, hx, hy, hs⟩ := triple_inj x y s d e (.down f) hQ
    cases hC
    cases hE
    cases hx
    cases hy
    cases hs
    refine ⟨_,r,t,collect r t d e zs,rfl,?_⟩
    change (ScopedDiagram.atBoundary _).eval = (ScopedDiagram.atBoundary _).eval
    apply (ScopedDiagram.eval_atBoundary_eq_iff _ _).2
    change (par r t d e zs).interpret.eval.horizontal _ =
      (par r t d e (DotLabel.terms (collect r t d e zs))).interpret.eval.horizontal _
    rw [eval_collect] <;> rfl

/-- Invert the final singleton. The ordered output forces the exact two target embeddings
and the exact restriction strand on both sides. -/
theorem normalizeThird {p q : Word G K} (stage : LabelledDrawing Complex p q)
    (hc : PlanarCode.encode stage.erase.geometry = [.vertex 0 .parallelUp])
    (hw : p.directions = [true, true, false])
    {C E : Subgroup V} (d : ConjEmbedding C G) (e : ConjEmbedding E C)
    (f : ConjEmbedding E K) (hq : q.boundary = (triple d e (.down f)).boundary) :
    ∃ (B : Subgroup V) (r : ConjEmbedding B G) (t : ConjEmbedding E B)
      (Z : DotLabel Complex (r.comp t) (d.comp e))
      (hp : p.boundary = (triple r t (.down f)).boundary),
      cast (congrArg₂ (fun X Y : Boundary G K => HomAt X Y) hp hq) stage.interpret.atBoundary.eval =
        (par r t d e (DotLabel.terms Z) |>.horizontal (IdDraw (.down f))).interpret.atBoundary.eval := by
  have hl : p.directions.length = 3 := by rw [hw]; rfl
  exact witness (drawing stage hc hl.le) (by simpa only [word_boundaryDirs] using hl) d e f hq

/-- Match the inputs of the final crossing to labels already recovered at stage two. -/
theorem normalizeThirdFixed {p q : Word G K} (stage : LabelledDrawing Complex p q)
    (hc : PlanarCode.encode stage.erase.geometry = [.vertex 0 .parallelUp])
    {B C E : Subgroup V} (r : ConjEmbedding B G) (t : ConjEmbedding E B)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E K)
    (hp : p.boundary = (triple r t (.down f)).boundary)
    (hq : q.boundary = (triple d e (.down f)).boundary) :
    ∃ Z : DotLabel Complex (r.comp t) (d.comp e),
      cast (congrArg₂ (fun X Y : Boundary G K => HomAt X Y) hp hq) stage.interpret.atBoundary.eval =
        (par r t d e (DotLabel.terms Z) |>.horizontal (IdDraw (.down f))).interpret.atBoundary.eval := by
  have hw : p.directions = [true, true, false] := by
    rw [← word_boundaryDirs, hp]
    rfl
  obtain ⟨B',r',t',Z,hp',h⟩ := normalizeThird stage hc hw d e f hq
  obtain ⟨hB, _, hr, ht, _⟩ := triple_inj r' t' (.down f) r t (.down f) (hp'.symm.trans hp)
  cases hB
  cases hr
  cases ht
  exact ⟨Z,h⟩

end CaseTwoStageThree

namespace CaseTwoAudit

open CaseTwoStageThree

theorem normalize_case_two_third_atTop {p q : Word G F} (stage : LabelledDrawing Complex p q)
    (hc : PlanarCode.encode stage.erase.geometry = [.vertex 0 .parallelUp])
    (hw : p.directions = [true, true, false]) (hq : q.boundary = top.boundary) :
    ∃ (B : Subgroup U) (r : ConjEmbedding B G) (t : ConjEmbedding E B)
      (Z : DotLabel Complex (comp r t) de)
      (hp : p.boundary = (tensor (tensor (up r) (up t)) (down f)).boundary),
      cast (congrArg₂ (fun P Q : Boundary G F => Biset.Hom Complex P.word.basis Q.word.basis)
        hp hq) stage.interpret.atBoundary.eval =
        (LabelledDrawing.horizontal (LabelledDrawing.parallelUp r t d e (DotLabel.terms Z))
          (drawId (down f))).interpret.atBoundary.eval :=
  normalizeThird stage hc hw d e f hq

theorem normalize_case_two_third {p q : Word G F} (stage : LabelledDrawing Complex p q)
    (hc : PlanarCode.encode stage.erase.geometry = [.vertex 0 .parallelUp])
    {B : Subgroup U} (r : ConjEmbedding B G) (t : ConjEmbedding E B)
    (hp : p.boundary = (tensor (tensor (up r) (up t)) (down f)).boundary)
    (hq : q.boundary = top.boundary) :
    ∃ Z : DotLabel Complex (comp r t) de,
      cast (congrArg₂ (fun P Q : Boundary G F => Biset.Hom Complex P.word.basis Q.word.basis)
        hp hq) stage.interpret.atBoundary.eval =
        (LabelledDrawing.horizontal (LabelledDrawing.parallelUp r t d e (DotLabel.terms Z))
          (drawId (down f))).interpret.atBoundary.eval :=
  normalizeThirdFixed stage hc r t d e f hp hq

end CaseTwoAudit


namespace CaseTwoAudit

open MackeyDiagrams

section BoundaryComposition

variable {V : Type*} [Group V] {K H : Subgroup V}
variable {R : Type*} [CommSemiring R]
variable {p q r s : Word K H}

theorem atBoundary_eval_vertical (d : ScopedDiagram R p q) (e : ScopedDiagram R q r) :
    (ScopedDiagram.vertical d e).atBoundary.eval =
      d.atBoundary.eval.vertical e.atBoundary.eval := by
  change (p.reorderFromBoundary (R := R)).eval.vertical
      (d.eval.vertical (e.eval.vertical (r.reorderToBoundary (R := R)).eval)) =
    ((p.reorderFromBoundary (R := R)).eval.vertical
      (d.eval.vertical (q.reorderToBoundary (R := R)).eval)).vertical
    ((q.reorderFromBoundary (R := R)).eval.vertical
      (e.eval.vertical (r.reorderToBoundary (R := R)).eval))
  have hcancel : (q.reorderToBoundary (R := R)).eval.vertical q.reorderFromBoundary.eval =
      Biset.Hom.id q.basis := Word.eval_reorderToFrom q
  simp only [Biset.Hom.vertical_assoc]
  rw [← Biset.Hom.vertical_assoc (q.reorderToBoundary (R := R)).eval,
    hcancel, Biset.Hom.id_vertical]

theorem atBoundary_eval_stack (d₁ : ScopedDiagram R p q) (d₂ : ScopedDiagram R q r)
    (d₃ : ScopedDiagram R r s) :
    (ScopedDiagram.vertical d₁ (ScopedDiagram.vertical d₂ d₃)).atBoundary.eval =
      d₁.atBoundary.eval.vertical (d₂.atBoundary.eval.vertical d₃.atBoundary.eval) := by
  rw [atBoundary_eval_vertical, atBoundary_eval_vertical]

theorem cut_eval_atBoundary {d : ScopedDiagram R p s}
    {d₁ : ScopedDiagram R p q} {d₂ : ScopedDiagram R q r} {d₃ : ScopedDiagram R r s}
    (h : d.eval = d₁.eval.vertical (d₂.eval.vertical d₃.eval)) :
    d.atBoundary.eval =
      d₁.atBoundary.eval.vertical (d₂.atBoundary.eval.vertical d₃.atBoundary.eval) := by
  have h' : d.eval = (ScopedDiagram.vertical d₁ (ScopedDiagram.vertical d₂ d₃)).eval := h
  exact ((ScopedDiagram.eval_atBoundary_eq_iff _ _).mpr h').trans
    (atBoundary_eval_stack d₁ d₂ d₃)

def reindexBoundaryHom {a b a' b' : Boundary K H}
    (ha : a = a') (hb : b = b') (f : Biset.Hom R a.word.basis b.word.basis) :
    Biset.Hom R a'.word.basis b'.word.basis := by
  subst a'
  subst b'
  exact f

theorem reindexBoundaryHom_vertical {a b c a' b' c' : Boundary K H}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (f : Biset.Hom R a.word.basis b.word.basis) (g : Biset.Hom R b.word.basis c.word.basis) :
    reindexBoundaryHom ha hc (f.vertical g) =
      (reindexBoundaryHom ha hb f).vertical (reindexBoundaryHom hb hc g) := by
  subst a'
  subst b'
  subst c'
  rfl

theorem eval_planarAtBoundary {a b : Boundary K H} {shape : PlanarShape}
    (replacement : LabelledDrawing.PlanarAtBoundary R a b shape) :
    replacement.interpret.eval = reindexBoundaryHom replacement.bottom_eq replacement.top_eq
      replacement.diagram.interpret.atBoundary.eval := by
  obtain ⟨bottom, top, drawing, hb, ht, hs⟩ := replacement
  subst a
  subst b
  rfl

theorem combine_cut_stage_equalities
    {p' q' r' s' : Word K H}
    {d : ScopedDiagram R p s}
    {d₁ : ScopedDiagram R p q} {d₂ : ScopedDiagram R q r} {d₃ : ScopedDiagram R r s}
    {e₁ : ScopedDiagram R p' q'} {e₂ : ScopedDiagram R q' r'} {e₃ : ScopedDiagram R r' s'}
    (hp : p.boundary = p'.boundary) (hq : q.boundary = q'.boundary)
    (hr : r.boundary = r'.boundary) (hs : s.boundary = s'.boundary)
    (h : d.eval = d₁.eval.vertical (d₂.eval.vertical d₃.eval))
    (h₁ : reindexBoundaryHom hp hq d₁.atBoundary.eval = e₁.atBoundary.eval)
    (h₂ : reindexBoundaryHom hq hr d₂.atBoundary.eval = e₂.atBoundary.eval)
    (h₃ : reindexBoundaryHom hr hs d₃.atBoundary.eval = e₃.atBoundary.eval) :
    reindexBoundaryHom hp hs d.atBoundary.eval =
      (ScopedDiagram.vertical e₁ (ScopedDiagram.vertical e₂ e₃)).atBoundary.eval := by
  rw [cut_eval_atBoundary h, reindexBoundaryHom_vertical hp hq hs,
    reindexBoundaryHom_vertical hq hr hs, h₁, h₂, h₃, atBoundary_eval_stack]

end BoundaryComposition
end CaseTwoAudit


namespace CaseTwoAudit

open MackeyDiagrams

private theorem collect_terms {X : Type*} (xs : X →₀ Complex) :
    CaseTwoFirstStage.collectProjection (terms xs) = xs := by
  unfold CaseTwoFirstStage.collectProjection terms
  rw [List.map_map, Finset.sum_map_toList]
  exact Finsupp.sum_single xs

private theorem projection_eval_collect {V : Type*} [Group V]
    {K H P L : Subgroup V} (α : ConjEmbedding K P) (β : ConjEmbedding H P)
    (η : ConjEmbedding L K) (θ : ConjEmbedding L H)
    (xs : List (Complex × ProjectionDot.Mixed α β η θ)) :
    (LabelledDrawing.compactProjection α β η θ xs).interpret.eval =
      (LabelledDrawing.compactProjection α β η θ
        (terms (CaseTwoFirstStage.collectProjection xs))).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  rw [CaseTwoFirstStage.eval_collectProjection, CaseTwoFirstStage.eval_collectProjection,
    collect_terms]

private theorem castBoundary_eq_reindex {V : Type*} [Group V] {K H : Subgroup V}
    {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (m : Biset.Hom Complex p.word.basis q.word.basis) :
    CaseTwoFirstStage.castBoundary hp hq m = reindexBoundaryHom hp hq m := by
  cases hp
  cases hq
  rfl

private theorem cast_eq_reindex {V : Type*} [Group V] {K H : Subgroup V}
    {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (m : Biset.Hom Complex p.word.basis q.word.basis) :
    cast (congrArg₂ (fun X Y : Boundary K H => Biset.Hom Complex X.word.basis Y.word.basis)
      hp hq) m = reindexBoundaryHom hp hq m := by
  cases hp
  cases hq
  rfl

private theorem reindex_stage_two {V : Type*} [Group V] {K H : Subgroup V}
    {p q p' q' : Word K H} (stage : LabelledDrawing Complex p q)
    (normal : LabelledDrawing Complex p' q')
    (hp : p.boundary = p'.boundary) (hq : q'.boundary = q.boundary)
    (h : CaseTwoStage.evalAt stage hp rfl = CaseTwoStage.evalAt normal rfl hq) :
    reindexBoundaryHom hp hq.symm stage.interpret.atBoundary.eval =
      normal.interpret.atBoundary.eval := by
  have hf {P Q P' Q' : Boundary K H} (h₁ : P = P') (h₂ : Q' = Q)
      (m : Biset.Hom Complex P.word.basis Q.word.basis)
      (n : Biset.Hom Complex P'.word.basis Q'.word.basis)
      (he : reindexBoundaryHom h₁ rfl m = reindexBoundaryHom rfl h₂ n) :
      reindexBoundaryHom h₁ h₂.symm m = n := by
    cases h₁
    cases h₂
    exact he
  apply hf hp hq
  have same {x y : Word K H} (d : LabelledDrawing Complex x y)
      {P Q : Boundary K H} (a : x.boundary = P) (b : y.boundary = Q) :
      CaseTwoStage.evalAt d a b = reindexBoundaryHom a b d.interpret.atBoundary.eval := by
    cases a
    cases b
    rfl
  simpa only [same] using h

private theorem first_collected {B : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (xs : List (Complex × ProjectionLabel a b r s)) :
    let lhs := (LabelledDrawing.compactProjection a b r s xs).horizontal (drawId (up c))
    let rhs := (LabelledDrawing.compactProjection a b r s
      (terms (CaseTwoFirstStage.collectProjection xs))).horizontal (drawId (up c))
    lhs.interpret.atBoundary.eval = rhs.interpret.atBoundary.eval := by
  dsimp only
  apply (ScopedDiagram.eval_atBoundary_eq_iff _ _).2
  exact congrArg (fun m => m.horizontal (drawId (up c)).interpret.eval)
    (projection_eval_collect a b r s xs)

private theorem second_collected {B : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (t : ConjEmbedding T B)
    (ys : List (Complex × ProjectionLabel s c t f)) :
    (CaseTwoStage.rightProjection r s c t f ys).interpret.atBoundary.eval =
      (atRight (up r) (LabelledDrawing.compactProjection s c t f
        (terms (CaseTwoFirstStage.collectProjection ys)))).interpret.atBoundary.eval := by
  apply (ScopedDiagram.eval_atBoundary_eq_iff _ _).2
  exact congrArg (fun m =>
    (Diagram.associate (R := Complex) (up r) (down s) (up c)).eval.vertical
      (((drawId (up r)).interpret.eval.horizontal m).vertical
        (Diagram.unassociate (R := Complex) (up r) (up t) (down f)).eval))
    (projection_eval_collect s c t f ys)

/-- Normalize the three actual singleton stages at their common ordered boundaries. -/
theorem checked_left_inversion : CaseTwoLeftInversion := by
  intro replacement
  obtain ⟨m, n, stage₁, stage₂, stage₃, hc₁, hc₂, hc₃, hcut⟩ :=
    CaseTwoFactor.factor_left replacement.diagram
      (checked_leftCode replacement.diagram replacement.shape_eq)
  obtain ⟨B, r, s, xs, hm, h₁⟩ :=
    first_stage_at_boundary stage₁ hc₁ replacement.bottom_eq
  obtain ⟨t, ys, hn, h₂⟩ :=
    CaseTwoStage.secondStage_fixedSuffix r s c d e f stage₂ stage₃ hc₂ hc₃ hm replacement.top_eq
  obtain ⟨zs, h₃⟩ := normalize_case_two_third stage₃ hc₃ r t hn.symm replacement.top_eq
  refine ⟨B, r, s, t, CaseTwoFirstStage.collectProjection xs,
    CaseTwoFirstStage.collectProjection ys, zs, ?_⟩
  have he₁ := ((castBoundary_eq_reindex _ _ _).symm.trans h₁).trans (first_collected r s xs)
  have he₂ := (reindex_stage_two _ _ hm hn h₂).trans (second_collected r s t ys)
  have he₃ := (cast_eq_reindex hn.symm replacement.top_eq
    stage₃.interpret.atBoundary.eval).symm.trans h₃
  exact (eval_planarAtBoundary replacement).trans
    (combine_cut_stage_equalities replacement.bottom_eq hm hn.symm replacement.top_eq
      hcut he₁ he₂ he₃)

end CaseTwoAudit

set_option maxHeartbeats 2000000

namespace CaseTwoAudit
open MackeyDiagrams

private def GroupObstruction : Prop :=
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D)
      (x : MackeyDiagrams.Dot (comp a r) (comp b s)),
      MackeyDiagrams.Dot.element x ∈ swapCoset →
      B = ⊥ ∧ ∀ y : MackeyDiagrams.Dot (comp a r) (comp b s),
        MackeyDiagrams.Dot.element y ∈ line →
        ¬ Set.Finite {j | MackeyDiagrams.Generator.mixedMultiplicationBasis a b r s y j =
          MackeyDiagrams.Generator.mixedPair a b (MackeyDiagrams.Dot.element y)})

private theorem group_obstruction : GroupObstruction := by
  intro B r s x hx
  have hB := forced_bot r s x hx
  refine ⟨hB, ?_⟩
  subst B
  exact unbounded_line_fiber r s

private theorem rhs_one_nonzero : eval rhs (basisVector 1) ≠ 0 := by
  intro h
  have hu := congrArg (fun x => x unitOut) h
  rw [rhs_probe_one] at hu
  exact one_ne_zero hu

private theorem rhs_swap_nonzero : eval rhs (basisVector τ) ≠ 0 := by
  intro h
  have hu := congrArg (fun x => x unitOut) h
  rw [rhs_probe_swap] at hu
  exact one_ne_zero hu

theorem endpoint_of_checked_inversion (normal : CaseTwoLeftInversion) :
    CaseTwoReviewedType := by
  unfold CaseTwoReviewedType
  refine ⟨?_, ?_, ?_, ?_, first, mid 1, mid τ, last, overall 1, overall τ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cup_indices.1
  · exact cup_indices.2
  · exact intersect_calc
  · exact group_obstruction
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact right_sum
  · exact rhs_one_nonzero
  · exact rhs_swap_nonzero
  · intro allowed drawings hd he
    refine allowed_crossings allowed drawings hd ?_
    cases drawings with
    | nil => exact he
    | cons drawing rest => exact he
  · exact two_left_drawings
  · exact no_replacement_of_canonical normal

end CaseTwoAudit

