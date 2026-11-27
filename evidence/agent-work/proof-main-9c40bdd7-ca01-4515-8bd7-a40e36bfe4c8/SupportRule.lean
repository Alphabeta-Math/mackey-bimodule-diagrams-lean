import Sized
import Raw

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

universe u
variable {V : Type u} [Group V] {A B C : Subgroup V}

def rawOne : {A B : Subgroup V} → (p : Word A B) → Raw p
  | _, _, .empty _ => PUnit.unit
  | _, _, .up _ => 1
  | _, _, .down _ => 1
  | _, _, .tensor p q => (rawOne p, rawOne q)

def PreservesSlots {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) : Prop :=
  ∀ x : Raw p, ∃ y : Raw q, slots q y = slots p x ∧
    f.toLinearMap (basisVector p x) = basisVector q y

theorem PreservesSlots.width {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    (h : PreservesSlots f) : q.directions.length = p.directions.length := by
  obtain ⟨y, hy, _⟩ := h (rawOne p)
  simpa only [slots_length] using congrArg List.length hy

def FirstProjection {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) (j : Nat) : Prop :=
  j+1 < p.directions.length ∧
  ∃ finite : Finset V, ∀ (xy : Raw p) (x : V),
    Selected (slots p xy) j x → x ∉ finite →
      f.toLinearMap (basisVector p xy) = 0

-- A vertex-free prefix transports the chosen raw representatives through
-- associators and unitors. At a first projection, evaluation is zero away
-- from a finite set of products of its two input coordinates.
def SupportRule {p q : Word A B} (f : Biset.Hom Complex p.basis q.basis) (events : Code) : Prop :=
  (events = [] → PreservesSlots f) ∧
  ∀ j, events.head? = some (.vertex j .mixedProjection) → FirstProjection f j

theorem SupportRule.structural {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    (h : PreservesSlots f) : SupportRule f [] := ⟨fun _ => h, fun _ h => by cases h⟩

theorem SupportRule.other {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {e : PlanarEvent} {es : Code} (h : ∀ j, e ≠ .vertex j .mixedProjection) :
    SupportRule f (e::es) :=
  ⟨(fun h => by cases h), fun j he => False.elim (h j (Option.some.inj he))⟩

theorem SupportRule.projection {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    (h : FirstProjection f 0) : SupportRule f [.vertex 0 .mixedProjection] := by
  refine ⟨(fun h => by cases h), ?_⟩
  intro j hj
  have e := PlanarEvent.vertex.inj (Option.some.inj hj)
  rwa [← e.1]

theorem support_seq {p q t : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {g : Biset.Hom Complex q.basis t.basis} {as bs : Code}
    (hf : SupportRule f as) (hg : SupportRule g bs) : SupportRule (f.vertical g) (as ++ bs) := by
  constructor
  · intro he x
    obtain ⟨ha,hb⟩ := List.append_eq_nil_iff.mp he
    obtain ⟨y, hy, hfy⟩ := hf.1 ha x
    obtain ⟨z, hz, hgz⟩ := hg.1 hb y
    refine ⟨z, hz.trans hy, ?_⟩
    change g.toLinearMap (f.toLinearMap (basisVector p x)) = _
    rw [hfy, hgz]
  · intro j hj
    cases as with
    | nil =>
      have hp := hf.1 rfl
      obtain ⟨hlen, S, hS⟩ := hg.2 j hj
      refine ⟨hp.width ▸ hlen, S, ?_⟩
      intro xy x hx hxS
      obtain ⟨yz, hy, hfy⟩ := hp xy
      change g.toLinearMap (f.toLinearMap (basisVector p xy)) = 0
      rw [hfy]
      exact hS yz x (hy ▸ hx) hxS
    | cons e es =>
      obtain ⟨hlen,S,hS⟩ := hf.2 j hj
      refine ⟨hlen,S,?_⟩
      intro xy x hx hxS
      change g.toLinearMap (f.toLinearMap (basisVector p xy)) = 0
      rw [hS xy x hx hxS, map_zero]

theorem basis_horizontal {p q : Word A B} {r s : Word B C}
    (f : Biset.Hom Complex p.basis q.basis) (g : Biset.Hom Complex r.basis s.basis)
    (x : Raw p) (y : Raw r) :
    (f.horizontal g).toLinearMap (basisVector (p.tensor r) (x,y)) =
      Biset.pairLinear Complex q.basis s.basis (f.toLinearMap (basisVector p x))
        (g.toLinearMap (basisVector r y)) := by
  unfold basisVector
  change (f.horizontal g).toLinearMap (Finsupp.single (p.basis.pair r.basis (rawPoint p x) (rawPoint r y)) 1) = _
  rw [Biset.Hom.horizontal_single, one_smul]

theorem shift_first {ls : Code} {n j : Nat}
    (h : (shift n ls).head? = some (.vertex j .mixedProjection)) :
    ∃ k, j = n+k ∧ ls.head? = some (.vertex k .mixedProjection) := by
  cases ls with
  | nil => cases h
  | cons e es =>
    cases e with
    | vertex k v =>
      have he : PlanarEvent.vertex (n+k) v = .vertex j .mixedProjection := Option.some.inj h
      obtain ⟨rfl,rfl⟩ := PlanarEvent.vertex.inj he
      exact ⟨k,rfl,rfl⟩
    | zero | add | scale => cases h

theorem support_par {p q : Word A B} {r s : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    {as bs : Code} (hf : SupportRule f as) (hg : SupportRule g bs) :
    SupportRule (p := p.tensor r) (q := q.tensor s) (f.horizontal g) (as ++ shift q.directions.length bs) := by
  constructor
  · intro he xy
    obtain ⟨ha,hb⟩ := List.append_eq_nil_iff.mp he
    have hb' : bs = [] := by
      cases bs with
      | nil => rfl
      | cons e es => cases hb
    obtain ⟨x, hx, hfx⟩ := hf.1 ha xy.1
    obtain ⟨y, hy, hgy⟩ := hg.1 hb' xy.2
    refine ⟨(x,y), by simp only [slots,hx,hy], ?_⟩
    change (f.horizontal g).toLinearMap (basisVector (p.tensor r) (xy.1,xy.2)) = _
    rw [basis_horizontal, hfx, hgy]
    simp only [basisVector, Biset.pairLinear_single, one_mul]
    rfl
  · intro j hj
    cases as with
    | nil =>
      have hp := hf.1 rfl
      obtain ⟨k, rfl, hk⟩ := shift_first hj
      obtain ⟨hlen,S,hS⟩ := hg.2 k hk
      rw [hp.width]
      refine ⟨?_,S,?_⟩
      · simp only [Word.directions,List.length_append]
        omega
      · intro xy x hx hxS
        have hx' := selected_append_right (slots p xy.1) (slots r xy.2) k x
          (by simpa only [slots_length, slots] using hx)
        change (f.horizontal g).toLinearMap (basisVector (p.tensor r) (xy.1,xy.2)) = _
        rw [basis_horizontal, hS xy.2 x hx' hxS, map_zero]
    | cons e es =>
      obtain ⟨hlen,S,hS⟩ := hf.2 j hj
      refine ⟨?_,S,?_⟩
      · simp only [Word.directions,List.length_append]
        omega
      · intro xy x hx hxS
        have hx' := selected_append_left (slots p xy.1) (slots r xy.2) j x
          (by rwa [slots_length]) hx
        change (f.horizontal g).toLinearMap (basisVector (p.tensor r) (xy.1,xy.2)) = _
        rw [basis_horizontal, hS xy.1 x hx' hxS, map_zero, LinearMap.zero_apply]

theorem support_projection (a : ConjEmbedding A C) (b : ConjEmbedding B C)
    {D : Subgroup V} (l : ConjEmbedding D A) (r : ConjEmbedding D B)
    (s : ProjectionDot.Mixed a b l r) :
    FirstProjection (Diagram.mixedProjection (R := Complex) a b l r s.dot s.finite).eval 0 := by
  classical
  refine ⟨by change 1 < 2; decide, {s.dot.element.val}, ?_⟩
  intro xy x hx hS
  exact raw_projection_zero a b l r s xy x hx (by simpa using hS)

theorem projections_zero (a : ConjEmbedding A C) (b : ConjEmbedding B C)
    {D : Subgroup V} (l : ConjEmbedding D A) (r : ConjEmbedding D B)
    (ss : List (Complex × ProjectionDot.Mixed a b l r))
    (xy : Raw ((Word.down a).tensor (.up b))) (x : V)
    (hx : Selected (slots ((Word.down a).tensor (.up b)) xy) 0 x)
    (outside : ∀ t ∈ ss, x ≠ t.2.dot.element.val) :
    (LabelledDrawing.compactProjection a b l r ss).interpret.eval.toLinearMap
      (basisVector ((Word.down a).tensor (.up b)) xy) = 0 := by
  rw [LabelledDrawing.interpret, ScopedDiagram.eval_linearCombination_apply
    (p := (Word.down a).tensor (.up b)) (q := (Word.up l).tensor (.down r)), List.map_map]
  let contribution := fun (t : Complex × ProjectionDot.Mixed a b l r) =>
    t.1 • (Diagram.mixedProjection a b l r t.2.dot t.2.finite).eval.toLinearMap
      (basisVector ((Word.down a).tensor (.up b)) xy)
  change (ss.map contribution).sum = 0
  have hz (t : Complex × ProjectionDot.Mixed a b l r) (ht : t ∈ ss) :
      contribution t = 0 := by
    unfold contribution
    rw [raw_projection_zero a b l r t.2 xy x hx (outside t ht), smul_zero]
  rw [List.map_congr_left hz, List.sum_map_zero]

theorem support_projections (a : ConjEmbedding A C) (b : ConjEmbedding B C)
    {D : Subgroup V} (l : ConjEmbedding D A) (r : ConjEmbedding D B)
    (ss : List (Complex × ProjectionDot.Mixed a b l r)) :
    FirstProjection (LabelledDrawing.compactProjection a b l r ss).interpret.eval 0 := by
  classical
  let elements := ss.toFinset.image (fun t => t.2.dot.element.val)
  refine ⟨by change 1 < 2; decide, elements, ?_⟩
  intro xy x hx hS
  apply projections_zero a b l r ss xy x hx
  intro t ht he
  exact hS (Finset.mem_image.mpr ⟨t, List.mem_toFinset.mpr ht, he.symm⟩)

end CaseFiveInfiniteAux
