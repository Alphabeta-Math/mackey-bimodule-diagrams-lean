import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Core
import Proofs.DotSlidePreorderNotSymmetric

open MackeyDiagrams
open private code drawing_code_vert drawing_code_horiz diagram_code_vert diagram_code_horiz
  encode_stack shift_zero StraightAt normalize normalize_vertical normalize_horizontal
  normalize_id juxtaposeMap pad_left_eval pad_right_eval boundaryDirs boundaryDirs_append word_boundaryDirs
  append_singleton shift_eq_nil merge_empty_coherence straight_boundary_eq
  from Proofs.DotSlidePreorderNotSymmetric

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

#print axioms CaseTwoStageThree.eval_collect
#print axioms CaseTwoStageThree.normalizeThird
#print axioms CaseTwoStageThree.normalizeThirdFixed
#print axioms CaseTwoAudit.normalize_case_two_third_atTop
#print axioms CaseTwoAudit.normalize_case_two_third
