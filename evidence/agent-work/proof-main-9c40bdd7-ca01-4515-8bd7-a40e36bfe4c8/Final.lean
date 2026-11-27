import MackeyDiagrams
import Proofs.ExpansionIntoRightDiagrams
import Proofs.EvaluationWithOneProjection

set_option maxHeartbeats 2000000

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

def plainVertex : PlanarEvent → Prop
  | .vertex _ _ => True
  | _ => False

def Rigid (a : Code) : Prop :=
  (∀ e ∈ a, plainVertex e) ∧
  ∀ (pre post : Code) (e f : PlanarEvent), a = pre ++ [e, f] ++ post →
    f.position < e.position + e.outputs.length ∧
    e.position < f.position + f.inputs.length

theorem Rigid.inContext {a pre post : Code} (h : Rigid (pre ++ a ++ post)) :
    Rigid a := by
  constructor
  · intro e he
    exact h.1 e (by simp [he])
  · intro before after e f he
    exact h.2 (pre ++ before) (after ++ post) e f (by simp [he, List.append_assoc])

theorem position_place (e : PlanarEvent) (i : Nat) : (e.place i).position = i := by
  cases e <;> rfl

theorem inputs_place (e : PlanarEvent) (i : Nat) : (e.place i).inputs = e.inputs := by
  cases e <;> rfl

theorem outputs_place (e : PlanarEvent) (i : Nat) : (e.place i).outputs = e.outputs := by
  cases e <;> rfl

-- The two orientations of exchange are both excluded by intersecting
-- adjacent vertices. The context case passes rigidity to its inner segment.
theorem rigid_eq {a b : Code} (h : Equivalent a b) : (Rigid a → a = b) ∧ (Rigid b → a = b) := by
  induction h with
  | refl => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact ⟨fun h => (ih.2 h).symm, fun h => (ih.1 h).symm⟩
  | trans _ _ ih₁ ih₂ =>
    constructor
    · intro hr
      have e := ih₁.1 hr
      exact e.trans (ih₂.1 (e ▸ hr))
    · intro hr
      have e := ih₂.2 hr
      exact (ih₁.2 (e.symm ▸ hr)).trans e
  | context pre post _ ih =>
    exact ⟨fun h => congrArg (fun c => pre ++ c ++ post) (ih.1 h.inContext),
      fun h => congrArg (fun c => pre ++ c ++ post) (ih.2 h.inContext)⟩
  | exchange pre post i gap l r =>
    constructor <;> intro h
    · have bad := (h.2 pre post _ _ rfl).1
      simp only [position_place, outputs_place] at bad
      omega
    · have bad := (h.2 pre post _ _ rfl).2
      simp only [position_place, inputs_place] at bad
      omega
  | scale => constructor <;> intro h <;> exact False.elim (h.1 _ (List.mem_cons_self))
  | add => constructor <;> intro h <;> exact False.elim (h.1 _ (List.mem_cons_self))

def rightCode : Code :=
  [.vertex 1 .mixedProjection, .vertex 0 .parallelUp, .vertex 1 .mixedMultiplication]

theorem rigid_rightCode : Rigid rightCode := by
  constructor
  · intro e h
    simp only [rightCode, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> trivial
  · intro pre post e f he
    have hlen := congrArg List.length he
    simp only [rightCode, List.length_append, List.length_cons, List.length_nil] at hlen
    change 3 = pre.length + 2 + post.length at hlen
    cases pre with
    | nil =>
      simp only [rightCode, List.nil_append, List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl, _⟩ := he
      decide
    | cons p pre =>
      cases pre with
      | nil =>
        simp only [rightCode, List.cons_append, List.nil_append, List.cons.injEq] at he
        obtain ⟨_, rfl, rfl, _⟩ := he
        decide
      | cons q pre =>
        simp only [List.length_cons] at hlen
        omega

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

structure ShapeInfo where
  ins : Nat
  outs : Nat
  events : Code

def info (s : DrawingShape) : ShapeInfo :=
  ⟨s.inputs.length, s.outputs.length, encode s⟩

def ShapeInfo.seq (a b : ShapeInfo) : ShapeInfo :=
  ⟨a.ins, b.outs, a.events ++ b.events⟩

def ShapeInfo.par (a b : ShapeInfo) : ShapeInfo :=
  ⟨a.ins + b.ins, a.outs + b.outs, a.events ++ shift a.outs b.events⟩

theorem shift_add (n m : Nat) (xs : Code) : shift n (shift m xs) = shift (n + m) xs := by
  unfold shift
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  cases e <;> simp [PlanarEvent.place, PlanarEvent.position, Nat.add_assoc]

theorem shift_zero (xs : Code) : shift 0 xs = xs := by
  unfold shift
  conv_rhs => rw [← List.map_id xs]
  apply List.map_congr_left
  intro e _
  cases e <;> simp [PlanarEvent.place, PlanarEvent.position]

theorem ShapeInfo.par_assoc (a b c : ShapeInfo) : (a.par b).par c = a.par (b.par c) := by
  simp [ShapeInfo.par, shift, Nat.add_assoc, List.map_append, List.append_assoc, List.map_map,
    show ∀ e : PlanarEvent, (e.place (b.outs + e.position)).position = b.outs + e.position by
      intro e; cases e <;> rfl,
    show ∀ (e : PlanarEvent) (j k : Nat), (e.place j).place k = e.place k by
      intro e j k; cases e <;> rfl]

theorem info_vertical (a b : DrawingShape) : info (.vertical a b) = (info a).seq (info b) := rfl

theorem info_horizontal (a b : DrawingShape) : info (.horizontal a b) = (info a).par (info b) := by
  simp [info, ShapeInfo.par, DrawingShape.inputs, DrawingShape.outputs, encode]

theorem info_stack (a b : DrawingShape) (h : (info a).outs = (info b).ins) :
    info (a.stack b) = (info a).seq (info b) := by
  induction a generalizing b with
  | straight s =>
    cases b <;> simp_all [DrawingShape.stack, info, ShapeInfo.seq, DrawingShape.inputs,
      DrawingShape.outputs, encode]
  | vertical f rest ihf ihr =>
    cases b with
    | straight s =>
      simp_all [DrawingShape.stack, info, ShapeInfo.seq, DrawingShape.inputs,
        DrawingShape.outputs, encode]
    | vertex k =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | vertical x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | horizontal x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | zero x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | add x y =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
    | scale d =>
      change info (.vertical f (rest.stack _)) = _
      simp only [info_vertical, ihr _ h, ShapeInfo.seq, List.append_assoc]
  | vertex | horizontal | zero | add | scale =>
    cases b <;> simp_all [DrawingShape.stack, info, ShapeInfo.seq, DrawingShape.inputs,
      DrawingShape.outputs, encode]

theorem info_juxtapose (a b : DrawingShape) :
    info (a.juxtapose b) = (info a).par (info b) := by
  induction a generalizing b with
  | straight s =>
    cases s with
    | nil => simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
        DrawingShape.outputs, encode, shift_zero]
    | cons d s =>
      cases b with
      | straight t =>
        cases t <;>
          simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
            DrawingShape.outputs, encode, shift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      | vertex | vertical | horizontal | zero | add | scale =>
        exact info_horizontal _ _
  | horizontal f rest ihf ihr =>
    cases b with
    | straight s =>
      cases s with
      | nil => simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
          DrawingShape.outputs, encode, shift]
      | cons d s =>
        change info (.horizontal f (rest.juxtapose _)) = _
        simp only [info_horizontal, ihr, ShapeInfo.par_assoc]
    | vertex | vertical | horizontal | zero | add | scale =>
      change info (.horizontal f (rest.juxtapose _)) = _
      simp only [info_horizontal, ihr, ShapeInfo.par_assoc]
  | vertex | vertical | zero | add | scale =>
    cases b with
    | straight s =>
      cases s with
      | nil => simp [DrawingShape.juxtapose, info, ShapeInfo.par, DrawingShape.inputs,
          DrawingShape.outputs, encode, shift]
      | cons d s => exact info_horizontal _ _
    | vertex | vertical | horizontal | zero | add | scale =>
      exact info_horizontal _ _

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

def geoInfo (s : DrawingShape) : ShapeInfo := info s.geometry

def Valid : DrawingShape → Prop
  | .vertical a b => Valid a ∧ Valid b ∧ (geoInfo a).outs = (geoInfo b).ins
  | .horizontal a b => Valid a ∧ Valid b
  | _ => True

theorem geo_vertical {a b : DrawingShape} (h : (geoInfo a).outs = (geoInfo b).ins) :
    geoInfo (.vertical a b) = (geoInfo a).seq (geoInfo b) :=
  info_stack _ _ h

theorem geo_horizontal (a b : DrawingShape) :
    geoInfo (.horizontal a b) = (geoInfo a).par (geoInfo b) :=
  info_juxtapose _ _

theorem ShapeInfo.seq_assoc (a b c : ShapeInfo) :
    (a.seq b).seq c = a.seq (b.seq c) := by
  simp [ShapeInfo.seq, List.append_assoc]

theorem geo_stack {a b : DrawingShape} (ha : Valid a) (hb : Valid b)
    (h : (geoInfo a).outs = (geoInfo b).ins) :
    Valid (a.stack b) ∧ geoInfo (a.stack b) = (geoInfo a).seq (geoInfo b) := by
  have rightStraight {a : ShapeInfo} {n : Nat} (h : a.outs = n) :
      a = a.seq ⟨n,n,[]⟩ := by
    cases a
    simp_all [ShapeInfo.seq]
  induction a generalizing b with
  | straight s =>
    have hh : s.length = (geoInfo b).ins := h
    have leftStraight (I : ShapeInfo) (h : s.length = I.ins) :
        I = (ShapeInfo.mk s.length s.length []).seq I := by
      cases I
      simp_all [ShapeInfo.seq]
    cases b <;> exact ⟨hb, leftStraight _ hh⟩
  | vertical f rest ihf ihr =>
    obtain ⟨hf, hr, hm⟩ := ha
    have hm' := geo_vertical hm
    have hrest : (geoInfo rest).outs = (geoInfo b).ins := by rwa [hm'] at h
    obtain ⟨hv, he⟩ := ihr hr hb hrest
    cases b with
    | straight ds =>
      constructor
      · exact ⟨hf,hr,hm⟩
      · change (geoInfo (.vertical f rest)) = (geoInfo (.vertical f rest)).seq ⟨ds.length,ds.length,[]⟩
        rw [hm']
        have hlen : (geoInfo rest).outs = ds.length := hrest
        simp [ShapeInfo.seq, hlen]
    | vertex | vertical | horizontal | zero | add | scale =>
      have hnext := hm.trans (congrArg ShapeInfo.ins he).symm
      refine ⟨⟨hf,hv,hnext⟩, ?_⟩
      change geoInfo (.vertical f (rest.stack _)) = _
      simp only [geo_vertical hnext, he, hm', ShapeInfo.seq_assoc]
  | vertex | horizontal | zero | add | scale =>
    cases b with
    | straight ds =>
      exact ⟨ha, rightStraight h⟩
    | vertex | vertical | horizontal | zero | add | scale =>
      exact ⟨⟨ha,hb,h⟩, geo_vertical h⟩

theorem geo_juxtapose {a b : DrawingShape} (ha : Valid a) (hb : Valid b) :
    Valid (a.juxtapose b) ∧ geoInfo (a.juxtapose b) = (geoInfo a).par (geoInfo b) := by
  have rightNil (s : DrawingShape) :
      (geoInfo s).par (geoInfo (.straight [])) = geoInfo s := by
    simp [geoInfo, info, ShapeInfo.par, encode, shift, DrawingShape.geometry,
      DrawingShape.inputs, DrawingShape.outputs]
  induction a generalizing b with
  | straight s =>
    cases s with
    | nil =>
      exact ⟨hb, by
        simp [DrawingShape.juxtapose, geoInfo, info, ShapeInfo.par, encode, shift_zero,
          DrawingShape.geometry, DrawingShape.inputs, DrawingShape.outputs]⟩
    | cons d s =>
      cases b with
      | straight t =>
        cases t <;> exact ⟨trivial, by
          simp [DrawingShape.juxtapose, geoInfo, info, ShapeInfo.par, encode, shift,
            DrawingShape.geometry, DrawingShape.inputs, DrawingShape.outputs,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩
      | vertex | vertical | horizontal | zero | add | scale =>
        exact ⟨⟨ha,hb⟩, geo_horizontal _ _⟩
  | horizontal f rest ihf ihr =>
    obtain ⟨hf,hr⟩ := ha
    obtain ⟨hv,he⟩ := ihr hr hb
    cases b with
    | straight ds =>
      cases ds with
      | nil => exact ⟨⟨hf,hr⟩, (rightNil _).symm⟩
      | cons d ds =>
        refine ⟨⟨hf,hv⟩, ?_⟩
        change geoInfo (.horizontal f (rest.juxtapose _)) = _
        simp only [geo_horizontal, he, ShapeInfo.par_assoc]
    | vertex | vertical | horizontal | zero | add | scale =>
      refine ⟨⟨hf,hv⟩, ?_⟩
      change geoInfo (.horizontal f (rest.juxtapose _)) = _
      simp only [geo_horizontal, he, ShapeInfo.par_assoc]
  | vertex | vertical | zero | add | scale =>
    cases b with
    | straight ds =>
      cases ds with
      | nil => exact ⟨ha, (rightNil _).symm⟩
      | cons d ds =>
        exact ⟨⟨ha,hb⟩, geo_horizontal _ _⟩
    | vertex | vertical | horizontal | zero | add | scale =>
      exact ⟨⟨ha,hb⟩, geo_horizontal _ _⟩

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

theorem dot_width (n : Nat) :
    (info (DrawingShape.upwardDots n)).ins = 1 ∧
    (info (DrawingShape.upwardDots n)).outs = 1 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h : (info (.vertex .upDot)).outs = (info (DrawingShape.upwardDots n)).ins := ih.1.symm
    unfold DrawingShape.upwardDots
    rw [info_stack _ _ h]
    exact ⟨rfl,ih.2⟩

theorem down_dot_width (n : Nat) :
    (info (DrawingShape.downwardDots n)).ins = 1 ∧
    (info (DrawingShape.downwardDots n)).outs = 1 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h : (info (.vertex .downDot)).outs = (info (DrawingShape.downwardDots n)).ins := ih.1.symm
    unfold DrawingShape.downwardDots
    rw [info_stack _ _ h]
    exact ⟨rfl,ih.2⟩

theorem parallel_chain_width (n : Nat) :
    (geoInfo (.vertex (.parallelUpChain n))).ins = 2 ∧
    (geoInfo (.vertex (.parallelUpChain n))).outs = 2 ∧
    (geoInfo (.vertex (.parallelUpChain n))).events.head? = some (.vertex 0 (.trivalent .mergeUp)) := by
  let ds := DrawingShape.upwardDots n
  have h := dot_width n
  have hs : (info ds).outs = (info (.vertex .splitUp)).ins := h.2
  have ht : (info (.vertex .mergeUp)).outs = (info (ds.stack (.vertex .splitUp))).ins := by
    rw [info_stack _ _ hs]
    exact h.1.symm
  change (info ((.vertex .mergeUp : DrawingShape).stack (ds.stack (.vertex .splitUp)))).ins = _ ∧
    (info ((.vertex .mergeUp : DrawingShape).stack (ds.stack (.vertex .splitUp)))).outs = _ ∧
    (info ((.vertex .mergeUp : DrawingShape).stack (ds.stack (.vertex .splitUp)))).events.head? = _
  rw [info_stack _ _ ht, info_stack _ _ hs]
  exact ⟨rfl,rfl,rfl⟩

theorem down_chain_width (n : Nat) :
    (geoInfo (.vertex (.parallelDownChain n))).ins = 2 ∧
    (geoInfo (.vertex (.parallelDownChain n))).outs = 2 ∧
    (geoInfo (.vertex (.parallelDownChain n))).events.head? = some (.vertex 0 (.trivalent .mergeDown)) := by
  let ds := DrawingShape.downwardDots n
  have h := down_dot_width n
  have hs : (info ds).outs = (info (.vertex .splitDown)).ins := h.2
  have ht : (info (.vertex .mergeDown)).outs = (info (ds.stack (.vertex .splitDown))).ins := by
    rw [info_stack _ _ hs]
    exact h.1.symm
  change (info ((.vertex .mergeDown : DrawingShape).stack (ds.stack (.vertex .splitDown)))).ins = _ ∧
    (info ((.vertex .mergeDown : DrawingShape).stack (ds.stack (.vertex .splitDown)))).outs = _ ∧
    (info ((.vertex .mergeDown : DrawingShape).stack (ds.stack (.vertex .splitDown)))).events.head? = _
  rw [info_stack _ _ ht, info_stack _ _ hs]
  exact ⟨rfl,rfl,rfl⟩

theorem expanded_info (n : Nat) (o : ProjectionOpening) (c : ProjectionClosing) :
    let I := info (DrawingShape.expandedProjectionGeometry n o c)
    I.ins = 2 ∧ I.outs = 2 ∧ I.events ≠ [] ∧
      ∀ j : Nat, I.events.head? ≠ some (.vertex j .mixedProjection) := by
  let middle : DrawingShape := .horizontal (.straight [false])
    (.horizontal (DrawingShape.upwardDots n) (.straight [false]))
  have mw : (info middle).ins = 3 ∧ (info middle).outs = 3 := by
    unfold middle
    rw [info_horizontal, info_horizontal]
    have h := dot_width n
    simp [ShapeInfo.par, h.1, h.2]
    exact ⟨rfl,rfl⟩
  have frame (a b : DrawingShape) (ha : (info a).outs = 3) (hb : (info b).ins = 3) :
      info (a.stack (middle.stack b)) = (info a).seq ((info middle).seq (info b)) := by
    have hm := mw.2.trans hb.symm
    have hn : (info a).outs = (info (middle.stack b)).ins := by
      rw [info_stack _ _ hm]
      exact ha.trans mw.1.symm
    rw [info_stack _ _ hn, info_stack _ _ hm]
  dsimp only [DrawingShape.expandedProjectionGeometry]
  cases o <;> cases c <;>
    change
      let a : DrawingShape := _
      let b : DrawingShape := _
      (info (a.stack (middle.stack b))).ins = 2 ∧
        (info (a.stack (middle.stack b))).outs = 2 ∧ (info (a.stack (middle.stack b))).events ≠ [] ∧
        ∀ j, (info (a.stack (middle.stack b))).events.head? ≠
          some (.vertex j .mixedProjection)
  all_goals
    dsimp only
    rw [frame _ _ (by rfl) (by rfl)]
    refine ⟨rfl, rfl, (fun h => by cases h), ?_⟩
    intro j h
    -- The first event is the opening cup vertex in both allowed frames.
    cases h

universe u
variable {V : Type u} [Group V] {A B C : Subgroup V}
variable {p q t : Word A B}

def Sized (s : DrawingShape) (p q : Word A B) : Prop :=
  Valid s ∧ (geoInfo s).ins = p.directions.length ∧ (geoInfo s).outs = q.directions.length

theorem sized_seq {a b : DrawingShape} (ha : Sized a p q) (hb : Sized b q t) :
    Sized (a.stack b) p t ∧ geoInfo (a.stack b) = (geoInfo a).seq (geoInfo b) := by
  obtain ⟨hv, he⟩ := geo_stack ha.1 hb.1 (ha.2.2.trans hb.2.1.symm)
  exact ⟨⟨hv, (congrArg ShapeInfo.ins he).trans ha.2.1,
    (congrArg ShapeInfo.outs he).trans hb.2.2⟩, he⟩

theorem sized_par {r s : Word B C} {a b : DrawingShape} (ha : Sized a p q) (hb : Sized b r s) :
    Sized (a.juxtapose b) (p.tensor r) (q.tensor s) ∧
      geoInfo (a.juxtapose b) = (geoInfo a).par (geoInfo b) := by
  obtain ⟨hv, he⟩ := geo_juxtapose ha.1 hb.1
  refine ⟨⟨hv, ?_, ?_⟩, he⟩ <;>
    simp only [he, ShapeInfo.par, ha.2.1, ha.2.2, hb.2.1, hb.2.2,
      Word.directions, List.length_append]

theorem sized_diagram (d : Diagram Complex p q) : Sized d.drawing p q := by
  induction d with
  | vertical _ _ ha hb => exact (sized_seq ha hb).1
  | horizontal _ _ ha hb => exact (sized_par ha hb).1
  | add _ _ ha _ => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | scale _ _ ha => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | associate | unassociate =>
    exact ⟨trivial, by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry,
      DrawingShape.inputs, Word.directions, List.append_assoc],
      by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry, DrawingShape.outputs,
        Word.directions, List.append_assoc]⟩
  | leftUnit | rightUnit | insertLeftUnit | insertRightUnit =>
    exact ⟨trivial, by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry,
      DrawingShape.inputs, Word.directions],
      by simp [geoInfo, info, Diagram.drawing, DrawingShape.geometry,
        DrawingShape.outputs, Word.directions]⟩
  | _ => exact ⟨trivial,rfl,rfl⟩

theorem sized_drawing (d : LabelledDrawing Complex p q) : Sized d.erase p q := by
  induction d with
  | ordinary d => exact sized_diagram d
  | vertical _ _ ha hb => exact (sized_seq ha hb).1
  | horizontal _ _ ha hb => exact (sized_par ha hb).1
  | add _ _ ha _ => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | scale _ _ ha => exact ⟨trivial, ha.2.1, ha.2.2⟩
  | trivalent v => cases v <;> exact ⟨trivial,rfl,rfl⟩
  | bentVertex v => cases v <;> exact ⟨trivial,rfl,rfl⟩
  | parallelUpChain _ _ _ _ ls => exact ⟨trivial, (parallel_chain_width ls.length).1, (parallel_chain_width ls.length).2.1⟩
  | parallelDownChain _ _ _ _ ls => exact ⟨trivial, (down_chain_width ls.length).1, (down_chain_width ls.length).2.1⟩
  | expandedProjection _ _ _ _ _ o c =>
    exact ⟨trivial, (expanded_info 1 o c).1, (expanded_info 1 o c).2.1⟩
  | expandedProjectionChain _ _ _ _ ls _ o c =>
    exact ⟨trivial, (expanded_info ls.length o c).1, (expanded_info ls.length o c).2.1⟩
  | expandedLinearDotProjection _ _ _ _ ls _ o c =>
    exact ⟨trivial, (expanded_info ls.length o c).1, (expanded_info ls.length o c).2.1⟩
  | _ => exact ⟨trivial,rfl,rfl⟩

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams

universe u
variable {V : Type u} [Group V] {A B C D : Subgroup V}

@[reducible] def Raw : {A B : Subgroup V} → Word A B → Type u
  | _, _, .empty _ => PUnit
  | _, _, @Word.up _ _ _ H _ => H
  | _, _, @Word.down _ _ _ H _ => H
  | _, _, .tensor p q => Raw p × Raw q

def rawPoint : {A B : Subgroup V} → (p : Word A B) → Raw p → p.basis.carrier
  | _, _, .empty _, _ => 1
  | _, _, .up _, x => x
  | _, _, .down _, x => x
  | _, _, .tensor p q, x => p.basis.pair q.basis (rawPoint p x.1) (rawPoint q x.2)

abbrev Slot (V : Type u) [Group V] := Subgroup V × Subgroup V × V

def slots : {A B : Subgroup V} → (p : Word A B) → Raw p → List (Slot V)
  | _, _, .empty _, _ => []
  | A, B, .up _, x => [(A, B, x.val)]
  | A, B, .down _, x => [(A, B, x.val)]
  | _, _, .tensor p q, x => slots p x.1 ++ slots q x.2

noncomputable def basisVector (p : Word A B) (x : Raw p) : p.basis.carrier →₀ Complex :=
  Finsupp.single (rawPoint p x) 1

theorem slots_length (p : Word A B) (x : Raw p) :
    (slots p x).length = p.directions.length := by
  induction p with
  | empty | up | down => rfl
  | tensor p q hp hq => simp [slots, Word.directions, hp, hq]

def Selected (xs : List (Slot V)) (n : Nat) (x : V) : Prop :=
  ∃ G G' y z, xs[n]? = some (⊥, G, y) ∧ xs[n+1]? = some (G', ⊥, z) ∧ y*z = x

theorem selected_append_left (l r : List (Slot V)) (n : Nat) (x : V)
    (h : n+1 < l.length) : Selected (l ++ r) n x → Selected l n x := by
  intro ⟨G,G',y,z,hy,hz,hx⟩
  have hn : n < l.length := by omega
  rw [List.getElem?_append_left hn] at hy
  rw [List.getElem?_append_left h] at hz
  exact ⟨G,G',y,z,hy,hz,hx⟩

theorem selected_append_right (l r : List (Slot V)) (n : Nat) (x : V) :
    Selected (l ++ r) (l.length + n) x → Selected r n x := by
  intro ⟨G,G',y,z,hy,hz,hx⟩
  rw [List.getElem?_append_right (by omega), show l.length + n - l.length = n by omega] at hy
  rw [List.getElem?_append_right (by omega), show l.length + n + 1 - l.length = n+1 by omega] at hz
  exact ⟨G,G',y,z,hy,hz,hx⟩

theorem raw_projection_zero (a : ConjEmbedding A C) (b : ConjEmbedding B C)
    (l : ConjEmbedding D A) (r : ConjEmbedding D B) (s : ProjectionDot.Mixed a b l r)
    (xy : Raw ((Word.down a).tensor (.up b))) (z : V)
    (hx : Selected (slots ((Word.down a).tensor (.up b)) xy) 0 z)
    (h : z ≠ s.dot.element.val) :
    (Diagram.mixedProjection (R := Complex) a b l r s.dot s.finite).eval.toLinearMap
      (basisVector ((Word.down a).tensor (.up b)) xy) = 0 := by
  obtain ⟨G,G',y,w,hy,hw,hz⟩ := hx
  change some (A,C,xy.1.val) = some (⊥,G,y) at hy
  change some (C,B,xy.2.val) = some (G',⊥,w) at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hy hw
  have he (t : (Word.basis ((Word.up l).tensor (.down r))).carrier) :
      Generator.mixedProduct a b (Generator.mixedMultiplicationBasis a b l r s.dot t) =
        s.dot.element := by
    refine Quotient.inductionOn t (fun uv => ?_)
    have h₁ : uv.1 = 1 := Subtype.ext (hy.1 ▸ uv.1.property)
    have h₂ : uv.2 = 1 := Subtype.ext (hw.2.1 ▸ uv.2.property)
    change Generator.mixedProduct a b
      (Generator.mixedPair a b (a.toHom uv.1 * s.dot.element * b.toHom uv.2)) = _
    simp [h₁, h₂]
  change (Generator.mixedProjection a b l r s.dot Complex s.finite).toLinearMap
    (Finsupp.single ((Biset.restriction a).pair (Biset.induction b) xy.1 xy.2) 1) = 0
  rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]
  apply Finset.sum_eq_zero
  intro t ht
  exfalso
  rw [Set.Finite.mem_toFinset] at ht
  have hf := ht
  change Generator.mixedMultiplicationBasis a b l r s.dot t =
    (Biset.restriction a).pair (Biset.induction b) xy.1 xy.2 at hf
  have ht' := he t
  rw [hf] at ht'
  let v₁ : C := xy.1
  let v₂ : C := xy.2
  change v₁ * v₂ = _ at ht'
  apply h
  rw [← hz, ← hy.2.2, ← hw.2.2]
  exact congrArg Subtype.val ht'

end CaseFiveInfiniteAux

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

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

universe u
variable {V : Type u} [Group V] {A B C D : Subgroup V}

theorem PreservesSlots.seq {p q t : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {g : Biset.Hom Complex q.basis t.basis} (hf : PreservesSlots f) (hg : PreservesSlots g) :
    PreservesSlots (f.vertical g) :=
  (support_seq (.structural hf) (.structural hg)).1 rfl

theorem PreservesSlots.par {p q : Word A B} {r s : Word B C}
    {f : Biset.Hom Complex p.basis q.basis} {g : Biset.Hom Complex r.basis s.basis}
    (hf : PreservesSlots f) (hg : PreservesSlots g) : PreservesSlots (p := p.tensor r) (q := q.tensor s) (f.horizontal g) :=
  (support_par (.structural hf) (.structural hg)).1 rfl

theorem preserve_id (p : Word A B) : PreservesSlots (Diagram.id (R := Complex) p).eval := by
  intro x
  exact ⟨x,rfl,Diagram.eval_id_apply p _⟩

theorem preserve_leftUnit (p : Word A B) :
    PreservesSlots (Diagram.leftUnit (R := Complex) p).eval := by
  intro x
  refine ⟨x.2, rfl, ?_⟩
  unfold basisVector
  change (Diagram.leftUnit (R := Complex) p).eval.toLinearMap
    (Finsupp.single ((Biset.regular A).pair p.basis 1 (rawPoint p x.2)) 1) = _
  rw [Diagram.eval_leftUnit_single, show ((1,1) : A × B) = 1 from rfl, p.basis.one_act]

theorem preserve_rightUnit (p : Word A B) :
    PreservesSlots (Diagram.rightUnit (R := Complex) p).eval := by
  intro x
  refine ⟨x.1, by simp [slots], ?_⟩
  unfold basisVector
  change (Diagram.rightUnit (R := Complex) p).eval.toLinearMap
    (Finsupp.single (p.basis.pair (Biset.regular B) (rawPoint p x.1) 1) 1) = _
  rw [Diagram.eval_rightUnit_single, inv_one, show ((1,1) : A × B) = 1 from rfl, p.basis.one_act]

theorem preserve_insertLeftUnit (p : Word A B) :
    PreservesSlots (Diagram.insertLeftUnit (R := Complex) p).eval := by
  intro x
  exact ⟨(PUnit.unit,x), rfl, Diagram.eval_insertLeftUnit_single p (rawPoint p x) 1⟩

theorem preserve_insertRightUnit (p : Word A B) :
    PreservesSlots (Diagram.insertRightUnit (R := Complex) p).eval := by
  intro x
  refine ⟨(x,PUnit.unit), by simp [slots], ?_⟩
  change (Biset.insertRightUnit p.basis Complex).toLinearMap (Finsupp.single (rawPoint p x) 1) =
    Finsupp.single (p.basis.pair (Biset.regular B) (rawPoint p x) 1) 1
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]

theorem preserve_associate (p : Word A B) (q : Word B C) (t : Word C D) :
    PreservesSlots (Diagram.associate (R := Complex) p q t).eval := by
  intro x
  exact ⟨(x.1.1,x.1.2,x.2), by simp [slots,List.append_assoc],
    Diagram.eval_associate_single p q t (rawPoint p x.1.1) (rawPoint q x.1.2) (rawPoint t x.2) 1⟩

theorem preserve_unassociate (p : Word A B) (q : Word B C) (t : Word C D) :
    PreservesSlots (Diagram.unassociate (R := Complex) p q t).eval := by
  intro x
  exact ⟨((x.1,x.2.1),x.2.2), by simp [slots,List.append_assoc],
    Diagram.eval_unassociate_single p q t (rawPoint p x.1) (rawPoint q x.2.1) (rawPoint t x.2.2) 1⟩

theorem preserve_boundary_append (a : Boundary A B) (b : Boundary B C) :
    PreservesSlots (a.appendDiagram (R := Complex) b).eval := by
  induction a with
  | empty => exact preserve_leftUnit b.word
  | cons s t ih =>
    exact (preserve_associate s.word t.word b.word).seq ((preserve_id s.word).par (ih b))

theorem preserve_boundary_split (a : Boundary A B) (b : Boundary B C) :
    PreservesSlots (a.splitDiagram (R := Complex) b).eval := by
  induction a with
  | empty => exact preserve_insertLeftUnit b.word
  | cons s t ih =>
    exact ((preserve_id s.word).par (ih b)).seq (preserve_unassociate s.word t.word b.word)

theorem preserve_reorder_to (p : Word A B) : PreservesSlots (p.reorderToBoundary (R := Complex)).eval := by
  induction p with
  | empty => exact preserve_id _
  | up | down => exact preserve_insertRightUnit _
  | tensor p q hp hq => exact (hp.par hq).seq (preserve_boundary_append p.boundary q.boundary)

theorem preserve_reorder_from (p : Word A B) : PreservesSlots (p.reorderFromBoundary (R := Complex)).eval := by
  induction p with
  | empty => exact preserve_id _
  | up | down => exact preserve_rightUnit _
  | tensor p q hp hq => exact (preserve_boundary_split p.boundary q.boundary).seq (hp.par hq)

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

universe u
variable {V : Type u} [Group V] {A B : Subgroup V} {w t : Word A B}

theorem SupportRule.reject {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {events : Code} (hne : events ≠ []) (hn : ∀ j, events.head? ≠ some (.vertex j .mixedProjection)) :
    SupportRule f events :=
  ⟨fun he => False.elim (hne he), fun j hj => False.elim (hn j hj)⟩

theorem reject_head {p q : Word A B} {f : Biset.Hom Complex p.basis q.basis}
    {events : Code} {e : PlanarEvent}
    (he : events.head? = some e) (hn : ∀ j, e ≠ .vertex j .mixedProjection) :
    SupportRule f events := by
  apply SupportRule.reject
  · intro h
    rw [h] at he
    cases he
  · intro j h
    exact hn j (Option.some.inj (he.symm.trans h))

theorem support_diagram (d : Diagram Complex w t) : SupportRule d.eval (geoInfo d.drawing).events := by
  induction d with
  | id p => exact .structural (preserve_id p)
  | leftUnit p => exact .structural (preserve_leftUnit p)
  | rightUnit p => exact .structural (preserve_rightUnit p)
  | insertLeftUnit p => exact .structural (preserve_insertLeftUnit p)
  | insertRightUnit p => exact .structural (preserve_insertRightUnit p)
  | associate p q r => exact .structural (preserve_associate p q r)
  | unassociate p q r => exact .structural (preserve_unassociate p q r)
  | mixedProjection a b l r s hf => exact .projection (support_projection a b l r ⟨s, hf⟩)
  | vertical d e hd he =>
    change SupportRule (d.eval.vertical e.eval) (geoInfo (d.drawing.stack e.drawing)).events
    rw [(sized_seq (sized_diagram d) (sized_diagram e)).2]
    exact support_seq hd he
  | horizontal d e hd he =>
    have h := sized_diagram d
    rw [show geoInfo (Diagram.horizontal d e).drawing = _ from (sized_par h (sized_diagram e)).2]
    simpa only [Diagram.eval, LabelledDrawing.interpret, ScopedDiagram.eval, ShapeInfo.par, h.2.2] using support_par hd he
  | _ => exact SupportRule.other (fun j h => by cases h)

theorem support_drawing (d : LabelledDrawing Complex w t) :
    SupportRule d.interpret.eval (geoInfo d.erase).events := by
  induction d with
  | ordinary d => exact support_diagram d
  | trivalent v => cases v <;> exact SupportRule.other (fun j h => by cases h)
  | bentVertex v => cases v <;> exact SupportRule.other (fun j h => by cases h)
  | parallelUpChain _ _ _ _ ls =>
    exact reject_head (parallel_chain_width ls.length).2.2 (fun j h => by cases h)
  | parallelDownChain _ _ _ _ ls =>
    exact reject_head (down_chain_width ls.length).2.2 (fun j h => by cases h)
  | expandedProjection _ _ _ _ _ o c =>
    exact .reject (expanded_info 1 o c).2.2.1 (expanded_info 1 o c).2.2.2
  | expandedProjectionChain _ _ _ _ ls _ o c =>
    exact .reject (expanded_info ls.length o c).2.2.1 (expanded_info ls.length o c).2.2.2
  | expandedLinearDotProjection _ _ _ _ ls _ o c =>
    exact .reject (expanded_info ls.length o c).2.2.1 (expanded_info ls.length o c).2.2.2
  | compactProjection a b l r ss => exact .projection (support_projections a b l r ss)
  | vertical d e hd he =>
    change SupportRule (d.interpret.eval.vertical e.interpret.eval) (geoInfo (d.erase.stack e.erase)).events
    rw [(sized_seq (sized_drawing d) (sized_drawing e)).2]
    exact support_seq hd he
  | horizontal d e hd he =>
    have h := sized_drawing d
    rw [show geoInfo (LabelledDrawing.horizontal d e).erase = _ from (sized_par h (sized_drawing e)).2]
    simpa only [Diagram.eval, LabelledDrawing.interpret, ScopedDiagram.eval, ShapeInfo.par, h.2.2] using support_par hd he
  | _ => exact SupportRule.other (fun j h => by cases h)

theorem support_atBoundary {b t : Boundary A B} {s : PlanarShape}
    (d : LabelledDrawing.PlanarAtBoundary Complex b t s) :
    SupportRule d.interpret.eval (geoInfo d.diagram.erase).events := by
  cases d with
  | mk w q d hb ht hs =>
    subst b t
    change SupportRule ((w.reorderFromBoundary (R := Complex)).eval.vertical
      (d.interpret.eval.vertical (q.reorderToBoundary (R := Complex)).eval)) _
    simpa only [List.nil_append, List.append_nil] using
      support_seq (.structural (preserve_reorder_from w))
        (support_seq (support_drawing d) (.structural (preserve_reorder_to q)))

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams

abbrev U := Multiplicative Int
abbrev P : Subgroup U := ⊤
abbrev T : Subgroup U := ⊥
abbrev p := MackeyDiagrams.ConjEmbedding.id P
abbrev a : MackeyDiagrams.ConjEmbedding T P :=
  { toHom := Subgroup.inclusion bot_le
    hasRepresentative := ⟨1, fun _ => by simp⟩ }
abbrev i := MackeyDiagrams.ConjEmbedding.id T
abbrev comp := @MackeyDiagrams.ConjEmbedding.comp U _
abbrev up := @MackeyDiagrams.Word.up U _
abbrev down := @MackeyDiagrams.Word.down U _
abbrev tensor := @MackeyDiagrams.Word.tensor U _
abbrev stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
abbrev beside := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
abbrev plain := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
abbrev ga := up a
abbrev ad := down a
abbrev df := up a
abbrev gc := up p
abbrev ce := down p
abbrev ef := up a
abbrev ai := up i
abbrev fj := down i
abbrev ck := up a
abbrev bottom := tensor ga (tensor ad df)
abbrev top := tensor gc (tensor ce ef)
theorem indexOne : (MackeyDiagrams.ConjEmbedding.toHom p).range.index = 1 := by
  change (MonoidHom.id P).range.index = 1
  rw [MonoidHom.range_eq_top_of_surjective (MonoidHom.id P) (fun x => ⟨x, rfl⟩),
    Subgroup.index_top]
abbrev leftDot := MackeyDiagrams.Dot.id (comp p p)
theorem leftFinite :
    ∀ z, Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis p p p p leftDot w = z} := by
  intro z
  have finite : (MackeyDiagrams.ConjEmbedding.toHom p).range.FiniteIndex :=
    ⟨by rw [indexOne]; decide⟩
  refine Set.Finite.subset (MackeyDiagrams.Generator.multiplicationCap_finiteFiber
    p finite (MackeyDiagrams.Generator.mixedProduct p p z)) ?_
  intro w hw
  have hcap : MackeyDiagrams.Generator.mixedProduct p p
      (MackeyDiagrams.Generator.mixedMultiplicationBasis p p p p leftDot w) =
      MackeyDiagrams.Generator.multiplicationCapBasis p w := by
    refine Quotient.inductionOn w (fun xy => ?_)
    change MackeyDiagrams.Generator.mixedProduct p p
      (MackeyDiagrams.Generator.mixedPair p p (xy.1 * 1 * xy.2)) = xy.1 * xy.2
    rw [MackeyDiagrams.Generator.mixedProduct_mixedPair, mul_one]
  exact hcap.symm.trans (congrArg (MackeyDiagrams.Generator.mixedProduct p p) hw)
abbrev drawId := fun {K H : Subgroup U} (w : MackeyDiagrams.Word K H) =>
  plain (MackeyDiagrams.Diagram.id w)
abbrev leftMixed := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex)
  p p a a [(1, MackeyDiagrams.Dot.id (comp p a))]
abbrev leftParallel := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex)
  p a p a [(1, MackeyDiagrams.Dot.id (comp p a))]
abbrev leftProject := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex)
  p p p p [(1, ⟨leftDot, leftFinite⟩)]
abbrev left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
  stack (plain (MackeyDiagrams.Diagram.unassociate ga ad df))
    (stack (beside leftMixed (drawId df))
      (stack (plain (MackeyDiagrams.Diagram.associate ce gc df))
        (stack (beside (drawId ce) leftParallel)
          (stack (plain (MackeyDiagrams.Diagram.unassociate ce gc ef))
            (stack (beside leftProject (drawId ef))
              (plain (MackeyDiagrams.Diagram.associate gc ce ef)))))))
abbrev dot := fun (b c : MackeyDiagrams.ConjEmbedding T P) (x : P) =>
  ({ element := x
     intertwines := fun h => by
       have hh : h = 1 := Subsingleton.elim _ _
       simp [hh] } : MackeyDiagrams.Dot b c)
abbrev Lower := MackeyDiagrams.DotLabel Complex (comp a i) (comp a i)
abbrev Middle := MackeyDiagrams.DotLabel Complex (comp a i) (comp p a)
abbrev Upper := MackeyDiagrams.DotLabel Complex (comp p a) (comp a i)
theorem rightFinite : ∀ (d : MackeyDiagrams.Dot (comp a i) (comp a i)) z,
    Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a a i i d w = z} := by
  let : Finite (MackeyDiagrams.Word.basis (tensor ai fj)).carrier := by
    change Finite (Quotient (MackeyDiagrams.Biset.balance
      (MackeyDiagrams.Biset.induction i) (MackeyDiagrams.Biset.restriction i)))
    infer_instance
  intro d z
  exact Set.toFinite _
noncomputable def right := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
  let projectionTerms : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a a i i) :=
    List.map (fun (term : Complex × MackeyDiagrams.Dot (comp a i) (comp a i)) =>
      (term.1, (⟨term.2, rightFinite term.2⟩ : MackeyDiagrams.ProjectionDot.Mixed a a i i)))
      (MackeyDiagrams.DotLabel.terms lower)
  let first := MackeyDiagrams.LabelledDrawing.compactProjection a a i i projectionTerms
  let second := MackeyDiagrams.LabelledDrawing.parallelUp a i p a
    (MackeyDiagrams.DotLabel.terms middle)
  let third := MackeyDiagrams.LabelledDrawing.mixedMultiplication p a a i
    (MackeyDiagrams.DotLabel.terms upper)
  (stack (beside (drawId ga) first)
    (stack (plain (MackeyDiagrams.Diagram.unassociate ga ai fj))
      (stack (beside second (drawId fj))
        (stack (plain (MackeyDiagrams.Diagram.associate gc ck fj))
          (beside (drawId gc) third)))) :
    MackeyDiagrams.LabelledDrawing Complex bottom top)
noncomputable def rightShape := MackeyDiagrams.LabelledDrawing.planarShape (right 0 0 0)
abbrev bottomBoundary := MackeyDiagrams.Word.boundary bottom
abbrev topBoundary := MackeyDiagrams.Word.boundary top
abbrev RightDrawing := MackeyDiagrams.LabelledDrawing.PlanarAtBoundary
  Complex bottomBoundary topBoundary rightShape
noncomputable def rightAt := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
  ({ bottom := bottom
     top := top
     diagram := right lower middle upper
     bottom_eq := rfl
     top_eq := rfl
     shape_eq := by rfl } : RightDrawing)
noncomputable def rightTerm := fun r : P =>
  right (Finsupp.single (dot (comp a i) (comp a i) r) 1)
    (Finsupp.single (dot (comp a i) (comp p a) r) 1)
    (Finsupp.single (dot (comp p a) (comp a i) 1) 1)
abbrev X := MackeyDiagrams.Word.basis bottom
abbrev Y := MackeyDiagrams.Word.basis top
abbrev inputPair := fun g x : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair a a x)
abbrev outputPair := fun h y : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction p)
    (MackeyDiagrams.Word.basis (tensor ce ef)) h (MackeyDiagrams.Generator.mixedPair p a y)
noncomputable def input := fun g x : P => Finsupp.single (inputPair g x) (1 : Complex)
noncomputable def output := fun z : P => Finsupp.single (outputPair z 1) (1 : Complex)
noncomputable def eval := fun (d : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d))
noncomputable def evalAt := fun (d : MackeyDiagrams.ScopedDiagram Complex
    (MackeyDiagrams.Boundary.word bottomBoundary) (MackeyDiagrams.Boundary.word topBoundary)) =>
  MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
    (MackeyDiagrams.ScopedDiagram.vertical
      (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderToBoundary bottom))
      (MackeyDiagrams.ScopedDiagram.vertical d
        (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderFromBoundary top)))))
noncomputable def interpretRight := fun (d : RightDrawing) =>
  MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret (s := rightShape) d
noncomputable def rightSum := fun (terms : List (Complex × RightDrawing)) =>
  MackeyDiagrams.ScopedDiagram.linearCombination
    (List.map (fun term => (term.1, interpretRight term.2)) terms)

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams

-- Example 6.6 and (6.3)–(6.4), archived p. 27, published 28 November
-- revision p. 29. The column calculations use the actual balanced basis.
theorem bot_forced (Q : Subgroup U) (e : ConjEmbedding Q T) : Q = T := by
  apply le_antisymm _ bot_le
  intro x hx
  have he : e.toHom ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
  have hinj := e.injective (he.trans (map_one _).symm)
  exact (congrArg Subtype.val hinj : x = 1)

theorem input_surj (v : X.carrier) : ∃ g x : P, inputPair g x = v := by
  refine Quotient.inductionOn v (fun gy => ?_)
  exact ⟨gy.1, Generator.mixedProduct a a gy.2,
    congrArg ((Biset.induction a).pair _ gy.1) (Generator.mixedPair_mixedProduct a a gy.2)⟩

theorem output_mul (g x : P) : outputPair g x = outputPair (g * x) 1 := by
  have h := (Biset.induction p).pair_balance (Word.basis (tensor ce ef))
    x g (Generator.mixedPair p a 1)
  rw [show (Biset.induction p).act (1, x⁻¹) g = g * x by
    change 1 * g * (p.toHom (x⁻¹))⁻¹ = _
    simp [ConjEmbedding.id]] at h
  change outputPair (g * x) 1 =
    (Biset.induction p).pair _ g
      ((Word.basis (tensor ce ef)).act (x,1) (Generator.mixedPair p a 1)) at h
  rw [show (Word.basis (tensor ce ef)).act (x,1) (Generator.mixedPair p a 1) =
      Generator.mixedPair p a x by
    unfold Generator.mixedPair
    rw [Biset.act_pair]
    change (Biset.restriction p).pair (Biset.induction a)
      (p.toHom x * 1 * (1 : P)⁻¹) (1 * 1 * (a.toHom 1)⁻¹) = _
    simp [ConjEmbedding.id]] at h
  exact h.symm

theorem target_identification :
    ∃ identify : Y.carrier ≃ P, ∀ h y : P, identify (outputPair h y) = h * y := by
  let pr := Biset.leftUnitBasis (Word.basis (tensor ce ef))
  let prod := fun z : Y.carrier => Generator.mixedProduct p a (pr z)
  have pr_mul (g x : P) : prod (outputPair g x) = g * x := by
    unfold prod pr outputPair
    change Generator.mixedProduct p a
      ((Word.basis (tensor ce ef)).act (g,1) (Generator.mixedPair p a x)) = _
    unfold Generator.mixedPair
    rw [Biset.act_pair]
    change (p.toHom g * x * (1 : P)⁻¹) * (1 * 1 * (a.toHom 1)⁻¹) = _
    simp [ConjEmbedding.id]
  refine ⟨⟨prod, (outputPair · 1), ?_, ?_⟩, pr_mul⟩
  · intro z
    refine Quotient.inductionOn z (fun gy => ?_)
    change outputPair (prod ((Biset.induction p).pair _ gy.1 gy.2)) 1 =
      (Biset.induction p).pair _ gy.1 gy.2
    rw [← Generator.mixedPair_mixedProduct p a gy.2] at *
    -- Keep the inner quotient representative independent of its normal form.
    change outputPair (prod (outputPair gy.1 (Generator.mixedProduct p a gy.2))) 1 =
      outputPair gy.1 (Generator.mixedProduct p a gy.2)
    rw [pr_mul, output_mul gy.1 (Generator.mixedProduct p a gy.2)]
  · intro z
    rw [pr_mul, mul_one]

theorem terms_single {S K : Subgroup U} {b c : ConjEmbedding S K} (d : Dot b c) :
    DotLabel.terms (Finsupp.single d (1 : Complex)) = [(1, d)] := by
  classical
  simp [DotLabel.terms]

theorem right_fiber (d : Dot (comp a i) (comp a i)) (x : P) :
    {w | Generator.mixedProduct a a (Generator.mixedMultiplicationBasis a a i i d w) = x} =
      if x = d.element then
        {Biset.pair (Biset.induction i) (Biset.restriction i) 1 1} else ∅ := by
  classical
  have all (w : (Word.basis (tensor ai fj)).carrier) :
      w = Biset.pair (Biset.induction i) (Biset.restriction i) 1 1 := by
    refine Quotient.inductionOn w (fun xy => ?_)
    have he : xy = (1, 1) := Subsingleton.elim _ _
    rw [he]
    rfl
  ext w
  rw [all w]
  change Generator.mixedProduct a a (Generator.mixedPair a a
    (a.toHom 1 * d.element * a.toHom 1)) = x ↔ _
  rw [Generator.mixedProduct_mixedPair, map_one, one_mul, mul_one]
  by_cases h : x = d.element <;> simp [h, eq_comm]

-- Step 1 of the checked right-hand calculation uses the finite transfer
-- fiber. The middle and upper steps use its actual basis representatives.
theorem right_column (r g x : P) :
    eval (rightTerm r) (input g x) = if x = r then output (g*x) else 0 := by
  classical
  let lower := dot (comp a i) (comp a i) r
  let middle := dot (comp a i) (comp p a) r
  let upper := dot (comp p a) (comp a i) 1
  have hf (z : P) : Set.Finite {w | Generator.mixedProduct a a
      (Generator.mixedMultiplicationBasis a a i i lower w) = z} := by
    rw [right_fiber]
    split <;> simp
  have h := ((EvaluationWithOneProjection a a a p p a).2 T i i a).1 lower hf middle upper g x
  -- The two proofs of finiteness on the same mixed-product fiber are
  -- definitionally interchangeable by proof irrelevance.
  unfold rightTerm right
  simp only [terms_single, List.map_cons, List.map_nil]
  refine h.trans ?_
  symm
  -- The displayed term has support at the one admissible second coordinate.
  let w₀ := Biset.pair (Biset.induction i) (Biset.restriction i) 1 1
  change (if x = r then output (g*x) else 0) =
    (hf x).toFinset.sum (fun w =>
      Finsupp.single (outputPair (g * a.toHom (Quotient.out w).1 * r)
        ((1 : P) * a.toHom (Quotient.out w).2)) 1)
  have value (w : (Word.basis (tensor ai fj)).carrier) :
      Finsupp.single (outputPair (g * a.toHom (Quotient.out w).1 * r)
        ((1 : P) * a.toHom (Quotient.out w).2)) (1 : Complex) = output (g*r) := by
    rw [show (Quotient.out w).1 = (1 : T) from Subsingleton.elim _ _,
      show (Quotient.out w).2 = (1 : T) from Subsingleton.elim _ _]
    simp [output]
  by_cases hx : x = r
  · have ht : (hf x).toFinset = {w₀} := by
      ext w
      rw [Set.Finite.mem_toFinset, right_fiber]
      simp [hx, lower, w₀]
    rw [ite_eq_left hx, ht, Finset.sum_singleton, value, hx]
  · have ht : (hf x).toFinset = ∅ := by
      ext w
      rw [Set.Finite.mem_toFinset, right_fiber]
      simp [hx, lower]
    rw [ite_eq_right hx, ht, Finset.sum_empty]



theorem capPair (v w : P) :
    (Biset.induction p).pair (Biset.restriction p) v w =
      (Biset.induction p).pair (Biset.restriction p) (v*w) 1 := by
  have h := (Biset.induction p).pair_balance (Biset.restriction p) w v 1
  change (Biset.induction p).pair (Biset.restriction p)
    (1 * v * (p.toHom w⁻¹)⁻¹) 1 =
    (Biset.induction p).pair (Biset.restriction p) v (p.toHom w * 1 * (1:P)⁻¹) at h
  simpa [ConjEmbedding.id] using h.symm

theorem left_fiber (z : P) :
    {w | Generator.mixedProduct p p (Generator.mixedMultiplicationBasis p p p p leftDot w) = z} =
      {(Biset.induction p).pair (Biset.restriction p) z 1} := by
  ext w
  refine Quotient.inductionOn w (fun xy => ?_)
  change Generator.mixedProduct p p (Generator.mixedPair p p (xy.1 * 1 * xy.2)) = z ↔
    (Biset.induction p).pair (Biset.restriction p) xy.1 xy.2 =
      (Biset.induction p).pair (Biset.restriction p) z 1
  rw [Generator.mixedProduct_mixedPair, mul_one, capPair]
  constructor
  · exact fun h => congrArg (fun v => (Biset.induction p).pair (Biset.restriction p) v 1) h
  · intro h
    have he := congrArg (Generator.multiplicationCapBasis p) h
    change (xy.1 * xy.2) * 1 = z * 1 at he
    simpa using he

noncomputable def leftNative :
    LabelledDrawing Complex (tensor (tensor ga ad) df) (tensor (tensor gc ce) ef) :=
  stack (beside leftMixed (drawId df))
    (stack (plain (Diagram.associate ce gc df))
      (stack (beside (drawId ce) leftParallel)
        (stack (plain (Diagram.unassociate ce gc ef))
          (beside leftProject (drawId ef)))))

-- Steps 1–3 of the checked Case 5 left-shape evaluation apply locally.
-- The two structural isomorphisms below align its native parentheses with
-- Example 6.6. The fiber proof uses the full-range inclusion p.
theorem left_column (g x : P) : eval left (input g x) = output (g*x) := by
  classical
  let q := fun z : P => {w | Generator.mixedProduct p p
      (Generator.mixedMultiplicationBasis p p p p leftDot w) = z}
  have hf (z : P) : (q z).Finite := by
    change Set.Finite {w | Generator.mixedProduct p p
      (Generator.mixedMultiplicationBasis p p p p leftDot w) = z}
    rw [left_fiber]
    exact Set.finite_singleton _
  let nativeIn := (Biset.induction a).pair (Biset.restriction a) g x
  have h := ((EvaluationWithOneProjection a a a p p a).1 p p p).1
    (Dot.id (comp p a)) (Dot.id (comp p a)) leftDot hf g x
  have hNative :
      leftNative.interpret.eval.toLinearMap
        (Finsupp.single ((Word.basis (tensor ga ad)).pair (Biset.induction a) nativeIn 1) 1) =
      (hf (g*x)).toFinset.sum (fun w =>
        Finsupp.single ((Word.basis (tensor gc ce)).pair (Biset.induction a) w 1) 1) := by
    have hh : p.toHom g * (Dot.id (comp p a)).element * p.toHom x *
        (Dot.id (comp p a)).element = g*x := by
      change g * 1 * x * 1 = _
      simp
    dsimp only at h
    rw [hh] at h
    exact h
  let w₀ := (Biset.induction p).pair (Biset.restriction p) (g*x) 1
  have hff : (hf (g*x)).toFinset = {w₀} := by
    ext w
    rw [Set.Finite.mem_toFinset]
    change w ∈ {w | Generator.mixedProduct p p
      (Generator.mixedMultiplicationBasis p p p p leftDot w) = g*x} ↔ _
    rw [left_fiber]
    simp [w₀]
  rw [hff, Finset.sum_singleton] at hNative
  have htail : (Biset.associate (Word.basis gc) (Word.basis ce) (Word.basis ef) Complex).toLinearMap
      (leftNative.interpret.eval.toLinearMap
        (Finsupp.single ((Word.basis (tensor ga ad)).pair (Biset.induction a) nativeIn 1) 1)) =
      output (g*x) := by
    rw [hNative]
    exact Diagram.eval_associate_single (R := Complex) gc ce ef (g*x) 1 1 1
  have h_split :
      eval left (input g x) =
      (Biset.associate (Word.basis gc) (Word.basis ce) (Word.basis ef) Complex).toLinearMap
        (leftNative.interpret.eval.toLinearMap
          ((Biset.unassociate (Word.basis ga) (Word.basis ad) (Word.basis df) Complex).toLinearMap
            (input g x))) := by
    -- Change only the association of the vertical composite.
    have e : left.interpret.eval =
        ((Diagram.unassociate (R := Complex) ga ad df).eval.vertical leftNative.interpret.eval).vertical
        (Diagram.associate (R := Complex) gc ce ef).eval := by
      unfold leftNative
      simp only [LabelledDrawing.interpret, ScopedDiagram.eval, Biset.Hom.vertical_assoc]
    exact congrArg (fun m : Biset.Hom Complex X Y => m.toLinearMap (input g x)) e
  rw [h_split]
  change (Biset.associate (Word.basis gc) (Word.basis ce) (Word.basis ef) Complex).toLinearMap
    (leftNative.interpret.eval.toLinearMap
      ((Diagram.unassociate (R := Complex) ga ad df).eval.toLinearMap
        (Finsupp.single ((Word.basis ga).pair (Word.basis (tensor ad df)) g
          ((Word.basis ad).pair (Word.basis df) x 1)) 1))) = _
  rw [Diagram.eval_unassociate_single]
  exact htail

end CaseFiveInfiniteAux

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

theorem right_named_support (lower : Lower) (middle : Middle) (upper : Upper) (g x : P)
    (hx : x ∉ Finset.image Dot.element (Finsupp.support lower)) :
    eval (LabelledDrawing.PlanarAtBoundary.diagram (rightAt lower middle upper)) (input g x) = 0 := by
  classical
  let ss := List.map (fun (t : Complex × Dot (comp a i) (comp a i)) =>
      (t.1, (⟨t.2, rightFinite t.2⟩ : ProjectionDot.Mixed a a i i))) (DotLabel.terms lower)
  let prj := (LabelledDrawing.compactProjection (R := Complex) a a i i ss).interpret.eval
  let xx : Raw (tensor ad df) := (x,1)
  have hz : prj.toLinearMap (basisVector (tensor ad df) xx) = 0 := by
    apply projections_zero a a i i ss xx (x : U)
    · exact ⟨P,P,(x : U),1,rfl,rfl,mul_one _⟩
    · intro t ht he
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp ht
      obtain ⟨d, hd, hd'⟩ := List.mem_map.mp hterm
      apply hx
      refine Finset.mem_image.mpr ⟨d, by simpa using hd, ?_⟩
      apply Subtype.ext
      exact (congrArg (fun u : Complex × Dot (comp a i) (comp a i) => u.2.element.val) hd').trans he.symm
  suffices h : ((Diagram.id (R := Complex) ga).eval.horizontal prj).toLinearMap (input g x) = 0 by
    let second := LabelledDrawing.parallelUp a i p a (DotLabel.terms middle)
    let third := LabelledDrawing.mixedMultiplication p a a i (DotLabel.terms upper)
    let tail := stack (plain (Diagram.unassociate ga ai fj))
      (stack (beside second (drawId fj))
        (stack (plain (Diagram.associate gc ck fj)) (beside (drawId gc) third)))
    change tail.interpret.eval.toLinearMap (((Diagram.id (R := Complex) ga).eval.horizontal prj).toLinearMap
      (input g x)) = 0
    rw [h, map_zero]
  change ((Diagram.id (R := Complex) ga).eval.horizontal prj).toLinearMap
    (basisVector bottom (g,xx)) = 0
  rw [basis_horizontal, hz, map_zero]

theorem fixed_right_code (d : RightDrawing) : (geoInfo d.diagram.erase).events = rightCode := by
  have hs := congrArg PlanarShape.wiring d.shape_eq
  change Quotient.mk PlanarCode.setoid (geoInfo d.diagram.erase).events =
    Quotient.mk PlanarCode.setoid rightCode at hs
  exact (rigid_eq (Quotient.exact hs)).2 rigid_rightCode

-- The shape fiber in the statement is wider than the explicit family in
-- ExpansionIntoRightDiagrams. Its finite-orbit iff applies only to that
-- family. Rigidity and the support induction retain arbitrary typed syntax.
theorem right_all_support (d : RightDrawing) :
    ∃ S : Finset P, ∀ g x : P, x ∉ S → evalAt (interpretRight d) (input g x) = 0 := by
  classical
  have h := support_atBoundary d
  rw [fixed_right_code d] at h
  have he := support_seq (.structural (preserve_reorder_to bottom))
    (support_seq h (.structural (preserve_reorder_from top)))
  change SupportRule
    (Biset.Hom.vertical (Word.reorderToBoundary (R := Complex) bottom).eval
      ((interpretRight d).eval.vertical (Word.reorderFromBoundary (R := Complex) top).eval))
    rightCode at he
  obtain ⟨_, S, hS⟩ := he.2 1 rfl
  let lift : U → P := fun u => ⟨u, Subgroup.mem_top u⟩
  refine ⟨S.image lift, ?_⟩
  intro g x hx
  let inp : Raw bottom := (g,x,1)
  have hx' : (x : U) ∉ S := fun hh =>
    hx (Finset.mem_image.mpr ⟨x.val, hh, Subtype.ext rfl⟩)
  have hp : Selected (slots bottom inp) 1 (x : U) :=
    ⟨P,P,(x : U),1,rfl,rfl,mul_one _⟩
  exact hS inp (x : U) hp hx'

theorem evalAt_sum (terms : List (Complex × RightDrawing)) (v : X.carrier →₀ Complex) :
    evalAt (rightSum terms) v = (terms.map (fun t => t.1 • evalAt (interpretRight t.2) v)).sum := by
  let start := (Word.reorderToBoundary (R := Complex) bottom).eval.toLinearMap
  let finish := (Word.reorderFromBoundary (R := Complex) top).eval.toLinearMap
  induction terms with
  | nil =>
    change finish 0 = 0
    exact map_zero finish
  | cons t ts ih =>
    have split : rightSum (t::ts) = .add (.scale t.1 (interpretRight t.2)) (rightSum ts) := rfl
    rw [split, List.map_cons, List.sum_cons, ← ih]
    change finish (t.1 • (interpretRight t.2).eval.toLinearMap (start v) +
      (rightSum ts).eval.toLinearMap (start v)) =
      t.1 • finish ((interpretRight t.2).eval.toLinearMap (start v)) +
        finish ((rightSum ts).eval.toLinearMap (start v))
    rw [map_add, map_smul]

theorem finite_right_sum (terms : List (Complex × RightDrawing)) :
    (∃ S : Finset P, ∀ g x : P, x ∉ S → evalAt (rightSum terms) (input g x) = 0) ∧
    evalAt (rightSum terms) ≠ eval left := by
  classical
  have support : ∃ S : Finset P, ∀ g x : P, x ∉ S → evalAt (rightSum terms) (input g x) = 0 := by
    induction terms with
    | nil => exact ⟨∅, fun _ _ _ => by rw [evalAt_sum]; rfl⟩
    | cons t ts ih =>
      obtain ⟨S, hs⟩ := right_all_support t.2
      obtain ⟨T, ht⟩ := ih
      refine ⟨S ∪ T, ?_⟩
      intro g x hx
      have hS : x ∉ S := fun h => hx (Finset.mem_union.mpr (Or.inl h))
      have hT : x ∉ T := fun h => hx (Finset.mem_union.mpr (Or.inr h))
      rw [evalAt_sum, List.map_cons, List.sum_cons, ← evalAt_sum, hs g x hS, ht g x hT, smul_zero, add_zero]
  refine ⟨support, ?_⟩
  intro he
  obtain ⟨S, hS⟩ := support
  have : Infinite U := by
    change Infinite Int
    infer_instance
  have : Infinite P := Infinite.of_injective (fun u : U => (⟨u,Subgroup.mem_top u⟩ : P))
    (fun _ _ h => congrArg Subtype.val h)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
  have hz := hS 1 x hx
  rw [he, left_column, one_mul] at hz
  exact Finsupp.single_ne_zero.mpr one_ne_zero hz

theorem pointwise_finiteness (v : X.carrier →₀ Complex) :
    Set.Finite {r : P | eval (rightTerm r) v ≠ 0} := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero, ne_eq, not_true_eq_false, Set.ofPred_false] using
      (Set.finite_empty : (∅ : Set P).Finite)
  | add v w hv hw =>
    refine (hv.union hw).subset ?_
    intro r hr
    change eval (rightTerm r) (v+w) ≠ 0 at hr
    rw [map_add] at hr
    by_cases h : eval (rightTerm r) v = 0
    · exact Or.inr (fun hw => hr (by rw [h, hw, add_zero]))
    · exact Or.inl h
  | single v c =>
    obtain ⟨g,x,rfl⟩ := input_surj v
    refine (Set.finite_singleton x).subset ?_
    intro r hr
    change eval (rightTerm r) (Finsupp.single (inputPair g x) c) ≠ 0 at hr
    rw [← Finsupp.smul_single_one, map_smul] at hr
    change c • eval (rightTerm r) (input g x) ≠ 0 at hr
    rw [right_column] at hr
    by_contra h
    have hx : x ≠ r := fun he => h (Set.mem_singleton_iff.mpr he.symm)
    exact hr (by rw [ite_eq_right hx, smul_zero])

-- Use the full cyclic index in the single indexed drawing. On a basis column
-- all terms away from the named index are zero. The checked linear evaluation
-- of PointwiseIndexedDrawing extends this calculation to every input.
theorem pointwise_column_sum :
    ∃ finite : ∀ v : X.carrier →₀ Complex,
      Set.Finite {x : P | eval (rightTerm x) v ≠ 0},
    let drawing : PointwiseIndexedDrawing Complex bottom top P := ⟨rightTerm, finite⟩
    ∀ v : X.carrier →₀ Complex, eval left v = drawing.evalAt v := by
  classical
  refine ⟨pointwise_finiteness, ?_⟩
  let drawing : PointwiseIndexedDrawing Complex bottom top P := ⟨rightTerm, pointwise_finiteness⟩
  change ∀ v : X.carrier →₀ Complex, eval left v = drawing.evalAt v
  suffices h : eval left = drawing.eval by
    intro v
    exact (LinearMap.congr_fun h v).trans (drawing.eval_apply v)
  apply Finsupp.lhom_ext
  intro v c
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  congr 1
  obtain ⟨g,x,rfl⟩ := input_surj v
  change eval left (input g x) = drawing.eval (input g x)
  rw [left_column, PointwiseIndexedDrawing.eval_apply, PointwiseIndexedDrawing.evalAt_def]
  let indices := (pointwise_finiteness (input g x)).toFinset
  change output (g*x) = ∑ r ∈ indices, eval (rightTerm r) (input g x)
  rw [Finset.sum_eq_single x]
  · rw [right_column, ite_eq_left rfl]
  · intro r _ hr
    rw [right_column, ite_eq_right (Ne.symm hr)]
  · intro hn
    have hz : eval (rightTerm x) (input g x) = 0 := by
      by_contra h
      exact hn ((Set.Finite.mem_toFinset _).2 h)
    rw [right_column, ite_eq_left rfl] at hz
    exact False.elim (Finsupp.single_ne_zero.mpr one_ne_zero hz)

end CaseFiveInfiniteAux

theorem CaseFiveRequiresInfiniteExpansion : (
let U := Multiplicative Int
let P : Subgroup U := ⊤
let T : Subgroup U := ⊥
let p := MackeyDiagrams.ConjEmbedding.id P
let a : MackeyDiagrams.ConjEmbedding T P :=
  { toHom := Subgroup.inclusion bot_le
    hasRepresentative := ⟨1, fun _ => by simp⟩ }
let i := MackeyDiagrams.ConjEmbedding.id T
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let beside := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let plain := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let ga := up a
let ad := down a
let df := up a
let gc := up p
let ce := down p
let ef := up a
let ai := up i
let fj := down i
let ck := up a
let bottom := tensor ga (tensor ad df)
let top := tensor gc (tensor ce ef)
let indexOne : (MackeyDiagrams.ConjEmbedding.toHom p).range.index = 1 := by
  change (MonoidHom.id P).range.index = 1
  rw [MonoidHom.range_eq_top_of_surjective (MonoidHom.id P) (fun x => ⟨x, rfl⟩),
    Subgroup.index_top]
let leftDot := MackeyDiagrams.Dot.id (comp p p)
let leftFinite :
    ∀ z, Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis p p p p leftDot w = z} := by
  intro z
  have finite : (MackeyDiagrams.ConjEmbedding.toHom p).range.FiniteIndex :=
    ⟨by rw [indexOne]; decide⟩
  refine Set.Finite.subset (MackeyDiagrams.Generator.multiplicationCap_finiteFiber
    p finite (MackeyDiagrams.Generator.mixedProduct p p z)) ?_
  intro w hw
  have hcap : MackeyDiagrams.Generator.mixedProduct p p
      (MackeyDiagrams.Generator.mixedMultiplicationBasis p p p p leftDot w) =
      MackeyDiagrams.Generator.multiplicationCapBasis p w := by
    refine Quotient.inductionOn w (fun xy => ?_)
    change MackeyDiagrams.Generator.mixedProduct p p
      (MackeyDiagrams.Generator.mixedPair p p (xy.1 * 1 * xy.2)) = xy.1 * xy.2
    rw [MackeyDiagrams.Generator.mixedProduct_mixedPair, mul_one]
  exact hcap.symm.trans (congrArg (MackeyDiagrams.Generator.mixedProduct p p) hw)
let drawId := fun {K H : Subgroup U} (w : MackeyDiagrams.Word K H) =>
  plain (MackeyDiagrams.Diagram.id w)
let leftMixed := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := Complex)
  p p a a [(1, MackeyDiagrams.Dot.id (comp p a))]
let leftParallel := MackeyDiagrams.LabelledDrawing.parallelUp (R := Complex)
  p a p a [(1, MackeyDiagrams.Dot.id (comp p a))]
let leftProject := MackeyDiagrams.LabelledDrawing.compactProjection (R := Complex)
  p p p p [(1, ⟨leftDot, leftFinite⟩)]
let left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
  stack (plain (MackeyDiagrams.Diagram.unassociate ga ad df))
    (stack (beside leftMixed (drawId df))
      (stack (plain (MackeyDiagrams.Diagram.associate ce gc df))
        (stack (beside (drawId ce) leftParallel)
          (stack (plain (MackeyDiagrams.Diagram.unassociate ce gc ef))
            (stack (beside leftProject (drawId ef))
              (plain (MackeyDiagrams.Diagram.associate gc ce ef)))))))
let dot := fun (b c : MackeyDiagrams.ConjEmbedding T P) (x : P) =>
  ({ element := x
     intertwines := fun h => by
       have hh : h = 1 := Subsingleton.elim _ _
       simp [hh] } : MackeyDiagrams.Dot b c)
let Lower := MackeyDiagrams.DotLabel Complex (comp a i) (comp a i)
let Middle := MackeyDiagrams.DotLabel Complex (comp a i) (comp p a)
let Upper := MackeyDiagrams.DotLabel Complex (comp p a) (comp a i)
let rightFinite : ∀ (d : MackeyDiagrams.Dot (comp a i) (comp a i)) z,
    Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis a a i i d w = z} := by
  let : Finite (MackeyDiagrams.Word.basis (tensor ai fj)).carrier := by
    change Finite (Quotient (MackeyDiagrams.Biset.balance
      (MackeyDiagrams.Biset.induction i) (MackeyDiagrams.Biset.restriction i)))
    infer_instance
  intro d z
  exact Set.toFinite _
let right := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
  let projectionTerms : List (Complex × MackeyDiagrams.ProjectionDot.Mixed a a i i) :=
    List.map (fun (term : Complex × MackeyDiagrams.Dot (comp a i) (comp a i)) =>
      (term.1, (⟨term.2, rightFinite term.2⟩ : MackeyDiagrams.ProjectionDot.Mixed a a i i)))
      (MackeyDiagrams.DotLabel.terms lower)
  let first := MackeyDiagrams.LabelledDrawing.compactProjection a a i i projectionTerms
  let second := MackeyDiagrams.LabelledDrawing.parallelUp a i p a
    (MackeyDiagrams.DotLabel.terms middle)
  let third := MackeyDiagrams.LabelledDrawing.mixedMultiplication p a a i
    (MackeyDiagrams.DotLabel.terms upper)
  (stack (beside (drawId ga) first)
    (stack (plain (MackeyDiagrams.Diagram.unassociate ga ai fj))
      (stack (beside second (drawId fj))
        (stack (plain (MackeyDiagrams.Diagram.associate gc ck fj))
          (beside (drawId gc) third)))) :
    MackeyDiagrams.LabelledDrawing Complex bottom top)
let rightShape := MackeyDiagrams.LabelledDrawing.planarShape (right 0 0 0)
let bottomBoundary := MackeyDiagrams.Word.boundary bottom
let topBoundary := MackeyDiagrams.Word.boundary top
let RightDrawing := MackeyDiagrams.LabelledDrawing.PlanarAtBoundary
  Complex bottomBoundary topBoundary rightShape
let rightAt := fun (lower : Lower) (middle : Middle) (upper : Upper) =>
  ({ bottom := bottom
     top := top
     diagram := right lower middle upper
     bottom_eq := rfl
     top_eq := rfl
     shape_eq := by rfl } : RightDrawing)
let rightTerm := fun r : P =>
  right (Finsupp.single (dot (comp a i) (comp a i) r) 1)
    (Finsupp.single (dot (comp a i) (comp p a) r) 1)
    (Finsupp.single (dot (comp p a) (comp a i) 1) 1)
let X := MackeyDiagrams.Word.basis bottom
let Y := MackeyDiagrams.Word.basis top
let inputPair := fun g x : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
    (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair a a x)
let outputPair := fun h y : P =>
  MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction p)
    (MackeyDiagrams.Word.basis (tensor ce ef)) h (MackeyDiagrams.Generator.mixedPair p a y)
let input := fun g x : P => Finsupp.single (inputPair g x) (1 : Complex)
let output := fun z : P => Finsupp.single (outputPair z 1) (1 : Complex)
let eval := fun (d : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
  MackeyDiagrams.Biset.Hom.toLinearMap
    (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d))
let evalAt := fun (d : MackeyDiagrams.ScopedDiagram Complex
    (MackeyDiagrams.Boundary.word bottomBoundary) (MackeyDiagrams.Boundary.word topBoundary)) =>
  MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.ScopedDiagram.eval
    (MackeyDiagrams.ScopedDiagram.vertical
      (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderToBoundary bottom))
      (MackeyDiagrams.ScopedDiagram.vertical d
        (MackeyDiagrams.ScopedDiagram.ordinary (MackeyDiagrams.Word.reorderFromBoundary top)))))
let interpretRight := fun (d : RightDrawing) =>
  MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret (s := rightShape) d
let rightSum := fun (terms : List (Complex × RightDrawing)) =>
  MackeyDiagrams.ScopedDiagram.linearCombination
    (List.map (fun term => (term.1, interpretRight term.2)) terms)
(MackeyDiagrams.ConjEmbedding.toHom p).range.index = 1 ∧
  (∀ (Q : Subgroup U), MackeyDiagrams.ConjEmbedding Q T → Q = T) ∧
  (∃ identify : Y.carrier ≃ P, ∀ h y : P, identify (outputPair h y) = h * y) ∧
  (∀ g x : P, eval left (input g x) = output (g * x)) ∧
  (∀ (lower : Lower) (middle : Middle) (upper : Upper) (g x : P),
    x ∉ Finset.image MackeyDiagrams.Dot.element (Finsupp.support lower) →
      eval (MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.diagram
        (rightAt lower middle upper)) (input g x) = 0) ∧
  (∀ d : RightDrawing, ∃ support : Finset P, ∀ g x : P, x ∉ support →
    evalAt (interpretRight d) (input g x) = 0) ∧
  (∀ terms : List (Complex × RightDrawing),
    (∃ support : Finset P, ∀ g x : P, x ∉ support →
      evalAt (rightSum terms) (input g x) = 0) ∧
    evalAt (rightSum terms) ≠ eval left) ∧
  (∀ r g x : P, eval (rightTerm r) (input g x) =
    (if x = r then output (g * x) else 0)) ∧
  (∃ finite : ∀ v : Finsupp X.carrier Complex,
      Set.Finite {x : P | eval (rightTerm x) v ≠ 0},
    let drawing : MackeyDiagrams.PointwiseIndexedDrawing Complex bottom top P :=
      ⟨rightTerm, finite⟩
    ∀ v : Finsupp X.carrier Complex, eval left v = drawing.evalAt v)
) :=
(by
  -- Xiao, Example 6.6, with the basis computations in (6.3) and (6.4).
  exact ⟨CaseFiveInfiniteAux.indexOne, CaseFiveInfiniteAux.bot_forced,
    CaseFiveInfiniteAux.target_identification, CaseFiveInfiniteAux.left_column,
    CaseFiveInfiniteAux.right_named_support, CaseFiveInfiniteAux.right_all_support,
    CaseFiveInfiniteAux.finite_right_sum, CaseFiveInfiniteAux.right_column,
    CaseFiveInfiniteAux.pointwise_column_sum⟩)

#print axioms CaseFiveRequiresInfiniteExpansion
