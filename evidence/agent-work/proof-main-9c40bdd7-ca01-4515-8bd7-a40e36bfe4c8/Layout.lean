import Shape

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
