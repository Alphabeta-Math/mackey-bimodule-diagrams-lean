import MackeyDiagrams
import Proofs.ThreeInductionCrossingMultipliers
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks

set_option maxHeartbeats 2000000
namespace ExtremalThreeInduction
open MackeyDiagrams

private abbrev conj {V : Type*} [Group V] (p : V) (H : Subgroup V) :=
  H.map (MulAut.conj p).toMonoidHom

section Group
variable {V : Type*} [Group V]

private theorem conj_mul (p q : V) (H : Subgroup V) :
    conj p (conj q H) = conj (p * q) H := by
  rw [conj, conj, Subgroup.map_map]
  congr 1
  ext x
  change p * (q * x * q⁻¹) * p⁻¹ = (p * q) * x * (p * q)⁻¹
  group

private theorem conj_one (H : Subgroup V) : conj 1 H = H := by
  have h : (MulAut.conj (1 : V)).toMonoidHom = MonoidHom.id V := by
    ext x
    simp
  change H.map _ = H
  rw [h, Subgroup.map_id]

private theorem conj_inner {H : Subgroup V} {p : V} (hp : p ∈ H) :
    conj p H = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hp hx) (H.inv_mem hp)
  · intro x hx
    refine ⟨p⁻¹ * x * p, H.mul_mem (H.mul_mem (H.inv_mem hp) hx) hp, ?_⟩
    change p * (p⁻¹ * x * p) * p⁻¹ = x
    group

private theorem conj_mono (r : V) {H K : Subgroup V} (h : H ≤ K) :
    conj r H ≤ conj r K := Subgroup.map_mono h

private theorem undo_conj {H K : Subgroup V} {r : V} (h : H ≤ conj r K) :
    conj r⁻¹ H ≤ K := by
  simpa only [conj_mul, inv_mul_cancel, conj_one] using conj_mono r⁻¹ h

private theorem conj_eq_of_action {H : Subgroup V} {a b : V}
    (h : ∀ x : H, a * (x : V) * a⁻¹ = b * (x : V) * b⁻¹) :
    conj a H = conj b H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (h ⟨x, hx⟩).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, h ⟨x, hx⟩⟩

private abbrev embed {H K : Subgroup V} (r : V) (h : conj r H ≤ K) :
    ConjEmbedding H K :=
  ConjEmbedding.ofConjugator r (fun x => h ⟨x, x.property, rfl⟩)

private theorem comp_conj {H K L : Subgroup V} {r s : V}
    {hr : conj r K ≤ L} {hs : conj s H ≤ K} (x : H) :
    ((embed r hr).comp (embed s hs) |>.toHom x : V) =
      (r * s) * (x : V) * (r * s)⁻¹ := by
  simp only [ConjEmbedding.comp_apply, ConjEmbedding.ofConjugator_apply, mul_inv_rev]
  group

private theorem dot_conj {H K : Subgroup V}
    {i j : ConjEmbedding H K} (dot : Dot i j) {r s : V}
    (hi : ∀ x : H, (i.toHom x : V) = r * (x : V) * r⁻¹)
    (hj : ∀ x : H, (j.toHom x : V) = s * (x : V) * s⁻¹) :
    conj r H = conj (dot.element * s) H := by
  apply conj_eq_of_action
  intro x
  have hd := congrArg (fun k : K => (k : V)) (dot.intertwines x)
  simp only [Subgroup.coe_mul, hi, hj] at hd
  calc
    r * (x : V) * r⁻¹ = (r * x * r⁻¹ * dot.element) * (dot.element : V)⁻¹ := by group
    _ = (dot.element * (s * x * s⁻¹)) * (dot.element : V)⁻¹ := by rw [hd]
    _ = _ := by group

private def mkDot {H K : Subgroup V} {i j : ConjEmbedding H K}
    (z : K) {r s : V}
    (hi : ∀ x : H, (i.toHom x : V) = r * (x : V) * r⁻¹)
    (hj : ∀ x : H, (j.toHom x : V) = s * (x : V) * s⁻¹)
    (h : ∀ x : H, r * (x : V) * r⁻¹ = ((z : V) * s) * (x : V) * ((z : V) * s)⁻¹) :
    Dot i j where
  element := z
  intertwines x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hi, hj, h]
    group

end Group
noncomputable section Evaluation
variable {V : Type*} [Group V]
variable {G A D F C E B : Subgroup V}

private abbrev GA (H : Subgroup V) := MonoidAlgebra Complex H

private abbrev word {P Q S T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) (k : ConjEmbedding T S) :=
  Word.tensor (Word.tensor (Word.up i) (Word.up j)) (Word.up k)

private abbrev straight {P Q : Subgroup V} (i : ConjEmbedding Q P) :=
  LabelledDrawing.ordinary (Diagram.id (R := Complex) (Word.up i))

private abbrev merge {P Q S : Subgroup V} (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) :=
  LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.mergeUp i j)

private abbrev split {P Q S : Subgroup V} (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) :=
  LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.splitUp i j)

private abbrev dCrossing {P Q Q' S : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (i' : ConjEmbedding Q' P) (j' : ConjEmbedding S Q')
    (dot : Dot (ConjEmbedding.comp i j)
      (ConjEmbedding.comp i' j')) :=
  Diagram.vertical (Diagram.mergeUp (R := Complex) i j)
    (Diagram.vertical (Diagram.upDot dot)
      (Diagram.splitUp i' j'))
private abbrev dCrossLeft {P Q Q' S T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (i' : ConjEmbedding Q' P) (j' : ConjEmbedding S Q')
    (k : ConjEmbedding T S)
    (dot : Dot (ConjEmbedding.comp i j)
      (ConjEmbedding.comp i' j')) :=
  Diagram.horizontal (dCrossing i j i' j' dot)
    (Diagram.id (Word.up k))
private abbrev dCrossRight {P Q S S' T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (k : ConjEmbedding T S)
    (j' : ConjEmbedding S' Q) (k' : ConjEmbedding T S')
    (dot : Dot (ConjEmbedding.comp j k)
      (ConjEmbedding.comp j' k')) :=
  Diagram.vertical
    (Diagram.associate (Word.up i)
      (Word.up j) (Word.up k))
    (Diagram.vertical
      (Diagram.horizontal (Diagram.id (Word.up i))
        (dCrossing j k j' k' dot))
      (Diagram.unassociate (Word.up i)
        (Word.up j') (Word.up k')))

private abbrev wCrossing {P Q Q' S : Subgroup V}
    (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q')
    (weights : DotLabel Complex (ConjEmbedding.comp a b)
      (ConjEmbedding.comp a' b')) :=
  LabelledDrawing.vertical (merge a b)
    (LabelledDrawing.vertical (DotLabel.upDrawing weights)
      (split a' b'))
private abbrev wCrossLeft {P Q Q' S T : Subgroup V}
    (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q')
    (c : ConjEmbedding T S)
    (weights : DotLabel Complex (ConjEmbedding.comp a b)
      (ConjEmbedding.comp a' b')) :=
  LabelledDrawing.horizontal (wCrossing a b a' b' weights)
    (straight c)
private abbrev wCrossRight {P Q S S' T : Subgroup V}
    (a : ConjEmbedding Q P)
    (b : ConjEmbedding S Q) (c : ConjEmbedding T S)
    (b' : ConjEmbedding S' Q) (c' : ConjEmbedding T S')
    (weights : DotLabel Complex (ConjEmbedding.comp b c)
      (ConjEmbedding.comp b' c')) :=
  LabelledDrawing.vertical
    (LabelledDrawing.ordinary
      (Diagram.associate (Word.up a) (Word.up b)
        (Word.up c)))
    (LabelledDrawing.vertical
      (LabelledDrawing.horizontal (straight a)
        (wCrossing b c b' c' weights))
      (LabelledDrawing.ordinary
        (Diagram.unassociate (Word.up a) (Word.up b')
          (Word.up c'))))


private theorem singleton_dot {P Q : Subgroup V} {i j : ConjEmbedding Q P}
    (x : Dot i j) :
    (DotLabel.upDrawing (R := Complex) (Finsupp.single x 1)).interpret.eval =
      (Diagram.upDot (R := Complex) x).eval := by
  rw [DotLabel.eval_upDrawing]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  rw [Diagram.eval_linearUpDot_apply, freeLift_single, one_smul]

private theorem crossLeft_eval {P Q Q' S T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q)
    (i' : ConjEmbedding Q' P) (j' : ConjEmbedding S Q') (k : ConjEmbedding T S)
    (x : Dot (i.comp j) (i'.comp j')) :
    (wCrossLeft i j i' j' k (Finsupp.single x 1)).interpret.eval =
      (dCrossLeft i j i' j' k x).eval := by
  simp only [LabelledDrawing.interpret,
    ScopedDiagram.eval, TrivalentVertex.expand, Diagram.eval, singleton_dot]

private theorem crossRight_eval {P Q S S' T : Subgroup V}
    (i : ConjEmbedding Q P) (j : ConjEmbedding S Q) (k : ConjEmbedding T S)
    (j' : ConjEmbedding S' Q) (k' : ConjEmbedding T S')
    (x : Dot (j.comp k) (j'.comp k')) :
    (wCrossRight i j k j' k' (Finsupp.single x 1)).interpret.eval =
      (dCrossRight i j k j' k' x).eval := by
  simp only [LabelledDrawing.interpret,
    ScopedDiagram.eval, TrivalentVertex.expand, Diagram.eval, singleton_dot]

private abbrev splitBottom (ga : ConjEmbedding A G) (ad : ConjEmbedding D A)
    (df : ConjEmbedding F D) :=
  Diagram.vertical (Diagram.splitUp (R := Complex) (ga.comp ad) df)
    (Diagram.horizontal (Diagram.splitUp ga ad) (Diagram.id (Word.up df)))

private abbrev mergeTop (gc : ConjEmbedding C G) (ce : ConjEmbedding E C)
    (ef : ConjEmbedding F E) :=
  Diagram.vertical (Diagram.horizontal (Diagram.mergeUp (R := Complex) gc ce)
    (Diagram.id (Word.up ef))) (Diagram.mergeUp (gc.comp ce) ef)

private abbrev framed
    {ga : ConjEmbedding A G} {ad : ConjEmbedding D A} {df : ConjEmbedding F D}
    {gc : ConjEmbedding C G} {ce : ConjEmbedding E C} {ef : ConjEmbedding F E}
    (d : Diagram Complex (word ga ad df) (word gc ce ef)) (z : GA G) : GA G :=
  MonoidAlgebra.ofCoeff
    (((splitBottom ga ad df).vertical (d.vertical (mergeTop gc ce ef))).eval.toLinearMap
      (MonoidAlgebra.coeff z))

private abbrev framedDrawing
    {ga : ConjEmbedding A G} {ad : ConjEmbedding D A} {df : ConjEmbedding F D}
    {gc : ConjEmbedding C G} {ce : ConjEmbedding E C} {ef : ConjEmbedding F E}
    (d : LabelledDrawing Complex (word ga ad df) (word gc ce ef)) (z : GA G) : GA G :=
  MonoidAlgebra.ofCoeff
    (((split (ga.comp ad) df).vertical ((split ga ad).horizontal (straight df)) |>.interpret.eval).vertical
      (d.interpret.eval.vertical
        ((((merge gc ce).horizontal (straight ef)).vertical (merge (gc.comp ce) ef)).interpret.eval))
      |>.toLinearMap (MonoidAlgebra.coeff z))

private theorem framed_eq
    {ga : ConjEmbedding A G} {ad : ConjEmbedding D A} {df : ConjEmbedding F D}
    {gc : ConjEmbedding C G} {ce : ConjEmbedding E C} {ef : ConjEmbedding F E}
    (d : Diagram Complex (word ga ad df) (word gc ce ef))
    (w : LabelledDrawing Complex (word ga ad df) (word gc ce ef))
    (h : w.interpret.eval = d.eval) (z : GA G) :
    framedDrawing w z = framed d z := by
  unfold framedDrawing framed
  rw [h]
  rfl

private theorem dotValue_single {P Q : Subgroup V} {i j : ConjEmbedding Q P} (x : Dot i j) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element (Finsupp.single x (1 : Complex))) =
      MonoidAlgebra.single x.element 1 := by
  rw [Finsupp.mapDomain_single, MonoidAlgebra.ofCoeff_single]

private theorem along_single {P Q : Subgroup V} (i : ConjEmbedding Q P) (x : Q) :
    MonoidAlgebra.mapDomainAlgHom Complex Complex i.toHom (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single (i.toHom x) 1 :=
  MonoidAlgebra.mapDomain_single


section Boundary
variable (ga : ConjEmbedding A G) (ad : ConjEmbedding D A) (df : ConjEmbedding F D)
variable (gc : ConjEmbedding C G) (ce : ConjEmbedding E C) (ef : ConjEmbedding F E)

private abbrev dLeft (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) :=
  Diagram.vertical (dCrossLeft ga ad gb bd df x₁)
    (Diagram.vertical (dCrossRight gb bd df be ef x₂) (dCrossLeft gb be gc ce ef x₃))

private abbrev wLeft (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) :=
  LabelledDrawing.vertical (wCrossLeft ga ad gb bd df (Finsupp.single x₁ 1))
    (LabelledDrawing.vertical (wCrossRight gb bd df be ef (Finsupp.single x₂ 1)) (wCrossLeft gb be gc ce ef (Finsupp.single x₃ 1)))

private abbrev leftMultiplier (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) : G :=
  x₁.element * gb.toHom x₂.element * x₃.element

private theorem leftDrawing_eval (gb : ConjEmbedding B G) (bd : ConjEmbedding D B) (be : ConjEmbedding E B)
    (x₁ : Dot (ga.comp ad) (gb.comp bd)) (x₂ : Dot (bd.comp df) (be.comp ef))
    (x₃ : Dot (gb.comp be) (gc.comp ce)) :
    (wLeft ga ad df gc ce ef gb bd be x₁ x₂ x₃).interpret.eval = (dLeft ga ad df gc ce ef gb bd be x₁ x₂ x₃).eval := by
  change Biset.Hom.vertical _ (Biset.Hom.vertical _ _) =
    Biset.Hom.vertical _ (Biset.Hom.vertical _ _)
  rw [crossLeft_eval, crossRight_eval, crossLeft_eval]

private abbrev dRight (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) :=
  Diagram.vertical (dCrossRight ga ad df ab bf y₁)
    (Diagram.vertical (dCrossLeft ga ab gc cb bf y₂) (dCrossRight gc cb bf ce ef y₃))

private abbrev wRight (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) :=
  LabelledDrawing.vertical (wCrossRight ga ad df ab bf (Finsupp.single y₁ 1))
    (LabelledDrawing.vertical (wCrossLeft ga ab gc cb bf (Finsupp.single y₂ 1)) (wCrossRight gc cb bf ce ef (Finsupp.single y₃ 1)))

private abbrev rightMultiplier (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) : G :=
  ga.toHom y₁.element * y₂.element * gc.toHom y₃.element

private theorem rightDrawing_eval (ab : ConjEmbedding B A) (cb : ConjEmbedding B C) (bf : ConjEmbedding F B)
    (y₁ : Dot (ad.comp df) (ab.comp bf)) (y₂ : Dot (ga.comp ab) (gc.comp cb))
    (y₃ : Dot (cb.comp bf) (ce.comp ef)) :
    (wRight ga ad df gc ce ef ab cb bf y₁ y₂ y₃).interpret.eval = (dRight ga ad df gc ce ef ab cb bf y₁ y₂ y₃).eval := by
  change Biset.Hom.vertical _ (Biset.Hom.vertical _ _) =
    Biset.Hom.vertical _ (Biset.Hom.vertical _ _)
  rw [crossRight_eval, crossLeft_eval, crossRight_eval]

end Boundary
section Representatives
variable (a d df c e ef : V)
variable (ha : conj a A ≤ G) (hd : conj d D ≤ A) (hdf : conj df F ≤ D)
variable (hc : conj c C ≤ G) (he : conj e E ≤ C) (hef : conj ef F ≤ E)

local notation "ga" => embed a ha
local notation "ad" => embed d hd
local notation "dfE" => embed df hdf
local notation "gc" => embed c hc
local notation "ce" => embed e he
local notation "efE" => embed ef hef

private theorem left_evaluation (gb : ConjEmbedding B G) (bd : ConjEmbedding D B)
    (be : ConjEmbedding E B) (x₁ : Dot (ga.comp ad) (gb.comp bd))
    (x₂ : Dot (bd.comp dfE) (be.comp efE)) (x₃ : Dot (gb.comp be) (gc.comp ce))
    (z : GA G) :
    framed (dLeft ga ad dfE gc ce efE gb bd be x₁ x₂ x₃) z =
      z * MonoidAlgebra.single (leftMultiplier ga ad dfE gc ce efE gb bd be x₁ x₂ x₃) 1 := by
  obtain ⟨_, _, hAll, _, _, hLeft, _⟩ :=
    ThreeInductionCrossingMultipliers G A D F C E a d df c e ef
      (fun x => (ga.toHom x).property) (fun x => (ad.toHom x).property)
      (fun x => (dfE.toHom x).property) (fun x => (gc.toHom x).property)
      (fun x => (ce.toHom x).property) (fun x => (efE.toHom x).property)
  let w := wLeft ga ad dfE gc ce efE gb bd be x₁ x₂ x₃
  have atOne := (hLeft B gb bd be (Finsupp.single x₁ 1) (Finsupp.single x₂ 1)
    (Finsupp.single x₃ 1)).1
  have hz : framedDrawing w z = z * framedDrawing w 1 := hAll w z
  have product : framedDrawing w 1 =
      MonoidAlgebra.single (leftMultiplier ga ad dfE gc ce efE gb bd be x₁ x₂ x₃) 1 := by
    simpa only [dotValue_single, along_single, MonoidAlgebra.single_mul_single, one_mul]
      using atOne
  rw [← framed_eq _ w (leftDrawing_eval ga ad dfE gc ce efE gb bd be x₁ x₂ x₃), hz, product]

private theorem right_evaluation (ab : ConjEmbedding B A) (cb : ConjEmbedding B C)
    (bf : ConjEmbedding F B) (y₁ : Dot (ad.comp dfE) (ab.comp bf))
    (y₂ : Dot (ga.comp ab) (gc.comp cb)) (y₃ : Dot (cb.comp bf) (ce.comp efE))
    (z : GA G) :
    framed (dRight ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃) z =
      z * MonoidAlgebra.single (rightMultiplier ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃) 1 := by
  obtain ⟨_, _, hAll, _, _, _, hRight⟩ :=
    ThreeInductionCrossingMultipliers G A D F C E a d df c e ef
      (fun x => (ga.toHom x).property) (fun x => (ad.toHom x).property)
      (fun x => (dfE.toHom x).property) (fun x => (gc.toHom x).property)
      (fun x => (ce.toHom x).property) (fun x => (efE.toHom x).property)
  let w := wRight ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃
  have atOne := (hRight B ab cb bf (Finsupp.single y₁ 1) (Finsupp.single y₂ 1)
    (Finsupp.single y₃ 1)).1
  have hz : framedDrawing w z = z * framedDrawing w 1 := hAll w z
  have product : framedDrawing w 1 =
      MonoidAlgebra.single (rightMultiplier ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃) 1 := by
    simpa only [dotValue_single, along_single, MonoidAlgebra.single_mul_single, one_mul]
      using atOne
  rw [← framed_eq _ w (rightDrawing_eval ga ad dfE gc ce efE ab cb bf y₁ y₂ y₃), hz, product]

private theorem evaluation_eq
    (l r : LabelledDrawing Complex (word ga ad dfE) (word gc ce efE))
    (h : framedDrawing l 1 = framedDrawing r 1) : l.interpret.eval = r.interpret.eval := by
  obtain ⟨_, _, _, hEq, _, _, _⟩ :=
    ThreeInductionCrossingMultipliers G A D F C E a d df c e ef
      (fun x => (ga.toHom x).property) (fun x => (ad.toHom x).property)
      (fun x => (dfE.toHom x).property) (fun x => (gc.toHom x).property)
      (fun x => (ce.toHom x).property) (fun x => (efE.toHom x).property)
  exact (hEq l r).mpr h

end Representatives
end Evaluation

end ExtremalThreeInduction
