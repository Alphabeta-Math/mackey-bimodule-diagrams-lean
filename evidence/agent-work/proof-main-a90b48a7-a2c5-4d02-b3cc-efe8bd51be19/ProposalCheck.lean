import MackeyDiagrams
import Proofs.ExpansionIntoRightDiagrams
import Proofs.RightOrbitDiagramFromProjectedStabilizer

set_option maxHeartbeats 2000000

namespace CaseFivePointwiseAux

open MackeyDiagrams

private theorem finite_linear_support {X I V : Type*} [AddCommMonoid V] [Module Complex V]
    (L : I → (X →₀ Complex) →ₗ[Complex] V)
    (h : ∀ x, Set.Finite {i | L i (Finsupp.single x 1) ≠ 0})
    (v : X →₀ Complex) : Set.Finite {i | L i v ≠ 0} := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero, ne_eq, not_true_eq_false, Set.ofPred_false] using
      (Set.finite_empty : (∅ : Set I).Finite)
  | add v w hv hw =>
      refine (hv.union hw).subset ?_
      intro i hi
      change L i (v + w) ≠ 0 at hi
      rw [map_add] at hi
      by_cases hvi : L i v = 0
      · exact Or.inr (fun hwi => hi (by rw [hvi, hwi, add_zero]))
      · exact Or.inl hvi
  | single x c =>
      refine (h x).subset ?_
      intro i hi
      change L i (Finsupp.single x c) ≠ 0 at hi
      rw [← Finsupp.smul_single_one, map_smul] at hi
      exact fun hz => hi (by rw [hz, smul_zero])

private theorem sum_orbit_drawings {U : Type*} [Group U] {G F : Subgroup U}
    {bottom top : Word G F} {O : Type*}
    (orbit : bottom.basis.carrier × top.basis.carrier → O)
    (M : (bottom.basis.carrier →₀ Complex) →ₗ[Complex] (top.basis.carrier →₀ Complex))
    (I : Set O) (weight : I → Complex)
    (drawing : I → LabelledDrawing Complex bottom top)
    (hit : ∀ x y, M (Finsupp.single x 1) y ≠ 0 → orbit (x, y) ∈ I)
    (weight_eq : ∀ (i : I) x y, orbit (x, y) = i.val → weight i = M (Finsupp.single x 1) y)
    (finiteOrbits : ∀ x, Set.Finite {o : O |
      ∃ y, M (Finsupp.single x 1) y ≠ 0 ∧ o = orbit (x, y)})
    (matrix : ∀ (i : I) x y,
      (weight i • (drawing i).interpret.eval.toLinearMap (Finsupp.single x 1)) y =
        @ite Complex (orbit (x, y) = i.val) (Classical.propDecidable _) (weight i) 0) :
    ∃ (finite : ∀ v : bottom.basis.carrier →₀ Complex, Set.Finite
        {i : I | weight i • (drawing i).interpret.eval.toLinearMap v ≠ 0}),
      let sum : PointwiseIndexedDrawing Complex bottom top I :=
        ⟨fun i => LabelledDrawing.scale (weight i) (drawing i), finite⟩
      ∀ v, M v = sum.evalAt v := by
  classical
  let L (i : I) := weight i • (drawing i).interpret.eval.toLinearMap
  have entry (i : I) (x : bottom.basis.carrier) (y : top.basis.carrier) :
      L i (Finsupp.single x 1) y = if orbit (x, y) = i.val then weight i else 0 :=
    matrix i x y
  -- Step 3. The nonzero entries in a basis column bound the contributing
  -- orbits. Finite linear extension handles arbitrary inputs.
  have finiteColumn (x : bottom.basis.carrier) :
      Set.Finite {i : I | L i (Finsupp.single x 1) ≠ 0} := by
    apply ((finiteOrbits x).preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
    intro i hi
    change L i (Finsupp.single x 1) ≠ 0 at hi
    have h : ∃ y, L i (Finsupp.single x 1) y ≠ 0 := by
      by_contra! hall
      exact hi (Finsupp.ext fun y => hall y)
    obtain ⟨y, hy⟩ := h
    have he : orbit (x, y) = i.val := by
      by_contra hn
      exact hy ((entry i x y).trans (ite_eq_right hn))
    exact ⟨y, by rwa [entry, ite_eq_left he, weight_eq i x y he] at hy, he.symm⟩
  let finite := finite_linear_support L finiteColumn
  let sum : PointwiseIndexedDrawing Complex bottom top I :=
    ⟨fun i => LabelledDrawing.scale (weight i) (drawing i), finite⟩
  refine ⟨finite, ?_⟩
  suffices h : M = sum.eval from fun v => (LinearMap.congr_fun h v).trans (sum.eval_apply v)
  apply Finsupp.lhom_ext
  intro x c
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  congr 1
  rw [PointwiseIndexedDrawing.eval_apply, PointwiseIndexedDrawing.evalAt_def]
  change M (Finsupp.single x 1) = (finite (Finsupp.single x 1)).toFinset.sum
    (fun i => L i (Finsupp.single x 1))
  apply Finsupp.ext
  intro y
  rw [Finsupp.finsetSum_apply]
  by_cases hc : M (Finsupp.single x 1) y = 0
  · rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases he : orbit (x, y) = i.val
    · rw [entry, ite_eq_left he, weight_eq i x y he, hc]
    · rw [entry, ite_eq_right he]
  · let i : I := ⟨orbit (x, y), hit x y hc⟩
    have he : orbit (x, y) = i.val := rfl
    have hval : L i (Finsupp.single x 1) y = M (Finsupp.single x 1) y := by
      rw [entry, ite_eq_left he, weight_eq i x y he]
    rw [Finset.sum_eq_single i]
    · exact hval.symm
    · intro j _ hj
      have hne : orbit (x, y) ≠ j.val := fun he' => hj (Subtype.ext (he'.symm.trans he))
      rw [entry, ite_eq_right hne]
    · intro hi
      rw [Set.Finite.mem_toFinset] at hi
      have hz : L i (Finsupp.single x 1) = 0 := not_ne_iff.mp hi
      exact False.elim (hc (hval.symm.trans (congrArg (fun w => w y) hz)))

private theorem finite_eval {U : Type*} [Group U] {G F : Subgroup U}
    {bottom top : Word G F} (terms : List (Complex × LabelledDrawing Complex bottom top)) :
    let folded := terms.foldr
      (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
      (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))
    let indexed : IndexedDrawing Complex bottom top (Fin terms.length) :=
      ⟨Finset.univ, fun i => LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩
    folded.interpret.eval.toLinearMap = indexed.eval := by
  intro folded indexed
  apply LinearMap.ext
  intro v
  let termValue (term : Complex × LabelledDrawing Complex bottom top) :=
    term.1 • term.2.interpret.eval.toLinearMap v
  have hfold (l : List (Complex × LabelledDrawing Complex bottom top)) :
      (l.foldr (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
        (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))).interpret.eval.toLinearMap v =
        (l.map termValue).sum := by
    induction l with
    | nil => rfl
    | cons t l ih =>
        rw [List.map_cons, List.sum_cons]
        change termValue t + _ = termValue t + _
        exact congrArg (termValue t + ·) ih
  rw [IndexedDrawing.eval_apply]
  change folded.interpret.eval.toLinearMap v =
    Finset.univ.sum (fun i : Fin terms.length => termValue (terms.get i))
  exact (hfold terms).trans (Fin.sum_univ_fun_getElem terms termValue).symm

end CaseFivePointwiseAux

theorem CaseFivePointwiseFiniteDiagramIdentity : (
∀ {U : Type*} [Group U] (G A D F C E : Subgroup U)
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let ga := up a
  let ad := down b
  let df := up d
  let gc := up c
  let ce := down e
  let ef := up f
  let bottom := tensor ga (tensor ad df)
  let top := tensor gc (tensor ce ef)
  let X := MackeyDiagrams.Word.basis bottom
  let Y := MackeyDiagrams.Word.basis top
  let Pair := X.carrier × Y.carrier
  let input := fun (g : G) (x : D) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let orbit : Pair → Set Pair := MulAction.orbit (G × F)
  let stabilizer : Pair → Subgroup (G × F) := MulAction.stabilizer (G × F)
  let projected := fun z : Pair =>
    Subgroup.map (MonoidHom.comp (Subgroup.subtype F) (MonoidHom.snd G F)) (stabilizer z)
  let coefficient := fun (M : MackeyDiagrams.Biset.Hom Complex X Y) (z : Pair) =>
    MackeyDiagrams.Biset.Hom.toLinearMap M (Finsupp.single z.1 (1 : Complex)) z.2
  let MiddleLabel := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (k : MackeyDiagrams.ConjEmbedding P C) =>
    MackeyDiagrams.Dot (comp a i) (comp c k)
  let UpperLabel := fun (P : Subgroup U)
      (j : MackeyDiagrams.ConjEmbedding P F) (k : MackeyDiagrams.ConjEmbedding P C) =>
    MackeyDiagrams.Dot (comp e k) (comp f j)
  let ProjectionTerm := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F) =>
    MackeyDiagrams.ProjectionDot.Mixed b d i j
  let drawId := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) p)
  let rightDrawing := fun (P : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
      (k : MackeyDiagrams.ConjEmbedding P C)
      (lower : List (Complex × ProjectionTerm P i j))
      (middle : List (Complex × MiddleLabel P i k))
      (upper : List (Complex × UpperLabel P j k)) =>
    let ai := up i
    let fj := down j
    let ck := up k
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId ga)
        (MackeyDiagrams.LabelledDrawing.compactProjection b d i j lower))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.parallelUp a i c k middle) (drawId fj))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId gc)
              (MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j upper))))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let eval := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let IsRightTerm := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
    ∃ (P : Subgroup U) (i : MackeyDiagrams.ConjEmbedding P A)
      (j : MackeyDiagrams.ConjEmbedding P F) (k : MackeyDiagrams.ConjEmbedding P C)
      (lower : List (Complex × ProjectionTerm P i j))
      (middle : List (Complex × MiddleLabel P i k))
      (upper : List (Complex × UpperLabel P j k)),
      drawing = rightDrawing P i j k lower middle upper
  ∀ (B : Subgroup U)
      (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B),
    let LeftUpper := MackeyDiagrams.ProjectionDot.Mixed u w c e
    let leftDrawing := fun
        (rs : List (Complex × MackeyDiagrams.Dot (comp u a) (comp v b)))
        (ts : List (Complex × MackeyDiagrams.Dot (comp v d) (comp w f)))
        (ss : List (Complex × LeftUpper)) =>
      let ug := down u
      let dv := up v
      let ew := up w
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b rs) (drawId df))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate ug dv df))
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.horizontal (drawId ug)
                (MackeyDiagrams.LabelledDrawing.parallelUp v d w f ts))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ug ew ef))
                (MackeyDiagrams.LabelledDrawing.vertical
                  (MackeyDiagrams.LabelledDrawing.horizontal
                    (MackeyDiagrams.LabelledDrawing.compactProjection u w c e ss) (drawId ef))
                  (MackeyDiagrams.LabelledDrawing.ordinary
                    (MackeyDiagrams.Diagram.associate gc ce ef))))))) :
        MackeyDiagrams.LabelledDrawing Complex bottom top)
    ∀ (rs : MackeyDiagrams.DotLabel Complex (comp u a) (comp v b))
      (ts : MackeyDiagrams.DotLabel Complex (comp v d) (comp w f))
      (ss : Finsupp LeftUpper Complex),
    let upperTerms := List.map (fun s => (ss s, s)) (Finset.toList (Finsupp.support ss))
    let M := eval (leftDrawing (MackeyDiagrams.DotLabel.terms rs)
      (MackeyDiagrams.DotLabel.terms ts) upperTerms)
    let supported := {O : Set Pair | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0}
    (∃ (diagram : supported → MackeyDiagrams.LabelledDrawing Complex bottom top)
        (weight : supported → Complex),
      (∀ O : supported,
        ∃ (r : D) (t : G) (s : E),
          let z := (input 1 r, output t s)
          let P := projected z
          O.val = orbit z ∧
          weight O = coefficient M z ∧
          ∃ (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
            (k : MackeyDiagrams.ConjEmbedding P C)
            (rDot : ProjectionTerm P i j) (tDot : MiddleLabel P i k) (sDot : UpperLabel P j k),
            (∀ h : P, (MackeyDiagrams.ConjEmbedding.toHom j h : U) = (h : U)) ∧
            MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot rDot) = r ∧
            MackeyDiagrams.Dot.element tDot = t ∧
            MackeyDiagrams.Dot.element sDot = s ∧
            diagram O = rightDrawing P i j k [(1, rDot)] [(1, tDot)] [(1, sDot)]) ∧
      let term := fun (O : supported) (x : Finsupp X.carrier Complex) =>
        weight O • MackeyDiagrams.Biset.Hom.toLinearMap (eval (diagram O)) x
      ∃ (finite : ∀ x : Finsupp X.carrier Complex, Set.Finite {O : supported | term O x ≠ 0}),
        let sum : MackeyDiagrams.PointwiseIndexedDrawing Complex bottom top supported :=
          ⟨fun O => MackeyDiagrams.LabelledDrawing.scale (weight O) (diagram O), finite⟩
        ∀ x : Finsupp X.carrier Complex,
          MackeyDiagrams.Biset.Hom.toLinearMap M x = sum.evalAt x) ∧
    ((∃ terms : List (Complex × MackeyDiagrams.LabelledDrawing Complex bottom top),
        (∀ term ∈ terms, IsRightTerm term.2) ∧
        let drawing : MackeyDiagrams.IndexedDrawing Complex bottom top (Fin terms.length) :=
          ⟨Finset.univ, fun i => MackeyDiagrams.LabelledDrawing.scale (terms.get i).1 (terms.get i).2⟩
        MackeyDiagrams.Biset.Hom.toLinearMap M = drawing.eval) ↔
      Set.Finite supported)
) :=
(by
  classical
  intro U inst G A D F C E a b d c e f up down tensor comp ga ad df gc ce ef bottom top
    X Y Pair input output orbit stabilizer projected coefficient MiddleLabel UpperLabel
    ProjectionTerm drawId rightDrawing eval IsRightTerm B u v w LeftUpper leftDrawing
    rs ts ss upperTerms M supported
  -- Alphabeta Math, § 6.3.1, Theorem 6.7. Steps 1–4 follow the proof in prose.
  -- The scoped drawing appears on archived p. 27 and published (28 Nov 2026) p. 29.
  -- Published p. 6 specifies equality of evaluated maps and pointwise evaluation of this sum.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=29
  let supplier := RightOrbitDiagramFromProjectedStabilizer G A D F C E a b d c e f
  have constant (z p : Pair) (hp : p ∈ orbit z) : coefficient M p = coefficient M z :=
    supplier.1 M z p hp
  let action : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  have orbit_eq (z p : Pair) : orbit z = orbit p ↔ z ∈ orbit p :=
    @MulAction.orbit_eq_iff _ _ _ action z p
  -- Steps 1 and 2. Normalize the input–output pair and transport the nonzero
  -- coefficient to the normalized representative. This is the hypothesis
  -- for the checked lower finite fibers and the indicator formula from (6.4).
  have realize (O : supported) :
      ∃ (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) (weight : Complex),
        (∃ (r : D) (t : G) (s : E),
          let z := (input 1 r, output t s)
          let P := projected z
          O.val = orbit z ∧ weight = coefficient M z ∧
          ∃ (i : MackeyDiagrams.ConjEmbedding P A) (j : MackeyDiagrams.ConjEmbedding P F)
            (k : MackeyDiagrams.ConjEmbedding P C)
            (rDot : ProjectionTerm P i j) (tDot : MiddleLabel P i k) (sDot : UpperLabel P j k),
            (∀ h : P, (MackeyDiagrams.ConjEmbedding.toHom j h : U) = (h : U)) ∧
            MackeyDiagrams.Dot.element (MackeyDiagrams.ProjectionDot.dot rDot) = r ∧
            MackeyDiagrams.Dot.element tDot = t ∧ MackeyDiagrams.Dot.element sDot = s ∧
            drawing = rightDrawing P i j k [(1, rDot)] [(1, tDot)] [(1, sDot)]) ∧
        (∀ p : Pair, orbit p = O.val → weight = coefficient M p) ∧
        ∀ p : Pair, coefficient (eval drawing) p = if p ∈ O.val then 1 else 0 := by
    obtain ⟨z, he, hz⟩ := O.property
    obtain ⟨r, t, s, hnorm⟩ := supplier.2.1 z
    let z₀ : Pair := (input 1 r, output t s)
    have h₀ : coefficient M z₀ ≠ 0 := (constant z₀ z hnorm) ▸ hz
    have he₀ : O.val = orbit z₀ := he.trans ((orbit_eq z z₀).mpr hnorm)
    obtain ⟨i, j, k, rDot, tDot, sDot, hj, hr, ht, hs, _, _, realizeAt⟩ :=
      (supplier.2.2.1 r t s).2.2.2
    obtain ⟨_, finite, indicator⟩ := realizeAt M h₀
    let lower : ProjectionTerm (projected z₀) i j := ⟨rDot, finite⟩
    let drawing := rightDrawing (projected z₀) i j k [(1, lower)] [(1, tDot)] [(1, sDot)]
    refine ⟨drawing, coefficient M z₀, ⟨r, t, s, he₀, rfl,
      i, j, k, lower, tDot, sDot, hj, hr, ht, hs, rfl⟩, ?_, ?_⟩
    · intro p hp
      exact (constant z₀ p ((orbit_eq p z₀).mp (hp.trans he₀))).symm
    · intro p
      rw [he₀]
      exact indicator p
  choose diagram weight hdiagram hweight hindicator using realize
  refine ⟨⟨diagram, weight, hdiagram, ?_⟩, ?_⟩
  · -- Step 3. Assemble the fixed family of scaled orbit drawings. The
    -- finite set in evalAt selects values only during evaluation.
    refine CaseFivePointwiseAux.sum_orbit_drawings orbit M.toLinearMap supported weight diagram
      (fun x y h => ⟨(x, y), rfl, h⟩) (fun O x y => hweight O (x, y))
      (supplier.2.2.2.2.2 M) ?_
    intro O x y
    obtain ⟨z, he, _⟩ := O.property
    have hm : ((x, y) : Pair) ∈ O.val ↔ orbit (x, y) = O.val := by
      rw [he]
      exact (orbit_eq (x, y) z).symm
    rw [Finsupp.smul_apply]
    change weight O * coefficient (eval (diagram O)) (x, y) = _
    rw [hindicator]
    by_cases h : orbit (x, y) = O.val
    · rw [ite_eq_left h, ite_eq_left (hm.mpr h), mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun hw => h (hm.mp hw)), mul_zero]
  · -- Step 4. The supplier proves the finite orbit criterion for evaluated
    -- finite linear combinations. Reindex the evaluations by list positions
    -- so the reviewed sum keeps its scope, including empty and singleton cases.
    have criterion := (ExpansionIntoRightDiagrams G A D F C E a b d c e f M).2
    refine Iff.trans ?_ criterion
    constructor
    · rintro ⟨terms, hterms, hM⟩
      refine ⟨terms, hterms, MackeyDiagrams.Biset.Hom.ext ?_⟩
      exact hM.trans (CaseFivePointwiseAux.finite_eval terms).symm
    · rintro ⟨terms, hterms, hM⟩
      refine ⟨terms, hterms, ?_⟩
      exact (congrArg MackeyDiagrams.Biset.Hom.toLinearMap hM).trans
        (CaseFivePointwiseAux.finite_eval terms))

#print axioms CaseFivePointwiseFiniteDiagramIdentity
