import MackeyDiagrams
import Proofs.EvaluationWithOneProjection
import Proofs.RightOrbitDiagramFromProjectedStabilizer

set_option maxHeartbeats 2000000

namespace ExpansionIntoRightDiagramsAux

open MackeyDiagrams

private theorem basis_ext {X : Type*} {V : Type*} [AddCommMonoid V] [Module Complex V]
    {L M : (X →₀ Complex) →ₗ[Complex] V}
    (h : ∀ x, L (Finsupp.single x 1) = M (Finsupp.single x 1)) : L = M := by
  apply Finsupp.lhom_ext
  intro x c
  rw [← Finsupp.smul_single_one, map_smul, map_smul, h x]

private theorem assemble {X I V : Type*} [AddCommMonoid V] [Module Complex V]
    (M : (X →₀ Complex) →ₗ[Complex] V) (L : I → (X →₀ Complex) →ₗ[Complex] V)
    (finiteColumn : ∀ x, Set.Finite {i : I | L i (Finsupp.single x 1) ≠ 0})
    (columnSum : ∀ x, M (Finsupp.single x 1) =
      (finiteColumn x).toFinset.sum (fun i => L i (Finsupp.single x 1))) :
    ∃ finite : ∀ v, Set.Finite {i : I | L i v ≠ 0},
      ∀ v, M v = (finite v).toFinset.sum (fun i => L i v) := by
  classical
  -- Step 3. Collect each finite column over the orbit index. Linear extension
  -- gives one finitely supported vector of contributions for every finite input.
  let column (x : X) : I →₀ V :=
    Finsupp.ofSupportFinite (fun i => L i (Finsupp.single x 1)) (finiteColumn x)
  let collect := Finsupp.linearCombination Complex column
  have collect_basis (x : X) : collect (Finsupp.single x 1) = column x := by
    simp only [collect, Finsupp.linearCombination_single, one_smul]
  have entry (i : I) (v : X →₀ Complex) : collect v i = L i v := by
    have he : (Finsupp.lapply (R := Complex) i).comp collect = L i := by
      apply basis_ext
      intro x
      change collect (Finsupp.single x 1) i = _
      rw [collect_basis]
      rfl
    exact LinearMap.congr_fun he v
  let total := Finsupp.lsum Complex (fun _ : I => LinearMap.id (R := Complex) (M := V))
  have total_apply (w : I →₀ V) : total w = w.support.sum (fun i => w i) := by
    rw [Finsupp.lsum_apply]
    rfl
  have hM : M = total.comp collect := by
    apply basis_ext
    intro x
    change M (Finsupp.single x 1) = total (collect (Finsupp.single x 1))
    rw [columnSum x, collect_basis, total_apply]
    rfl
  have support_eq (v : X →₀ Complex) : (↑(collect v).support : Set I) = {i | L i v ≠ 0} := by
    ext i
    change i ∈ (collect v).support ↔ L i v ≠ 0
    rw [Finsupp.mem_support_iff, entry]
  let finite (v : X →₀ Complex) : Set.Finite {i : I | L i v ≠ 0} :=
    support_eq v ▸ (collect v).support.finite_toSet
  refine ⟨finite, fun v => ?_⟩
  have hfin : (finite v).toFinset = (collect v).support := by
    ext i
    rw [Set.Finite.mem_toFinset]
    exact (Set.ext_iff.mp (support_eq v) i).symm
  rw [hfin]
  calc
    M v = total (collect v) := LinearMap.congr_fun hM v
    _ = (collect v).support.sum (fun i => collect v i) := total_apply _
    _ = _ := Finset.sum_congr rfl (fun i _ => entry i v)

private theorem orbit_columns {X Y O : Type*} (orbit : X × Y → O)
    (M : (X →₀ Complex) →ₗ[Complex] (Y →₀ Complex))
    (I : Set O) (weight : I → Complex)
    (L : I → (X →₀ Complex) →ₗ[Complex] (Y →₀ Complex))
    (hit : ∀ x y, M (Finsupp.single x 1) y ≠ 0 → orbit (x, y) ∈ I)
    (weight_eq : ∀ (i : I) x y, orbit (x, y) = ↑i → weight i = M (Finsupp.single x 1) y)
    (finiteOrbits : ∀ x, Set.Finite {o : O |
      ∃ y, M (Finsupp.single x 1) y ≠ 0 ∧ o = orbit (x, y)})
    (matrix : ∀ (i : I) x y,
      L i (Finsupp.single x 1) y =
        @ite Complex (orbit (x, y) = ↑i) (Classical.propDecidable _) (weight i) 0) :
    ∃ finite : ∀ v, Set.Finite {i : I | L i v ≠ 0},
      ∀ v, M v = (finite v).toFinset.sum (fun i => L i v) := by
  classical
  have finiteColumn (x : X) : Set.Finite {i : I | L i (Finsupp.single x 1) ≠ 0} := by
    apply ((finiteOrbits x).preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
    intro i hi
    change L i (Finsupp.single x 1) ≠ 0 at hi
    have h : ∃ y, L i (Finsupp.single x 1) y ≠ 0 := by
      by_contra! hall
      exact hi (Finsupp.ext fun y => hall y)
    obtain ⟨y, hy⟩ := h
    have horbit : orbit (x, y) = ↑i := by
      by_contra hne
      exact hy ((matrix i x y).trans (ite_eq_right hne))
    refine ⟨y, ?_, horbit.symm⟩
    rw [matrix, ite_eq_left horbit, weight_eq i x y horbit] at hy
    exact hy
  apply assemble M L finiteColumn
  intro x
  ext y
  rw [Finsupp.finsetSum_apply]
  by_cases hc : M (Finsupp.single x 1) y = 0
  · rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases he : orbit (x, y) = ↑i
    · rw [matrix, ite_eq_left he, weight_eq i x y he, hc]
    · rw [matrix, ite_eq_right he]
  · let i : I := ⟨orbit (x, y), hit x y hc⟩
    have he : orbit (x, y) = ↑i := rfl
    have hval : L i (Finsupp.single x 1) y = M (Finsupp.single x 1) y := by
      rw [matrix, ite_eq_left he, weight_eq i x y he]
    rw [Finset.sum_eq_single i]
    · exact hval.symm
    · intro j _ hj
      have hne : orbit (x, y) ≠ ↑j := fun hj' => hj (Subtype.ext (hj'.symm.trans he))
      rw [matrix, ite_eq_right hne]
    · intro hi
      rw [Set.Finite.mem_toFinset] at hi
      have hzero : L i (Finsupp.single x 1) = 0 := by simpa using hi
      exact False.elim (hc (hval.symm.trans (congrArg (fun w : Y →₀ Complex => w y) hzero)))

private theorem fold_finset {U : Type*} [Group U] {G F : Subgroup U}
    {bottom top : Word G F} {I : Type*}
    (weight : I → Complex) (diagram : I → LabelledDrawing Complex bottom top)
    (s : Finset I) :
    ∃ terms : List (Complex × LabelledDrawing Complex bottom top),
      (∀ term ∈ terms, ∃ i, term = (weight i, diagram i)) ∧
      ∀ v : bottom.basis.carrier →₀ Complex,
        (terms.foldr (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
          (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))).interpret.eval.toLinearMap v =
          s.sum (fun i => weight i • (diagram i).interpret.eval.toLinearMap v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨[], by simp, fun v => ?_⟩
    change 0 = Finset.sum ∅ _
    simp
  | @insert i s hi ih =>
    obtain ⟨terms, hterms, hsum⟩ := ih
    refine ⟨(weight i, diagram i) :: terms, ?_, fun v => ?_⟩
    · intro term ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨i, rfl⟩
      · exact hterms term ht
    · let folded := terms.foldr
        (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
        (LabelledDrawing.ordinary (Diagram.zero (R := Complex) bottom top))
      change weight i • (diagram i).interpret.eval.toLinearMap v +
        folded.interpret.eval.toLinearMap v = _
      rw [Finset.sum_insert hi]
      exact congrArg (_ + ·) (hsum v)

end ExpansionIntoRightDiagramsAux

theorem ExpansionIntoRightDiagrams : (
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
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let orbit : Pair → Set Pair := MulAction.orbit (G × F)
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
  ∀ (M : MackeyDiagrams.Biset.Hom Complex X Y),
    (∃ (I : Set (Set Pair)) (weight : I → Complex)
        (diagram : I → MackeyDiagrams.LabelledDrawing Complex bottom top),
      (∀ i, IsRightTerm (diagram i)) ∧
      let term := fun (i : I) (v : Finsupp X.carrier Complex) =>
        weight i • MackeyDiagrams.Biset.Hom.toLinearMap (eval (diagram i)) v
      ∃ finite : ∀ v : Finsupp X.carrier Complex, Set.Finite {i : I | term i v ≠ 0},
        ∀ v : Finsupp X.carrier Complex,
          MackeyDiagrams.Biset.Hom.toLinearMap M v =
            Finset.sum (Set.Finite.toFinset (finite v)) (fun i => term i v)) ∧
    ((∃ terms : List (Complex × MackeyDiagrams.LabelledDrawing Complex bottom top),
        (∀ term ∈ terms, IsRightTerm term.2) ∧
        let drawing := List.foldr
          (fun term rest => MackeyDiagrams.LabelledDrawing.add
            (MackeyDiagrams.LabelledDrawing.scale term.1 term.2) rest)
          (MackeyDiagrams.LabelledDrawing.ordinary
            (MackeyDiagrams.Diagram.zero (R := Complex) bottom top)) terms
        M = eval drawing) ↔
      Set.Finite {O : Set Pair | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0})
) :=
(by
  classical
  intro U inst G A D F C E a b d c e f up down tensor comp ga ad df gc ce ef bottom top
    X Y Pair orbit coefficient MiddleLabel UpperLabel ProjectionTerm drawId rightDrawing eval
    IsRightTerm M
  -- Ian Xiao, Theorem 6.7, archived PDF p. 26 and revised published PDF p. 28.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The downloaded revision matches article-revision/mackey-bimodules.pdf.
  -- The archived original has a distinct SHA-256 digest. Both pages contain
  -- the same theorem, so the reviewed Lean type is used verbatim.
  -- Alphabeta Math presents the proof in paragraphs. Steps 1–4 here follow
  -- its coefficient invariance, stabilizer construction, and two finiteness arguments.
  let supplier := RightOrbitDiagramFromProjectedStabilizer G A D F C E a b d c e f
  -- Step 1. The supplier checks equivariance for this very action, including
  -- the inverse on the exterior right coordinate.
  have constant (z w : Pair) (hw : w ∈ orbit z) : coefficient M w = coefficient M z :=
    supplier.1 M z w hw
  let action : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  have orbit_eq (z w : Pair) : orbit z = orbit w ↔ z ∈ orbit w :=
    @MulAction.orbit_eq_iff _ _ _ action z w
  let supported : Set (Set Pair) := {O | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0}
  -- Step 2. Use the normalized pair and the projected stabilizer. The
  -- nonzero coefficient at that pair supplies the finite-fiber hypothesis.
  -- The supplier connects the typed compact projection, parallel induction
  -- crossing, and multiplication to (6.4) via CaseSixRightShapeEvaluation.
  -- EvaluationWithOneProjection gives the underlying basis formula in coordinates
  -- in D. The orbit supplier already checks the needed indicator for the exact
  -- list-labelled syntax and the finite-label converse.
  have realize (O : supported) :
      ∃ drawing : MackeyDiagrams.LabelledDrawing Complex bottom top,
        IsRightTerm drawing ∧ ∀ w : Pair,
          coefficient (eval drawing) w = if w ∈ O.val then 1 else 0 := by
    obtain ⟨z, he, hz⟩ := O.property
    obtain ⟨r, t, s, hz'⟩ := supplier.2.1 z
    let z₀ : Pair :=
      (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
        (MackeyDiagrams.Word.basis (tensor ad df)) 1 (MackeyDiagrams.Generator.mixedPair b d r),
       MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
        (MackeyDiagrams.Word.basis (tensor ce ef)) t (MackeyDiagrams.Generator.mixedPair e f s))
    have h₀ : coefficient M z₀ ≠ 0 := (constant z₀ z hz') ▸ hz
    obtain ⟨i, j, k, rDot, tDot, sDot, _, _, _, _, _, _, realizeAt⟩ :=
      (supplier.2.2.1 r t s).2.2.2
    obtain ⟨_, finite, indicator⟩ := realizeAt M h₀
    let lower := [((1 : Complex), (⟨rDot, finite⟩ : ProjectionTerm _ i j))]
    let drawing := rightDrawing _ i j k lower [(1, tDot)] [(1, sDot)]
    refine ⟨drawing, ⟨_, i, j, k, lower, [(1, tDot)], [(1, sDot)], rfl⟩, fun w => ?_⟩
    have he' : O.val = orbit z₀ := he.trans ((orbit_eq z z₀).mpr hz')
    rw [he']
    exact indicator w
  let diagram (O : supported) := Classical.choose (realize O)
  have right (O : supported) : IsRightTerm (diagram O) := (Classical.choose_spec (realize O)).1
  let weight (O : supported) := coefficient M (Classical.choose O.property)
  have weight_eq (O : supported) (x : X.carrier) (y : Y.carrier) (h : orbit (x, y) = O.val) :
      weight O = coefficient M (x, y) := by
    have he := (Classical.choose_spec O.property).1
    exact (constant _ _ ((orbit_eq _ _).mp (h.trans he))).symm
  let L (O : supported) := weight O • (eval (diagram O)).toLinearMap
  have matrix (O : supported) (x : X.carrier) (y : Y.carrier) :
      L O (Finsupp.single x 1) y =
        if orbit (x, y) = O.val then weight O else 0 := by
    obtain ⟨z, he, _⟩ := O.property
    have hm : ((x, y) : Pair) ∈ O.val ↔ orbit (x, y) = O.val := by
      rw [he]
      exact (orbit_eq (x, y) z).symm
    have indicator := (Classical.choose_spec (realize O)).2 (x, y)
    change (weight O • (eval (diagram O)).toLinearMap (Finsupp.single x 1)) y = _
    rw [Finsupp.smul_apply]
    change weight O * coefficient (eval (diagram O)) (x, y) = _
    rw [indicator]
    by_cases h : orbit (x, y) = O.val
    · rw [ite_eq_left h, ite_eq_left (hm.mpr h), mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun hw => h (hm.mp hw)), mul_zero]
  -- Step 3. Finiteness for every input is obtained by a linear extension of
  -- the assembled basis columns. Each coordinate of the sum has at most
  -- one contributing orbit, though a column may involve several orbits.
  have pointwise := ExpansionIntoRightDiagramsAux.orbit_columns orbit M.toLinearMap
    supported weight L (fun x y h => ⟨(x, y), rfl, h⟩) weight_eq (supplier.2.2.2.2.2 M) matrix
  refine ⟨⟨supported, weight, diagram, right, pointwise⟩, ?_⟩
  -- Step 4. The checked converse covers the three independent finite vertex
  -- labels and the outer finite sum. For the reverse implication, realize
  -- the finite orbit family by the specified list fold of typed drawings.
  constructor
  · rintro ⟨terms, hterms, hM⟩
    rw [hM]
    exact supplier.2.2.2.2.1 terms hterms
  · intro h
    let all : Finset supported := @Finset.univ supported h.fintype
    obtain ⟨terms, hterms, hsum⟩ :=
      ExpansionIntoRightDiagramsAux.fold_finset weight diagram all
    refine ⟨terms, ?_, ?_⟩
    · intro term ht
      obtain ⟨O, rfl⟩ := hterms term ht
      exact right O
    · apply MackeyDiagrams.Biset.Hom.ext
      apply LinearMap.ext
      intro v
      obtain ⟨finite, sum⟩ := pointwise
      calc
        M.toLinearMap v = (finite v).toFinset.sum (fun O => L O v) := sum v
        _ = all.sum (fun O => L O v) := by
          apply Finset.sum_subset (@Finset.subset_univ supported h.fintype _)
          intro O _ hO
          rw [Set.Finite.mem_toFinset] at hO
          exact not_ne_iff.mp hO
        _ = _ := (hsum v).symm
)

#print axioms EvaluationWithOneProjection
#print axioms RightOrbitDiagramFromProjectedStabilizer
#print axioms ExpansionIntoRightDiagrams
