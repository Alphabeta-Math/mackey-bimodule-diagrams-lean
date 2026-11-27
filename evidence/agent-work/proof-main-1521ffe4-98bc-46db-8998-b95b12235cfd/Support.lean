namespace CaseFiveUnscaled

open MackeyDiagrams
noncomputable section

universe u v

variable {R : Type v} [CommSemiring R]

private abbrev castVec {ι : Type*} : (ι →₀ Nat) →+ (ι →₀ R) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom R)

private theorem cast_single {ι : Type*} (i : ι) (n : Nat) :
    castVec (R := R) (Finsupp.single i n) = Finsupp.single i (n : R) :=
  Finsupp.mapRange_single (hf := map_zero (Nat.castAddMonoidHom R))

private theorem cast_entry {ι : Type*} (x : ι →₀ Nat) (i : ι) :
    castVec (R := R) x i = (x i : R) := rfl

private theorem cast_nsmul {ι : Type*} (n : Nat) (v : ι →₀ Nat) :
    castVec (R := R) (n • v) = (n : R) • castVec v := by
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]

private def Compatible {ι κ : Type*}
    (N : (ι →₀ Nat) →ₗ[Nat] (κ →₀ Nat)) (T : (ι →₀ R) →ₗ[R] (κ →₀ R)) :=
  ∀ v, castVec (N v) = T (castVec v)

private theorem compatible_columns {ι κ : Type*}
    {N : (ι →₀ Nat) →ₗ[Nat] (κ →₀ Nat)} {T : (ι →₀ R) →ₗ[R] (κ →₀ R)}
    (h : ∀ i, castVec (N (Finsupp.single i 1)) = T (Finsupp.single i 1)) :
    Compatible N T := by
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | single i n =>
    rw [← Finsupp.smul_single_one i n, map_smul, cast_nsmul, h, cast_nsmul,
      cast_single, Nat.cast_one, map_smul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

private theorem cast_pair {K H J : Type u} [Group K] [Group H] [Group J]
    (X : Biset K H) (Y : Biset H J) (p : X.carrier →₀ Nat) (q : Y.carrier →₀ Nat) :
    castVec (R := R) (Biset.pairLinear Nat X Y p q) =
      Biset.pairLinear R X Y (castVec p) (castVec q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' =>
    rw [map_add, LinearMap.add_apply, map_add, hp, hp', map_add, map_add, LinearMap.add_apply]
  | single x a =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' => rw [map_add, map_add, hq, hq', map_add, map_add]
    | single y b => simp only [Biset.pairLinear_single, cast_single, Nat.cast_mul]

variable {K H J : Type u} [Group K] [Group H] [Group J]

private abbrev Natural {X Y : Biset K H} (N : Biset.Hom Nat X Y) (T : Biset.Hom R X Y) :=
  Compatible N.toLinearMap T.toLinearMap

private theorem natural_vertical {X Y Z : Biset K H}
    {N : Biset.Hom Nat X Y} {M : Biset.Hom Nat Y Z}
    {T : Biset.Hom R X Y} {S : Biset.Hom R Y Z}
    (hN : Natural N T) (hM : Natural M S) :
    Natural (N.vertical M) (T.vertical S) := by
  intro v
  change castVec (M.toLinearMap (N.toLinearMap v)) = S.toLinearMap (T.toLinearMap (castVec v))
  rw [hM, hN]

private theorem natural_horizontal {X X' : Biset K H} {Y Y' : Biset H J}
    {N : Biset.Hom Nat X X'} {M : Biset.Hom Nat Y Y'}
    {T : Biset.Hom R X X'} {S : Biset.Hom R Y Y'}
    (hN : Natural N T) (hM : Natural M S) :
    Natural (N.horizontal M) (T.horizontal S) := by
  apply compatible_columns
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨x, y⟩
  change castVec ((N.horizontal M).toLinearMap (Finsupp.single (X.pair Y x y) 1)) =
    (T.horizontal S).toLinearMap (Finsupp.single (X.pair Y x y) 1)
  simp only [Biset.Hom.horizontal_single, one_smul, cast_pair]
  rw [hN _, hM _, cast_single, cast_single, Nat.cast_one]

private theorem natural_id (X : Biset K H) :
    Natural (Biset.Hom.id X) (Biset.Hom.id (R := R) X) := fun _ => rfl

private theorem natural_push {X Y : Biset K H} (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x)) :
    Natural (Biset.Hom.ofFunction f hf) (Biset.Hom.ofFunction (R := R) f hf) := by
  apply compatible_columns
  intro x
  simp only [Biset.Hom.ofFunction_single, cast_single, Nat.cast_one]

private theorem natural_transfer {X Y : Biset K H} (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) :
    Natural (Biset.Hom.transfer Nat f hf finite) (Biset.Hom.transfer R f hf finite) := by
  apply compatible_columns
  intro y
  simp only [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum,
    map_sum, cast_single, Nat.cast_one]

variable {U : Type u} [Group U]

private theorem eval_singleton {K H : Subgroup U} {p q : Word K H} (d : ScopedDiagram R p q) :
    (ScopedDiagram.linearCombination [(1, d)]).eval = d.eval := by
  apply Biset.Hom.ext
  ext v w
  simp [ScopedDiagram.eval_linearCombination_apply]

private abbrev drawingEval {S : Type*} [CommSemiring S]
    {K H : Subgroup U} {p q : Word K H} (d : LabelledDrawing S p q) :=
  d.interpret.eval

private def NaturalDrawing {K H : Subgroup U} {p q : Word K H}
    (N : LabelledDrawing Nat p q) (T : LabelledDrawing R p q) :=
  Natural (drawingEval N) (drawingEval T)

private theorem natural_drawing_vertical {K H : Subgroup U} {p q s : Word K H}
    {N : LabelledDrawing Nat p q} {M : LabelledDrawing Nat q s}
    {T : LabelledDrawing R p q} {S : LabelledDrawing R q s}
    (hN : NaturalDrawing N T) (hM : NaturalDrawing M S) :
    NaturalDrawing (.vertical N M) (.vertical T S) := natural_vertical hN hM

private theorem natural_drawing_horizontal {K H J : Subgroup U}
    {p p' : Word K H} {q q' : Word H J}
    {N : LabelledDrawing Nat p p'} {M : LabelledDrawing Nat q q'}
    {T : LabelledDrawing R p p'} {S : LabelledDrawing R q q'}
    (hN : NaturalDrawing N T) (hM : NaturalDrawing M S) :
    NaturalDrawing (.horizontal N M) (.horizontal T S) := natural_horizontal hN hM

private theorem natural_drawing_id {K H : Subgroup U} (p : Word K H) :
    NaturalDrawing (.ordinary (.id p)) (.ordinary (.id p) : LabelledDrawing R p p) :=
  natural_id p.basis

private theorem natural_associate {K H J F : Subgroup U}
    (p : Word K H) (q : Word H J) (r : Word J F) :
    NaturalDrawing (.ordinary (.associate p q r))
      (.ordinary (Diagram.associate (R := R) p q r)) := by
  apply compatible_columns
  intro z
  simp only [drawingEval, LabelledDrawing.interpret, ScopedDiagram.eval, Diagram.eval,
    Biset.associate, Biset.Hom.ofFunction_single, cast_single, Nat.cast_one]

private theorem natural_unassociate {K H J F : Subgroup U}
    (p : Word K H) (q : Word H J) (r : Word J F) :
    NaturalDrawing (.ordinary (.unassociate p q r))
      (.ordinary (Diagram.unassociate (R := R) p q r)) := by
  apply compatible_columns
  intro z
  simp only [drawingEval, LabelledDrawing.interpret, ScopedDiagram.eval, Diagram.eval,
    Biset.unassociate, Biset.Hom.ofFunction_single, cast_single, Nat.cast_one]

private theorem natural_parallel {F A C G : Subgroup U}
    (a : ConjEmbedding A G) (i : ConjEmbedding F A)
    (c : ConjEmbedding C G) (k : ConjEmbedding F C) (t : Dot (a.comp i) (c.comp k)) :
    NaturalDrawing (.parallelUp a i c k [(1,t)])
      (LabelledDrawing.parallelUp (R := R) a i c k [(1,t)]) := by
  change Natural (ScopedDiagram.linearCombination [(1, .ordinary (.parallelUp a i c k t))]).eval
    (ScopedDiagram.linearCombination [(1, .ordinary (Diagram.parallelUp (R := R) a i c k t))]).eval
  rw [eval_singleton, eval_singleton]
  simp only [ScopedDiagram.eval, Diagram.parallelUp, Diagram.eval]
  apply natural_vertical (natural_vertical ?_ ?_) ?_
  · apply compatible_columns
    intro z
    rw [Generator.mergeUp, Generator.mergeUp, Biset.Hom.ofFunction_single, Biset.Hom.ofFunction_single, cast_single, Nat.cast_one]
  · apply compatible_columns
    intro z
    rw [Generator.upDot, Generator.upDot, Biset.Hom.ofFunction_single, Biset.Hom.ofFunction_single, cast_single, Nat.cast_one]
  · apply compatible_columns
    intro z
    rw [Generator.splitUp, Generator.splitUp, Biset.Hom.ofFunction_single, Biset.Hom.ofFunction_single, cast_single, Nat.cast_one]

private theorem natural_multiplication {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (t : Dot (a.comp l) (b.comp r)) :
    NaturalDrawing (.mixedMultiplication a b l r [(1,t)])
      (LabelledDrawing.mixedMultiplication (R := R) a b l r [(1,t)]) := by
  change Natural (ScopedDiagram.linearCombination [(1, .ordinary (.mixedMultiplication a b l r t))]).eval
    (ScopedDiagram.linearCombination [(1, .ordinary (Diagram.mixedMultiplication (R := R) a b l r t))]).eval
  rw [eval_singleton, eval_singleton]
  exact natural_push _ (Generator.mixedMultiplication_equivariant a b l r t)

private theorem natural_projection {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (t : ProjectionDot.Mixed a b l r) :
    NaturalDrawing (.compactProjection a b l r [(1,t)])
      (LabelledDrawing.compactProjection (R := R) a b l r [(1,t)]) := by
  change Natural
    (ScopedDiagram.linearCombination [(1, .ordinary (.mixedProjection a b l r t.dot t.finite))]).eval
    (ScopedDiagram.linearCombination [(1, .ordinary (Diagram.mixedProjection (R := R) a b l r t.dot t.finite))]).eval
  rw [eval_singleton, eval_singleton]
  exact natural_transfer _ (Generator.mixedMultiplication_equivariant a b l r t.dot) t.finite

private theorem coefficient_cast {K H : Subgroup U} {p q : Word K H}
    {N : LabelledDrawing Nat p q} {D : LabelledDrawing R p q}
    (hd : NaturalDrawing N D) (x : p.basis.carrier) (y : q.basis.carrier) :
    (drawingEval D).toLinearMap (Finsupp.single x 1) y =
      (((drawingEval N).toLinearMap (Finsupp.single x 1) y : Nat) : R) := by
  have he := congrArg (fun v : q.basis.carrier →₀ R => v y) (hd (Finsupp.single x 1))
  change castVec (R := R) ((drawingEval N).toLinearMap (Finsupp.single x 1)) y =
    (drawingEval D).toLinearMap (castVec (Finsupp.single x 1)) y at he
  rw [cast_entry, cast_single, Nat.cast_one] at he
  exact he.symm

private theorem coefficient_transport {K H : Subgroup U} {p q : Word K H}
    {N : LabelledDrawing Nat p q} {C : LabelledDrawing Complex p q} {T : LabelledDrawing R p q}
    (hc : NaturalDrawing N C) (ht : NaturalDrawing N T)
    (x : p.basis.carrier) (y : q.basis.carrier) (n : Nat)
    (h : (drawingEval C).toLinearMap (Finsupp.single x 1) y = (n : Complex)) :
    (drawingEval T).toLinearMap (Finsupp.single x 1) y = (n : R) := by
  rw [coefficient_cast hc x y] at h
  rw [coefficient_cast ht x y, Nat.cast_injective (R := Complex) h]


private theorem linearCombination_map {K H : Subgroup U} {p q : Word K H}
    {ι : Type*} (l : ι →₀ R) (f : ι → ScopedDiagram R p q)
    (x : p.basis.carrier →₀ R) :
    (ScopedDiagram.linearCombination (l.support.toList.map (fun i => (l i, f i)))).eval.toLinearMap x =
      l.sum (fun i r => r • (f i).eval.toLinearMap x) := by
  classical
  rw [ScopedDiagram.eval_linearCombination_apply, List.map_map]
  change _ = ∑ i ∈ l.support, l i • (f i).eval.toLinearMap x
  have h := List.sum_toFinset (fun i => l i • (f i).eval.toLinearMap x) l.support.nodup_toList
  rw [Finset.toList_toFinset] at h
  exact h.symm

private theorem frame_right_sum {K H J : Type u} [Group K] [Group H] [Group J]
    {X X' : Biset K H} {Y Y' : Biset H J} {ι : Type*}
    (l : ι →₀ R) (N : Biset.Hom R X X') (f : ι → Biset.Hom R X X') (g : Biset.Hom R Y Y')
    (h : ∀ x, N.toLinearMap x = l.sum (fun i r => r • (f i).toLinearMap x))
    (m : (X.tensor Y).carrier →₀ R) :
    (N.horizontal g).toLinearMap m = l.sum (fun i r => r • ((f i).horizontal g).toLinearMap m) := by
  let M := l.sum (fun i r => r • ((f i).horizontal g).toLinearMap)
  have hM : (N.horizontal g).toLinearMap = M := by
    apply Finsupp.lhom_ext
    intro z r
    refine Quotient.inductionOn z ?_
    rintro ⟨x, y⟩
    change (N.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r) =
      (∑ i ∈ l.support, l i • ((f i).horizontal g).toLinearMap) (Finsupp.single (X.pair Y x y) r)
    simp only [Biset.Hom.horizontal_single, LinearMap.sum_apply, LinearMap.smul_apply, h,
      Finsupp.sum]
    let frame := (Biset.pairLinear R X' Y').flip (g.toLinearMap (Finsupp.single y 1))
    change r • frame (∑ i ∈ l.support, l i • (f i).toLinearMap (Finsupp.single x 1)) = _
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_comm]
    rfl
  rw [hM]
  simp only [M, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem frame_left_sum {K H J : Type u} [Group K] [Group H] [Group J]
    {X X' : Biset K H} {Y Y' : Biset H J} {ι : Type*}
    (l : ι →₀ R) (g : Biset.Hom R X X') (N : Biset.Hom R Y Y') (f : ι → Biset.Hom R Y Y')
    (h : ∀ y, N.toLinearMap y = l.sum (fun i r => r • (f i).toLinearMap y))
    (m : (X.tensor Y).carrier →₀ R) :
    (g.horizontal N).toLinearMap m = l.sum (fun i r => r • (g.horizontal (f i)).toLinearMap m) := by
  let M := l.sum (fun i r => r • (g.horizontal (f i)).toLinearMap)
  have hM : (g.horizontal N).toLinearMap = M := by
    apply Finsupp.lhom_ext
    intro z r
    refine Quotient.inductionOn z ?_
    rintro ⟨x, y⟩
    change (g.horizontal N).toLinearMap (Finsupp.single (X.pair Y x y) r) =
      (∑ i ∈ l.support, l i • (g.horizontal (f i)).toLinearMap) (Finsupp.single (X.pair Y x y) r)
    simp only [Biset.Hom.horizontal_single, LinearMap.sum_apply, LinearMap.smul_apply, h,
      Finsupp.sum, map_sum, Finset.smul_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  rw [hM]
  simp only [M, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem eq_of_columns {ι κ : Type*} {f g : (ι →₀ R) →ₗ[R] (κ →₀ R)}
    (h : ∀ x y, f (Finsupp.single x 1) y = g (Finsupp.single x 1) y) : f = g := by
  apply Finsupp.lhom_ext
  intro x r
  rw [← Finsupp.smul_single_one x r, map_smul, map_smul]
  exact congrArg (r • ·) (Finsupp.ext (h x))

private theorem orbit_sum_entries {Q : Type*} {L : Type*} [Group L] [MulAction L Q]
    {S : Set (Set Q)} (finite : (Set.univ : Set S).Finite) (z : Q)
    (isOrbit : ∀ O ∈ S, ∃ w : Q, O = MulAction.orbit L w) :
    (∑ O ∈ (Set.Finite.toFinset finite),
      @ite R (z ∈ O.val) (Classical.propDecidable _) 1 0) =
      @ite R (MulAction.orbit L z ∈ S) (Classical.propDecidable _) 1 0 := by
  classical
  let indices := Set.Finite.toFinset finite
  have unique (O : S) (h : z ∈ O.val) : O.val = MulAction.orbit L z := by
    obtain ⟨w, hw⟩ := isOrbit O.val O.property
    rw [hw] at h ⊢
    exact (MulAction.orbit_eq_iff.mpr h).symm
  by_cases hs : MulAction.orbit L z ∈ S
  · let O : S := ⟨MulAction.orbit L z, hs⟩
    change (∑ O ∈ indices, _) = _
    rw [ite_eq_left hs, Finset.sum_eq_single O, ite_eq_left (MulAction.mem_orbit_self z)]
    · intro O' _ hne
      exact ite_eq_right (fun hz => hne (Subtype.ext (unique O' hz)))
    · intro h
      exact (h (finite.mem_toFinset.mpr (Set.mem_univ _))).elim
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro O _
    exact ite_eq_right (fun hz => hs (unique O hz ▸ O.property))

private abbrev caseWord {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :=
  (Word.up a).tensor ((Word.down b).tensor (.up d))

private abbrev casePoint {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (g : G) (x : D) : (caseWord a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis g (Generator.mixedPair b d x)

private theorem casePoint_surjective {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (z : (caseWord a b d).basis.carrier) : ∃ g x, casePoint a b d g x = z := by
  obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective y
  exact ⟨g, x, rfl⟩

private theorem caseWord_finite {G A D F : Subgroup U}
    [Finite G] [Finite D]
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :
    Finite (caseWord a b d).basis.carrier :=
  Finite.of_surjective (fun p : G × D => casePoint a b d p.1 p.2) (by
    intro z
    obtain ⟨g, x, h⟩ := casePoint_surjective a b d z
    exact ⟨(g, x), h⟩)
private abbrev Sinf := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
private abbrev ParabolicPerm (H : Subgroup (Equiv.Perm Nat)) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    H = ⨆ l, blockSym (blocks l)
private abbrev Parabolic (H : Subgroup Sinf) := ParabolicPerm (H.map Sinf.subtype)
-- The finite block-union argument from the registered orbit-multiplicity proof.
private theorem parabolic_finite {H : Subgroup Sinf} (hH : Parabolic H) : Finite H := by
  classical
  obtain ⟨n, blocks, _, _, hblocks⟩ := hH
  let X := Finset.univ.biUnion blocks
  have hsub : H.map Sinf.subtype ≤ blockSym X := by
    rw [hblocks]
    refine iSup_le fun i σ hs => ?_
    obtain ⟨τ, rfl⟩ := hs
    let σ : Equiv.Perm Nat := Equiv.Perm.ofSubtype τ
    have moved_mem (x : Nat) (hx : σ x ≠ x) : x ∈ X := by
      by_contra hn
      have hi : x ∉ blocks i := fun hx' => hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx'⟩)
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem τ hi)
    have preserves (x : Nat) : σ x ∈ X ↔ x ∈ X := by
      by_cases h : σ x = x
      · rw [h]
      · have hy : σ (σ x) ≠ σ x := fun hh => h (σ.injective hh)
        exact iff_of_true (moved_mem (σ x) hy) (moved_mem x h)
    exact ⟨σ.subtypePerm preserves, Equiv.Perm.ofSubtype_subtypePerm preserves moved_mem⟩
  let : Finite (blockSym X) :=
    (Set.finite_range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))).to_subtype
  exact Finite.of_injective
    (fun h : H => (⟨(h.val : Equiv.Perm Nat), hsub ⟨h.val, h.property, rfl⟩⟩ : blockSym X))
    (fun _ _ hh => Subtype.ext (Subtype.ext (congrArg (fun y : blockSym X => y.val) hh)))


section Drawings

variable {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (u : ConjEmbedding G B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)

private abbrev lowerLabel := Dot (u.comp a) (v.comp b)
private abbrev middleLabel := Dot (v.comp d) (w.comp f)
private abbrev upperLabel := Dot (u.comp c) (w.comp e)

private abbrev leftDrawing
    (rs : List (R × lowerLabel a b u v)) (ts : List (R × middleLabel d f v w))
    (ss : List (R × ProjectionDot.Mixed u w c e)) :
    LabelledDrawing R (caseWord a b d) (caseWord c e f) :=
  .vertical (.ordinary (.unassociate (.up a) (.down b) (.up d)))
    (.vertical (.horizontal (.mixedMultiplication u v a b rs) (.ordinary (.id (.up d))))
      (.vertical (.ordinary (.associate (.down u) (.up v) (.up d)))
        (.vertical (.horizontal (.ordinary (.id (.down u))) (.parallelUp v d w f ts))
          (.vertical (.ordinary (.unassociate (.down u) (.up w) (.up f)))
            (.vertical (.horizontal (.compactProjection u w c e ss) (.ordinary (.id (.up f))))
              (.ordinary (.associate (.up c) (.down e) (.up f))))))))

private abbrev rightDrawing (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (k : ConjEmbedding B C) (r : ProjectionDot.Mixed b d i j)
    (t : Dot (a.comp i) (c.comp k)) (s : Dot (e.comp k) (f.comp j)) :
    LabelledDrawing R (caseWord a b d) (caseWord c e f) :=
  .vertical (.horizontal (.ordinary (.id (.up a))) (.compactProjection b d i j [(1,r)]))
    (.vertical (.ordinary (.unassociate (.up a) (.up i) (.down j)))
      (.vertical (.horizontal (.parallelUp a i c k [(1,t)]) (.ordinary (.id (.down j))))
        (.vertical (.ordinary (.associate (.up c) (.up k) (.down j)))
          (.horizontal (.ordinary (.id (.up c))) (.mixedMultiplication e f k j [(1,s)])))))

-- The coefficient count in the proof of Proposition 8.7 is independent of the ring.
-- Check the same singleton drawing first over Nat. Its identity and reassociation
-- columns are deterministic, and its compact projection sums over the same fiber.
private theorem natural_left (r : lowerLabel a b u v) (t : middleLabel d f v w)
    (s : ProjectionDot.Mixed u w c e) :
    NaturalDrawing (leftDrawing a b d c e f u v w [(1,r)] [(1,t)] [(1,s)])
      (leftDrawing (R := R) a b d c e f u v w [(1,r)] [(1,t)] [(1,s)]) := by
  exact natural_drawing_vertical (natural_unassociate (.up a) (.down b) (.up d))
    (natural_drawing_vertical
      (natural_drawing_horizontal (natural_multiplication u v a b r) (natural_drawing_id (.up d)))
      (natural_drawing_vertical (natural_associate (.down u) (.up v) (.up d))
        (natural_drawing_vertical
          (natural_drawing_horizontal (natural_drawing_id (.down u)) (natural_parallel v d w f t))
          (natural_drawing_vertical (natural_unassociate (.down u) (.up w) (.up f))
            (natural_drawing_vertical
              (natural_drawing_horizontal (natural_projection u w c e s) (natural_drawing_id (.up f)))
              (natural_associate (.up c) (.down e) (.up f)))))))

private theorem natural_right (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (k : ConjEmbedding B C) (r : ProjectionDot.Mixed b d i j)
    (t : Dot (a.comp i) (c.comp k)) (s : Dot (e.comp k) (f.comp j)) :
    NaturalDrawing (rightDrawing a b d c e f i j k r t s)
      (rightDrawing (R := R) a b d c e f i j k r t s) := by
  exact natural_drawing_vertical
    (natural_drawing_horizontal (natural_drawing_id (.up a)) (natural_projection b d i j r))
    (natural_drawing_vertical (natural_unassociate (.up a) (.up i) (.down j))
      (natural_drawing_vertical
        (natural_drawing_horizontal (natural_parallel a i c k t) (natural_drawing_id (.down j)))
        (natural_drawing_vertical (natural_associate (.up c) (.up k) (.down j))
          (natural_drawing_horizontal (natural_drawing_id (.up c)) (natural_multiplication e f k j s)))))

-- The wording correction in published § 1.2 makes the scalar action on
-- maps explicit. For the extension to R in § 8.3, these balanced basis
-- formulas are R-linear in each map. The group-algebra balancing remains
-- encoded by the quotient carrier used in Biset.Hom.horizontal_single.
private theorem weighted_left
    (rs : DotLabel R (u.comp a) (v.comp b)) (ts : DotLabel R (v.comp d) (w.comp f))
    (ss : DotLabel R (u.comp c) (w.comp e))
    (fin : ∀ s : upperLabel c e u w, ∀ z,
      Set.Finite {p | Generator.mixedMultiplicationBasis u w c e s p = z})
    (m : (caseWord a b d).basis.carrier →₀ R) :
    (drawingEval (leftDrawing a b d c e f u v w rs.terms ts.terms
      (ss.terms.map (fun (cs,s) => (cs, ⟨s, fin s⟩))))).toLinearMap m =
    rs.sum (fun r cr => ts.sum (fun t ct => ss.sum (fun s cs => (cr * ct * cs) •
      (drawingEval (leftDrawing a b d c e f u v w [(1,r)] [(1,t)]
        [(1, ⟨s, fin s⟩)] )).toLinearMap m))) := by
  classical
  let ga := Word.up a
  let ad := Word.down b
  let df := Word.up d
  let gc := Word.up c
  let ce := Word.down e
  let ef := Word.up f
  let du := Word.down u
  let uv := Word.up v
  let uw := Word.up w
  let pre := (Diagram.unassociate (R := R) ga ad df).eval.toLinearMap
  let mid₁ := (Diagram.associate (R := R) du uv df).eval.toLinearMap
  let mid₂ := (Diagram.unassociate (R := R) du uw ef).eval.toLinearMap
  let post := (Diagram.associate (R := R) gc ce ef).eval.toLinearMap
  let lower (r : lowerLabel a b u v) := ScopedDiagram.ordinary (Diagram.mixedMultiplication (R := R) u v a b r)
  let center (t : middleLabel d f v w) := ScopedDiagram.ordinary (Diagram.parallelUp (R := R) v d w f t)
  let upper (s : upperLabel c e u w) := ScopedDiagram.ordinary (Diagram.mixedProjection (R := R) u w c e s (fin s))
  let terms {ι : Type u} {K H : Subgroup U} {p q : Word K H}
      (l : ι →₀ R) (Dg : ι → ScopedDiagram R p q) :=
    ScopedDiagram.linearCombination (l.support.toList.map (fun i => (l i, Dg i)))
  let L := ((terms rs lower).eval.horizontal (Biset.Hom.id df.basis)).toLinearMap
  let M := ((Biset.Hom.id du.basis).horizontal (terms ts center).eval).toLinearMap
  let N := ((terms ss upper).eval.horizontal (Biset.Hom.id ef.basis)).toLinearMap
  let Lr := fun r => ((lower r).eval.horizontal (Biset.Hom.id df.basis)).toLinearMap
  let Mt := fun t => ((Biset.Hom.id du.basis).horizontal (center t).eval).toLinearMap
  let Ns := fun s => ((upper s).eval.horizontal (Biset.Hom.id ef.basis)).toLinearMap
  have hL x : L x = rs.sum (fun r cr => cr • Lr r x) :=
    frame_right_sum rs _ _ _ (linearCombination_map rs lower) x
  have hM x : M x = ts.sum (fun t ct => ct • Mt t x) :=
    frame_left_sum ts _ _ _ (linearCombination_map ts center) x
  have hN x : N x = ss.sum (fun s cs => cs • Ns s x) :=
    frame_right_sum ss _ _ _ (linearCombination_map ss upper) x
  have singleton r t s :
      (drawingEval (leftDrawing a b d c e f u v w [(1,r)] [(1,t)]
        [(1, ⟨s, fin s⟩)])).toLinearMap m =
      post (Ns s (mid₂ (Mt t (mid₁ (Lr r (pre m)))))) := by
    let L' := ((ScopedDiagram.linearCombination [(1, lower r)]).eval.horizontal
      (Biset.Hom.id df.basis)).toLinearMap
    let M' := ((Biset.Hom.id du.basis).horizontal
      (ScopedDiagram.linearCombination [(1, center t)]).eval).toLinearMap
    let N' := ((ScopedDiagram.linearCombination [(1, upper s)]).eval.horizontal
      (Biset.Hom.id ef.basis)).toLinearMap
    change post (N' (mid₂ (M' (mid₁ (L' (pre m)))))) = _
    dsimp only [L', M', N']
    rw [eval_singleton, eval_singleton, eval_singleton]
  have hmain :
      (drawingEval (leftDrawing a b d c e f u v w rs.terms ts.terms
        (ss.terms.map (fun (cs,s) => (cs, ⟨s, fin s⟩))))).toLinearMap m =
      post (N (mid₂ (M (mid₁ (L (pre m)))))) := by
    let rawLower := rs.terms.map (fun (cr,r) => (cr, lower r))
    let rawCenter := ts.terms.map (fun (ct,t) => (ct, center t))
    let rawUpper := (ss.terms.map (fun (cs,s) => (cs, (⟨s, fin s⟩ : ProjectionDot.Mixed u w c e)))).map
        (fun (cs,s) => (cs, ScopedDiagram.ordinary
          (Diagram.mixedProjection (R := R) u w c e s.dot s.finite)))
    have hLower : rawLower = rs.support.toList.map (fun r => (rs r, lower r)) := by
      simp only [rawLower, DotLabel.terms, List.map_map]
      rfl
    have hCenter : rawCenter = ts.support.toList.map (fun t => (ts t, center t)) := by
      simp only [rawCenter, DotLabel.terms, List.map_map]
      rfl
    have hUpper : rawUpper = ss.support.toList.map (fun s => (ss s, upper s)) := by
      simp only [rawUpper, DotLabel.terms, List.map_map]
      rfl
    let L' := ((ScopedDiagram.linearCombination rawLower).eval.horizontal
      (Biset.Hom.id df.basis)).toLinearMap
    let M' := ((Biset.Hom.id du.basis).horizontal
      (ScopedDiagram.linearCombination rawCenter).eval).toLinearMap
    let N' := ((ScopedDiagram.linearCombination rawUpper).eval.horizontal
      (Biset.Hom.id ef.basis)).toLinearMap
    change post (N' (mid₂ (M' (mid₁ (L' (pre m)))))) = _
    dsimp only [L', M', N']
    rw [hLower, hCenter, hUpper]

  rw [hmain, hL]
  simp only [Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [hM]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [hN]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum, singleton, smul_smul, mul_assoc]

end Drawings

end
end CaseFiveUnscaled

open MackeyDiagrams CaseFiveUnscaled

open MackeyDiagrams CaseFiveUnscaled
