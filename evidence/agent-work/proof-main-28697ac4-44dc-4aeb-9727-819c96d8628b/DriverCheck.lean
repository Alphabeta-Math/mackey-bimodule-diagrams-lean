import Mathlib.Data.ZMod.Basic
import MackeyDiagrams
import Proofs.ParabolicCaseFiveCoefficientOneExpansion
import Proofs.ParabolicRightOrbitMultiplicity

set_option maxHeartbeats 2000000

namespace RightSpanProof

open MackeyDiagrams
open scoped BigOperators
noncomputable section

universe u
variable {R S : Type*} [CommSemiring R] [CommSemiring S]

private abbrev castVector (f : R →+* S) {I : Type*} :=
  Finsupp.mapRange.addMonoidHom f.toAddMonoidHom (ι := I)

private theorem cast_single (f : R →+* S) {I : Type*} (x : I) (r : R) :
    castVector f (Finsupp.single x r) = Finsupp.single x (f r) :=
  Finsupp.mapRange_single (hf := f.map_zero)

private theorem cast_smul (f : R →+* S) {I : Type*} (r : R) (x : I →₀ R) :
    castVector f (r • x) = f r • castVector f x := by
  ext i
  exact map_mul f r (x i)

private def compatible (f : R →+* S) {I J : Type*}
    (A : (I →₀ R) →ₗ[R] J →₀ R) (B : (I →₀ S) →ₗ[S] J →₀ S) : Prop :=
  ∀ x, castVector f (A x) = B (castVector f x)

private theorem compatible_of_single (f : R →+* S) {I J : Type*}
    {A : (I →₀ R) →ₗ[R] J →₀ R} {B : (I →₀ S) →ₗ[S] J →₀ S}
    (h : ∀ i, castVector f (A (Finsupp.single i 1)) = B (Finsupp.single i 1)) :
    compatible f A B := by
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single i r =>
    rw [← Finsupp.smul_single_one i r, map_smul, cast_smul, cast_smul, map_smul,
      cast_single, map_one, h]

private theorem compatible_comp (f : R →+* S) {I J K : Type*}
    {A : (I →₀ R) →ₗ[R] J →₀ R} {B : (I →₀ S) →ₗ[S] J →₀ S}
    {C : (J →₀ R) →ₗ[R] K →₀ R} {D : (J →₀ S) →ₗ[S] K →₀ S}
    (h : compatible f A B) (k : compatible f C D) :
    compatible f (C.comp A) (D.comp B) := fun x =>
  (k (A x)).trans (congrArg D (h x))

private theorem compatible_pair (f : R →+* S) {K H J : Type u} [Group K] [Group H] [Group J]
    (X : Biset K H) (Y : Biset H J) (x : X.carrier →₀ R) (y : Y.carrier →₀ R) :
    castVector f (Biset.pairLinear R X Y x y) =
      Biset.pairLinear S X Y (castVector f x) (castVector f y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | single a r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' h h' => simp only [map_add, h, h']
    | single b s => rw [Biset.pairLinear_single, cast_single, cast_single, cast_single,
        Biset.pairLinear_single, map_mul]

private abbrev homCompatible (f : R →+* S) {K H : Type u} [Group K] [Group H]
    {X Y : Biset K H} (a : Biset.Hom R X Y) (b : Biset.Hom S X Y) :=
  compatible f a.toLinearMap b.toLinearMap

private theorem compatible_horizontal (f : R →+* S) {K H J : Type u}
    [Group K] [Group H] [Group J]
    {X X' : Biset K H} {Y Y' : Biset H J}
    {a : Biset.Hom R X X'} {b : Biset.Hom S X X'}
    {c : Biset.Hom R Y Y'} {d : Biset.Hom S Y Y'}
    (h : homCompatible f a b) (k : homCompatible f c d) :
    homCompatible f (a.horizontal c) (b.horizontal d) := by
  apply compatible_of_single
  intro z
  refine Quotient.inductionOn z fun ⟨x,y⟩ => ?_
  change castVector f ((a.horizontal c).toLinearMap (Finsupp.single (X.pair Y x y) 1)) =
    (b.horizontal d).toLinearMap (Finsupp.single (X.pair Y x y) 1)
  simp only [Biset.Hom.horizontal_single, one_smul]
  rw [compatible_pair, h, k, cast_single, cast_single, map_one]

private theorem compatible_push (f : R →+* S) {K H : Type u} [Group K] [Group H]
    {X Y : Biset K H} (k : X.carrier → Y.carrier)
    (hk : ∀ g x, k (X.act g x) = Y.act g (k x)) :
    homCompatible f (Biset.Hom.ofFunction k hk) (Biset.Hom.ofFunction k hk) := by
  apply compatible_of_single
  intro x
  simp only [Biset.Hom.ofFunction_single, cast_single, map_one]

private theorem compatible_pull (f : R →+* S) {K H : Type u} [Group K] [Group H]
    {X Y : Biset K H} (k : X.carrier → Y.carrier)
    (hk : ∀ g x, k (X.act g x) = Y.act g (k x))
    (fin : ∀ y, Set.Finite {x | k x = y}) :
    homCompatible f (Biset.Hom.transfer R k hk fin) (Biset.Hom.transfer S k hk fin) := by
  apply compatible_of_single
  intro y
  simp only [Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum,
    map_sum, cast_single, map_one]

private abbrev evalD {U : Type*} [Group U] {K H : Subgroup U} {p q : Word K H}
    (D : LabelledDrawing R p q) := D.interpret.eval

section Words

variable {U : Type*} [Group U] {K H J F G A C D E B : Subgroup U}

private theorem compatible_id (f : R →+* S) (p : Word K H) :
    homCompatible f (evalD (.ordinary (.id p))) (evalD (.ordinary (.id p))) := fun _ => rfl

private theorem compatible_assoc (f : R →+* S) (p : Word K H) (q : Word H J) (r : Word J F) :
    homCompatible f (evalD (.ordinary (.associate p q r)))
      (evalD (.ordinary (.associate p q r))) :=
  compatible_push f _ (by
    intro g w
    refine Quotient.inductionOn w (fun ⟨xy,z⟩ => ?_)
    exact Quotient.inductionOn xy (fun _ => rfl))

private theorem compatible_unassoc (f : R →+* S) (p : Word K H) (q : Word H J) (r : Word J F) :
    homCompatible f (evalD (.ordinary (.unassociate p q r)))
      (evalD (.ordinary (.unassociate p q r))) :=
  compatible_push f _ (by
    intro g w
    refine Quotient.inductionOn w (fun ⟨x,yz⟩ => ?_)
    exact Quotient.inductionOn yz (fun _ => rfl))

private theorem compatible_mult (f : R →+* S) (b : ConjEmbedding K G) (d : ConjEmbedding H G)
    (i : ConjEmbedding J K) (j : ConjEmbedding J H) (r : Dot (b.comp i) (d.comp j)) :
    homCompatible f ((Diagram.mixedMultiplication b d i j r).eval)
      ((Diagram.mixedMultiplication b d i j r).eval) :=
  compatible_push f _ (Generator.mixedMultiplication_equivariant b d i j r)

private theorem compatible_proj (f : R →+* S) (b : ConjEmbedding K G) (d : ConjEmbedding H G)
    (i : ConjEmbedding J K) (j : ConjEmbedding J H) (r : Dot (b.comp i) (d.comp j))
    (fin : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis b d i j r w = z}) :
    homCompatible f ((Diagram.mixedProjection b d i j r fin).eval)
      ((Diagram.mixedProjection b d i j r fin).eval) :=
  compatible_pull f _ (Generator.mixedMultiplication_equivariant b d i j r) fin

private theorem compatible_up (f : R →+* S) (a : ConjEmbedding A G) (i : ConjEmbedding B A)
    (c : ConjEmbedding C G) (k : ConjEmbedding B C) (t : Dot (a.comp i) (c.comp k)) :
    homCompatible f ((Diagram.parallelUp a i c k t).eval) ((Diagram.parallelUp a i c k t).eval) := by
  apply compatible_of_single
  intro z
  refine Quotient.inductionOn z fun ⟨x,y⟩ => ?_
  change castVector f ((Diagram.parallelUp a i c k t).eval.toLinearMap
    (Finsupp.single ((Biset.induction a).pair (Biset.induction i) x y) 1)) =
      (Diagram.parallelUp a i c k t).eval.toLinearMap
        (Finsupp.single ((Biset.induction a).pair (Biset.induction i) x y) 1)
  change G at x
  change A at y
  change castVector f ((Diagram.splitUp c k).eval.toLinearMap
    ((Diagram.upDot t).eval.toLinearMap ((Diagram.mergeUp a i).eval.toLinearMap _))) =
    (Diagram.splitUp c k).eval.toLinearMap
      ((Diagram.upDot t).eval.toLinearMap ((Diagram.mergeUp a i).eval.toLinearMap _))
  rw [Diagram.eval_mergeUp_single, Diagram.eval_mergeUp_single,
    Diagram.eval_upDot_single, Diagram.eval_upDot_single,
    Diagram.eval_splitUp_single, Diagram.eval_splitUp_single, cast_single, map_one]

private theorem singleton_label {p q : Word K H} (D : Diagram R p q) :
    (ScopedDiagram.linearCombination [(1, ScopedDiagram.ordinary D)]).eval = D.eval := by
  apply Biset.Hom.ext
  ext x
  simp [ScopedDiagram.eval_linearCombination_apply, ScopedDiagram.eval]

private theorem compatible_vertical (f : R →+* S) {p q r : Word K H}
    {a : LabelledDrawing R p q} {b : LabelledDrawing S p q}
    {c : LabelledDrawing R q r} {d : LabelledDrawing S q r}
    (h : homCompatible f (evalD a) (evalD b)) (k : homCompatible f (evalD c) (evalD d)) :
    homCompatible f (evalD (.vertical a c)) (evalD (.vertical b d)) :=
  compatible_comp f h k

private theorem compatible_side (f : R →+* S)
    {p p' : Word K H} {q q' : Word H J}
    {a : LabelledDrawing R p p'} {b : LabelledDrawing S p p'}
    {c : LabelledDrawing R q q'} {d : LabelledDrawing S q q'}
    (h : homCompatible f (evalD a) (evalD b)) (k : homCompatible f (evalD c) (evalD d)) :
    homCompatible f (evalD (.horizontal a c)) (evalD (.horizontal b d)) :=
  compatible_horizontal f h k

end Words
end
end RightSpanProof
namespace RightSpanProof
open MackeyDiagrams
open scoped BigOperators
noncomputable section
universe v
variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)

private abbrev word (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :=
  (Word.up a).tensor ((Word.down b).tensor (.up d))

private abbrev drawId (R : Type v) [CommSemiring R] {K H : Subgroup U} (p : Word K H) :=
  LabelledDrawing.ordinary (Diagram.id (R := R) p)

include a b d c e f in
private abbrev rightDrawing (R : Type v) [CommSemiring R] {B' : Subgroup U}
      (i : ConjEmbedding B' A) (j : ConjEmbedding B' F)
      (k : ConjEmbedding B' C)
      (r : List (R × ProjectionDot.Mixed b d i j))
      (t : List (R × Dot (a.comp i) (c.comp k)))
      (s : List (R × Dot (e.comp k) (f.comp j))) : LabelledDrawing R (word a b d) (word c e f) :=
    let ai := Word.up i
    let fj := Word.down j
    let ck := Word.up k
    let lower := LabelledDrawing.compactProjection b d i j r
    let middle := LabelledDrawing.parallelUp a i c k t
    let upper := LabelledDrawing.mixedMultiplication e f k j s
    LabelledDrawing.vertical
      (LabelledDrawing.horizontal (drawId R (Word.up a)) lower)
      (LabelledDrawing.vertical
        (LabelledDrawing.ordinary (Diagram.unassociate (Word.up a) ai fj))
        (LabelledDrawing.vertical
          (LabelledDrawing.horizontal middle (drawId R fj))
          (LabelledDrawing.vertical
            (LabelledDrawing.ordinary (Diagram.associate (Word.up c) ck fj))
            (LabelledDrawing.horizontal (drawId R (Word.up c)) upper))))

private abbrev leftUpperFiber {B : Subgroup U}
      (u : ConjEmbedding G B) (w : ConjEmbedding E B)
      (s : Dot (u.comp c) (w.comp e)) :=
    ∀ z, Set.Finite {p | Generator.mixedMultiplicationBasis u w c e s p = z}
private abbrev leftDrawing (R : Type v) [CommSemiring R] {B : Subgroup U}
      (u : ConjEmbedding G B) (v : ConjEmbedding D B)
      (w : ConjEmbedding E B)
      (r : Dot (u.comp a) (v.comp b))
      (t : Dot (v.comp d) (w.comp f))
      (s : Dot (u.comp c) (w.comp e)) (finite : leftUpperFiber c e u w s) : LabelledDrawing R (word a b d) (word c e f) :=
    let lower := LabelledDrawing.mixedMultiplication (R := R) u v a b [(1, r)]
    let middle := LabelledDrawing.parallelUp (R := R) v d w f [(1, t)]
    let upper := LabelledDrawing.compactProjection (R := R) u w c e [(1, ⟨s, finite⟩)]
    LabelledDrawing.vertical
      (LabelledDrawing.ordinary (Diagram.unassociate (Word.up a) (Word.down b) (Word.up d)))
      (LabelledDrawing.vertical
        (LabelledDrawing.horizontal lower (drawId R (Word.up d)))
        (LabelledDrawing.vertical
          (LabelledDrawing.ordinary (Diagram.associate (Word.down u) (Word.up v) (Word.up d)))
          (LabelledDrawing.vertical
            (LabelledDrawing.horizontal (drawId R (Word.down u)) middle)
            (LabelledDrawing.vertical
              (LabelledDrawing.ordinary (Diagram.unassociate (Word.down u) (Word.up w) (Word.up f)))
              (LabelledDrawing.vertical
                (LabelledDrawing.horizontal upper (drawId R (Word.up f)))
                (LabelledDrawing.ordinary (Diagram.associate (Word.up c) (Word.down e) (Word.up f))))))))

private theorem compatible_label {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {p q : Word A D} (T : Diagram R p q) (T' : Diagram S p q)
    (h : homCompatible φ T.eval T'.eval) :
    homCompatible φ (ScopedDiagram.linearCombination [(1, ScopedDiagram.ordinary T)]).eval
      (ScopedDiagram.linearCombination [(1, ScopedDiagram.ordinary T')]).eval := by
  simpa only [singleton_label] using h

private theorem right_cast {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (r : ProjectionDot.Mixed b d i j) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j)) :
    homCompatible φ (evalD (rightDrawing a b d c e f R i j k [(1,r)] [(1,t)] [(1,s)]))
      (evalD (rightDrawing a b d c e f S i j k [(1,r)] [(1,t)] [(1,s)])) := by
  unfold rightDrawing
  apply compatible_vertical
  · apply compatible_side
    · exact compatible_id φ _
    · exact compatible_label φ _ _ (compatible_proj φ b d i j r.dot r.finite)
  apply compatible_vertical (k := ?_)
  · exact compatible_unassoc φ _ _ _
  apply compatible_vertical
  · apply compatible_side
    · exact compatible_label φ _ _ (compatible_up φ a i c k t)
    · exact compatible_id φ _
  apply compatible_vertical (k := ?_)
  · exact compatible_assoc φ _ _ _
  apply compatible_side
  · exact compatible_id φ _
  · exact compatible_label φ _ _ (compatible_mult φ e f k j s)

private theorem left_cast {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (u : ConjEmbedding G B) (v : ConjEmbedding D B)
    (w : ConjEmbedding E B) (r : Dot (u.comp a) (v.comp b))
    (t : Dot (v.comp d) (w.comp f)) (s : Dot (u.comp c) (w.comp e))
    (fin : leftUpperFiber c e u w s) :
    homCompatible φ (evalD (leftDrawing a b d c e f R u v w r t s fin))
      (evalD (leftDrawing a b d c e f S u v w r t s fin)) := by
  unfold leftDrawing
  apply compatible_vertical (k := ?_)
  · exact compatible_unassoc φ _ _ _
  apply compatible_vertical
  · apply compatible_side
    · exact compatible_label φ _ _ (compatible_mult φ u v a b r)
    · exact compatible_id φ _
  apply compatible_vertical (k := ?_)
  · exact compatible_assoc φ _ _ _
  apply compatible_vertical
  · apply compatible_side
    · exact compatible_id φ _
    · exact compatible_label φ _ _ (compatible_up φ v d w f t)
  apply compatible_vertical (k := ?_)
  · exact compatible_unassoc φ _ _ _
  apply compatible_vertical
  · apply compatible_side
    · exact compatible_label φ _ _ (compatible_proj φ u w c e s fin)
    · exact compatible_id φ _
  exact compatible_assoc φ _ _ _

private theorem compatible_entry {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {p q : Word G F} {T : LabelledDrawing R p q}
    {T' : LabelledDrawing S p q} (h : homCompatible φ (evalD T) (evalD T'))
    (z : p.basis.carrier × q.basis.carrier) :
    φ ((evalD T).toLinearMap (Finsupp.single z.1 1) z.2) =
      (evalD T').toLinearMap (Finsupp.single z.1 1) z.2 := by
  have hvec := h (Finsupp.single z.1 1)
  rw [cast_single, map_one] at hvec
  have h' := DFunLike.congr_fun hvec z.2
  change φ (((evalD T).toLinearMap (Finsupp.single z.1 1)) z.2) = _ at h'
  exact h'

end
end RightSpanProof
namespace RightSpanProof
open MackeyDiagrams
open scoped BigOperators
noncomputable section
universe u
variable {K H : Type u} [Group K] [Group H]
variable {X Y : Biset K H}

private abbrev pairAction (X Y : Biset K H) : MulAction (K × H) (X.carrier × Y.carrier) where
  smul g z := (X.act g z.1, Y.act g z.2)
  one_smul z := Prod.ext (X.one_act z.1) (Y.one_act z.2)
  mul_smul g k z := Prod.ext (X.mul_act g k z.1) (Y.mul_act g k z.2)

private local instance : MulAction (K × H) (X.carrier × Y.carrier) := pairAction X Y

private abbrev OrbitIndex (X Y : Biset K H) :=
  ↥(Set.range (MulAction.orbit (K × H) : X.carrier × Y.carrier → _))

private def orbitOf (z : X.carrier × Y.carrier) : OrbitIndex X Y :=
  ⟨MulAction.orbit (K × H) z, ⟨z, rfl⟩⟩

private def orbitRep (O : OrbitIndex X Y) : X.carrier × Y.carrier :=
  Classical.choose O.property

private theorem orbitOf_rep (O : OrbitIndex X Y) : orbitOf (orbitRep O) = O :=
  Subtype.ext (Classical.choose_spec O.property)

private theorem orbitOf_eq (O : OrbitIndex X Y) (z : X.carrier × Y.carrier) :
    orbitOf z = O ↔ z ∈ O.val := by
  rw [← orbitOf_rep O]
  exact ⟨fun h => MulAction.orbit_eq_iff.mp (congrArg Subtype.val h),
    fun h => Subtype.ext (MulAction.orbit_eq_iff.mpr h)⟩

private abbrev matrixEntry {R : Type*} [CommRing R]
    (M : (X.carrier →₀ R) →ₗ[R] Y.carrier →₀ R) (z : X.carrier × Y.carrier) : R :=
  M (Finsupp.single z.1 1) z.2

private def equivariant (R : Type*) [CommRing R] (X Y : Biset K H) :
    Submodule R ((X.carrier →₀ R) →ₗ[R] Y.carrier →₀ R) where
  carrier := {m | ∀ g x, m (X.actLinear R g x) = Y.actLinear R g (m x)}
  zero_mem' := by simp
  add_mem' := by
    intro m n hm hn g x
    change (m + n) (X.actLinear R g x) = Y.actLinear R g ((m + n) x)
    simp only [LinearMap.add_apply, map_add, hm g x, hn g x]
  smul_mem' := by
    intro r m hm g x
    change (r • m) (X.actLinear R g x) = Y.actLinear R g ((r • m) x)
    simp only [LinearMap.smul_apply, map_smul, hm g x]

private theorem actLinear_apply_act {R : Type*} [CommRing R] (g : K × H)
    (w : Y.carrier →₀ R) (y : Y.carrier) :
    Y.actLinear R g w (Y.act g y) = w y := by
  apply Finsupp.mapDomain_apply_of_injective
  intro a b h
  simpa only [← Y.mul_act, inv_mul_cancel, Y.one_act] using congrArg (Y.act g⁻¹) h

private theorem matrix_invariant {R : Type*} [CommRing R] (M : equivariant R X Y)
    (z : X.carrier × Y.carrier) (g : K × H) :
    matrixEntry M.val (g • z) = matrixEntry M.val z := by
  change M.val (Finsupp.single (X.act g z.1) 1) (Y.act g z.2) = _
  rw [← Biset.actLinear_single, M.property g, actLinear_apply_act]

private def coordinates (R : Type*) [CommRing R] [Finite Y.carrier] :
    equivariant R X Y ≃ₗ[R] OrbitIndex X Y → R := by
  let coord : equivariant R X Y →ₗ[R] OrbitIndex X Y → R :=
    { toFun := fun M O => matrixEntry M.val (orbitRep O)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearEquiv.ofBijective coord
  have hM (M : equivariant R X Y) (z : X.carrier × Y.carrier) :
      matrixEntry M.val z = coord M (orbitOf z) := by
    have h := (orbitOf_eq (orbitOf z) z).mp rfl
    rw [← orbitOf_rep (orbitOf z)] at h
    obtain ⟨g, hg⟩ := h
    exact (congrArg (matrixEntry M.val) hg).symm.trans (matrix_invariant M _ g)
  constructor
  · intro M N h
    apply Subtype.ext
    apply Finsupp.lhom_ext
    intro x r
    rw [← Finsupp.smul_single_one x r, map_smul, map_smul]
    congr 1
    ext y
    exact (hM M (x,y)).trans ((congrFun h (orbitOf (x,y))).trans (hM N (x,y)).symm)
  · intro v
    let col (x : X.carrier) : Y.carrier →₀ R :=
      Finsupp.equivFunOnFinite.symm (fun y => v (orbitOf (x,y)))
    have hcol (x : X.carrier) (y : Y.carrier) : col x y = v (orbitOf (x,y)) :=
      Finsupp.equivFunOnFinite_symm_apply_apply _ _
    let M := Biset.Hom.ofBasis col (by
      intro g x
      ext y
      have sur : Function.Surjective (Y.act g) :=
        fun z => ⟨Y.act g⁻¹ z, by rw [← Y.mul_act, mul_inv_cancel, Y.one_act]⟩
      obtain ⟨w, rfl⟩ := sur y
      rw [actLinear_apply_act, hcol, hcol]
      apply congrArg v
      exact Subtype.ext (MulAction.orbit_eq_iff.mpr ⟨g,rfl⟩))
    refine ⟨⟨M.toLinearMap,M.commutes⟩, ?_⟩
    funext O
    change M.toLinearMap (Finsupp.single (orbitRep O).1 1) (orbitRep O).2 = v O
    rw [Biset.Hom.ofBasis_single, one_smul, hcol, orbitOf_rep]

private theorem coordinates_apply {R : Type*} [CommRing R] [Finite Y.carrier]
    (M : equivariant R X Y) (O : OrbitIndex X Y) :
    coordinates R M O = matrixEntry M.val (orbitRep O) := rfl

private theorem coordinates_entry {R : Type*} [CommRing R] [Finite Y.carrier]
    (M : equivariant R X Y) (z : X.carrier × Y.carrier) :
    matrixEntry M.val z = coordinates R M (orbitOf z) := by
  have h := (orbitOf_eq (orbitOf z) z).mp rfl
  rw [← orbitOf_rep (orbitOf z)] at h
  obtain ⟨g, hg⟩ := h
  exact (congrArg (matrixEntry M.val) hg).symm.trans (matrix_invariant M _ g)

private theorem span_coordinates {R : Type*} [CommRing R] {I M : Type*}
    [Finite I] [AddCommMonoid M] [Module R M] (b : Module.Basis I R M) (n : I → R)
    (s : Set M) (h : ∀ x ∈ s, ∀ i, b.repr x i ∈ Ideal.span ({n i} : Set R))
    (gen : ∀ i, n i • b i ∈ Submodule.span R s) (x : M) :
    x ∈ Submodule.span R s ↔ ∀ i, b.repr x i ∈ Ideal.span ({n i} : Set R) := by
  classical
  letI := Fintype.ofFinite I
  constructor
  · refine Submodule.span_induction h (fun i => by simp) ?_ ?_
    · intro x y _ _ hx hy i
      simpa only [map_add, Finsupp.add_apply] using (Ideal.span ({n i} : Set R)).add_mem (hx i) (hy i)
    · intro r x _ hx i
      simpa only [map_smul, Finsupp.smul_apply] using (Ideal.span ({n i} : Set R)).smul_mem r (hx i)
  · intro hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (hx i)
    rw [hr, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ r (gen i)

private theorem integer_quotient {I M : Type*} [Fintype I] [AddCommGroup M] [Module (ULift Int) M]
    (e : M ≃ₗ[ULift Int] I → ULift Int) (n : I → Nat) (s : Set M)
    (hs : ∀ x, x ∈ Submodule.span (ULift Int) s ↔
      ∀ i, e x i ∈ Ideal.span ({(n i : ULift Int)} : Set (ULift Int))) :
    Nonempty ((M ⧸ AddSubgroup.closure s) ≃+ DirectSum I (fun i => ZMod (n i))) := by
  let modCoord (i : I) : M →+ ZMod (n i) :=
    { toFun := fun x => ((e x i).down : ZMod (n i))
      map_zero' := by simp
      map_add' := fun x y => by simp [map_add, ULift.add_down] }
  let p := AddMonoidHom.pi modCoord
  have hsur : Function.Surjective p := by
    intro z
    choose a ha using fun i => (ZMod.intCast_surjective (n := n i)) (z i)
    refine ⟨e.symm (fun i => ULift.up (a i)), ?_⟩
    funext i
    change (((e (e.symm fun i => ULift.up (a i))) i).down : ZMod (n i)) = z i
    rw [e.apply_symm_apply]
    exact ha i
  have hc : AddSubgroup.closure s = (Submodule.span (ULift Int) s).toAddSubgroup := by
    apply le_antisymm
    · exact (AddSubgroup.closure_le _).mpr (Submodule.subset_span (R := ULift Int))
    · intro x hx
      change x ∈ Submodule.span (ULift Int) s at hx
      refine Submodule.span_induction (fun x h => AddSubgroup.subset_closure h)
        (AddSubgroup.zero_mem _) (fun x y _ _ => AddSubgroup.add_mem _) ?_ hx
      intro r x _ h
      have hr : (r.down : ULift Int) = r := rfl
      rw [← hr, Int.cast_smul_eq_zsmul]
      exact AddSubgroup.zsmul_mem _ h _
  have hk : AddSubgroup.closure s = p.ker := by
    ext x
    rw [hc]
    change x ∈ Submodule.span (ULift Int) s ↔ p x = 0
    rw [hs, funext_iff]
    apply forall_congr'
    intro i
    rw [Ideal.mem_span_singleton]
    change (n i : ULift Int) ∣ e x i ↔ ((e x i).down : ZMod (n i)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r.down, congrArg ULift.down hr⟩
    · rintro ⟨r, hr⟩
      exact ⟨ULift.up r, ULift.down_injective hr⟩
  rw [hk]
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective p hsur).trans
    (DirectSum.addEquivProd (fun i => ZMod (n i))).symm⟩
end
end RightSpanProof
namespace RightSpanProof
open MackeyDiagrams
noncomputable section
private abbrev Sinf := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
private abbrev ParabolicPerm (H : Subgroup (Equiv.Perm Nat)) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    H = ⨆ l, blockSym (blocks l)
private abbrev IsParabolic (H : Subgroup Sinf) := ParabolicPerm (H.map Sinf.subtype)
private abbrev swaps (P : Subgroup Sinf) :=
  Subgroup.closure {σ : Sinf | σ ∈ P ∧ Equiv.Perm.IsSwap (σ : Equiv.Perm Nat)}

private theorem parabolic_finite {H : Subgroup Sinf} (hH : IsParabolic H) : Finite H := by
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

private theorem parabolic_extremal (P : Subgroup Sinf) [Finite P] :
    IsGreatest {K : Subgroup Sinf | IsParabolic K ∧ K ≤ P} (swaps P) := by
  classical
  let Q := P.map Sinf.subtype
  letI : Finite Q := Finite.of_surjective (fun p : P => (⟨p.val.val, ⟨p.val, p.property, rfl⟩⟩ : Q))
    (by rintro ⟨_, i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩)
  have hQ : Q ≤ Sinf := fun _ ⟨p, _, hp⟩ => hp ▸ p.property
  have unionWitness (H : Subgroup (Equiv.Perm Nat)) :
      ParabolicPerm H ↔ ∃ X : Finset Nat, ∃ (n : Nat) (blocks : Fin n → Finset Nat),
        (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
        (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ H = ⨆ l, blockSym (blocks l) := by
    constructor
    · rintro ⟨n, blocks, hn, hd, he⟩
      exact ⟨Finset.univ.biUnion blocks, n, blocks, hn, hd, by simp, he⟩
    · rintro ⟨_, n, blocks, hn, hd, _, he⟩
      exact ⟨n, blocks, hn, hd, he⟩
  have hmap : (swaps P).map Sinf.subtype =
      Subgroup.closure {σ | σ ∈ Q ∧ Equiv.Perm.IsSwap σ} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext σ
    constructor
    · rintro ⟨p, ⟨hp, hs⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hs⟩
    · rintro ⟨⟨p, hp, rfl⟩, hs⟩
      exact ⟨p, ⟨hp, hs⟩, rfl⟩
  have h := (ExtremalParabolicsOfFiniteGroup Q hQ).1
  rw [← hmap] at h
  refine ⟨⟨(unionWitness _).mpr h.1.1, ?_⟩, ?_⟩
  · exact (Subgroup.map_le_map_iff_of_injective Sinf.subtype_injective).mp h.1.2
  · intro K hK
    exact (Subgroup.map_le_map_iff_of_injective Sinf.subtype_injective).mp
      (h.2 ⟨(unionWitness _).mp hK.1, Subgroup.map_mono hK.2⟩)

private theorem conjugate_parabolic {B F : Subgroup Sinf} (j : ConjEmbedding B F)
    (hB : IsParabolic B) : IsParabolic ((F.subtype.comp j.toHom).range) := by
  classical
  obtain ⟨q, hq⟩ := j.hasRepresentative
  let conj := (MulAut.conj (q : Equiv.Perm Nat)).toMonoidHom
  have hmap : ((F.subtype.comp j.toHom).range).map Sinf.subtype =
      (B.map Sinf.subtype).map conj := by
    ext σ
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨p.val.val, ⟨p.val, p.property, rfl⟩, (congrArg Subtype.val (hq p)).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨j.toHom ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, congrArg Subtype.val (hq ⟨p, hp⟩)⟩
  have hcarrier : ∃ X : Finset Nat, ∃ (n : Nat) (blocks : Fin n → Finset Nat),
      (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
      (∀ m : Nat, m ∈ X ↔ ∃ i, m ∈ blocks i) ∧ B.map Sinf.subtype = ⨆ l, blockSym (blocks l) := by
    obtain ⟨n, blocks, hn, hd, he⟩ := hB
    exact ⟨Finset.univ.biUnion blocks, n, blocks, hn, hd, by simp, he⟩
  obtain ⟨_, n, blocks, hn, hd, _, he⟩ := FiniteParabolicClosure.1 (B.map Sinf.subtype) hcarrier q
  exact ⟨n, blocks, hn, hd, hmap.trans he⟩

variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
private abbrev point (g : G) (x : D) : (word a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b |>.tensor (.up d)).basis) g (Generator.mixedPair b d x)
private theorem point_surjective (z : (word a b d).basis.carrier) :
    ∃ g x, point a b d g x = z := by
  obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective y
  exact ⟨g, x, rfl⟩

private theorem finite_word_of_groups {W : Type*} [Group W] {G A D F : Subgroup W}
    [Finite G] [Finite D]
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :
    Finite (word a b d).basis.carrier :=
  Finite.of_surjective (fun p : G × D => point a b d p.1 p.2) (by
    intro x
    obtain ⟨g, x', h⟩ := point_surjective a b d x
    exact ⟨(g, x'), h⟩)


private theorem act_left (g h : G) (x : D) :
    (word a b d).basis.act (g, (1 : F)) (point a b d h x) = point a b d (g * h) x := by
  change (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    (g * h * (a.toHom 1)⁻¹)
    (((Word.down b).tensor (.up d)).basis.act (1, 1) (Generator.mixedPair b d x)) = _
  simp only [map_one, inv_one, mul_one, ← Prod.one_eq_mk, Biset.one_act]

private theorem normalize_left (z : (word a b d).basis.carrier × (word c e f).basis.carrier) :
    letI := pairAction (word a b d).basis (word c e f).basis
    ∃ (g : G) (r : D) (t : G) (s : E),
      (g, (1 : F)) • z = (point a b d 1 r, point c e f t s) := by
  letI := pairAction (word a b d).basis (word c e f).basis
  obtain ⟨x, y⟩ := z
  obtain ⟨h, r, rfl⟩ := point_surjective a b d x
  obtain ⟨k, s, rfl⟩ := point_surjective c e f y
  refine ⟨h⁻¹, r, h⁻¹ * k, s, Prod.ext ?_ ?_⟩
  · change (word a b d).basis.act (h⁻¹, (1 : F)) (point a b d h r) = _
    rw [act_left, inv_mul_cancel]
  · exact act_left c e f h⁻¹ k s

private theorem projected_left (z : (word a b d).basis.carrier × (word c e f).basis.carrier) (g : G) :
    letI := pairAction (word a b d).basis (word c e f).basis
    let π := F.subtype.comp (MonoidHom.snd G F)
    (MulAction.stabilizer (G × F) ((g, (1 : F)) • z)).map π =
      (MulAction.stabilizer (G × F) z).map π := by
  letI := pairAction (word a b d).basis (word c e f).basis
  dsimp only
  let π := F.subtype.comp (MonoidHom.snd G F)
  change (MulAction.stabilizer (G × F) ((g, (1 : F)) • z)).map π = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map]
  congr 1
  ext q
  change (((1 : F) * q.2 * (1 : F)⁻¹ : F) : U) = (q.2 : U)
  simp

end
end RightSpanProof
namespace RightSpanProof
open MackeyDiagrams
open scoped BigOperators
noncomputable section
universe u
variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {R : Type*} [CommRing R]
variable {X X' Z : Biset K H} {Y Y' : Biset H J}

private abbrev asMap (f : Biset.Hom R X X') : equivariant R X X' :=
  ⟨f.toLinearMap, f.commutes⟩

private abbrev asHom (f : equivariant R X X') : Biset.Hom R X X' :=
  ⟨f.val, f.property⟩

private def after (g : Biset.Hom R X' Z) : equivariant R X X' →ₗ[R] equivariant R X Z where
  toFun f := asMap ((asHom f).vertical g)
  map_add' x y := by
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    exact map_add g.toLinearMap _ _
  map_smul' r x := by
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    exact map_smul g.toLinearMap r _

private def before (f : Biset.Hom R X X') : equivariant R X' Z →ₗ[R] equivariant R X Z where
  toFun g := asMap (f.vertical (asHom g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tensorLeft (f : Biset.Hom R X X') :
    equivariant R Y Y' →ₗ[R] equivariant R (X.tensor Y) (X'.tensor Y') where
  toFun g := asMap (f.horizontal (asHom g))
  map_add' g k := by
    apply Subtype.ext
    apply Finsupp.lhom_ext
    intro z r
    refine Quotient.inductionOn z fun ⟨x,y⟩ => ?_
    change (f.horizontal ((asHom g).add (asHom k))).toLinearMap
      (Finsupp.single (X.pair Y x y) r) =
      (f.horizontal (asHom g)).toLinearMap (Finsupp.single (X.pair Y x y) r) +
      (f.horizontal (asHom k)).toLinearMap (Finsupp.single (X.pair Y x y) r)
    simp only [Biset.Hom.horizontal_single, Biset.Hom.add, LinearMap.add_apply, map_add, smul_add]
  map_smul' r g := by
    apply Subtype.ext
    exact congrArg Biset.Hom.toLinearMap (Biset.Hom.horizontal_scale_right r f (asHom g))

private def tensorRight (g : Biset.Hom R Y Y') :
    equivariant R X X' →ₗ[R] equivariant R (X.tensor Y) (X'.tensor Y') where
  toFun f := asMap ((asHom f).horizontal g)
  map_add' f k := by
    apply Subtype.ext
    apply Finsupp.lhom_ext
    intro z r
    refine Quotient.inductionOn z fun ⟨x,y⟩ => ?_
    change (((asHom f).add (asHom k)).horizontal g).toLinearMap
      (Finsupp.single (X.pair Y x y) r) =
      ((asHom f).horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r) +
      ((asHom k).horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r)
    simp only [Biset.Hom.horizontal_single, Biset.Hom.add, LinearMap.add_apply, map_add, smul_add]
  map_smul' r f := by
    apply Subtype.ext
    exact congrArg Biset.Hom.toLinearMap (Biset.Hom.horizontal_scale_left r (asHom f) g)

private theorem weighted_mem {U : Type*} [Group U] {K H : Subgroup U}
    {p q : Word K H} {L M : Type*} [AddCommMonoid M] [Module R M]
    (D : L → Diagram R p q) (ls : List (R × L))
    (φ : equivariant R p.basis q.basis →ₗ[R] M) (V : Submodule R M)
    (h : ∀ d : L, φ (asMap (D d).eval) ∈ V) :
    φ (asMap (ScopedDiagram.linearCombination
      (ls.map fun (r,d) => (r, ScopedDiagram.ordinary (D d)))).eval) ∈ V := by
  induction ls with
  | nil =>
    change φ 0 ∈ V
    rw [map_zero]
    exact V.zero_mem
  | cons x xs ih =>
    change φ (x.1 • asMap (D x.2).eval + asMap
      (ScopedDiagram.linearCombination (xs.map fun (r,d) => (r, ScopedDiagram.ordinary (D d)))).eval) ∈ V
    rw [map_add, map_smul]
    exact V.add_mem (V.smul_mem _ (h _)) ih

private theorem right_weighted_mem {U : Type*} [Group U] {G A D F C E B : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
    (i : ConjEmbedding B A) (j : ConjEmbedding B F) (k : ConjEmbedding B C)
    (V : Submodule R (equivariant R (word a b d).basis (word c e f).basis))
    (h : ∀ r t s, asMap (evalD (rightDrawing a b d c e f R i j k [(1,r)] [(1,t)] [(1,s)])) ∈ V)
    (r : List (R × ProjectionDot.Mixed b d i j))
    (t : List (R × Dot (a.comp i) (c.comp k))) (s : List (R × Dot (e.comp k) (f.comp j))) :
    asMap (evalD (rightDrawing a b d c e f R i j k r t s)) ∈ V := by
  let lower (r : List (R × ProjectionDot.Mixed b d i j)) :=
    evalD (LabelledDrawing.compactProjection b d i j r)
  let middle (t : List (R × Dot (a.comp i) (c.comp k))) :=
    evalD (LabelledDrawing.parallelUp a i c k t)
  let upper (s : List (R × Dot (e.comp k) (f.comp j))) :=
    evalD (LabelledDrawing.mixedMultiplication e f k j s)
  let I₁ := Biset.Hom.id (R := R) (Word.up a).basis
  let I₂ := Biset.Hom.id (R := R) (Word.down j).basis
  let I₃ := Biset.Hom.id (R := R) (Word.up c).basis
  let α := (Diagram.unassociate (R := R) (.up a) (.up i) (.down j)).eval
  let β := (Diagram.associate (R := R) (.up c) (.up k) (.down j)).eval
  let front (r : Biset.Hom R ((Word.down b).tensor (.up d)).basis
      ((Word.up i).tensor (.down j)).basis) := I₁.horizontal r
  let mid (t : Biset.Hom R ((Word.up a).tensor (.up i)).basis
      ((Word.up c).tensor (.up k)).basis) := t.horizontal I₂
  let back (s : Biset.Hom R ((Word.up k).tensor (.down j)).basis
      ((Word.down e).tensor (.up f)).basis) := I₃.horizontal s
  let path (r : Biset.Hom R _ _) (t : Biset.Hom R _ _) (s : Biset.Hom R _ _) :=
    asMap ((front r).vertical (α.vertical ((mid t).vertical (β.vertical (back s)))))
  change path (lower r) (middle t) (upper s) ∈ V
  let slot₁ := (after (α.vertical ((mid (middle t)).vertical (β.vertical (back (upper s)))))).comp
    (tensorLeft (Y := ((Word.down b).tensor (.up d)).basis) I₁)
  apply weighted_mem (fun x : ProjectionDot.Mixed b d i j => .mixedProjection b d i j x.dot x.finite)
    r slot₁ V
  intro r₀
  let R₀ := (Diagram.mixedProjection (R := R) b d i j r₀.dot r₀.finite).eval
  change path R₀ (middle t) (upper s) ∈ V
  let slot₂ := (before (front R₀)).comp ((before α).comp
    ((after (β.vertical (back (upper s)))).comp (tensorRight (X' := ((Word.up c).tensor (.up k)).basis) I₂)))
  apply weighted_mem (Diagram.parallelUp a i c k) t slot₂ V
  intro t₀
  let T₀ := (Diagram.parallelUp (R := R) a i c k t₀).eval
  change path R₀ T₀ (upper s) ∈ V
  let slot₃ := (before (front R₀)).comp ((before α).comp
    ((before (mid T₀)).comp ((before β).comp (tensorLeft (Y' := ((Word.down e).tensor (.up f)).basis) I₃))))
  apply weighted_mem (Diagram.mixedMultiplication e f k j) s slot₃ V
  intro s₀
  change path R₀ T₀ (Diagram.mixedMultiplication (R := R) e f k j s₀).eval ∈ V
  have hr : lower [(1,r₀)] = R₀ := singleton_label _
  have ht : middle [(1,t₀)] = T₀ := singleton_label _
  have hs : upper [(1,s₀)] = (Diagram.mixedMultiplication (R := R) e f k j s₀).eval :=
    singleton_label _
  have used := h r₀ t₀ s₀
  change path (lower [(1,r₀)]) (middle [(1,t₀)]) (upper [(1,s₀)]) ∈ V at used
  rwa [hr, ht, hs] at used

end
end RightSpanProof

open MackeyDiagrams RightSpanProof
open scoped BigOperators

theorem ParabolicRightDiagramSpanOverCommutativeRings : (
let Sinf : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ | Equiv.Perm.IsSwap σ}
let U := ↥Sinf
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun X => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
let parabolic : Subgroup U → Prop :=
  fun H => ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, Finset.Nonempty (blocks l)) ∧
    Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    Subgroup.map (Subgroup.subtype Sinf) H = iSup (fun l => blockSym (blocks l))
∀ (G A D F C E : Subgroup U),
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  ∀ (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
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
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis ga)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis gc)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  let pair := fun (r : D) (t : G) (s : E) => (input 1 r, output t s)
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
  let swaps := fun P : Subgroup U =>
    Subgroup.closure {σ : U | σ ∈ P ∧ Equiv.Perm.IsSwap (σ : Equiv.Perm Nat)}
  let RightData := fun B' : Subgroup U =>
    Σ (i : MackeyDiagrams.ConjEmbedding B' A)
      (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C),
      MackeyDiagrams.Dot (comp b i) (comp d j) ×
      MackeyDiagrams.Dot (comp a i) (comp c k) ×
      MackeyDiagrams.Dot (comp e k) (comp f j)
  let labels : {B' : Subgroup U} → RightData B' → D × G × E :=
    fun ⟨_, _, _, r, t, s⟩ =>
      (MackeyDiagrams.Dot.element r, MackeyDiagrams.Dot.element t, MackeyDiagrams.Dot.element s)
  let representative := fun {B'} (data : RightData B') =>
    let (r, t, s) := labels data
    pair r t s
  let Fiber : {B' : Subgroup U} → RightData B' → Type :=
    fun ⟨i, j, _, _, _, _⟩ => (MackeyDiagrams.Word.basis (tensor (up i) (down j))).carrier
  let lowerMap : {B' : Subgroup U} → (data : RightData B') → Fiber data →
      (MackeyDiagrams.Word.basis (tensor ad df)).carrier :=
    fun ⟨i, j, _, r, _, _⟩ => MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r
  let finiteFibers := fun {B'} (data : RightData B') =>
    ∀ z, Set.Finite {w : Fiber data | lowerMap data w = z}
  let RightTerm := {term : Σ B' : Subgroup U, RightData B' //
    parabolic term.1 ∧ finiteFibers term.2}
  let rightRepresentative := fun term : RightTerm => representative term.val.2
  let rightOrbit := fun term : RightTerm => orbit (rightRepresentative term)
  let image : {B' : Subgroup U} → RightData B' → Subgroup U :=
    fun ⟨_, j, _, _, _, _⟩ =>
      MonoidHom.range (MonoidHom.comp (Subgroup.subtype F)
        (MackeyDiagrams.ConjEmbedding.toHom j))
  let rightImage := fun term : RightTerm => image term.val.2
  let isInclusion := fun {B'} (data : RightData B') =>
    ∀ h : B', ((MackeyDiagrams.ConjEmbedding.toHom data.2.1) h : U) = (h : U)
  let drawId := fun (R : Type*) [CommRing R] {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := R) p)
  let rightDrawing := fun (R : Type _) [CommRing R] {B' : Subgroup U}
      (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C)
      (r : List (R × MackeyDiagrams.ProjectionDot.Mixed b d i j))
      (t : List (R × MackeyDiagrams.Dot (comp a i) (comp c k)))
      (s : List (R × MackeyDiagrams.Dot (comp e k) (comp f j))) =>
    let ai := up i
    let fj := down j
    let ck := up k
    let lower := MackeyDiagrams.LabelledDrawing.compactProjection b d i j r
    let middle := MackeyDiagrams.LabelledDrawing.parallelUp a i c k t
    let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j s
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId R ga) lower)
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal middle (drawId R fj))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId R gc) upper))))
  let rightDiagramOf (R : Type _) [CommRing R] : {B' : Subgroup U} →
      (data : RightData B') → finiteFibers data → MackeyDiagrams.LabelledDrawing R bottom top :=
    fun ⟨i, j, k, r, t, s⟩ finite =>
      rightDrawing R i j k [(1, ⟨r, finite⟩)] [(1, t)] [(1, s)]
  let rightDiagram := fun (R : Type _) [CommRing R] (term : RightTerm) =>
    rightDiagramOf R term.val.2 term.property.2
  let RightLabels := fun (R : Type _) =>
    Σ (B' : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding B' A)
      (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C),
      List (R × MackeyDiagrams.ProjectionDot.Mixed b d i j) ×
      List (R × MackeyDiagrams.Dot (comp a i) (comp c k)) ×
      List (R × MackeyDiagrams.Dot (comp e k) (comp f j))
  let fullRightDiagram (R : Type _) [CommRing R] :
      {data : RightLabels R // parabolic data.1} → MackeyDiagrams.LabelledDrawing R bottom top :=
    fun ⟨⟨_, i, j, k, r, t, s⟩, _⟩ => rightDrawing R i j k r t s
  let LeftUpperFiber := fun {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (w : MackeyDiagrams.ConjEmbedding E B)
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) =>
    ∀ z, Set.Finite {p | MackeyDiagrams.Generator.mixedMultiplicationBasis u w c e s p = z}
  let leftDiagram := fun (R : Type _) [CommRing R] {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (r : MackeyDiagrams.Dot (comp u a) (comp v b))
      (t : MackeyDiagrams.Dot (comp v d) (comp w f))
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) (finite : LeftUpperFiber u w s) =>
    let lower := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := R) u v a b [(1, r)]
    let middle := MackeyDiagrams.LabelledDrawing.parallelUp (R := R) v d w f [(1, t)]
    let upper := MackeyDiagrams.LabelledDrawing.compactProjection (R := R) u w c e [(1, ⟨s, finite⟩)]
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal lower (drawId R df))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate (down u) (up v) df))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId R (down u)) middle)
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate (down u) (up w) ef))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.horizontal upper (drawId R ef))
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ce ef)))))))
  let Orbits := ↥(Set.range orbit)
  let rep : Orbits → Pair := fun O => Classical.choose O.property
  let P : Orbits → Subgroup U := fun O => projected (rep O)
  let L : Orbits → Subgroup U := fun O => swaps (P O)
  let index : Orbits → Nat := fun O => Subgroup.relIndex (L O) (P O)
  let coefficient := fun (R : Type _) [CommRing R]
      (M : (Finsupp X.carrier R) →ₗ[R] (Finsupp Y.carrier R)) (z : Pair) =>
    M (Finsupp.single z.1 (1 : R)) z.2
  let entry := fun (R : Type _) [CommRing R] (O : Set Pair) (r : R) (z : Pair) =>
    @ite R (z ∈ O) (Classical.propDecidable (z ∈ O)) r 0
  let evaluate := fun (R : Type _) [CommRing R]
      (T : MackeyDiagrams.LabelledDrawing R bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap
      (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret T))
  let bimoduleMaps := fun (R : Type _) [CommRing R] =>
    ({ carrier := {m | ∀ (g : G × F) (x : Finsupp X.carrier R),
          m (MackeyDiagrams.Biset.actLinear R X g x) =
            MackeyDiagrams.Biset.actLinear R Y g (m x)}
       zero_mem' := by simp
       add_mem' := by
         intro m n hm hn g x
         change (m + n) (MackeyDiagrams.Biset.actLinear R X g x) =
           MackeyDiagrams.Biset.actLinear R Y g ((m + n) x)
         simp only [LinearMap.add_apply, map_add, hm g x, hn g x]
       smul_mem' := by
         intro r m hm g x
         change (r • m) (MackeyDiagrams.Biset.actLinear R X g x) =
           MackeyDiagrams.Biset.actLinear R Y g ((r • m) x)
         simp only [LinearMap.smul_apply, map_smul, hm g x] } :
      Submodule R ((Finsupp X.carrier R) →ₗ[R] (Finsupp Y.carrier R)))
  let rightHom := fun (R : Type _) [CommRing R]
      (data : {data : RightLabels R // parabolic data.1}) =>
    MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (fullRightDiagram R data))
  let rightSpan := fun (R : Type _) [CommRing R] =>
    Submodule.span R (Set.range fun data : {data : RightLabels R // parabolic data.1} =>
      let M := rightHom R data
      (⟨MackeyDiagrams.Biset.Hom.toLinearMap M, MackeyDiagrams.Biset.Hom.commutes M⟩ :
        ↥(bimoduleMaps R)))
  let integerMaps :=
    ({ carrier := ↑(bimoduleMaps (ULift Int))
       zero_mem' := Submodule.zero_mem (bimoduleMaps (ULift Int))
       add_mem' := fun hm hn => Submodule.add_mem (bimoduleMaps (ULift Int)) hm hn
       neg_mem' := by
         intro m hm g x
         change (-m) (MackeyDiagrams.Biset.actLinear (ULift Int) X g x) =
           MackeyDiagrams.Biset.actLinear (ULift Int) Y g ((-m) x)
         simp only [LinearMap.neg_apply, map_neg, hm g x] } :
      AddSubgroup ((Finsupp X.carrier (ULift Int)) →ₗ[ULift Int]
        (Finsupp Y.carrier (ULift Int))))
  let integerRightSpan : AddSubgroup ↥integerMaps :=
    AddSubgroup.closure (Set.range fun data : {data : RightLabels (ULift Int) // parabolic data.1} =>
      let M := rightHom (ULift Int) data
      (⟨MackeyDiagrams.Biset.Hom.toLinearMap M, MackeyDiagrams.Biset.Hom.commutes M⟩ : ↥integerMaps))
  (∀ O : Orbits,
    P O ≤ F ∧
    IsGreatest {K : Subgroup U | K ≤ P O ∧ parabolic K} (L O) ∧
    (∀ z ∈ O.val, Subgroup.relIndex (swaps (projected z)) (projected z) = index O) ∧
    IsLeast {n : Nat | ∃ T : RightTerm, rightOrbit T = O.val ∧
      ∀ z : Pair, coefficient (ULift Int) (evaluate (ULift Int) (rightDiagram (ULift Int) T)) z =
        entry (ULift Int) O.val (n : ULift Int) z} (index O) ∧
    (index O = 1 ↔ parabolic (P O))) ∧
  (∀ (R : Type _) [CommRing R],
    (∀ T : RightTerm,
      let P' := projected (rightRepresentative T)
      rightImage T ≤ P' ∧
      Subgroup.relIndex (swaps P') P' ∣ Subgroup.relIndex (rightImage T) P' ∧
      ∀ z : Pair, coefficient R (evaluate R (rightDiagram R T)) z =
        entry R (rightOrbit T) (Subgroup.relIndex (rightImage T) P' : R) z) ∧
    (∀ O : Orbits,
      ∃ (data : RightData (L O)) (finite : finiteFibers data),
        orbit (representative data) = O.val ∧
        projected (representative data) = P O ∧ isInclusion data ∧
        ∀ z : Pair, coefficient R (evaluate R (rightDiagramOf R data finite)) z =
          entry R O.val (index O : R) z) ∧
    ∃ T : Module.Basis Orbits R ↥(bimoduleMaps R),
      (∀ (O : Orbits) (z : Pair),
        coefficient R (T O).val z = entry R O.val 1 z) ∧
      (∀ M : ↥(bimoduleMaps R), M ∈ rightSpan R ↔
        ∀ O : Orbits, Module.Basis.repr T M O ∈ Ideal.span ({(index O : R)} : Set R))) ∧
  Nonempty ((↥integerMaps ⧸ integerRightSpan) ≃+
    DirectSum Orbits (fun O => ZMod (index O))) ∧
  (∀ (B : Subgroup U), parabolic B →
    ∀ (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (r : MackeyDiagrams.Dot (comp u a) (comp v b))
      (t : MackeyDiagrams.Dot (comp v d) (comp w f))
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) (finite : LeftUpperFiber u w s),
    let left := fun (R : Type _) [CommRing R] => leftDiagram R u v w r t s finite
    let S : Set Orbits :=
      {O | ∃ z ∈ O.val, coefficient (ULift Int) (evaluate (ULift Int) (left (ULift Int))) z ≠ 0}
    ∃ summand : ∀ O : ↥S, {data : RightData (P O.val) // finiteFibers data},
      (∀ O : ↥S,
        let data := (summand O).val
        parabolic (P O.val) ∧ orbit (representative data) = O.val.val ∧
        projected (representative data) = P O.val ∧ isInclusion data) ∧
      ∀ (R : Type _) [CommRing R],
        ∃ expansion : MackeyDiagrams.IndexedDrawing R bottom top ↥S,
          (∀ O : ↥S, O ∈ MackeyDiagrams.IndexedDrawing.indices expansion) ∧
          (∀ O : ↥S,
            MackeyDiagrams.IndexedDrawing.summand expansion O =
              rightDiagramOf R (summand O).val (summand O).property ∧
            ∀ z : Pair,
              coefficient R (evaluate R (MackeyDiagrams.IndexedDrawing.summand expansion O)) z =
                entry R O.val.val 1 z) ∧
          evaluate R (left R) = MackeyDiagrams.IndexedDrawing.eval expansion)

) :=
(by
  classical
  intro Sinf U blockSym parabolic G A D F C E hG hA hD hF hC hE a b d c e f
    up down tensor comp ga ad df gc ce ef bottom top X Y Pair input output pair
    orbit stabilizer projected swaps RightData labels representative Fiber lowerMap finiteFibers
    RightTerm rightRepresentative rightOrbit image rightImage isInclusion drawId rightDrawing
    rightDiagramOf rightDiagram RightLabels fullRightDiagram LeftUpperFiber leftDiagram
    Orbits rep P L index coefficient entry evaluate bimoduleMaps rightHom rightSpan
    integerMaps integerRightSpan
  letI : MulAction (G × F) Pair := pairAction X Y
  letI : Finite G := parabolic_finite hG
  letI : Finite D := parabolic_finite hD
  letI : Finite E := parabolic_finite hE
  letI : Finite F := parabolic_finite hF
  letI : Finite X.carrier := finite_word_of_groups a b d
  letI : Finite Y.carrier := finite_word_of_groups c e f
  haveI : Finite Orbits := Finite.of_surjective
    (fun z : Pair => (⟨orbit z, ⟨z, rfl⟩⟩ : Orbits)) (fun O => ⟨rep O, Subtype.ext
      (Classical.choose_spec O.property)⟩)
  letI : Fintype Orbits := Fintype.ofFinite _
  -- Xiao, § 8.3, Other coefficient rings, archived PDF p. 40 and published
  -- 28 November revision p. 42. https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The portal proof is in paragraphs. Steps 1–6 below follow the numbering
  -- in the checked proof of Proposition 8.7 used by the coordinator.
  -- Steps 1–4. Keep the actual projected subgroup of the chosen representative.
  -- Left normalization uses only (g, 1), so it preserves that subgroup.
  have geometry := ParabolicRightOrbitMultiplicity G A D F C E hG hA hD hF hC hE a b d c e f
  have project_le (z : Pair) : projected z ≤ F := by
    rintro p ⟨q, _, rfl⟩
    exact q.2.property
  have extremal (z : Pair) : IsGreatest {K : Subgroup U | K ≤ projected z ∧ parabolic K}
      (swaps (projected z)) := by
    letI : Finite (projected z) :=
      Finite.of_injective (Subgroup.inclusion (project_le z)) (Subgroup.inclusion_injective _)
    have h := parabolic_extremal (projected z)
    exact ⟨⟨h.1.2,h.1.1⟩, fun K hK => h.2 ⟨hK.2,hK.1⟩⟩
  have norm (O : Orbits) : ∃ r t s, orbit (pair r t s) = O.val ∧ projected (pair r t s) = P O := by
    obtain ⟨g, r, t, s, hg⟩ := normalize_left a b d c e f (rep O)
    have hOrbit : orbit (rep O) = O.val := Classical.choose_spec O.property
    have hz : pair r t s ∈ orbit (rep O) := ⟨(g,1), hg⟩
    have hp := projected_left a b d c e f (rep O) g
    change projected ((g,(1 : F)) • rep O) = P O at hp
    rw [hg] at hp
    exact ⟨r,t,s,(MulAction.orbit_eq_iff.mpr hz).trans hOrbit,hp⟩
  have transport (O : Orbits) (z : Pair) (hz : z ∈ O.val) :
      (swaps (projected z)).relIndex (projected z) = index O := by
    have h : orbit (rep O) = O.val := Classical.choose_spec O.property
    have hz' : z ∈ orbit (rep O) := by rwa [h]
    exact (geometry.2.2.2.2.1 (rep O)).2.2 z hz'
  have indexOne (O : Orbits) : index O = 1 ↔ parabolic (P O) :=
    (geometry.2.2.2.2.1 (rep O)).2.1
  -- The registered singleton coefficient identity is over ℂ. Scalar
  -- compatibility computes the same natural-number matrix before either
  -- cast. Injectivity is used only for the cast into ℂ.
  have singleton {B' : Subgroup U} (hB' : parabolic B') (data : RightData B') :
      image data ≤ projected (representative data) ∧
      ∃ fin : finiteFibers data, ∀ (R : Type _) [CommRing R] (z : Pair),
        coefficient R (evaluate R (rightDiagramOf R data fin)) z =
          entry R (orbit (representative data))
            ((image data).relIndex (projected (representative data)) : R) z := by
    obtain ⟨hle, ⟨_, fin, hc⟩, _⟩ := geometry.2.2.2.1 B' hB' data
    refine ⟨hle, fin, ?_⟩
    rcases data with ⟨i,j,k,r,t,s⟩
    intro R _ z
    let data : RightData B' := ⟨i,j,k,r,t,s⟩
    let O := orbit (representative data)
    let n := (image data).relIndex (projected (representative data))
    let val := (evalD (RightSpanProof.rightDrawing a b d c e f Nat i j k
      [(1,⟨r,fin⟩)] [(1,t)] [(1,s)])).toLinearMap (Finsupp.single z.1 1) z.2
    have transferC := compatible_entry (Nat.castRingHom Complex)
      (right_cast a b d c e f (Nat.castRingHom Complex) i j k ⟨r,fin⟩ t s) z
    have transferR := compatible_entry (Nat.castRingHom R)
      (right_cast a b d c e f (Nat.castRingHom R) i j k ⟨r,fin⟩ t s) z
    change (val : R) = coefficient R (evaluate R (rightDiagramOf R data fin)) z at transferR
    change (val : Complex) = _ at transferC
    let cm := @ite Complex (z ∈ O) (Classical.propDecidable _) (n : Complex) 0
    have hc' : (val : Complex) = cm :=
      transferC.trans (hc z)
    change coefficient R (evaluate R (rightDiagramOf R data fin)) z = entry R O (n : R) z
    rw [← transferR]
    by_cases hz : z ∈ O
    · rw [show cm = (n : Complex) from ite_eq_left hz] at hc'
      rw [show entry R O (n : R) z = (n : R) from ite_eq_left hz, Nat.cast_injective hc']
    · rw [show cm = 0 from ite_eq_right hz] at hc'
      have hv : val = 0 := Nat.cast_injective (hc'.trans Nat.cast_zero.symm)
      rw [show entry R O (n : R) z = 0 from ite_eq_right hz, hv, Nat.cast_zero]
  -- Step 5. The image of a parabolic internal group is parabolic by
  -- conjugation closure. Multiplicativity in the tower gives divisibility.
  have allRight (R : Type _) [CommRing R] (T : RightTerm) :
      let P' := projected (rightRepresentative T)
      rightImage T ≤ P' ∧
      (swaps P').relIndex P' ∣ (rightImage T).relIndex P' ∧
      ∀ z, coefficient R (evaluate R (rightDiagram R T)) z =
        entry R (rightOrbit T) ((rightImage T).relIndex P' : R) z := by
    intro P'
    obtain ⟨leP, fin, hcoef⟩ := singleton T.property.1 T.val.2
    have pK : parabolic (rightImage T) := by
      rcases T with ⟨⟨B',i,j,k,r,t,s⟩,hB',fin⟩
      exact conjugate_parabolic j hB'
    have hL := extremal (rightRepresentative T)
    have tower := Subgroup.relIndex_mul_relIndex (rightImage T) (swaps P') P'
      (hL.2 ⟨leP,pK⟩) hL.1.1
    exact ⟨leP, ⟨(rightImage T).relIndex (swaps P'), by rw [mul_comm]; exact tower.symm⟩,
      hcoef R⟩
  have generate (O : Orbits) :
      ∃ (data : RightData (L O)) (fin : finiteFibers data),
        orbit (representative data) = O.val ∧ projected (representative data) = P O ∧
        isInclusion data ∧ ∀ (R : Type _) [CommRing R] z,
          coefficient R (evaluate R (rightDiagramOf R data fin)) z =
            entry R O.val (index O : R) z := by
    obtain ⟨r,t,s,hO,hP⟩ := norm O
    obtain ⟨_, full, hlab, _, _, _, hL, term, hp, hrest, hInc, _, _⟩ := geometry.2.2.1 r t s
    have hl : labels term = (r,t,s) := hrest.1.trans hlab
    have hr : representative term = pair r t s := by
      change pair (labels term).1 (labels term).2.1 (labels term).2.2 = pair r t s
      rw [hl]
    have hS : swaps (projected (pair r t s)) = L O := congrArg swaps hP
    obtain ⟨data, hd, hin⟩ :
        ∃ data : RightData (L O), labels data = (r,t,s) ∧ isInclusion data :=
      hS ▸ ⟨term, hl, hInc⟩
    have hrep : representative data = pair r t s := by
      change pair (labels data).1 (labels data).2.1 (labels data).2.2 = pair r t s
      rw [hd]
    have hi : image data = L O := by
      rcases data with ⟨i,j,k,rd,td,sd⟩
      ext p
      constructor
      · rintro ⟨z, rfl⟩
        change (j.toHom z : U) ∈ L O
        rw [hin z]
        exact z.property
      · intro hz
        exact ⟨⟨p,hz⟩, hin ⟨p,hz⟩⟩
    obtain ⟨_, fin, hf⟩ := singleton (extremal (rep O)).1.2 data
    refine ⟨data,fin, hrep ▸ hO, hrep ▸ hP, hin, ?_⟩
    intro R _ z
    have hc := hf R z
    rw [hrep, hO, hP, hi] at hc
    exact hc
  have minimum (O : Orbits) :
      IsLeast {n : Nat | ∃ T : RightTerm, rightOrbit T = O.val ∧
        ∀ z : Pair, coefficient (ULift Int) (evaluate (ULift Int) (rightDiagram (ULift Int) T)) z =
          entry (ULift Int) O.val (n : ULift Int) z} (index O) := by
    constructor
    · obtain ⟨data,fin,hO,_,_,hc⟩ := generate O
      exact ⟨⟨⟨L O,data⟩,(extremal (rep O)).1.2,fin⟩,hO,hc (ULift Int)⟩
    · rintro n ⟨T,hO,hn⟩
      let z := rightRepresentative T
      have self : z ∈ rightOrbit T := MulAction.mem_orbit_self z
      have hz : z ∈ O.val := hO ▸ self
      obtain ⟨_, div, hc⟩ := allRight (ULift Int) T
      have he := (hn z).symm.trans (hc z)
      rw [show entry (ULift Int) O.val (n : ULift Int) z = (n : ULift Int) from ite_eq_left hz,
        show entry (ULift Int) (rightOrbit T) ((rightImage T).relIndex (projected z) : ULift Int) z =
          ((rightImage T).relIndex (projected z) : ULift Int) from ite_eq_left self] at he
      have hdown : (n : Int) = ((rightImage T).relIndex (projected z) : Int) :=
        congrArg ULift.down he
      have eq := Nat.cast_injective hdown
      rw [transport O z hz, ← eq] at div
      haveI : Finite (projected z) :=
        Finite.of_injective (Subgroup.inclusion (project_le z)) (Subgroup.inclusion_injective _)
      have hn' : n ≠ 0 := by
        rw [eq, Subgroup.relIndex, Subgroup.index_eq_card]
        exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn') div
  let coord (R : Type _) [CommRing R] : ↥(bimoduleMaps R) ≃ₗ[R] Orbits → R :=
    coordinates R (X := X) (Y := Y)
  let basis (R : Type _) [CommRing R] := Module.Basis.ofEquivFun (coord R)
  have unitEntry (R : Type _) [CommRing R] (O : Orbits) (z : Pair) :
      coefficient R (basis R O).val z = entry R O.val 1 z := by
    change matrixEntry (basis R O).val z = _
    rw [coordinates_entry (X := X) (Y := Y) (basis R O) z]
    change (coord R) (basis R O) (orbitOf z) = _
    have hbase : basis R O = (coord R).symm (Pi.single O 1) :=
      congrFun (Module.Basis.coe_ofEquivFun (coord R)) O
    rw [hbase, LinearEquiv.apply_symm_apply, Pi.single_apply]
    by_cases h : orbitOf z = O
    · rw [ite_eq_left h]
      exact (ite_eq_left ((orbitOf_eq O z).mp h)).symm
    · rw [ite_eq_right h]
      exact (ite_eq_right (fun hz => h ((orbitOf_eq O z).mpr hz))).symm
  have span (R : Type _) [CommRing R] (M : ↥(bimoduleMaps R)) :
      M ∈ rightSpan R ↔ ∀ O, (basis R).repr M O ∈ Ideal.span ({(index O : R)} : Set R) := by
    apply span_coordinates (basis R) (fun O => (index O : R))
    · let Good : Submodule R ↥(bimoduleMaps R) :=
        { carrier := {M | ∀ O, coord R M O ∈ Ideal.span ({(index O : R)} : Set R)}
          zero_mem' := fun O => by simp
          add_mem' := fun hm hn O => by rw [map_add, Pi.add_apply]; exact Ideal.add_mem _ (hm O) (hn O)
          smul_mem' := fun r m hm O => by rw [map_smul, Pi.smul_apply]; exact (Ideal.span ({(index O : R)} : Set R)).smul_mem r (hm O) }
      rintro _ ⟨⟨⟨B',i,j,k,r,t,s⟩,hp⟩,rfl⟩ O
      rw [Module.Basis.ofEquivFun_repr_apply]
      have hg : asMap (evalD (RightSpanProof.rightDrawing a b d c e f R i j k r t s)) ∈ Good := by
        apply right_weighted_mem a b d c e f i j k Good
        intro r₀ t₀ s₀ Q
        let T : RightTerm := ⟨⟨B',i,j,k,r₀.dot,t₀,s₀⟩,hp,r₀.finite⟩
        obtain ⟨_, hd, hc⟩ := allRight R T
        change coefficient R (evaluate R (rightDiagram R T)) (rep Q) ∈ _
        rw [hc]
        by_cases hz : rep Q ∈ rightOrbit T
        · rw [show entry R (rightOrbit T) ((rightImage T).relIndex
              (projected (rightRepresentative T)) : R) (rep Q) = _ from ite_eq_left hz,
            Ideal.mem_span_singleton]
          have hOrb : orbit (rep Q) = Q.val := Classical.choose_spec Q.property
          have eQ : Q.val = rightOrbit T := hOrb.symm.trans (MulAction.orbit_eq_iff.mpr hz)
          have hz' : rightRepresentative T ∈ Q.val := eQ.symm ▸ MulAction.mem_orbit_self _
          rw [← transport Q _ hz']
          obtain ⟨m, hm⟩ := hd
          exact ⟨(m : R), by simpa only [Nat.cast_mul] using congrArg (Nat.cast : Nat → R) hm⟩
        · rw [show entry R (rightOrbit T) ((rightImage T).relIndex
              (projected (rightRepresentative T)) : R) (rep Q) = 0 from ite_eq_right hz]
          exact Ideal.zero_mem _
      exact hg O
    · intro O
      obtain ⟨data,fin,_,_,_,hcoef⟩ := generate O
      rcases data with ⟨i,j,k,r,t,s⟩
      let lab : {data : RightLabels R // parabolic data.1} :=
        ⟨⟨L O,i,j,k,[(1,⟨r,fin⟩)],[(1,t)],[(1,s)]⟩,(extremal (rep O)).1.2⟩
      let M : ↥(bimoduleMaps R) := asMap (rightHom R lab)
      have hm : M ∈ rightSpan R := Submodule.subset_span ⟨lab,rfl⟩
      have he : M = (index O : R) • basis R O := by
        apply Subtype.ext
        apply Finsupp.lhom_ext
        intro x r'
        rw [← Finsupp.smul_single_one x r', map_smul, map_smul]
        congr 1
        ext y
        change coefficient R (evaluate R (rightDiagramOf R ⟨i,j,k,r,t,s⟩ fin)) (x,y) =
          (index O : R) * coefficient R (basis R O).val (x,y)
        rw [hcoef R, unitEntry]
        by_cases hz : (x,y) ∈ O.val
        · rw [show entry R O.val (index O : R) (x,y) = _ from ite_eq_left hz,
            show entry R O.val 1 (x,y) = _ from ite_eq_left hz, mul_one]
        · rw [show entry R O.val (index O : R) (x,y) = 0 from ite_eq_right hz,
            show entry R O.val 1 (x,y) = 0 from ite_eq_right hz, mul_zero]
      exact he ▸ hm
  refine ⟨fun O => ⟨project_le _, extremal _, transport O, minimum O, indexOne O⟩, ?_, ?_, ?_⟩
  · intro R _
    exact ⟨allRight R, fun O => by
      obtain ⟨d,fin,ho,hp,hi,h⟩ := generate O
      exact ⟨d,fin,ho,hp,hi,h R⟩, basis R, unitEntry R, span R⟩
  ·
    -- The integral coordinate reduction is surjective. Its kernel is the
    -- additive closure because all ULift Int scalars act by integer multiples.
    apply integer_quotient (coord (ULift Int)) index
    intro M
    exact (span (ULift Int) M).trans (forall_congr' fun O => by
      rw [show (basis (ULift Int)).repr M O = coord (ULift Int) M O from
        Module.Basis.ofEquivFun_repr_apply _ _ _])
  ·
    -- Step 6. Transfer the checked coefficient-one expansion from ℂ via the
    -- common natural coefficients. Its support agrees with the integral
    -- support used in the endpoint.
    intro B hB u v w r t s fin left S
    obtain ⟨expC, _, complexTerms, _⟩ :=
      (ParabolicCaseFiveCoefficientOneExpansion G A D F C E hG hA hD hF hC hE a b d c e f).1
        B hB u v w r t s fin
    let M := (evalD (leftDrawing a b d c e f Complex u v w r t s fin)).toLinearMap
    let SC : Set (Set Pair) := {O | ∃ z : Pair, O = orbit z ∧ matrixEntry (X := X) (Y := Y) M z ≠ 0}
    have leftCoeff (R : Type _) [CommRing R] (z : Pair) (n : Nat)
        (hn : matrixEntry (X := X) (Y := Y) M z = (n : Complex)) :
        coefficient R (evaluate R (left R)) z = (n : R) := by
      let val := (evalD (leftDrawing a b d c e f Nat u v w r t s fin)).toLinearMap
        (Finsupp.single z.1 1) z.2
      have hC := compatible_entry (Nat.castRingHom Complex)
        (left_cast a b d c e f (Nat.castRingHom Complex) u v w r t s fin) z
      have hR := compatible_entry (Nat.castRingHom R)
        (left_cast a b d c e f (Nat.castRingHom R) u v w r t s fin) z
      change (val : Complex) = matrixEntry (X := X) (Y := Y) M z at hC
      change (val : R) = coefficient R (evaluate R (left R)) z at hR
      rw [← hR, Nat.cast_injective (hC.trans hn)]
    have supportedC (z : Pair) :
        coefficient (ULift Int) (evaluate (ULift Int) (left (ULift Int))) z ≠ 0 ↔
          matrixEntry (X := X) (Y := Y) M z ≠ 0 := by
      let val := (evalD (leftDrawing a b d c e f Nat u v w r t s fin)).toLinearMap
        (Finsupp.single z.1 1) z.2
      have hC := compatible_entry (Nat.castRingHom Complex)
        (left_cast a b d c e f (Nat.castRingHom Complex) u v w r t s fin) z
      have hI := compatible_entry (Nat.castRingHom (ULift Int))
        (left_cast a b d c e f (Nat.castRingHom (ULift Int)) u v w r t s fin) z
      change (val : Complex) = matrixEntry (X := X) (Y := Y) M z at hC
      change (val : ULift Int) = coefficient (ULift Int) (evaluate (ULift Int) (left (ULift Int))) z at hI
      rw [← hC, ← hI]
      have hZ : (val : ULift Int) = 0 ↔ val = 0 :=
        ⟨fun h => Nat.cast_injective (show (val : Int) = (0 : Nat) from congrArg ULift.down h),
          fun h => by rw [h, Nat.cast_zero]⟩
      have hComplex : (val : Complex) = 0 ↔ val = 0 := Nat.cast_eq_zero
      exact not_congr (hZ.trans hComplex.symm)
    have term (O : ↥S) : ∃ data : {data : RightData (P O.val) // finiteFibers data},
        parabolic (P O.val) ∧ orbit (representative data.val) = O.val.val ∧
        projected (representative data.val) = P O.val ∧ isInclusion data.val := by
      obtain ⟨z,hz,hn⟩ := O.property
      have hOrb : orbit z = O.val.val := congrArg Subtype.val ((orbitOf_eq O.val z).mpr hz)
      let Q : ↥SC := ⟨O.val.val, z, hOrb.symm, (supportedC z).mp hn⟩
      obtain ⟨r₀,t₀,s₀,hQ,hP,_,_,_,_,_,_⟩ := complexTerms Q
      have hz₀ : pair r₀ t₀ s₀ ∈ O.val.val :=
        hQ.symm ▸ MulAction.mem_orbit_self _
      have hone : index O.val = 1 :=
        (transport O.val _ hz₀).symm.trans ((geometry.2.2.2.2.1 (pair r₀ t₀ s₀)).2.1.mpr hP)
      have hPar := (indexOne O.val).mp hone
      obtain ⟨rd,td,sd,hO,hP'⟩ := norm O.val
      obtain ⟨_,data,hl,hi,_,_,_⟩ := geometry.2.2.1 rd td sd
      obtain ⟨data,hl,hi⟩ : ∃ data : RightData (P O.val),
          labels data = (rd,td,sd) ∧ isInclusion data := hP' ▸ ⟨data,hl,hi⟩
      have hr : representative data = pair rd td sd := by
        change pair (labels data).1 (labels data).2.1 (labels data).2.2 = pair rd td sd
        rw [hl]
      obtain ⟨_,fd,_⟩ := singleton hPar data
      exact ⟨⟨data,fd⟩,hPar,hr ▸ hO,hr ▸ hP',hi⟩
    choose data hd using term
    refine ⟨data,hd,?_⟩
    intro R _
    letI : Fintype ↥S := Fintype.ofFinite _
    let exp : IndexedDrawing R bottom top ↥S := ⟨Finset.univ, fun O =>
      rightDiagramOf R (data O).val (data O).property⟩
    have he (O : ↥S) (z : Pair) :
        coefficient R (evaluate R (exp.summand O)) z = entry R O.val.val 1 z := by
      obtain ⟨hp,ho,hp',hi⟩ := hd O
      obtain ⟨_,_,hc⟩ := singleton hp (data O).val
      have hi' : image (data O).val = P O.val := by
        rcases h : (data O).val with ⟨i,j,k,rd,td,sd⟩
        rw [h] at hi
        ext p
        constructor
        · rintro ⟨x,rfl⟩
          change (j.toHom x : U) ∈ P O.val
          rw [hi x]
          exact x.property
        · intro hz
          exact ⟨⟨p,hz⟩,hi ⟨p,hz⟩⟩
      have h := hc R z
      rw [ho,hp',hi',Subgroup.relIndex_self,Nat.cast_one] at h
      exact h
    refine ⟨exp,fun O => Finset.mem_univ O,fun O => ⟨rfl,he O⟩,?_⟩
    apply Finsupp.lhom_ext
    intro x q
    rw [← Finsupp.smul_single_one x q, map_smul, map_smul]
    congr 1
    ext y
    let z : Pair := (x,y)
    change coefficient R (evaluate R (left R)) z = (exp.eval (Finsupp.single x 1)) y
    rw [IndexedDrawing.eval_apply, Finset.sum_apply']
    change coefficient R (evaluate R (left R)) z =
      ∑ O : ↥S, coefficient R (evaluate R (exp.summand O)) z
    simp_rw [he]
    have orbitNonzero (O : ↥S) (hz : z ∈ O.val.val) : matrixEntry (X := X) (Y := Y) M z ≠ 0 := by
      obtain ⟨z',hz',hn⟩ := O.property
      have hor : orbit z' = O.val.val := congrArg Subtype.val ((orbitOf_eq O.val z').mpr hz')
      rw [← hor] at hz
      have hinv := geometry.1 (evalD (leftDrawing a b d c e f Complex u v w r t s fin)) z' z hz
      change matrixEntry (X := X) (Y := Y) M z = matrixEntry (X := X) (Y := Y) M z' at hinv
      rw [hinv]
      exact (supportedC z').mp hn
    by_cases h : matrixEntry (X := X) (Y := Y) M z = 0
    · rw [leftCoeff R z 0 (h.trans Nat.cast_zero.symm), Nat.cast_zero, Finset.sum_eq_zero]
      intro O _
      exact ite_eq_right (fun hz => orbitNonzero O hz h)
    · let O : ↥S := ⟨orbitOf z, z, MulAction.mem_orbit_self _, (supportedC z).mpr h⟩
      have hz : z ∈ O.val.val := MulAction.mem_orbit_self _
      rw [Finset.sum_eq_single O]
      · rw [show entry R O.val.val 1 z = 1 from ite_eq_left hz]
        have hOne : matrixEntry (X := X) (Y := Y) M z = 1 := by
          obtain ⟨_, _, _, _, _, _, _, _, supported, _⟩ :=
            SupportedLeftOrbitProjectedStabilizer hG hA hD hF hC hE hB a b d c e f u v w r t s
          exact (supported z h).2.2.2.2
        exact (leftCoeff R z 1 (hOne.trans Nat.cast_one.symm)).trans Nat.cast_one
      · intro O' _ hne
        exact ite_eq_right (fun hmem => hne (Subtype.ext ((orbitOf_eq O'.val z).mpr hmem).symm))
      · simp)

#print axioms ParabolicRightDiagramSpanOverCommutativeRings
