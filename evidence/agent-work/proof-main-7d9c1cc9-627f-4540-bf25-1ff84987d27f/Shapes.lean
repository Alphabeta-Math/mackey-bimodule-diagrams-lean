import MackeyDiagrams
import Proofs.ParabolicCaseFiveCoefficientOneExpansion
import Proofs.ParabolicRightOrbitMultiplicity
import Proofs.ExtremalParabolicsOfFiniteGroup
import Proofs.FiniteParabolicClosure

open MackeyDiagrams
open scoped BigOperators
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
  have h' := DFunLike.congr_fun (h (Finsupp.single z.1 1)) z.2
  simpa only [cast_single, RingHom.map_one, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply]
    using h'

end
end RightSpanProof
