import Perm
import Proofs.EvaluationWithOneProjection

set_option maxHeartbeats 2000000

namespace CaseSixTrivialAux
open MackeyDiagrams
noncomputable section

abbrev up := @Word.up U _
abbrev down := @Word.down U _
abbrev tensor := @Word.tensor U _
abbrev vertical := @LabelledDrawing.vertical U _ Complex _
abbrev horizontal := @LabelledDrawing.horizontal U _ Complex _
abbrev ordinary := @LabelledDrawing.ordinary U _ Complex _
abbrev straight {K L : Subgroup U} (p : Word K L) := ordinary (Diagram.id p)

abbrev atLeft {K J J' L M : Subgroup U}
    {p : Word K J} {q : Word J L} {p' : Word K J'} {q' : Word J' L}
    (tail : Word L M) (crossing : LabelledDrawing Complex (tensor p q) (tensor p' q')) :=
  vertical (ordinary (Diagram.unassociate p q tail))
    (vertical (horizontal crossing (straight tail)) (ordinary (Diagram.associate p' q' tail)))

abbrev ev {K L : Subgroup U} {p q : Word K L} (drawing : LabelledDrawing Complex p q) :=
  drawing.interpret.eval.toLinearMap

abbrev ad := tensor (down b) (up d)
abbrev word := tensor (up a) ad
abbrev coordinate (g : A) (x : D) := (up a).basis.pair ad.basis g (Generator.mixedPair b d x)
abbrev vector (x : D) := Finsupp.single (coordinate 1 x) (1 : Complex)

theorem coordinate_move (g : A) (x : D) :
    coordinate g x = coordinate 1 (b.toHom g * x) := by
  have eq := (up a).basis.pair_balance ad.basis g 1 (Generator.mixedPair b d x)
  have h₁ : (up a).basis.act (1, g⁻¹) 1 = g := by
    change (1 : A) * 1 * (a.toHom g⁻¹)⁻¹ = g
    change (1 : A) * 1 * (g⁻¹)⁻¹ = g
    simp only [one_mul, inv_inv]
  have h₂ : ad.basis.act (g, 1) (Generator.mixedPair b d x) =
      Generator.mixedPair b d (b.toHom g * x) := by
    change (down b).basis.pair (up d).basis (b.toHom g * x * (1 : D)⁻¹)
      (1 * 1 * (d.toHom 1)⁻¹) = _
    simp only [map_one, inv_one, mul_one]
    rfl
  rw [h₁, h₂] at eq
  exact eq

-- Step 1 of Example 8.6: the regular A factor and the balanced D pair
-- reduce to multiplication. Build the equivalence on the whole quotient.
def coordinates : word.basis.carrier ≃ D where
  toFun p := Generator.mixedProduct b d (Biset.leftUnitBasis ad.basis p)
  invFun := coordinate 1
  left_inv p := by
    refine Quotient.inductionOn p (fun ⟨g, z⟩ => ?_)
    obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective z
    change coordinate 1 (Generator.mixedProduct b d
      (ad.basis.act (g, 1) (Generator.mixedPair b d x))) = coordinate g x
    change coordinate 1 (Generator.mixedProduct b d
      ((down b).basis.pair (up d).basis (b.toHom g * x * (1 : D)⁻¹)
        (1 * 1 * (d.toHom 1)⁻¹))) = coordinate g x
    simp only [map_one, inv_one, mul_one]
    change coordinate 1 (Generator.mixedProduct b d (Generator.mixedPair b d (b.toHom g * x))) =
      coordinate g x
    rw [Generator.mixedProduct_mixedPair]
    exact (coordinate_move g x).symm
  right_inv x := by
    change Generator.mixedProduct b d (ad.basis.act (1, 1) (Generator.mixedPair b d x)) = x
    rw [show ((1, 1) : A × F) = 1 from rfl, Biset.one_act, Generator.mixedProduct_mixedPair]

theorem coordinates_pair (g : A) (x : D) : coordinates (coordinate g x) = b.toHom g * x := by
  rw [coordinate_move]
  exact coordinates.apply_symm_apply _

abbrev RDot {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B) :=
  Dot (u.comp a) (v.comp b)
abbrev TDot {B : Subgroup U} (v w : ConjEmbedding D B) := Dot (v.comp d) (w.comp d)
abbrev SDot {B : Subgroup U} (u : ConjEmbedding A B) (w : ConjEmbedding D B) :=
  ProjectionDot.Mixed u w a b

abbrev left {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (rs : List (Complex × RDot u v)) (ts : List (Complex × TDot v w))
    (ss : List (Complex × SDot u w)) :=
  vertical (atLeft (up d) (.mixedMultiplication u v a b rs))
    (vertical (horizontal (straight (down u)) (.parallelUp v d w d ts))
      (atLeft (up d) (.compactProjection u w a b ss)))

-- A fixed spectator is a linear map in the active tensor factor.
def frame {K J J' L M : Subgroup U} {p : Word K J} {q : Word J L}
    {p' : Word K J'} {q' : Word J' L} (tail : Word L M)
    (f : ((tensor p q).basis.carrier →₀ Complex) →ₗ[Complex]
      ((tensor p' q').basis.carrier →₀ Complex)) (z : tail.basis.carrier) :
    ((tensor p q).basis.carrier →₀ Complex) →ₗ[Complex]
      ((tensor p' (tensor q' tail)).basis.carrier →₀ Complex) :=
  (Diagram.associate (R := Complex) p' q' tail).eval.toLinearMap.comp
    (((Biset.pairLinear Complex (tensor p' q').basis tail.basis).flip (Finsupp.single z 1)).comp f)

theorem atLeft_pair {K J J' L M : Subgroup U} {p : Word K J} {q : Word J L}
    {p' : Word K J'} {q' : Word J' L} (tail : Word L M)
    (f : LabelledDrawing Complex (tensor p q) (tensor p' q'))
    (x : p.basis.carrier) (y : q.basis.carrier) (z : tail.basis.carrier) :
    ev (atLeft tail f) (Finsupp.single (p.basis.pair (tensor q tail).basis x (q.basis.pair tail.basis y z)) 1)
      = frame tail (ev f) z (Finsupp.single (p.basis.pair q.basis x y) 1) := by
  change (Diagram.associate p' q' tail).eval.toLinearMap
    ((f.interpret.eval.horizontal (Diagram.id tail).eval).toLinearMap
      ((Diagram.unassociate p q tail).eval.toLinearMap _)) = _
  rw [Diagram.eval_unassociate_single, Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply]
  rfl

abbrev mid {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B) (z : B) :=
  (down u).basis.pair (tensor (up v) (up d)).basis z ((up v).basis.pair (up d).basis 1 1)

-- Lemma 6.6, equation (6.3), steps 1–3. The registered left formula
-- brackets (up a, down b) first and normalizes the spectator to 1.
-- These local columns compute the same operations at the reviewed
-- right-associated boundary and on arbitrary label lists.
theorem lower_column {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B)
    (rs : List (Complex × RDot u v)) (x : D) :
    ev (atLeft (up d) (.mixedMultiplication u v a b rs)) (vector x) =
      (rs.map fun (c,r) => c • Finsupp.single (mid u v (r.element * v.toHom x)) 1).sum := by
  have eq := atLeft_pair (up d) (.mixedMultiplication u v a b rs) 1 x 1
  change ev (atLeft (up d) (.mixedMultiplication u v a b rs)) (vector x) = _ at eq
  rw [eq]
  let act := (Diagram.associate (R := Complex) (down u) (up v) (up d)).eval.toLinearMap.comp
    ((Biset.pairLinear Complex (tensor (down u) (up v)).basis (up d).basis).flip
      (Finsupp.single 1 1))
  change act ((ScopedDiagram.linearCombination (rs.map fun (c,r) =>
    (c, .ordinary (Diagram.mixedMultiplication u v a b r)))).eval.toLinearMap
      (Finsupp.single ((up a).basis.pair (down b).basis 1 x) 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨c,r⟩ _
  simp only [Function.comp_apply, map_smul]
  congr 1
  change act ((Generator.mixedMultiplication u v a b r Complex).toLinearMap
    (Finsupp.single ((up a).basis.pair (down b).basis 1 x) 1)) = _
  rw [Generator.mixedMultiplication, Biset.Hom.ofFunction_single]
  change act (Finsupp.single (Generator.mixedPair u v (u.toHom 1 * r.element * v.toHom x)) 1) = _
  rw [map_one, one_mul]
  simp only [act, LinearMap.comp_apply, LinearMap.flip_apply]
  rw [Biset.pairLinear_single, one_mul]
  exact Diagram.eval_associate_single (R := Complex) (down u) (up v) (up d) (r.element * v.toHom x) 1 1 1

theorem middle_column {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (ts : List (Complex × TDot v w)) (z : B) :
    ev (horizontal (straight (down u)) (.parallelUp v d w d ts))
      (Finsupp.single (mid u v z) 1) =
      (ts.map fun (c,t) => c • Finsupp.single (mid u w (z * t.element)) 1).sum := by
  let vword := tensor (up v) (up d)
  let wword := tensor (up w) (up d)
  let act := Biset.pairLinear Complex (down u).basis wword.basis (Finsupp.single z 1)
  let terms := ts.map fun (c,t) =>
    (c, ScopedDiagram.ordinary (Diagram.parallelUp (R := Complex) v d w d t))
  change ((Diagram.id (R := Complex) (down u)).eval.horizontal
    (ScopedDiagram.linearCombination terms).eval).toLinearMap
      (Finsupp.single ((down u).basis.pair vword.basis z ((up v).basis.pair (up d).basis 1 1)) 1) = _
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply]
  change act ((ScopedDiagram.linearCombination terms).eval.toLinearMap
    (Finsupp.single ((up v).basis.pair (up d).basis 1 1) 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [terms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨c,t⟩ _
  simp only [Function.comp_apply, map_smul]
  congr 1
  change act ((Diagram.splitUp (R := Complex) w d).eval.toLinearMap
    ((Diagram.upDot t).eval.toLinearMap
      ((Diagram.mergeUp v d).eval.toLinearMap (Finsupp.single ((up v).basis.pair (up d).basis 1 1) 1)))) = _
  rw [Diagram.eval_mergeUp_single, map_one, mul_one, Diagram.eval_upDot_single, one_mul,
    Diagram.eval_splitUp_single]
  unfold act
  rw [Biset.pairLinear_single, one_mul]
  congr 1
  have eq := (down u).basis.pair_balance wword.basis t.element z ((up w).basis.pair (up d).basis 1 1)
  change (down u).basis.pair wword.basis (u.toHom 1 * z * t.element⁻¹⁻¹)
    ((up w).basis.pair (up d).basis 1 1) =
    (down u).basis.pair wword.basis z
      ((up w).basis.pair (up d).basis (t.element * 1 * (w.toHom 1)⁻¹) (1 * 1 * (d.toHom 1)⁻¹)) at eq
  simpa only [map_one, one_mul, mul_one, inv_one, inv_inv] using eq.symm

end
end CaseSixTrivialAux
