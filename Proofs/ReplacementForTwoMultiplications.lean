import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention

set_option maxHeartbeats 2000000

/-!
Ian Xiao, Theorem 6.5, Cases 3 and 4, archived original p. 24
(SHA-256 bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
and revised published p. 26
(SHA-256 6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
The numbered Cases determine the two directions. The plan provides no
matching numbered Alphabeta Math proof for this endpoint.

The merge–dot–split calculation uses `Diagram.eval_mergeUp_single`,
`Diagram.eval_upDot_single`, `Diagram.eval_splitUp_single` and
`Diagram.mergeUp_splitUp` for arbitrary chosen embeddings. The registered
`InductionRestrictionMergesAndSplits` packages the merge, split and inverse
laws at embeddings presented by explicit conjugators. The shared lemmas
take the boundary embeddings of this theorem directly.

The weighted mixed column uses the multiplication conjunct of
`MixedCrossingFiniteFiberConvention` for the exact `DotLabel`; mixed
projection and the finite-index cup play no role in Cases 3 and 4.
The parallel column expands with `ScopedDiagram.eval_linearCombination_apply`.
Horizontal frames use `Biset.Hom.horizontal_single` and
`Biset.pairLinear_single`, with the reassociation columns
`Diagram.eval_associate_single` and `Diagram.eval_unassociate_single`.
`Generator.mixedEquiv` identifies the resolved target pair with its group
coordinate, and `Biset.associate_unassociate` supplies the structural
inverse at the target. Expanding the three finite supports keeps each
marked vertex in the original drawing and allows repeated products to
combine or cancel in the group algebra.
-/

namespace TwoMultiplicationsAux
open MackeyDiagrams

universe u
variable {U : Type u} [Group U]
variable {G A D F C E B K H J I L : Subgroup U}

private abbrev model {K H : Subgroup U} (p : Word K H) := p.basis.carrier →₀ Complex

private noncomputable abbrev run {p q : Word K H} (drawing : LabelledDrawing Complex p q) :
    model p →ₗ[Complex] model q :=
  drawing.interpret.eval.toLinearMap

private abbrev plain {p q : Word K H} := @LabelledDrawing.ordinary U _ Complex _ K H p q

private abbrev ident (p : Word K H) := plain (Diagram.id p)

private abbrev stack {p q s : Word K H} := @LabelledDrawing.vertical U _ Complex _ K H p q s

private abbrev juxtapose {p p' : Word K H} {q q' : Word H J} :=
  @LabelledDrawing.horizontal U _ Complex _ K H J p p' q q'

private abbrev pair (p : Word K H) (q : Word H J) := p.basis.pair q.basis

private noncomputable def onLastTwo (p : Word K H) {q : Word H J} {s : Word J L}
    {q' : Word H I} {s' : Word I L}
    (crossing : LabelledDrawing Complex (q.tensor s) (q'.tensor s')) :
    LabelledDrawing Complex ((p.tensor q).tensor s) ((p.tensor q').tensor s') :=
  stack (plain (Diagram.associate p q s))
    (stack (juxtapose (ident p) crossing)
      (plain (Diagram.unassociate p q' s')))

private noncomputable abbrev col {K H : Subgroup U} {p : Word K H} (x : p.basis.carrier) :
    model p := Finsupp.single x 1

private theorem run_stack {p q s : Word K H} (f : LabelledDrawing Complex p q)
    (g : LabelledDrawing Complex q s) (x : model p) :
    run (stack f g) x = run g (run f x) := rfl

private theorem firstColumn {p p' : Word K H} {q : Word H J}
    (d : LabelledDrawing Complex p p') (x : p.basis.carrier) (y : q.basis.carrier)
    {ι : Type*} (s : Finset ι) (w : ι → Complex) (z : ι → p'.basis.carrier)
    (hd : run d (col (p := p) x) = ∑ i ∈ s, w i • col (p := p') (z i)) :
    run (juxtapose d (ident q)) (col (p := p.tensor q) (pair p q x y)) =
      ∑ i ∈ s, w i • col (p := p'.tensor q) (pair p' q (z i) y) := by
  change (d.interpret.eval.horizontal (Diagram.id q).eval).toLinearMap _ = _
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply, hd]
  let P := (Biset.pairLinear Complex p'.basis q.basis).flip (col (p := q) y)
  change P (∑ i ∈ s, w i • col (p := p') (z i)) = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  change w i • Biset.pairLinear Complex p'.basis q.basis (Finsupp.single (z i) 1)
    (Finsupp.single y 1) = _
  rw [Biset.pairLinear_single, one_mul]

private theorem lastColumn {p : Word K H} {q : Word H J} {t : Word J L}
    {q' : Word H I} {t' : Word I L}
    (d : LabelledDrawing Complex (q.tensor t) (q'.tensor t'))
    (x : p.basis.carrier) (y : q.basis.carrier) (z : t.basis.carrier)
    {ι : Type*} (s : Finset ι) (w : ι → Complex)
    (y' : ι → q'.basis.carrier) (z' : ι → t'.basis.carrier)
    (hd : run d (col (p := q.tensor t) (pair q t y z)) =
      ∑ i ∈ s, w i • col (p := q'.tensor t') (pair q' t' (y' i) (z' i))) :
    run (onLastTwo p d) (col (p := (p.tensor q).tensor t)
      (pair (p.tensor q) t (pair p q x y) z)) =
      ∑ i ∈ s, w i • col (p := (p.tensor q').tensor t')
        (pair (p.tensor q') t' (pair p q' x (y' i)) (z' i)) := by
  change (Diagram.unassociate (R := Complex) p q' t').eval.toLinearMap
    (((Diagram.id p).eval.horizontal d.interpret.eval).toLinearMap
      ((Diagram.associate (R := Complex) p q t).eval.toLinearMap
        (Finsupp.single (pair (p.tensor q) t (pair p q x y) z) 1))) = _
  rw [Diagram.eval_associate_single, Biset.Hom.horizontal_single, one_smul,
    Diagram.eval_id_apply, hd, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  change w i • (Diagram.unassociate (R := Complex) p q' t').eval.toLinearMap
    (Biset.pairLinear Complex p.basis (q'.tensor t').basis
      (Finsupp.single x 1) (Finsupp.single (pair q' t' (y' i) (z' i)) 1)) = _
  rw [Biset.pairLinear_single, one_mul, Diagram.eval_unassociate_single]

private theorem mixedColumn (a : ConjEmbedding K A) (b : ConjEmbedding H A)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (m : DotLabel Complex (a.comp l) (b.comp r)) (x : K) (y : H) :
    run (LabelledDrawing.mixedMultiplication a b l r m.terms)
      (Finsupp.single (pair (.up l) (.down r) x y) 1) =
      ∑ i ∈ m.support, m i • Finsupp.single
        (pair (.down a) (.up b) (a.toHom x * i.element * b.toHom y) 1) 1 := by
  -- The registered convention supplies the weighted multiplication column.
  -- Its per-term finite-fiber condition belongs to the projection conjunct.
  calc
    _ = (m.terms.map fun term => term.1 • Finsupp.single
        (Generator.mixedMultiplicationBasis a b l r term.2 (pair (.up l) (.down r) x y)) 1).sum :=
      ((MixedCrossingFiniteFiberConvention (U := U)).2.2.1 a b l r m).1
        (pair (.up l) (.down r) x y)
    _ = _ := by
      rw [DotLabel.terms, List.map_map, Finset.sum_map_toList]
      rfl

private theorem parallelColumn (a : ConjEmbedding H A) (b : ConjEmbedding L H)
    (a' : ConjEmbedding J A) (b' : ConjEmbedding L J)
    (m : DotLabel Complex (a.comp b) (a'.comp b')) (x : A) (y : H) :
    run (LabelledDrawing.parallelUp a b a' b' m.terms)
      (Finsupp.single (pair (.up a) (.up b) x y) 1) =
      ∑ i ∈ m.support, m i • Finsupp.single
        (pair (.up a') (.up b') (x * a.toHom y * i.element) 1) 1 := by
  change (ScopedDiagram.linearCombination
    (m.terms.map fun (c,i) => (c, ScopedDiagram.ordinary
      (Diagram.parallelUp (R := Complex) a b a' b' i)))).eval.toLinearMap _ = _
  rw [ScopedDiagram.eval_linearCombination_apply, DotLabel.terms, List.map_map, List.map_map,
    Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro i _
  change m i • (Diagram.splitUp (R := Complex) a' b').eval.toLinearMap
    ((Diagram.upDot i).eval.toLinearMap ((Diagram.mergeUp a b).eval.toLinearMap
      (Finsupp.single (pair (.up a) (.up b) x y) 1))) = _
  rw [Diagram.eval_mergeUp_single, Diagram.eval_upDot_single, Diagram.eval_splitUp_single]

variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev bottom := ((Word.up d).tensor (.up e)).tensor (.down f)
private abbrev top := ((Word.down a).tensor (.up b)).tensor (.up c)
private abbrev bottom' := (Word.up (d.comp e)).tensor (.down f)
private abbrev top' := (Word.down a).tensor (.up (b.comp c))

private noncomputable def split :
    LabelledDrawing Complex (bottom' d e f) (bottom d e f) :=
  juxtapose (.trivalent (.splitUp d e)) (ident (.down f))

private noncomputable def merge :
    LabelledDrawing Complex (top a b c) (top' a b c) :=
  stack (plain (Diagram.associate (.down a) (.up b) (.up c)))
    (juxtapose (ident (.down a)) (.trivalent (.mergeUp b c)))

private theorem splitColumn (g : G) (h : F) :
    run (split d e f) (Finsupp.single (pair (.up (d.comp e)) (.down f) g h) 1) =
      Finsupp.single (pair ((Word.up d).tensor (.up e)) (.down f)
        (pair (.up d) (.up e) g 1) h) 1 := by
  change (Diagram.horizontal (R := Complex) (Diagram.splitUp d e) (Diagram.id (.down f))).eval.toLinearMap _ = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_splitUp_single,
    Diagram.eval_id_apply, Biset.pairLinear_single, one_mul]

private theorem mergeColumn (p q : A) (r : D) :
    run (merge a b c) (Finsupp.single (pair ((Word.down a).tensor (.up b)) (.up c)
      (pair (.down a) (.up b) p q) r) 1) =
      Finsupp.single (Generator.mixedPair a (b.comp c) (p * (q * b.toHom r))) 1 := by
  change (Diagram.horizontal (R := Complex) (Diagram.id (.down a)) (Diagram.mergeUp b c)).eval.toLinearMap
    ((Diagram.associate (.down a) (.up b) (.up c)).eval.toLinearMap
      (Finsupp.single (pair ((Word.down a).tensor (.up b)) (.up c)
        (pair (.down a) (.up b) p q) r) 1)) = _
  rw [Diagram.eval_associate_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, Diagram.eval_mergeUp_single, Biset.pairLinear_single, one_mul]
  congr 1
  apply (Generator.mixedEquiv a (b.comp c)).injective
  change p * (q * b.toHom r) = (p * (q * b.toHom r)) * 1
  rw [mul_one]

private noncomputable def left (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B) (x : DotLabel Complex (d.comp e) (r.comp t))
    (y : DotLabel Complex (s.comp t) (c.comp f))
    (z : DotLabel Complex (a.comp r) (b.comp s)) :
    LabelledDrawing Complex (bottom d e f) (top a b c) :=
  stack (juxtapose (.parallelUp d e r t x.terms) (ident (.down f)))
    (stack (onLastTwo (.up r) (.mixedMultiplication s c t f y.terms))
      (juxtapose (.mixedMultiplication a b r s z.terms) (ident (.up c))))

private noncomputable def right (u' : ConjEmbedding B A) (v : ConjEmbedding C B)
    (w : ConjEmbedding F B) (x : DotLabel Complex (v.comp e) (w.comp f))
    (y : DotLabel Complex (a.comp d) (u'.comp v))
    (z : DotLabel Complex (u'.comp w) (b.comp c)) :
    LabelledDrawing Complex (bottom d e f) (top a b c) :=
  stack (onLastTwo (.up d) (.mixedMultiplication v w e f x.terms))
    (stack (juxtapose (.mixedMultiplication a u' d v y.terms) (ident (.up w)))
      (onLastTwo (.down a) (.parallelUp u' w b c z.terms)))

private noncomputable abbrev combined (drawing : LabelledDrawing Complex (bottom d e f) (top a b c)) :=
  stack (split d e f) (stack drawing (merge a b c))


private abbrev eligible (a b : ConjEmbedding E A) (p : A) :=
  ∀ v : E, a.toHom v * p = p * b.toHom v

private def admissible (M : MonoidAlgebra Complex A) :=
  ∀ p ∈ M.coeff.support, eligible (a.comp (d.comp e)) ((b.comp c).comp f) p

private noncomputable def as
    (drawing : LabelledDrawing Complex (bottom d e f) (top a b c))
    (M : MonoidAlgebra Complex A) :=
  ∀ (g : G) (h : F),
    run (combined a b c d e f drawing)
      (Finsupp.single (pair (.up (d.comp e)) (.down f) g h) 1) =
    Finsupp.mapDomain (Generator.mixedPair a (b.comp c))
      (MonoidAlgebra.single (a.toHom g) 1 * M *
        MonoidAlgebra.single ((b.comp c).toHom h) 1).coeff

private noncomputable def productLabel {α β γ : Type*}
    (X : α →₀ Complex) (Y : β →₀ Complex) (Z : γ →₀ Complex)
    (p : α → β → γ → A) : MonoidAlgebra Complex A :=
  ∑ i ∈ X.support, ∑ j ∈ Y.support, ∑ k ∈ Z.support,
    MonoidAlgebra.single (p i j k) (X i * (Y j * Z k))

private theorem productAdmissible {α β γ : Type*}
    (X : α →₀ Complex) (Y : β →₀ Complex) (Z : γ →₀ Complex) (p : α → β → γ → A)
    (hp : ∀ i j k, eligible (a.comp (d.comp e)) ((b.comp c).comp f) (p i j k)) :
    admissible a b c d e f (productLabel X Y Z p) := by
  classical
  intro x hx
  by_contra hn
  apply Finsupp.mem_support_iff.mp hx
  simp only [productLabel, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  exact Finsupp.single_eq_of_ne (fun he => hn (he ▸ hp i j k))

private theorem productColumn {α β γ : Type*}
    (X : α →₀ Complex) (Y : β →₀ Complex) (Z : γ →₀ Complex) (p : α → β → γ → A)
    (g : G) (h : F) :
    Finsupp.mapDomain (Generator.mixedPair a (b.comp c))
      (MonoidAlgebra.single (a.toHom g) 1 * productLabel X Y Z p *
        MonoidAlgebra.single ((b.comp c).toHom h) 1).coeff =
      ∑ i ∈ X.support, ∑ j ∈ Y.support, ∑ k ∈ Z.support, (X i * (Y j * Z k)) •
        Finsupp.single (Generator.mixedPair a (b.comp c)
          (a.toHom g * p i j k * (b.comp c).toHom h)) 1 := by
  simp only [productLabel, Finset.mul_sum, Finset.sum_mul, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single, one_mul, mul_one, Finsupp.smul_single, smul_eq_mul]

variable (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding E B)
variable (u' : ConjEmbedding B A) (v : ConjEmbedding C B) (w : ConjEmbedding F B)

private def leftTerm (i : Dot (d.comp e) (r.comp t)) (j : Dot (s.comp t) (c.comp f))
    (k : Dot (a.comp r) (b.comp s)) : A :=
  a.toHom i.element * k.element * b.toHom j.element

private def rightTerm (i : Dot (v.comp e) (w.comp f)) (j : Dot (a.comp d) (u'.comp v))
    (k : Dot (u'.comp w) (b.comp c)) : A :=
  j.element * u'.toHom i.element * k.element

private theorem leftEligible (i : Dot (d.comp e) (r.comp t)) (j : Dot (s.comp t) (c.comp f))
    (k : Dot (a.comp r) (b.comp s)) :
    eligible (a.comp (d.comp e)) ((b.comp c).comp f) (leftTerm a b c d e f r s t i j k) := by
  intro x
  have hi := congrArg a.toHom (i.intertwines x)
  have hj := congrArg b.toHom (j.intertwines x)
  have hk := k.intertwines (t.toHom x)
  simp only [map_mul, ConjEmbedding.comp_apply] at hi hj hk ⊢
  unfold leftTerm
  calc
    _ = (a.toHom (d.toHom (e.toHom x)) * a.toHom i.element) * k.element *
        b.toHom j.element := by group
    _ = a.toHom i.element * (a.toHom (r.toHom (t.toHom x)) * k.element) *
        b.toHom j.element := by rw [hi]; group
    _ = a.toHom i.element * k.element * (b.toHom (s.toHom (t.toHom x)) *
        b.toHom j.element) := by rw [hk]; group
    _ = _ := by rw [hj]; group

private theorem rightEligible (i : Dot (v.comp e) (w.comp f)) (j : Dot (a.comp d) (u'.comp v))
    (k : Dot (u'.comp w) (b.comp c)) :
    eligible (a.comp (d.comp e)) ((b.comp c).comp f) (rightTerm a b c d e f u' v w i j k) := by
  intro x
  have hi := congrArg u'.toHom (i.intertwines x)
  have hj := j.intertwines (e.toHom x)
  have hk := k.intertwines (f.toHom x)
  simp only [map_mul, ConjEmbedding.comp_apply] at hi hj hk ⊢
  unfold rightTerm
  calc
    _ = (a.toHom (d.toHom (e.toHom x)) * j.element) * u'.toHom i.element *
        k.element := by group
    _ = j.element * (u'.toHom (v.toHom (e.toHom x)) * u'.toHom i.element) *
        k.element := by rw [hj]; group
    _ = j.element * u'.toHom i.element * (u'.toHom (w.toHom (f.toHom x)) *
        k.element) := by rw [hi]; group
    _ = _ := by rw [hk]; group

private theorem leftAs
    (X : DotLabel Complex (d.comp e) (r.comp t))
    (Y : DotLabel Complex (s.comp t) (c.comp f))
    (Z : DotLabel Complex (a.comp r) (b.comp s)) :
    as a b c d e f (left a b c d e f r s t X Y Z)
      (productLabel X Y Z (leftTerm a b c d e f r s t)) := by
  -- The left shape is the target of the Case 4 replacement. Its parallel
  -- vertex merges, multiplies by its dot and splits with a unit. The two
  -- mixed vertices then push pairs forward.
  intro g h
  unfold left
  unfold combined
  rw [run_stack, run_stack, run_stack, run_stack, splitColumn, productColumn]
  rw [firstColumn (q := .down f) (.parallelUp d e r t X.terms) (pair (.up d) (.up e) g 1) h X.support X
    (fun i => pair (.up r) (.up t) (g * d.toHom 1 * i.element) 1)
    (parallelColumn d e r t X g 1)]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [lastColumn (p := .up r) (.mixedMultiplication s c t f Y.terms) _ 1 h Y.support Y
    (fun j => s.toHom 1 * j.element * c.toHom h) (fun _ => 1)
    (mixedColumn s c t f Y 1 h)]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [firstColumn (q := .up c) (.mixedMultiplication a b r s Z.terms) _ 1 Z.support Z
    (fun k => pair (.down a) (.up b)
      (a.toHom (g * d.toHom 1 * i.element) * k.element *
        b.toHom (s.toHom 1 * j.element * c.toHom h)) 1)
    (mixedColumn a b r s Z (g * d.toHom 1 * i.element) (s.toHom 1 * j.element * c.toHom h))]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mergeColumn]
  simp only [map_one, one_mul, mul_one, smul_smul, leftTerm,
    map_mul, ConjEmbedding.comp_apply, mul_assoc]

private theorem rightAs
    (X : DotLabel Complex (v.comp e) (w.comp f))
    (Y : DotLabel Complex (a.comp d) (u'.comp v))
    (Z : DotLabel Complex (u'.comp w) (b.comp c)) :
    as a b c d e f (right a b c d e f u' v w X Y Z)
      (productLabel X Y Z (rightTerm a b c d e f u' v w)) := by
  -- The right shape is the target of the Case 3 replacement. Its last dot
  -- commutes past the F-coordinate by its own intertwining equation.
  intro g h
  unfold right
  unfold combined
  rw [run_stack, run_stack, run_stack, run_stack, splitColumn, productColumn]
  rw [lastColumn (p := .up d) (.mixedMultiplication v w e f X.terms) g 1 h X.support X
    (fun i => v.toHom 1 * i.element * w.toHom h) (fun _ => 1)
    (mixedColumn v w e f X 1 h)]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [firstColumn (q := .up w) (.mixedMultiplication a u' d v Y.terms) _ 1 Y.support Y
    (fun j => pair (.down a) (.up u')
      (a.toHom g * j.element * u'.toHom (v.toHom 1 * i.element * w.toHom h)) 1)
    (mixedColumn a u' d v Y g (v.toHom 1 * i.element * w.toHom h))]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [lastColumn (p := .down a) (.parallelUp u' w b c Z.terms) _ 1 1 Z.support Z
    (fun k => 1 * u'.toHom 1 * k.element) (fun _ => 1)
    (parallelColumn u' w b c Z 1 1)]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mergeColumn]
  have hk := k.intertwines h
  simp only [ConjEmbedding.comp_apply] at hk
  simp only [map_one, one_mul, mul_one, smul_smul, rightTerm, map_mul,
    ConjEmbedding.comp_apply, mul_assoc, hk]


private noncomputable def flatten {a b : ConjEmbedding E A}
    (label : DotLabel Complex a b) : MonoidAlgebra Complex A :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element label)

private noncomputable def labelFrom {a b : ConjEmbedding E A} (M : MonoidAlgebra Complex A) :
    DotLabel Complex a b :=
  (M.coeff.subtypeDomain (eligible a b)).mapDomain (fun p => ⟨p.val, p.property⟩)

private theorem flatten_labelFrom {a b : ConjEmbedding E A} (M : MonoidAlgebra Complex A)
    (hM : ∀ p ∈ M.coeff.support, eligible a b p) :
    flatten (labelFrom (a := a) (b := b) M) = M := by
  apply MonoidAlgebra.coeff_injective
  change Finsupp.mapDomain Dot.element
    ((M.coeff.subtypeDomain (eligible a b)).mapDomain _) = M.coeff
  rw [← Finsupp.mapDomain_comp]
  change (M.coeff.subtypeDomain (eligible a b)).mapDomain Subtype.val = _
  ext p
  by_cases hp : eligible a b p
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨p, hp⟩
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨⟨q, hq⟩, rfl⟩; exact hp hq)]
    exact (Finsupp.notMem_support_iff.mp (fun h => hp (hM p h))).symm

private theorem flatten_sum {a b : ConjEmbedding E A} (label : DotLabel Complex a b) :
    flatten label = ∑ p ∈ label.support, MonoidAlgebra.single p.element (label p) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.coeff_sum]
  change Finsupp.mapDomain Dot.element label = _
  rfl

private theorem realizeLeft (M : MonoidAlgebra Complex A) (hM : admissible a b c d e f M) :
    ∃ (X : DotLabel Complex (d.comp e) ((d.comp e).comp (ConjEmbedding.id E)))
      (Y : DotLabel Complex ((c.comp f).comp (ConjEmbedding.id E)) (c.comp f))
      (Z : DotLabel Complex (a.comp (d.comp e)) (b.comp (c.comp f))),
      as a b c d e f (left a b c d e f (d.comp e) (c.comp f) (ConjEmbedding.id E) X Y Z) M := by
  -- Case 4 of Theorem 6.5 uses the original E as the middle group. These
  -- coefficient-one unit labels retain their marked vertices.
  let i : Dot (d.comp e) ((d.comp e).comp (ConjEmbedding.id E)) :=
    ⟨1, fun x => by change _ * 1 = 1 * (d.comp e).toHom x; rw [mul_one, one_mul]⟩
  let j : Dot ((c.comp f).comp (ConjEmbedding.id E)) (c.comp f) :=
    ⟨1, fun x => by change (c.comp f).toHom x * 1 = 1 * _; rw [mul_one, one_mul]⟩
  let Z : DotLabel Complex (a.comp (d.comp e)) (b.comp (c.comp f)) := labelFrom M
  refine ⟨Finsupp.single i 1, Finsupp.single j 1, Z, ?_⟩
  have hprod : productLabel (Finsupp.single i 1) (Finsupp.single j 1) Z
      (leftTerm a b c d e f (d.comp e) (c.comp f) (ConjEmbedding.id E)) = M := by
    calc
      _ = flatten Z := by
        rw [flatten_sum]
        simp only [productLabel, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
          Finsupp.single_eq_same, leftTerm, i, j, map_one, one_mul, mul_one]
      _ = M := flatten_labelFrom M hM
  rw [← hprod]
  exact leftAs a b c d e f (d.comp e) (c.comp f) (ConjEmbedding.id E) _ _ _

private theorem realizeRight (M : MonoidAlgebra Complex A) (hM : admissible a b c d e f M) :
    ∃ (X : DotLabel Complex ((a.comp d).comp e) ((b.comp c).comp f))
      (Y : DotLabel Complex (a.comp d) ((ConjEmbedding.id A).comp (a.comp d)))
      (Z : DotLabel Complex ((ConjEmbedding.id A).comp (b.comp c)) (b.comp c)),
      as a b c d e f (right a b c d e f (ConjEmbedding.id A) (a.comp d) (b.comp c) X Y Z) M := by
  -- Case 3 uses A as the middle group and puts the whole eligible
  -- combination on the first mixed vertex. The two other marks stay present.
  let X : DotLabel Complex ((a.comp d).comp e) ((b.comp c).comp f) := labelFrom M
  let j : Dot (a.comp d) ((ConjEmbedding.id A).comp (a.comp d)) :=
    ⟨1, fun x => by change _ * 1 = 1 * (a.comp d).toHom x; rw [mul_one, one_mul]⟩
  let k : Dot ((ConjEmbedding.id A).comp (b.comp c)) (b.comp c) :=
    ⟨1, fun x => by change (b.comp c).toHom x * 1 = 1 * _; rw [mul_one, one_mul]⟩
  refine ⟨X, Finsupp.single j 1, Finsupp.single k 1, ?_⟩
  have hprod : productLabel X (Finsupp.single j 1) (Finsupp.single k 1)
      (rightTerm a b c d e f (ConjEmbedding.id A) (a.comp d) (b.comp c)) = M := by
    calc
      _ = flatten X := by
        rw [flatten_sum]
        simp only [productLabel, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
          Finsupp.single_eq_same, rightTerm, j, k, one_mul, mul_one]
        rfl
      _ = M := flatten_labelFrom M hM
  rw [← hprod]
  exact rightAs a b c d e f (ConjEmbedding.id A) (a.comp d) (b.comp c) _ _ _

private theorem splitRightInverse :
    let S := (split d e f).interpret.eval
    let M := (Diagram.horizontal (R := Complex) (Diagram.mergeUp d e)
      (Diagram.id (.down f))).eval
    M.vertical S = Biset.Hom.id (bottom d e f).basis := by
  dsimp only
  change ((Diagram.mergeUp (R := Complex) d e).eval.horizontal (Diagram.id (.down f)).eval).vertical
    ((Diagram.splitUp d e).eval.horizontal (Diagram.id (.down f)).eval) = _
  rw [Biset.Hom.horizontal_vertical]
  change (((Diagram.mergeUp (R := Complex) d e).vertical (Diagram.splitUp d e)).eval).horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem mergeLeftInverse :
    let M := (merge a b c).interpret.eval
    let S := ((Diagram.horizontal (R := Complex) (Diagram.id (.down a))
      (Diagram.splitUp b c)).vertical (Diagram.unassociate (.down a) (.up b) (.up c))).eval
    M.vertical S = Biset.Hom.id (top a b c).basis := by
  dsimp only
  change ((Biset.associate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex).vertical
    ((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.mergeUp b c).eval)).vertical
    (((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.splitUp b c).eval).vertical
      (Biset.unassociate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex)) = _
  refine Biset.Hom.cancel_middle _ _ _ _ ?_ Biset.associate_unassociate
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id (Word.down a).basis).horizontal
    (((Diagram.mergeUp (R := Complex) b c).vertical (Diagram.splitUp b c)).eval) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem eval_eq_iff
    {D₁ D₂ : LabelledDrawing Complex (bottom d e f) (top a b c)}
    {M N : MonoidAlgebra Complex A}
    (h₁ : as a b c d e f D₁ M) (h₂ : as a b c d e f D₂ N) :
    D₁.interpret.eval = D₂.interpret.eval ↔ M = N := by
  constructor
  · intro he
    -- The merged identity pair detects the multiplier as in Theorem 6.5.
    have hs : run (combined a b c d e f D₁) = run (combined a b c d e f D₂) := by
      change ((split d e f).interpret.eval.vertical
        (D₁.interpret.eval.vertical (merge a b c).interpret.eval)).toLinearMap =
        ((split d e f).interpret.eval.vertical
          (D₂.interpret.eval.vertical (merge a b c).interpret.eval)).toLinearMap
      rw [he]
    have hM := h₁ 1 1
    rw [hs] at hM
    have h := hM.symm.trans (h₂ 1 1)
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.mapDomain_injective (Generator.mixedEquiv a (b.comp c)).symm.injective
    change Finsupp.mapDomain (Generator.mixedPair a (b.comp c)) M.coeff =
      Finsupp.mapDomain (Generator.mixedPair a (b.comp c)) N.coeff
    simpa only [map_one, show MonoidAlgebra.single (1 : A) (1 : Complex) = 1 from rfl,
      one_mul, mul_one] using h
  rintro rfl
  -- Compare the full maps via the inverse boundary maps. Equal columns on
  -- merged pairs suffice by quotient induction and complex linearity.
  have eq : (combined a b c d e f D₁).interpret.eval =
      (combined a b c d e f D₂).interpret.eval := by
    apply Biset.Hom.ext
    apply Finsupp.lhom_ext
    intro z coef
    refine Quotient.inductionOn z fun ⟨g,h⟩ => ?_
    change run (combined a b c d e f D₁)
        (Finsupp.single (pair (.up (d.comp e)) (.down f) g h) coef) =
      run (combined a b c d e f D₂)
        (Finsupp.single (pair (.up (d.comp e)) (.down f) g h) coef)
    have hs : Finsupp.single (pair (.up (d.comp e)) (.down f) g h) coef =
        coef • Finsupp.single (pair (.up (d.comp e)) (.down f) g h) (1 : Complex) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul]
    exact congrArg (fun x : model (top' a b c) => coef • x) ((h₁ g h).trans (h₂ g h).symm)
  let P := (Diagram.horizontal (R := Complex) (Diagram.mergeUp d e)
    (Diagram.id (.down f))).eval
  let Q := ((Diagram.horizontal (R := Complex) (Diagram.id (.down a))
      (Diagram.splitUp b c)).vertical (Diagram.unassociate (.down a) (.up b) (.up c))).eval
  let S := (split d e f).interpret.eval
  let T := (merge a b c).interpret.eval
  change S.vertical (D₁.interpret.eval.vertical T) = S.vertical (D₂.interpret.eval.vertical T) at eq
  have h := congrArg (fun x => (P.vertical x).vertical Q) eq
  change (P.vertical (S.vertical (D₁.interpret.eval.vertical T))).vertical Q =
    (P.vertical (S.vertical (D₂.interpret.eval.vertical T))).vertical Q at h
  have hP : P.vertical S = Biset.Hom.id (bottom d e f).basis := splitRightInverse d e f
  have hQ : T.vertical Q = Biset.Hom.id (top a b c).basis := mergeLeftInverse a b c
  simpa only [← Biset.Hom.vertical_assoc P S, hP, Biset.Hom.id_vertical,
    Biset.Hom.vertical_assoc _ T Q, hQ, Biset.Hom.vertical_id] using h


private theorem quotientReplacement {Left Right Result : Type*}
    (leftEval : Left → Result) (rightEval : Right → Result)
    (hLeft : ∀ l, ∃ r, rightEval r = leftEval l)
    (hRight : ∀ r, ∃ l, leftEval l = rightEval r) :
    ∃ (replaceCase3 : Left → Right) (replaceCase4 : Right → Left)
      (replacement : Quotient (Setoid.ker leftEval) ≃ Quotient (Setoid.ker rightEval)),
      (∀ l, rightEval (replaceCase3 l) = leftEval l ∧
        replacement (Quotient.mk (Setoid.ker leftEval) l) =
          Quotient.mk (Setoid.ker rightEval) (replaceCase3 l)) ∧
      (∀ r, leftEval (replaceCase4 r) = rightEval r ∧
        replacement.symm (Quotient.mk (Setoid.ker rightEval) r) =
          Quotient.mk (Setoid.ker leftEval) (replaceCase4 r)) := by
  classical
  let toRight l := Classical.choose (hLeft l)
  let toLeft r := Classical.choose (hRight r)
  have hr l : rightEval (toRight l) = leftEval l := Classical.choose_spec (hLeft l)
  have hl r : leftEval (toLeft r) = rightEval r := Classical.choose_spec (hRight r)
  let forward : Quotient (Setoid.ker leftEval) → Quotient (Setoid.ker rightEval) :=
    Quotient.map toRight (fun {_ _} h => (hr _).trans (h.trans (hr _).symm))
  let backward : Quotient (Setoid.ker rightEval) → Quotient (Setoid.ker leftEval) :=
    Quotient.map toLeft (fun {_ _} h => (hl _).trans (h.trans (hl _).symm))
  let E : Quotient (Setoid.ker leftEval) ≃ Quotient (Setoid.ker rightEval) :=
    ⟨forward, backward,
      fun x => Quotient.inductionOn x (fun l => Quotient.sound ((hl (toRight l)).trans (hr l))),
      fun x => Quotient.inductionOn x (fun r => Quotient.sound ((hr (toLeft r)).trans (hl r)))⟩
  exact ⟨toRight, toLeft, E, fun l => ⟨hr l, rfl⟩, fun r => ⟨hl r, rfl⟩⟩

end TwoMultiplicationsAux

theorem ReplacementForTwoMultiplications : (
∀ {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
    (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F),
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let eval := fun {K H : Subgroup U} {p q : MackeyDiagrams.Word K H}
      (drawing : MackeyDiagrams.LabelledDrawing Complex p q) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let bc := comp b c
  let de := comp d e
  let bottom := tensor (tensor (up d) (up e)) (down f)
  let top := tensor (tensor (down a) (up b)) (up c)
  let Left := Σ B : Subgroup U,
    Σ r : MackeyDiagrams.ConjEmbedding B G,
    Σ s : MackeyDiagrams.ConjEmbedding B D,
    Σ t : MackeyDiagrams.ConjEmbedding E B,
      MackeyDiagrams.DotLabel Complex de (comp r t) ×
      MackeyDiagrams.DotLabel Complex (comp s t) (comp c f) ×
      MackeyDiagrams.DotLabel Complex (comp a r) (comp b s)
  let Right := Σ B' : Subgroup U,
    Σ u' : MackeyDiagrams.ConjEmbedding B' A,
    Σ v : MackeyDiagrams.ConjEmbedding C B',
    Σ w : MackeyDiagrams.ConjEmbedding F B',
      MackeyDiagrams.DotLabel Complex (comp v e) (comp w f) ×
      MackeyDiagrams.DotLabel Complex (comp a d) (comp u' v) ×
      MackeyDiagrams.DotLabel Complex (comp u' w) bc
  let onLastTwo := fun {K H J J' L : Subgroup U}
      (spectator : MackeyDiagrams.Word K H)
      (p : MackeyDiagrams.Word H J) (q : MackeyDiagrams.Word J L)
      (p' : MackeyDiagrams.Word H J') (q' : MackeyDiagrams.Word J' L)
      (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
    stack (ordinary (MackeyDiagrams.Diagram.associate spectator p q))
      (stack (juxtapose (ordinary (MackeyDiagrams.Diagram.id spectator)) crossing)
        (ordinary (MackeyDiagrams.Diagram.unassociate spectator p' q')))
  let leftDrawing : Left → MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨_, r, s, t, x, y, z⟩ =>
      let first := juxtapose
        (MackeyDiagrams.LabelledDrawing.parallelUp d e r t (MackeyDiagrams.DotLabel.terms x))
        (ordinary (MackeyDiagrams.Diagram.id (down f)))
      let second := onLastTwo (up r) (up t) (down f) (down s) (up c)
        (MackeyDiagrams.LabelledDrawing.mixedMultiplication s c t f (MackeyDiagrams.DotLabel.terms y))
      let third := juxtapose
        (MackeyDiagrams.LabelledDrawing.mixedMultiplication a b r s (MackeyDiagrams.DotLabel.terms z))
        (ordinary (MackeyDiagrams.Diagram.id (up c)))
      stack first (stack second third)
  let rightDrawing : Right → MackeyDiagrams.LabelledDrawing Complex bottom top :=
    fun ⟨_, u', v, w, x, y, z⟩ =>
      let first := onLastTwo (up d) (up e) (down f) (down v) (up w)
        (MackeyDiagrams.LabelledDrawing.mixedMultiplication v w e f (MackeyDiagrams.DotLabel.terms x))
      let second := juxtapose
        (MackeyDiagrams.LabelledDrawing.mixedMultiplication a u' d v (MackeyDiagrams.DotLabel.terms y))
        (ordinary (MackeyDiagrams.Diagram.id (up w)))
      let third := onLastTwo (down a) (up u') (up w) (up b) (up c)
        (MackeyDiagrams.LabelledDrawing.parallelUp u' w b c (MackeyDiagrams.DotLabel.terms z))
      stack first (stack second third)
  let splitBottom : MackeyDiagrams.LabelledDrawing Complex (tensor (up de) (down f)) bottom :=
    juxtapose (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp d e))
      (ordinary (MackeyDiagrams.Diagram.id (down f)))
  let mergeTop : MackeyDiagrams.LabelledDrawing Complex top (tensor (down a) (up bc)) :=
    stack (ordinary (MackeyDiagrams.Diagram.associate (down a) (up b) (up c)))
      (juxtapose (ordinary (MackeyDiagrams.Diagram.id (down a)))
        (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp b c)))
  let admissible := fun (M : MonoidAlgebra Complex A) =>
    ∀ p ∈ Finsupp.support (MonoidAlgebra.coeff M), ∀ v : E,
      MackeyDiagrams.ConjEmbedding.toHom (comp a de) v * p =
        p * MackeyDiagrams.ConjEmbedding.toHom (comp bc f) v
  let evaluatesAs := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top)
      (M : MonoidAlgebra Complex A) =>
    ∀ (g : G) (h : F),
      MackeyDiagrams.Biset.Hom.toLinearMap (eval (stack splitBottom (stack drawing mergeTop)))
        (Finsupp.single
          (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction de)
            (MackeyDiagrams.Biset.restriction f) g h) 1) =
      Finsupp.mapDomain (MackeyDiagrams.Generator.mixedPair a bc)
        (MonoidAlgebra.coeff
          (MonoidAlgebra.single (MackeyDiagrams.ConjEmbedding.toHom a g) 1 *
            M * MonoidAlgebra.single (MackeyDiagrams.ConjEmbedding.toHom bc h) 1))
  let leftEval := fun l : Left => eval (leftDrawing l)
  let rightEval := fun r : Right => eval (rightDrawing r)
  let leftClasses := Setoid.ker leftEval
  let rightClasses := Setoid.ker rightEval
  (∀ l : Left, ∃ M, admissible M ∧ evaluatesAs (leftDrawing l) M) ∧
  (∀ r : Right, ∃ M, admissible M ∧ evaluatesAs (rightDrawing r) M) ∧
  (∀ M, admissible M →
    (∃ l : Left, evaluatesAs (leftDrawing l) M) ∧
    (∃ r : Right, evaluatesAs (rightDrawing r) M)) ∧
  (∃ (replaceCase3 : Left → Right) (replaceCase4 : Right → Left)
      (replacement : Quotient leftClasses ≃ Quotient rightClasses),
    (∀ l : Left, rightEval (replaceCase3 l) = leftEval l ∧
      replacement (Quotient.mk leftClasses l) = Quotient.mk rightClasses (replaceCase3 l)) ∧
    (∀ r : Right, leftEval (replaceCase4 r) = rightEval r ∧
      Equiv.symm replacement (Quotient.mk rightClasses r) = Quotient.mk leftClasses (replaceCase4 r)))
) :=
(by
  intro U _ G A D F C E a b c d e f
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨B, r, s, t, X, Y, Z⟩
    exact ⟨TwoMultiplicationsAux.productLabel X Y Z
        (TwoMultiplicationsAux.leftTerm a b c d e f r s t),
      TwoMultiplicationsAux.productAdmissible a b c d e f X Y Z _
        (TwoMultiplicationsAux.leftEligible a b c d e f r s t),
      TwoMultiplicationsAux.leftAs a b c d e f r s t X Y Z⟩
  · rintro ⟨B, u', v, w, X, Y, Z⟩
    exact ⟨TwoMultiplicationsAux.productLabel X Y Z
        (TwoMultiplicationsAux.rightTerm a b c d e f u' v w),
      TwoMultiplicationsAux.productAdmissible a b c d e f X Y Z _
        (TwoMultiplicationsAux.rightEligible a b c d e f u' v w),
      TwoMultiplicationsAux.rightAs a b c d e f u' v w X Y Z⟩
  · intro M hM
    obtain ⟨Xₗ, Yₗ, Zₗ, hl⟩ := TwoMultiplicationsAux.realizeLeft a b c d e f M hM
    obtain ⟨Xᵣ, Yᵣ, Zᵣ, hr⟩ := TwoMultiplicationsAux.realizeRight a b c d e f M hM
    exact ⟨⟨⟨E, d.comp e, c.comp f, MackeyDiagrams.ConjEmbedding.id E, Xₗ, Yₗ, Zₗ⟩, hl⟩,
      ⟨⟨A, MackeyDiagrams.ConjEmbedding.id A, a.comp d, b.comp c, Xᵣ, Yᵣ, Zᵣ⟩, hr⟩⟩
  · apply TwoMultiplicationsAux.quotientReplacement
    · rintro ⟨B, r, s, t, X, Y, Z⟩
      let M := TwoMultiplicationsAux.productLabel X Y Z
        (TwoMultiplicationsAux.leftTerm a b c d e f r s t)
      have hM : TwoMultiplicationsAux.admissible a b c d e f M :=
        TwoMultiplicationsAux.productAdmissible a b c d e f X Y Z _
          (TwoMultiplicationsAux.leftEligible a b c d e f r s t)
      obtain ⟨X', Y', Z', hr⟩ := TwoMultiplicationsAux.realizeRight a b c d e f M hM
      exact ⟨⟨A, MackeyDiagrams.ConjEmbedding.id A, a.comp d, b.comp c, X', Y', Z'⟩,
        (TwoMultiplicationsAux.eval_eq_iff a b c d e f hr
          (TwoMultiplicationsAux.leftAs a b c d e f r s t X Y Z)).2 rfl⟩
    · rintro ⟨B, u', v, w, X, Y, Z⟩
      let M := TwoMultiplicationsAux.productLabel X Y Z
        (TwoMultiplicationsAux.rightTerm a b c d e f u' v w)
      have hM : TwoMultiplicationsAux.admissible a b c d e f M :=
        TwoMultiplicationsAux.productAdmissible a b c d e f X Y Z _
          (TwoMultiplicationsAux.rightEligible a b c d e f u' v w)
      obtain ⟨X', Y', Z', hl⟩ := TwoMultiplicationsAux.realizeLeft a b c d e f M hM
      exact ⟨⟨E, d.comp e, c.comp f, MackeyDiagrams.ConjEmbedding.id E, X', Y', Z'⟩,
        (TwoMultiplicationsAux.eval_eq_iff a b c d e f hl
          (TwoMultiplicationsAux.rightAs a b c d e f u' v w X Y Z)).2 rfl⟩)
