import Proofs.ParabolicCaseFiveCoefficientOneExpansion
import Proofs.SupportedLeftOrbitProjectedStabilizer
import Proofs.ParabolicRightOrbitMultiplicity
import MackeyDiagrams.IndexedDrawing
import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.MixedIdentities
import MackeyDiagrams.Parallel
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
universe u v w

open MackeyDiagrams
open scoped BigOperators
noncomputable section
namespace CaseFiveCoefficientChange

variable {R : Type v} [CommSemiring R]
variable {K H J : Type u} [Group K] [Group H] [Group J]

def castCoeffs (X : Type u) (R : Type v) [CommSemiring R] :
    (X →₀ ℕ) →+ (X →₀ R) :=
  Finsupp.mapRange.addMonoidHom (Nat.castRingHom R).toAddMonoidHom

@[simp] theorem castCoeffs_apply {X : Type u} (m : X →₀ ℕ) (x : X) :
    castCoeffs X R m x = (m x : R) := rfl

@[simp] theorem castCoeffs_single {X : Type u} (x : X) (n : ℕ) :
    castCoeffs X R (Finsupp.single x n) = Finsupp.single x (n : R) := by
  classical
  ext y
  by_cases h : x = y <;> simp [h]

def Compatible {X Y : Biset K H} (f : Biset.Hom ℕ X Y) (g : Biset.Hom R X Y) : Prop :=
  ∀ m, castCoeffs Y.carrier R (f.toLinearMap m) =
    g.toLinearMap (castCoeffs X.carrier R m)

theorem compatible_id (X : Biset K H) :
    Compatible (Biset.Hom.id X) (Biset.Hom.id (R := R) X) := fun _ => rfl

theorem compatible_function {X Y : Biset K H} (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x)) :
    Compatible (Biset.Hom.ofFunction f hf) (Biset.Hom.ofFunction (R := R) f hf) := by
  intro m
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single x n => simp

theorem cast_transferBasis {X Y : Biset K H} (f : X.carrier → Y.carrier)
    (finite : ∀ y, Set.Finite {x | f x = y}) (y : Y.carrier) :
    castCoeffs X.carrier R (Biset.Hom.transferBasis ℕ f finite y) =
      Biset.Hom.transferBasis R f finite y := by
  classical
  rw [Biset.Hom.transferBasis_sum, Biset.Hom.transferBasis_sum, map_sum]
  exact Finset.sum_congr rfl (fun x _ => by simp)

theorem compatible_transfer {X Y : Biset K H} (f : X.carrier → Y.carrier)
    (hf : ∀ g x, f (X.act g x) = Y.act g (f x))
    (finite : ∀ y, Set.Finite {x | f x = y}) :
    Compatible (Biset.Hom.transfer ℕ f hf finite) (Biset.Hom.transfer R f hf finite) := by
  intro m
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y n =>
    classical
    ext x
    simp only [castCoeffs_apply, castCoeffs_single, Biset.Hom.transfer_single,
      Finsupp.smul_apply, smul_eq_mul, Biset.Hom.transferBasis_apply, Nat.cast_mul]
    split <;> simp_all

theorem compatible_vertical {X Y Z : Biset K H}
    {f : Biset.Hom ℕ X Y} {f' : Biset.Hom R X Y}
    {g : Biset.Hom ℕ Y Z} {g' : Biset.Hom R Y Z}
    (hf : Compatible f f') (hg : Compatible g g') :
    Compatible (f.vertical g) (f'.vertical g') := by
  intro m
  change castCoeffs Z.carrier R (g.toLinearMap (f.toLinearMap m)) =
    g'.toLinearMap (f'.toLinearMap (castCoeffs X.carrier R m))
  rw [hg, hf]

private theorem castCoeffs_pairLinear (X : Biset K H) (Y : Biset H J)
    (m : X.carrier →₀ ℕ) (n : Y.carrier →₀ ℕ) :
    castCoeffs (X.tensor Y).carrier R (Biset.pairLinear ℕ X Y m n) =
      Biset.pairLinear R X Y (castCoeffs X.carrier R m) (castCoeffs Y.carrier R n) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single x a =>
    induction n using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single y b => simp [Nat.cast_mul]

theorem compatible_horizontal {X X' : Biset K H} {Y Y' : Biset H J}
    {f : Biset.Hom ℕ X X'} {f' : Biset.Hom R X X'}
    {g : Biset.Hom ℕ Y Y'} {g' : Biset.Hom R Y Y'}
    (hf : Compatible f f') (hg : Compatible g g') :
    Compatible (f.horizontal g) (f'.horizontal g') := by
  intro m
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single z n =>
    refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
    change castCoeffs _ R ((f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) n)) =
      (f'.horizontal g').toLinearMap (castCoeffs _ R (Finsupp.single (X.pair Y x y) n))
    have hsmul (m : (X'.tensor Y').carrier →₀ ℕ) :
        castCoeffs _ R (n • m) = (n : R) • castCoeffs _ R m := by
      ext w
      simp [smul_eq_mul]
    rw [castCoeffs_single, Biset.Hom.horizontal_single, Biset.Hom.horizontal_single,
      hsmul, castCoeffs_pairLinear, hf, hg, castCoeffs_single, castCoeffs_single, Nat.cast_one]

theorem compatible_entry {X Y : Biset K H} {f : Biset.Hom ℕ X Y}
    {g : Biset.Hom R X Y} (h : Compatible f g) (x : X.carrier) (y : Y.carrier) :
    g.toLinearMap (Finsupp.single x 1) y =
      (f.toLinearMap (Finsupp.single x 1) y : R) := by
  simpa using (DFunLike.congr_fun (h (Finsupp.single x 1)) y).symm

variable {U : Type u} [Group U]

local notation "evalD" => fun d => ScopedDiagram.eval (LabelledDrawing.interpret d)

theorem compatible_draw_id {A B : Subgroup U} (p : Word A B) :
    Compatible (evalD (LabelledDrawing.ordinary (Diagram.id (R := ℕ) p)))
      (evalD (LabelledDrawing.ordinary (Diagram.id (R := R) p))) :=
  compatible_id _

theorem compatible_draw_associate {A B C D : Subgroup U}
    (p : Word A B) (q : Word B C) (r : Word C D) :
    Compatible (evalD (LabelledDrawing.ordinary (Diagram.associate (R := ℕ) p q r)))
      (evalD (LabelledDrawing.ordinary (Diagram.associate (R := R) p q r))) :=
  compatible_function _ (by
    intro g w
    refine Quotient.inductionOn w (fun ⟨xy, z⟩ => ?_)
    exact Quotient.inductionOn xy (fun _ => rfl))

theorem compatible_draw_unassociate {A B C D : Subgroup U}
    (p : Word A B) (q : Word B C) (r : Word C D) :
    Compatible (evalD (LabelledDrawing.ordinary (Diagram.unassociate (R := ℕ) p q r)))
      (evalD (LabelledDrawing.ordinary (Diagram.unassociate (R := R) p q r))) :=
  compatible_function _ (by
    intro g w
    refine Quotient.inductionOn w (fun ⟨x, yz⟩ => ?_)
    exact Quotient.inductionOn yz (fun _ => rfl))

theorem compatible_draw_vertical {A B : Subgroup U} {p q t : Word A B}
    {d : LabelledDrawing ℕ p q} {e : LabelledDrawing ℕ q t}
    {d' : LabelledDrawing R p q} {e' : LabelledDrawing R q t}
    (hd : Compatible (evalD d) (evalD d')) (he : Compatible (evalD e) (evalD e')) :
    Compatible (evalD (d.vertical e)) (evalD (d'.vertical e')) :=
  compatible_vertical hd he

theorem compatible_draw_horizontal {A B C : Subgroup U}
    {p p' : Word A B} {q q' : Word B C}
    {d : LabelledDrawing ℕ p p'} {e : LabelledDrawing ℕ q q'}
    {d' : LabelledDrawing R p p'} {e' : LabelledDrawing R q q'}
    (hd : Compatible (evalD d) (evalD d')) (he : Compatible (evalD e) (evalD e')) :
    Compatible (evalD (d.horizontal e)) (evalD (d'.horizontal e')) :=
  compatible_horizontal hd he

private theorem eval_unit_label {A B : Subgroup U} {p q : Word A B}
    (d : ScopedDiagram R p q) :
    (ScopedDiagram.linearCombination [(1, d)]).eval = d.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro m
  rw [ScopedDiagram.eval_linearCombination_apply]
  simp

theorem compatible_draw_multiplication {A B C D : Subgroup U}
    (a : ConjEmbedding B A) (b : ConjEmbedding C A)
    (i : ConjEmbedding D B) (j : ConjEmbedding D C) (d : Dot (a.comp i) (b.comp j)) :
    Compatible (evalD (LabelledDrawing.mixedMultiplication (R := ℕ) a b i j [(1,d)]))
      (evalD (LabelledDrawing.mixedMultiplication (R := R) a b i j [(1,d)])) := by
  simp only [LabelledDrawing.interpret, List.map_cons, List.map_nil, eval_unit_label]
  exact compatible_function _ (Generator.mixedMultiplication_equivariant a b i j d)

theorem compatible_draw_projection {A B C D : Subgroup U}
    (a : ConjEmbedding B A) (b : ConjEmbedding C A)
    (i : ConjEmbedding D B) (j : ConjEmbedding D C) (d : ProjectionDot.Mixed a b i j) :
    Compatible (evalD (LabelledDrawing.compactProjection (R := ℕ) a b i j [(1,d)]))
      (evalD (LabelledDrawing.compactProjection (R := R) a b i j [(1,d)])) := by
  simp only [LabelledDrawing.interpret, List.map_cons, List.map_nil, eval_unit_label]
  exact compatible_transfer _ (Generator.mixedMultiplication_equivariant a b i j d.dot) d.finite

theorem compatible_draw_parallel {A B C D : Subgroup U}
    (a : ConjEmbedding B A) (b : ConjEmbedding D B)
    (c : ConjEmbedding C A) (d : ConjEmbedding D C) (t : Dot (a.comp b) (c.comp d)) :
    Compatible (evalD (LabelledDrawing.parallelUp (R := ℕ) a b c d [(1,t)]))
      (evalD (LabelledDrawing.parallelUp (R := R) a b c d [(1,t)])) := by
  simp only [LabelledDrawing.interpret, List.map_cons, List.map_nil, eval_unit_label]
  apply compatible_vertical (compatible_vertical (compatible_function _ ?_) (compatible_function _ ?_))
    (compatible_function _ ?_)
  · intro g z
    refine Quotient.inductionOn z (fun x => ?_)
    rcases g with ⟨g,h⟩
    change (g * x.1 * (a.toHom 1)⁻¹) * a.toHom (1 * x.2 * (b.toHom h)⁻¹) =
      g * (x.1 * a.toHom x.2) * (a.toHom (b.toHom h))⁻¹
    simp [mul_assoc]
  · rintro ⟨g,h⟩ x
    change (g * x * ((a.comp b).toHom h)⁻¹) * t.element =
      g * (x * t.element) * ((c.comp d).toHom h)⁻¹
    have ht : ((a.comp b).toHom h)⁻¹ * t.element = t.element * ((c.comp d).toHom h)⁻¹ := by
      simpa using t.intertwines h⁻¹
    simp only [mul_assoc, ht]
  · rintro ⟨g,h⟩ x
    let X := Biset.induction c
    let Y := Biset.induction d
    change X.pair Y (g * x * (c.toHom (d.toHom h))⁻¹) 1 =
      X.pair Y (g * x * (c.toHom 1)⁻¹) (1 * 1 * (d.toHom h)⁻¹)
    simpa [X, Y, Biset.induction] using X.pair_balance Y (d.toHom h)⁻¹ (g*x) 1

theorem integral_support {X Y : Biset K H} {n : Biset.Hom ℕ X Y}
    {i : Biset.Hom (ULift.{v} Int) X Y} {c : Biset.Hom Complex X Y}
    (hi : Compatible n i) (hc : Compatible n c) (x : X.carrier) (y : Y.carrier) :
    i.toLinearMap (Finsupp.single x 1) y ≠ 0 ↔
      c.toLinearMap (Finsupp.single x 1) y ≠ 0 := by
  rw [compatible_entry hi, compatible_entry hc]
  have h (k : ℕ) : (k : ULift.{v} Int) = 0 ↔ k = 0 := by
    constructor
    · intro hk
      exact Nat.cast_eq_zero.mp (show (k : Int) = 0 from congrArg ULift.down hk)
    · rintro rfl
      exact Nat.cast_zero
  rw [ne_eq, ne_eq, h, Nat.cast_eq_zero]

theorem transport_entry {X Y : Biset K H} {n : Biset.Hom ℕ X Y}
    {c : Biset.Hom Complex X Y} {r : Biset.Hom R X Y}
    (hc : Compatible n c) (hr : Compatible n r) (x : X.carrier) (y : Y.carrier)
    (m : ℕ) (hm : c.toLinearMap (Finsupp.single x 1) y = (m : Complex)) :
    r.toLinearMap (Finsupp.single x 1) y = (m : R) := by
  rw [compatible_entry hc] at hm
  rw [compatible_entry hr, Nat.cast_inj.mp hm]

theorem transport_indexed {A B : Subgroup U} {p q : Word A B} {ι : Type*}
    {n : Biset.Hom ℕ p.basis q.basis} {c : Biset.Hom Complex p.basis q.basis}
    {r : Biset.Hom R p.basis q.basis}
    (hc : Compatible n c) (hr : Compatible n r)
    (termsN : ι → LabelledDrawing ℕ p q)
    (termsC : ι → LabelledDrawing Complex p q)
    (termsR : ι → LabelledDrawing R p q) (s : Finset ι)
    (hC : ∀ j ∈ s, Compatible (evalD (termsN j)) (evalD (termsC j)))
    (hR : ∀ j ∈ s, Compatible (evalD (termsN j)) (evalD (termsR j)))
    (h : c.toLinearMap = (IndexedDrawing.mk s termsC).eval) :
    r.toLinearMap = (IndexedDrawing.mk s termsR).eval := by
  classical
  apply Finsupp.lhom_ext
  intro x a
  rw [← Finsupp.smul_single_one x a, map_smul, map_smul]
  congr 1
  ext y
  have hcomplex := DFunLike.congr_fun (LinearMap.congr_fun h (Finsupp.single x 1)) y
  rw [IndexedDrawing.eval_apply, Finset.sum_apply', compatible_entry hc] at hcomplex
  have hcomplexSum :
      (∑ j ∈ s, (evalD (termsC j)).toLinearMap (Finsupp.single x 1) y) =
        ((∑ j ∈ s, (evalD (termsN j)).toLinearMap (Finsupp.single x 1) y : ℕ) : Complex) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun j hj => compatible_entry (hC j hj) x y)
  change _ = ∑ j ∈ s, (evalD (termsC j)).toLinearMap (Finsupp.single x 1) y at hcomplex
  rw [hcomplexSum] at hcomplex
  rw [IndexedDrawing.eval_apply, Finset.sum_apply', compatible_entry hr, Nat.cast_inj.mp hcomplex, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun j hj => (compatible_entry (hR j hj) x y).symm)


section ExactComposites
variable {G A D F C E : Subgroup U}
  (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
  (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)

private def drawId (R : Type v) [CommSemiring R] {K H : Subgroup U} (p : Word K H) :=
  MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := R) p)

private def rightSingleton (R : Type v) [CommSemiring R] {B' : Subgroup U}
    (i : ConjEmbedding B' A) (j : ConjEmbedding B' F) (k : ConjEmbedding B' C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j))
    (finite : ∀ z, Set.Finite {p | Generator.mixedMultiplicationBasis b d i j r p = z}) :
    LabelledDrawing R ((Word.up a).tensor ((Word.down b).tensor (.up d)))
      ((Word.up c).tensor ((Word.down e).tensor (.up f))) :=
  let up := @Word.up U _
  let down := @Word.down U _
  let ga := up a
  let gc := up c
  let ai := up i
  let fj := down j
  let ck := up k
  let lower := MackeyDiagrams.LabelledDrawing.compactProjection b d i j [(1, ⟨r, finite⟩)]
  let middle := MackeyDiagrams.LabelledDrawing.parallelUp a i c k [(1,t)]
  let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j [(1,s)]
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal (drawId R ga) lower)
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal middle (drawId R fj))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
          (MackeyDiagrams.LabelledDrawing.horizontal (drawId R gc) upper))))

private def leftSingleton (R : Type v) [CommSemiring R] {B : Subgroup U}
    (u : ConjEmbedding G B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (r : Dot (u.comp a) (v.comp b)) (t : Dot (v.comp d) (w.comp f))
    (s : Dot (u.comp c) (w.comp e))
    (finite : ∀ z, Set.Finite {p | Generator.mixedMultiplicationBasis u w c e s p = z}) :
    LabelledDrawing R ((Word.up a).tensor ((Word.down b).tensor (.up d)))
      ((Word.up c).tensor ((Word.down e).tensor (.up f))) :=
  let up := @Word.up U _
  let down := @Word.down U _
  let ga := up a
  let ad := down b
  let df := up d
  let gc := up c
  let ce := down e
  let ef := up f
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

theorem exact_right_composite {B' : Subgroup U}
    (i : ConjEmbedding B' A) (j : ConjEmbedding B' F) (k : ConjEmbedding B' C)
    (r : Dot (b.comp i) (d.comp j)) (t : Dot (a.comp i) (c.comp k))
    (s : Dot (e.comp k) (f.comp j))
    (finite : ∀ z, Set.Finite {p | Generator.mixedMultiplicationBasis b d i j r p = z}) :
    Compatible (evalD (rightSingleton a b d c e f ℕ i j k r t s finite))
      (evalD (rightSingleton a b d c e f R i j k r t s finite)) := by
  unfold rightSingleton drawId
  refine compatible_draw_vertical (compatible_draw_horizontal (compatible_draw_id _) ?_) 
    (compatible_draw_vertical (compatible_draw_unassociate _ _ _)
      (compatible_draw_vertical (compatible_draw_horizontal ?_ (compatible_draw_id _))
        (compatible_draw_vertical (compatible_draw_associate _ _ _)
          (compatible_draw_horizontal (compatible_draw_id _) ?_))))
  · exact compatible_draw_projection _ _ _ _ _
  · exact compatible_draw_parallel _ _ _ _ _
  · exact compatible_draw_multiplication _ _ _ _ _


theorem exact_left_composite {B : Subgroup U}
    (u : ConjEmbedding G B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (r : Dot (u.comp a) (v.comp b)) (t : Dot (v.comp d) (w.comp f))
    (s : Dot (u.comp c) (w.comp e))
    (finite : ∀ z, Set.Finite {p | Generator.mixedMultiplicationBasis u w c e s p = z}) :
    Compatible (evalD (leftSingleton a b d c e f ℕ u v w r t s finite))
      (evalD (leftSingleton a b d c e f R u v w r t s finite)) := by
  unfold leftSingleton drawId
  refine compatible_draw_vertical (compatible_draw_unassociate _ _ _)
    (compatible_draw_vertical (compatible_draw_horizontal ?_ (compatible_draw_id _))
      (compatible_draw_vertical (compatible_draw_associate _ _ _)
        (compatible_draw_vertical (compatible_draw_horizontal (compatible_draw_id _) ?_)
          (compatible_draw_vertical (compatible_draw_unassociate _ _ _)
            (compatible_draw_vertical (compatible_draw_horizontal ?_ (compatible_draw_id _))
              (compatible_draw_associate _ _ _))))))
  · exact compatible_draw_multiplication _ _ _ _ _
  · exact compatible_draw_parallel _ _ _ _ _
  · exact compatible_draw_projection _ _ _ _ _


end ExactComposites

end CaseFiveCoefficientChange


open MackeyDiagrams
noncomputable section
namespace CaseFiveOrbitGlue

theorem projected_smul_left
    {U : Type u} [Group U] {G F : Subgroup U} {P : Type u} [MulAction (G × F) P]
    (g : G) (z : P) :
    (MulAction.stabilizer (G × F) ((g, (1 : F)) • z)).map
        (F.subtype.comp (MonoidHom.snd G F)) =
      (MulAction.stabilizer (G × F) z).map (F.subtype.comp (MonoidHom.snd G F)) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map]
  congr 1
  ext q
  simp [MonoidHom.comp_apply, MulAut.conj_apply]

private abbrev word {U : Type u} [Group U] {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :=
  (Word.up a).tensor ((Word.down b).tensor (.up d))

private abbrev point {U : Type u} [Group U] {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (g : G) (x : D) : (word a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis g (Generator.mixedPair b d x)

theorem point_surjective {U : Type u} [Group U] {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (z : (word a b d).basis.carrier) : ∃ g x, point a b d g x = z := by
  obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective y
  exact ⟨g, x, rfl⟩

theorem act_point_left {U : Type u} [Group U] {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (g h : G) (x : D) :
    (word a b d).basis.act (g, 1) (point a b d h x) = point a b d (g * h) x := by
  change (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    (g * h * (a.toHom 1)⁻¹)
    ((Biset.restriction b).pair (Biset.induction d)
      (b.toHom 1 * x * (1 : D)⁻¹) (1 * 1 * (d.toHom 1)⁻¹)) =
    point a b d (g * h) x
  simp [point, Generator.mixedPair]

theorem normalize_with_projection {U : Type u} [Group U] {G A D F C E : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E) :
    let X := (word a b d).basis
    let Y := (word c e f).basis
    let Pair := X.carrier × Y.carrier
    letI : MulAction (G × F) Pair :=
      { smul := fun q z => (X.act q z.1, Y.act q z.2)
        one_smul := fun z => Prod.ext (X.one_act z.1) (Y.one_act z.2)
        mul_smul := fun q q' z => Prod.ext (X.mul_act q q' z.1) (Y.mul_act q q' z.2) }
    let projected := fun z : Pair =>
      (MulAction.stabilizer (G × F) z).map (F.subtype.comp (MonoidHom.snd G F))
    ∀ z : Pair, ∃ (r : D) (t : G) (s : E),
      let z₀ : Pair := (point a b d 1 r, point c e f t s)
      MulAction.orbit (G × F) z₀ = MulAction.orbit (G × F) z ∧
        projected z₀ = projected z := by
  intro X Y Pair projected z
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (X.act q z.1, Y.act q z.2)
      one_smul := fun z => Prod.ext (X.one_act z.1) (Y.one_act z.2)
      mul_smul := fun q q' z => Prod.ext (X.mul_act q q' z.1) (Y.mul_act q q' z.2) }
  obtain ⟨x,y⟩ := z
  obtain ⟨g,r,rfl⟩ := point_surjective a b d x
  obtain ⟨h,s,rfl⟩ := point_surjective c e f y
  let z : Pair := (point a b d g r, point c e f h s)
  let q : G × F := (g⁻¹, 1)
  let z₀ : Pair := (point a b d 1 r, point c e f (g⁻¹ * h) s)
  have hn : q • z = z₀ := by
    change ((word a b d).basis.act (g⁻¹, 1) (point a b d g r),
      (word c e f).basis.act (g⁻¹, 1) (point c e f h s)) = _
    rw [act_point_left, act_point_left, inv_mul_cancel]
  refine ⟨r, g⁻¹ * h, s, ?_⟩
  change MulAction.orbit (G × F) z₀ = MulAction.orbit (G × F) z ∧ projected z₀ = projected z
  rw [← hn]
  exact ⟨MulAction.orbit_eq_iff.mpr ⟨q, rfl⟩, projected_smul_left g⁻¹ z⟩

def support_equiv {M : Type u} {G : Type u} [Group G] [MulAction G M]
    (intSupport complexSupport : M → Prop) (h : ∀ z, intSupport z ↔ complexSupport z) :
    let Orbits := ↥(Set.range (MulAction.orbit G : M → Set M))
    let S : Set Orbits := {O | ∃ z ∈ O.val, intSupport z}
    let SC : Set (Set M) := {O | ∃ z, O = MulAction.orbit G z ∧ complexSupport z}
    ↥S ≃ ↥SC := by
  intro Orbits S SC
  refine
    { toFun := fun O => ⟨O.val.val, ?_⟩
      invFun := fun O => ⟨⟨O.val, ?_⟩, ?_⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  · obtain ⟨z, hz, hzi⟩ := O.property
    obtain ⟨p, hp⟩ := O.val.property
    have hz' : z ∈ MulAction.orbit G p := hp.symm ▸ hz
    exact ⟨z, hp.symm.trans (MulAction.orbit_eq_iff.mpr hz').symm, (h z).mp hzi⟩
  · obtain ⟨z, hz, _⟩ := O.property
    exact ⟨z, hz.symm⟩
  · obtain ⟨z, hz, hzc⟩ := O.property
    exact ⟨z, hz.symm ▸ MulAction.mem_orbit_self z, (h z).mpr hzc⟩

end CaseFiveOrbitGlue

open MackeyDiagrams
open scoped BigOperators
noncomputable section
namespace CaseFiveIndexedOrbitSum

theorem indexed_of_orbit_indicators
    {U : Type u} [Group U] {A B : Subgroup U} {p q : Word A B}
    {R : Type v} [CommSemiring R] {G : Type w} [Group G]
    [MulAction G (p.basis.carrier × q.basis.carrier)]
    (left : Biset.Hom R p.basis q.basis)
    (support : (p.basis.carrier × q.basis.carrier) → Prop)
    (invariant : ∀ z w, w ∈ MulAction.orbit G z → (support z ↔ support w))
    (left_entry : ∀ z : p.basis.carrier × q.basis.carrier,
      left.toLinearMap (Finsupp.single z.1 1) z.2 =
        @ite R (support z) (Classical.propDecidable _) 1 0) :
    let Pair := p.basis.carrier × q.basis.carrier
    let Orbits := ↥(Set.range (MulAction.orbit G : Pair → Set Pair))
    let S : Set Orbits := {O | ∃ z ∈ O.val, support z}
    ∀ [Finite ↥S] (terms : ↥S → LabelledDrawing R p q),
      (∀ (O : ↥S) (z : Pair),
        (terms O).interpret.eval.toLinearMap (Finsupp.single z.1 1) z.2 =
          @ite R (z ∈ O.val.val) (Classical.propDecidable _) 1 0) →
      ∃ expansion : IndexedDrawing R p q ↥S,
        (∀ O, O ∈ expansion.indices) ∧ expansion.summand = terms ∧
          left.toLinearMap = expansion.eval := by
  classical
  intro Pair Orbits S finite terms hit
  letI : Fintype ↥S := Fintype.ofFinite _
  let expansion : IndexedDrawing R p q ↥S := ⟨Finset.univ, terms⟩
  refine ⟨expansion, fun _ => Finset.mem_univ _, rfl, ?_⟩
  apply Finsupp.lhom_ext
  intro x r
  rw [← Finsupp.smul_single_one x r, map_smul, map_smul]
  congr 1
  ext y
  let z : Pair := (x,y)
  rw [IndexedDrawing.eval_apply, Finset.sum_apply']
  change left.toLinearMap (Finsupp.single z.1 1) z.2 =
    ∑ O : ↥S, (terms O).interpret.eval.toLinearMap (Finsupp.single z.1 1) z.2
  simp_rw [left_entry, hit]
  have property_on (O : ↥S) (hz : z ∈ O.val.val) : support z := by
    obtain ⟨w, hw, hs⟩ := O.property
    obtain ⟨c, hc⟩ := O.val.property
    exact (invariant c z (hc.symm ▸ hz)).mp ((invariant c w (hc.symm ▸ hw)).mpr hs)
  by_cases hz : support z
  · let O : ↥S := ⟨⟨MulAction.orbit G z, ⟨z,rfl⟩⟩, ⟨z, MulAction.mem_orbit_self z, hz⟩⟩
    rw [ite_eq_left hz, Finset.sum_eq_single O]
    · exact (ite_eq_left (MulAction.mem_orbit_self z)).symm
    · intro O' _ hne
      apply ite_eq_right
      intro hz'
      obtain ⟨w, hw⟩ := O'.val.property
      have hOrbit : MulAction.orbit G z = MulAction.orbit G w :=
        MulAction.orbit_eq_iff.mpr (hw.symm ▸ hz')
      exact hne (Subtype.ext (Subtype.ext (hw.symm.trans hOrbit.symm)))
    · simp
  · rw [ite_eq_right hz, Finset.sum_eq_zero]
    intro O _
    exact ite_eq_right (fun h => hz (property_on O h))

end CaseFiveIndexedOrbitSum
set_option maxHeartbeats 800000 in
theorem auditedCaseFiveExpansion : (
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
) := by
  classical
  intro Sinf U blockSym parabolic G A D F C E hG hA hD hF hC hE a b d c e f
    up down tensor comp ga ad df gc ce ef bottom top X Y Pair input output pair orbit
    stabilizer projected swaps RightData labels representative Fiber lowerMap finiteFibers
    isInclusion drawId rightDrawing rightDiagramOf LeftUpperFiber leftDiagram Orbits rep P L
    index coefficient entry evaluate B hB u v w r t s finite left S
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (X.act q z.1, Y.act q z.2)
      one_smul := fun z => Prod.ext (X.one_act z.1) (Y.one_act z.2)
      mul_smul := fun q q' z => Prod.ext (X.mul_act q q' z.1) (Y.mul_act q q' z.2) }
  let M := (CaseFiveCoefficientChange.leftSingleton a b d c e f Complex u v w r t s finite).interpret.eval
  let coefficientC := fun (M : Biset.Hom Complex X Y) (z : Pair) =>
    M.toLinearMap (Finsupp.single z.1 (1 : Complex)) z.2
  let entryC := fun (O : Set Pair) (z : Pair) =>
    @ite Complex (z ∈ O) (Classical.propDecidable _) 1 0
  let rightC : {B' : Subgroup U} → (T : RightData B') → finiteFibers T →
      Biset.Hom Complex X Y :=
    fun ⟨i,j,k,rd,td,sd⟩ h =>
      (CaseFiveCoefficientChange.rightSingleton a b d c e f Complex i j k rd td sd h).interpret.eval
  let leftN := (CaseFiveCoefficientChange.leftSingleton a b d c e f ℕ u v w r t s finite).interpret.eval
  have hc : CaseFiveCoefficientChange.Compatible leftN M :=
    CaseFiveCoefficientChange.exact_left_composite a b d c e f u v w r t s finite
  have hi : CaseFiveCoefficientChange.Compatible leftN (left (ULift Int)).interpret.eval :=
    CaseFiveCoefficientChange.exact_left_composite a b d c e f u v w r t s finite
  have supportEq (z : Pair) :
      coefficient (ULift Int) (evaluate (ULift Int) (left (ULift Int))) z ≠ 0 ↔
      coefficientC M z ≠ 0 :=
    CaseFiveCoefficientChange.integral_support hi hc z.1 z.2
  let supported := fun z => coefficient (ULift Int) (evaluate (ULift Int) (left (ULift Int))) z ≠ 0
  let supportedC := fun z => coefficientC M z ≠ 0
  let SC : Set (Set Pair) := {O | ∃ z, O = orbit z ∧ supportedC z}
  let orbitEquiv : ↥S ≃ ↥SC := CaseFiveOrbitGlue.support_equiv supported supportedC supportEq
  obtain ⟨expC, allC, _, _⟩ :=
    (ParabolicCaseFiveCoefficientOneExpansion G A D F C E hG hA hD hF hC hE a b d c e f).1
      B hB u v w r t s finite
  letI : Finite ↥SC := Finite.of_injective
    (fun O : ↥SC => (⟨O, allC O⟩ : ↥expC.indices))
    (fun _ _ h => congrArg Subtype.val h)
  letI : Finite ↥S := Finite.of_injective orbitEquiv orbitEquiv.injective
  have invariant (z z' : Pair) (hz : z' ∈ orbit z) :
      coefficientC M z' = coefficientC M z :=
    (ParabolicRightOrbitMultiplicity G A D F C E hG hA hD hF hC hE a b d c e f).1 M z z' hz
  obtain ⟨_, _, _, _, _, _, _, _, supportInfo, rightInfo⟩ :=
    SupportedLeftOrbitProjectedStabilizer hG hA hD hF hC hE hB a b d c e f u v w r t s
  have leftOne (z : Pair) (hs : supportedC z) : coefficientC M z = 1 :=
    (supportInfo z hs).2.2.2.2
  have makeTerm (O : ↥S) :
      ∃ (data : RightData (P O.val)) (fin : finiteFibers data),
        parabolic (P O.val) ∧ orbit (representative data) = O.val.val ∧
        projected (representative data) = P O.val ∧ isInclusion data ∧
        ∀ z : Pair, coefficientC (rightC data fin) z =
          entryC O.val.val z := by
    have hRep : orbit (rep O.val) = O.val.val := Classical.choose_spec O.val.property
    have hSup : supportedC (rep O.val) := by
      obtain ⟨z, hz, hs⟩ := O.property
      exact fun he => (supportEq z).mp hs ((invariant (rep O.val) z (hRep.symm ▸ hz)).trans he)
    obtain ⟨r₀, t₀, s₀, hnOrbit, hnProj⟩ :=
      CaseFiveOrbitGlue.normalize_with_projection a b d c e f (rep O.val)
    let z₀ := pair r₀ t₀ s₀
    have hOrb : orbit z₀ = O.val.val := hnOrbit.trans hRep
    have hProj : projected z₀ = P O.val := hnProj
    have hz₀ : supportedC z₀ := by
      intro he
      have hz : z₀ ∈ orbit (rep O.val) := MulAction.orbit_eq_iff.mp hnOrbit
      exact hSup ((invariant (rep O.val) z₀ hz).symm.trans he)
    have hpar := (supportInfo z₀ hz₀).2.2.2.1
    have hpar' : parabolic (projected z₀) := by
      change parabolic ((Subgroup.map (MonoidHom.snd G F) (stabilizer z₀)).map F.subtype) at hpar
      rwa [Subgroup.map_map] at hpar
    obtain ⟨_, _, available⟩ := rightInfo r₀ t₀ s₀ hz₀
    have hPtype : (Subgroup.map (MonoidHom.snd G F) (stabilizer z₀)).map F.subtype = P O.val := by
      rw [Subgroup.map_map]
      exact hProj
    rw [hPtype] at available
    obtain ⟨i, j, k, rd, td, sd, hj, hr, ht, hs, fin, heval⟩ := available
    let data : RightData (P O.val) := ⟨i,j,k,rd,td,sd⟩
    have heq : representative data = z₀ := by
      change pair rd.element td.element sd.element = _
      rw [hr, ht, hs]
    refine ⟨data, fin, hProj ▸ hpar', ?_, ?_, hj, ?_⟩
    · rw [heq, hOrb]
    · rw [heq]
      exact hProj
    · intro z
      rw [← hOrb]
      exact heval z
  choose data fibers hpar horb hproj hincl hcomplex using makeTerm
  refine ⟨fun O => ⟨data O, fibers O⟩, fun O => ⟨hpar O, horb O, hproj O, hincl O⟩, ?_⟩
  intro R instR
  have hR : CaseFiveCoefficientChange.Compatible leftN (left R).interpret.eval :=
    CaseFiveCoefficientChange.exact_left_composite a b d c e f u v w r t s finite
  have hleft (z : Pair) : coefficient R (evaluate R (left R)) z =
      @ite R (supported z) (Classical.propDecidable _) 1 0 := by
    by_cases hz : supported z
    · rw [ite_eq_left hz]
      simpa only [Nat.cast_one] using CaseFiveCoefficientChange.transport_entry hc hR z.1 z.2 1
        (by simpa only [Nat.cast_one] using leftOne z ((supportEq z).mp hz))
    · rw [ite_eq_right hz]
      simpa only [Nat.cast_zero] using CaseFiveCoefficientChange.transport_entry hc hR z.1 z.2 0
        (by simpa only [Nat.cast_zero] using not_not.mp (mt (supportEq z).mpr hz))
  let terms := fun O : ↥S => rightDiagramOf R (data O) (fibers O)
  have htermAux (O : ↥S) (T : RightData (P O.val)) (fin : finiteFibers T)
      (hC : ∀ z, coefficientC (rightC T fin) z =
        entryC O.val.val z) (z : Pair) :
      coefficient R (evaluate R (rightDiagramOf R T fin)) z = entry R O.val.val 1 z := by
    rcases T with ⟨i,j,k,rd,td,sd⟩
    let hn := (CaseFiveCoefficientChange.rightSingleton a b d c e f ℕ i j k rd td sd fin).interpret.eval
    have hcr : CaseFiveCoefficientChange.Compatible hn
        (rightC ⟨i,j,k,rd,td,sd⟩ fin) :=
      CaseFiveCoefficientChange.exact_right_composite a b d c e f i j k rd td sd fin
    have hrr : CaseFiveCoefficientChange.Compatible hn
        (rightDiagramOf R ⟨i,j,k,rd,td,sd⟩ fin).interpret.eval :=
      CaseFiveCoefficientChange.exact_right_composite a b d c e f i j k rd td sd fin
    by_cases hz : z ∈ O.val.val
    · rw [show entry R O.val.val 1 z = 1 from ite_eq_left hz]
      simpa only [Nat.cast_one] using CaseFiveCoefficientChange.transport_entry hcr hrr z.1 z.2 1
        (by simpa only [entryC, ite_eq_left hz, Nat.cast_one] using hC z)
    · rw [show entry R O.val.val 1 z = 0 from ite_eq_right hz]
      simpa only [Nat.cast_zero] using CaseFiveCoefficientChange.transport_entry hcr hrr z.1 z.2 0
        (by simpa only [entryC, ite_eq_right hz, Nat.cast_zero] using hC z)
  have hterm (O : ↥S) (z : Pair) :
      coefficient R (evaluate R (terms O)) z = entry R O.val.val 1 z :=
    htermAux O (data O) (fibers O) (hcomplex O) z
  have supportInvariant (z z' : Pair) (hz : z' ∈ orbit z) : supported z ↔ supported z' :=
    calc
      supported z ↔ supportedC z := supportEq z
      _ ↔ supportedC z' := by
        change (coefficientC M z ≠ 0) ↔ (coefficientC M z' ≠ 0)
        rw [invariant z z' hz]
      _ ↔ supported z' := (supportEq z').symm
  obtain ⟨expansion, all, hsummand, heval⟩ :=
    CaseFiveIndexedOrbitSum.indexed_of_orbit_indicators (G := G × F) (left R).interpret.eval supported
      supportInvariant hleft terms hterm
  exact ⟨expansion, all, fun O => ⟨congrFun hsummand O, fun z => (congrArg (fun d => coefficient R
    (evaluate R d) z) (congrFun hsummand O)).trans (hterm O z)⟩, heval⟩

#print axioms auditedCaseFiveExpansion
